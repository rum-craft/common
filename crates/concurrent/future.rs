use crate::error::RumResult;

use super::{Thread, ThreadHost};
use std::{
  future::Future,
  sync::{Arc, Mutex},
  task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

pub struct ThreadFuture<T: Send + Clone + 'static> {
  completed: Arc<Mutex<(Option<RumResult<T>>, Option<Waker>)>>,
}

impl<T: Send + Clone> ThreadFuture<T> {
  pub fn new(
    threaded_function: impl (FnOnce(&Thread) -> RumResult<T>) + Send + Sync + 'static,
  ) -> Self {
    if let Some(thread) = Thread::get_thread() {
      let completed = Arc::new(Mutex::new((None, Option::<Waker>::None)));

      let c = completed.clone();

      thread.add_task(move |t| {
        if let Some(thread) = Thread::get_thread() {
          let result = threaded_function(thread);
          match c.lock() {
            Ok(mut t) => {
              t.0 = Some(result);
              if let Some(waker) = t.1.take() {
                waker.wake();
              }
            }
            _ => unreachable!(),
          }
        } else {
          panic!("Thread not initialized!")
        }
      });

      Self { completed }
    } else {
      panic!("Could not acquire global thread");
    }
  }
}

impl<T: Send + Clone> Future for ThreadFuture<T> {
  type Output = RumResult<T>;

  fn poll(
    self: std::pin::Pin<&mut Self>,
    cx: &mut std::task::Context<'_>,
  ) -> std::task::Poll<Self::Output> {
    match self.completed.lock() {
      Ok(mut t) => {
        if let Some(result) = t.0.take() {
          Poll::Ready(result)
        } else {
          t.1 = Some(cx.waker().clone());
          Poll::Pending
        }
      }
      _ => unreachable!(),
    }
  }
}

// -----------------------------------------------------------------------------------------
// Rum Waker
// -----------------------------------------------------------------------------------------

pub(super) struct FutureJobWaker {
  future_id: usize,
  thread:    *const Thread,
}

impl FutureJobWaker {
  const VIRTUAL_FUNCTION_TABLE: RawWakerVTable = FutureJobWaker::get_vtable();

  /// Creates a new Waker within the local thread.
  pub fn new(future_id: usize, thread: &Thread) -> Waker {
    unsafe { Waker::from_raw(FutureJobWaker::new_raw(future_id, thread)) }
  }

  fn new_raw(future_id: usize, thread: &Thread) -> RawWaker {
    let waker = Box::new(FutureJobWaker { thread: thread as *const _, future_id });

    let waker_ptr = Box::into_raw(waker);

    RawWaker::new(waker_ptr as *const _, &Self::VIRTUAL_FUNCTION_TABLE)
  }

  unsafe fn drop(rw: *const ()) {
    let rw = rw as *mut RawWaker;
    let _ = Box::from_raw(rw);
  }

  /// This function will be called when `wake` is called on the [`Waker`].
  /// It must wake up the task associated with this [`RawWaker`].
  ///
  /// The implementation of this function must make sure to release any
  /// resources that are associated with this instance of a [`RawWaker`] and
  /// associated task.
  ///
  /// Think `fn wake(self)`
  unsafe fn wake(rw: *const ()) {
    Self::wake_by_ref(rw);
    Self::drop(rw);
  }

  /// This function will be called when `wake_by_ref` is called on the
  /// [`Waker`]. It must wake up the task associated with this [`RawWaker`].
  ///
  /// This function is similar to `wake`, but must not consume the provided data
  /// pointer.
  ///
  /// Think `fn wake(&self)`
  unsafe fn wake_by_ref(rw: *const ()) {
    let rw = &*(rw as *mut Self);
    Thread::add_future_wake_task(&(*rw.thread), rw.future_id);
  }

  unsafe fn clone(rw: *const ()) -> RawWaker {
    let rw = &*(rw as *mut FutureJobWaker);
    FutureJobWaker::new_raw(rw.future_id, &*rw.thread)
  }

  pub const fn get_vtable() -> RawWakerVTable {
    RawWakerVTable::new(
      FutureJobWaker::clone,
      FutureJobWaker::wake,
      FutureJobWaker::wake_by_ref,
      FutureJobWaker::drop,
    )
  }
}

// -----------------------------------------------------------------------------------------
// LOCAL WAKER
// -----------------------------------------------------------------------------------------

/// Future runner that works locally, i.e all work is done one thread.
struct LocalWaker {}

impl LocalWaker {
  const VIRTUAL_FUNCTION_TABLE: RawWakerVTable = LocalWaker::get_vtable();

  /// Creates a new Waker within the local thread.
  pub fn new() -> Waker {
    unsafe { Waker::from_raw(LocalWaker::new_raw()) }
  }

  fn new_raw() -> RawWaker {
    //let waker = Box::new(LocalWaker {});
    //let waker_ptr = Box::into_raw(waker);
    RawWaker::new(std::ptr::null() as *const _, &Self::VIRTUAL_FUNCTION_TABLE)
  }

  unsafe fn drop(rw: *const ()) {
    //let rw = rw as *mut LocalWaker;
    //let _ = Box::from_raw(rw);
  }

  unsafe fn wake(rw: *const ()) {
    //Self::wake_by_ref(rw);
    //Self::drop(rw);
  }

  unsafe fn wake_by_ref(rw: *const ()) {
    //let rw = &*(rw as *mut Self);
  }

  unsafe fn clone(rw: *const ()) -> RawWaker {
    //let rw = &*(rw as *mut LocalWaker);
    LocalWaker::new_raw()
  }

  pub const fn get_vtable() -> RawWakerVTable {
    RawWakerVTable::new(
      LocalWaker::clone,
      LocalWaker::wake,
      LocalWaker::wake_by_ref,
      LocalWaker::drop,
    )
  }
}

/// Runs a future state machine on the current thread.
pub fn run_local<F: Future>(mut fut: F) -> F::Output {
  let mut pinned_future = unsafe { std::pin::Pin::new_unchecked(&mut fut) };

  let waker = LocalWaker::new();

  let mut ctx = Context::from_waker(&waker);

  loop {
    match pinned_future.as_mut().poll(&mut ctx) {
      std::task::Poll::Pending => {}
      std::task::Poll::Ready(result) => {
        break result;
      }
    }
  }
}

pub trait RunLocal: Future {
  /// Run this future's state machine on the current thread.
  fn block_on(self) -> Self::Output
  where
    Self: Sized,
  {
    run_local(self)
  }
}

impl<F: Future> RunLocal for F {}

#[test]
fn local_waker() {
  let temp = async {
    let block = async {
      println!("Waiting!");
    };

    block.await;
    std::thread::sleep(std::time::Duration::from_secs(2));

    true
  };

  let result = run_local(temp);

  assert_eq!(result, true);
}
