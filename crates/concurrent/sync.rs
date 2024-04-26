use std::{
  fmt::Debug,
  sync::atomic::{AtomicU32, Ordering::*},
  time::Duration,
};
///
/// A synchronization primitive that prevents a job from running until all
/// instances of it are dropped.
///
/// # Example
/// ```rust
/// # use rum_lib::thread::*;
/// # let mut pool = AppThreadPool::<_, 32>::new(6, 0).unwrap();
///
/// let fence = pool.add_fenced_job(|_,_| {
///    eprintln!("Goodbye!");
///    
/// });
///
/// // Creating a clone of the fence to allow it to block
/// // until both the `job_fence` and the original `fence`
/// // are dropped.
///
/// let job_fence = fence.clone();
///
/// pool.add_job(move |_,_| {
///    println!("Hello!");
///    drop(job_fence);
/// });
/// ```
pub struct Fence {
  /// Pointer the atomic U32 stored in the
  /// the Job that owns the fence.
  __fence: *mut AtomicU32,
  id:      usize,
}

impl Debug for Fence {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut s = f.debug_tuple("Fence");
    unsafe { s.field(&*self.__fence) };
    s.finish()
  }
}
unsafe impl Send for Fence {}
unsafe impl Sync for Fence {}

fn atomic_incr(__fence: *mut AtomicU32) -> u32 {
  unsafe {
    return (*__fence).fetch_add(1, Release);
  }
}

fn atomic_decr(__fence: *mut AtomicU32) -> u32 {
  unsafe {
    return (*__fence).fetch_sub(1, Release);
  }
}

impl Fence {
  pub(crate) fn new(__fence: *mut AtomicU32) -> Self {
    atomic_incr(__fence);
    Self { __fence, id: 0 }
  }

  pub fn wait(self) {
    unsafe {
      if self.id == 0 {
        atomic_decr(self.__fence);
        while (*self.__fence).load(Acquire) > 0 {
          std::thread::sleep(Duration::from_micros(1));
        }
        std::mem::forget(self);
      }
    }
  }
}

impl Clone for Fence {
  fn clone(&self) -> Self {
    atomic_incr(self.__fence);
    Self { __fence: self.__fence, id: self.id + 1 }
  }
}

impl Drop for Fence {
  fn drop(&mut self) {
    unsafe {
      atomic_decr(self.__fence);
      if self.id == 0 {
        while (*self.__fence).load(Acquire) > 0 {
          std::thread::sleep(Duration::from_micros(1));
          std::hint::spin_loop()
        }
      }
    }
  }
}

/// This object serves as a container for return values produced by another
/// thread through a LandingZone task.
///
/// # Safety
///
/// The `LandingZone` object relies on a stable address to allow it wait for and
/// receive data from another thread. As such, if the lz is allowed to go
/// out of scope, there are behaviors in place to prevent its cleanup from
/// causing undefined behavior. However, if the lz is allowed to
/// pass into another scope, such as from being returned from a function or
/// being moved into a closure, then the `move` that occurs WILL lead to data
/// corruption or at least undefined behavior, and mostly likely deadlock.
#[derive(Debug)]
pub struct LandingZone<Data> {
  /// Pointer the atomic U32 stored in the
  /// the Job that owns the lz.
  pub(super) data: Option<Data>,
  pub(super) __lz: AtomicU32,
}

impl<Data> Default for LandingZone<Data> {
  fn default() -> Self {
    Self::new()
  }
}

impl<Data> Drop for LandingZone<Data> {
  fn drop(&mut self) {
    let _ = self.wait();
  }
}

impl<Data> LandingZone<Data> {
  pub fn new<'b>() -> LandingZone<Data> {
    LandingZone { __lz: AtomicU32::new(2), data: None }
  }

  pub(super) fn start(&self) {
    loop {
      match self.__lz.compare_exchange_weak(2, 1, Release, Relaxed) {
        Err(val) => {
          panic!("Expected lz [{val}] to be 2")
        }
        _ => break,
      }
    }
  }

  pub(super) fn end(&self) {
    loop {
      match self.__lz.compare_exchange_weak(1, 0, Acquire, Relaxed) {
        Err(val) => {
          panic!("Expected lz [{val}] to be 0")
        }
        _ => break,
      }
    }
  }

  /// Returns a reference to the underlying data without.
  #[track_caller]
  pub fn read(&self) -> Option<&Data> {
    loop {
      match self.__lz.load(Acquire) {
        0 => break self.data.as_ref(),
        1 => {}
        lz => {
          panic!("Invalid lz state. Was this submitted as part of a task yet? {lz}")
        }
      }
      std::thread::sleep(std::time::Duration::from_nanos(500));
      std::hint::spin_loop();
    }
  }

  /// Returns the the underlying data, while also removing it from the lz.
  #[track_caller]
  pub fn wait(&mut self) -> Option<Data> {
    let val = loop {
      match self.__lz.load(Acquire) {
        0 => break self.data.take(),
        1 => {}
        2 => {
          // Landing zone has not been queued with a task
          return None;
        }
        lz => {
          panic!("Invalid lz state. Was this submitted as part of a task yet? {lz}")
        }
      }
      std::thread::sleep(std::time::Duration::from_nanos(500));
      std::hint::spin_loop();
    };

    // Reset the landing zone
    match self.__lz.compare_exchange_weak(0, 2, Relaxed, Relaxed) {
      Err(val) => {
        panic!("Expected lz [{val}] to be 2")
      }
      _ => {}
    }

    val
  }

  /// Waits for data to be set in the lz then returns that data.
  #[track_caller]
  pub fn take(&mut self) -> Data {
    let data = self.wait().unwrap();

    data
  }
}
