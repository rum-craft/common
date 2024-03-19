use super::{
  containers::MTLLNode16,
  thread::{Thread, ThreadDo},
};
use crate::error::RumResult;
use std::{cell::UnsafeCell, fmt::Debug, future::Future, pin::Pin, sync::atomic::AtomicU32};

pub trait RumFutureThreadFn: Future<Output = RumResult<()>> + Send + 'static {}
pub trait RumFuture: Future<Output = RumResult<()>> + 'static {}

impl<T: Future<Output = RumResult<()>> + Send + 'static> RumFuture for T {}

pub type RumBoxedFuture = Pin<Box<dyn RumFuture>>;

pub trait RumTask: FnOnce(&Thread) + Send + Sync {}

pub trait RumAsyncTask: (FnOnce(&Thread/*  */) ->( dyn RumFuture )) + Send + Sync {}

impl<T: FnOnce(&Thread) + Send + Sync> RumTask for T {}

#[derive(Default)]
pub enum Task {
  #[default]
  None,
  Command(ThreadDo),
  Closure(Box<dyn RumTask>),
  Future(UnsafeCell<RumBoxedFuture>),
}

impl Debug for Task {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Task::Closure(_) => {
        let mut s = f.debug_struct("Task::Closure");
        s
      }
      Task::Command(command) => {
        let mut s = f.debug_struct("Task::Command");
        s.field("command", command);
        s
      }
      Task::Future(..) => {
        let mut s = f.debug_struct("Task::Future");
        s
      }
      Task::None => {
        let mut s = f.debug_struct("Task::Empty");
        s
      }
    }
    .finish()
  }
}

impl Task {
  pub fn take(&mut self) -> Task {
    let mut existing = Task::None;
    std::mem::swap(&mut existing, self);
    existing
  }

  pub fn is_active(&self) -> bool {
    match self {
      Self::None => false,
      _ => true,
    }
  }
}

#[allow(unused)]
#[derive(Clone, Copy, Debug)]
pub enum JobType {
  None,
  LocalStealable,
  Global,
  Local,
}

pub struct Job {
  // pub(super) buffer:     StaticBuffer<64>,
  pub(super) task:   Task,
  pub(super) fence:  *mut AtomicU32,
  pub(super) signal: *mut AtomicU32,
  pub(super) id:     u16,
  pub(super) next:   u16,
}

impl Job {
  pub(super) fn clear(&mut self) {
    let _ = self.task.take();
  }
}

impl Debug for Job {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut s = f.debug_struct("Job");
    s.field("dependency", unsafe { &*self.fence });
    s.field("id", &self.id);
    s.field("next", &self.next);
    s.field("task", &self.task);
    s.finish()
  }
}

impl MTLLNode16 for Job {
  fn get_id(&mut self) -> u16 {
    self.id
  }

  fn get_next(&mut self) -> u16 {
    self.next
  }

  fn set_next(&mut self, next: u16) {
    self.next = next
  }
}

impl Default for Job {
  fn default() -> Self {
    Job {
      fence:  Box::into_raw(Box::new(AtomicU32::new(0))),
      signal: Box::into_raw(Box::new(AtomicU32::new(0))),
      // thread_waker: Box::into_raw(Box::new(None));
      task:   Default::default(),
      id:     u16::MAX,
      next:   u16::MAX,
      //buffer:     StaticBuffer::new(),
    }
  }
}

impl Drop for Job {
  fn drop(&mut self) {
    unsafe {
      let _ = Box::from_raw(self.fence);
      let _ = Box::from_raw(self.signal);
    }
  }
}
