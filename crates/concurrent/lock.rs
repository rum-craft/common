use super::Thread;
use std::time::Duration;

/// Simple spin lock with a 1microsecond pause on lock failure
///
/// # Panic
///
/// Will panic if the lock acquired by a thread is no longer in the lock state
/// when the thread attempts to unlock.
#[derive(Debug)]
pub struct SpinLock {
  lock: std::sync::atomic::AtomicU64,
}

impl SpinLock {
  pub fn new() -> Self {
    Self { lock: Default::default() }
  }

  pub fn lock(&self) -> SpinLockLock<'_> {
    let id = Thread::get_thread().map(|t| t.id.0).unwrap_or(usize::MAX) as u64;
    loop {
      match self.lock.compare_exchange_weak(
        0,
        id,
        std::sync::atomic::Ordering::Release,
        std::sync::atomic::Ordering::Relaxed,
      ) {
        Err(_) => std::thread::sleep(Duration::from_micros(1)),
        Ok(_) => break SpinLockLock { lock_id: id, lock: self },
      }
    }
  }

  fn unlock(&self, lock_id: u64) {
    match self.lock.compare_exchange_weak(
      lock_id,
      0,
      std::sync::atomic::Ordering::Release,
      std::sync::atomic::Ordering::Relaxed,
    ) {
      Err(_) => panic!("Poisoned SpinLock!"),
      Ok(_) => {}
    }
  }
}

pub struct SpinLockLock<'a> {
  lock_id: u64,
  lock:    &'a SpinLock,
}

impl<'a> Drop for SpinLockLock<'a> {
  fn drop(&mut self) {
    self.lock.unlock(self.lock_id)
  }
}

#[test]
fn spin_lock() -> crate::error::RumResult<()> {
  use crate::ThreadHost;
  let mut pool = crate::AppThreadPool::new(1, 2, 0, 0)?;
  pool.monitor();

  let lock = std::sync::Arc::new(SpinLock::new());

  let l = lock.clone();

  pool.add_task(move |_| {
    let _ = l.lock();
    println!("Locked in worker thread");
    println!("Unlocking")
  });

  let _ = lock.lock();
  println!("Locked From Main thread");

  std::thread::sleep(Duration::from_secs(1));

  Ok(())
}
