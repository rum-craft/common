use super::*;
use crate::error::{ConcurrentError, RumResult};
use std::time::Duration;

#[test]
fn allows_non_blocking_waiting_on_fence() -> crate::error::RumResult<()> {
  use std::time::Duration;
  let i = 1;

  let mut pool = AppThreadPool::new(6, 1024, 0, 0)?;

  let fence = pool.add_fenced_task(|_| {
    println!("Finished11");
  });

  for i in 0..100 {
    let b = fence.clone();
    pool.add_task(move |thread: &Thread| {
      println!("started {} - {i}", thread.id);
      std::thread::sleep(Duration::from_nanos(1));
      drop(b);
    });
  }

  pool.monitor();

  let fence2 = pool.add_fenced_task(move |thread| {
    eprintln!("Finished22");
    fence.wait();
  });

  fence2.wait();

  Ok(())
}

#[test]
fn provides_return_values_through_signals_boxed() -> crate::error::RumResult<()> {
  let mut pool = AppThreadPool::new(2, 1024, 0, 0)?;
  pool.monitor();

  fn test<'a>(pool: &'a mut AppThreadPool) -> Box<LandingZone<usize>> {
    //let mut d = None;

    let (_, signal) = pool.add_boxed_lz_task(false, |_| {
      std::thread::sleep(Duration::from_secs(2));
      let mut i = 1usize;
      for _ in 0..3 {
        i = (i + i) * i;
      }
      i
    });

    signal
  }

  let mut signal = test(&mut pool);

  assert_eq!(signal.take(), 128);

  Ok(())
}

#[test]
fn provides_return_values_through_signals_stack() -> crate::error::RumResult<()> {
  let mut pool: AppThreadPool = AppThreadPool::new(2, 1024, 0, 0)?;
  pool.monitor();

  fn test<'a>(pool: &'a mut AppThreadPool) -> LandingZone<usize> {
    //let mut d = None;
    let mut signal = Default::default();
    unsafe {
      pool.add_lz_task(&mut signal, false, |_| {
        std::thread::sleep(Duration::from_secs(2));
        let mut i = 1usize;
        for _ in 0..3 {
          i = (i + i) * i;
        }
        i
      })
    };

    assert_eq!(signal.take(), 128);

    signal
  }

  let mut signal = test(&mut pool);

  Ok(())
}

#[test]
fn handles_async_tasks() -> crate::error::RumResult<()> {
  use std::time::Duration;
  let i = 1;

  let mut pool = AppThreadPool::new(24, 1024, 0, 0)?;

  async fn sleep(dur: Duration) {
    for _ in 0..dur.as_micros() {}
  }

  let mut fence = pool.add_fenced_task(|t| {
    println!("Goodby, World {}", t.id());
  });

  for _ in 0..80 {
    let mut fence2 = fence.clone();

    pool.add_async_task(async move {
      println!("Hello, World");
      if let Some(thread) = Thread::get_thread() {
        println!("Got Thread! {}", thread.id());

        let f1 = thread.add_future_task(|t| {
          println!("Hello World! {}", t.id());
          std::thread::sleep(Duration::from_millis(100));

          RumResult::Ok(())
        });

        let f = thread.add_future_task(|t| {
          let mut vec = Vec::<usize>::with_capacity(50000);

          for i in 0usize..50000 {
            vec.push(i);
          }

          println!("Created Array! {}", t.id);

          RumResult::Ok(vec)
        });
        println!("Preparing to await future");
        std::thread::sleep(Duration::from_micros(1000));

        let v = f.await;
        f1.await;

        println!("{:?}", v.map(|v| v.len()));

        std::thread::sleep(Duration::from_millis(1));

        drop(fence2);
        println!("Future Completed!");
        Ok(())
      } else {
        drop(fence2);
        RumResult::Err(ConcurrentError::CouldNotAcquireThread)
      }
    });
  }

  fence.wait();

  Ok(())
}
