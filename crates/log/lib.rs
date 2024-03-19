use rum_concurrent::Thread;

#[macro_export]
macro_rules! rum_log {
  () => {
    rum_logger::ThreadLoggingBuffer::__log("\n")
  };
  ($($arg:tt)*) => {{
    rum_logger::ThreadLoggingBuffer::__log(&format!($($arg)*));
  }};
}

/// Like `debug_assert!`, except completely compiled out in release
/// builds
#[macro_export]
macro_rules! rum_debug_assert {
  ($expr:expr, $($arg:tt)*) => {
    #[cfg(debug_assertions)]
    assert!($expr, $($arg)*)
  };
}

pub struct ThreadLoggingBuffer {}

impl ThreadLoggingBuffer {
  pub fn new() -> Self {
    Self {}
  }

  pub fn log(&self, thread: &Thread, log: &str) {
    eprintln!("Thread: {} {log} \n", thread.id())
  }

  pub fn __log(log: &str) {
    if let Some(thread) = Thread::get_thread() {
      //thread.logger.log(thread, log);
      eprintln!("{log}")
    } else {
      eprintln!("{log}")
    }
  }
}

#[cfg(test)]
mod test {
  #[test]
  fn test() {}
}
