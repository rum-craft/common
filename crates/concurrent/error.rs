use std::fmt::{Debug, Display};

pub type RumResult<T> = Result<T, ConcurrentError>;

#[derive(Debug)]
pub enum ConcurrentError {
  /// Caused by thread exhaustion in a free pool
  CouldNotAcquireThread,
  /// The host platform does not support concurrent parralelism
  NoParallelismAvailable,
  /// A thread could not communicate with another thread. This usually
  /// indicates a thread has crashed
  InterthreadCommunicationError,
}

impl Display for ConcurrentError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Debug::fmt(self, f)
  }
}
