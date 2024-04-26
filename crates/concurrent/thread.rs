#![allow(unused)]

use crate::error::RumResult;

use super::{
  containers::MTLLFIFOQueue16,
  future::{FutureJobWaker, ThreadFuture},
  job::{Job, JobType, RumAsyncTask, RumBoxedFuture, RumFuture, RumTask, Task},
  specialists::{SpecializationPolicy, SpecializationTable},
  sync::Fence,
  LandingZone,
};

use std::{
  cell::UnsafeCell,
  fmt::{Debug, Display},
  future::Future,
  marker::PhantomData,
  pin::Pin,
  sync::{
    atomic::{AtomicU32, Ordering::*},
    mpsc::{Receiver, Sender},
  },
  task::{Context, RawWaker, RawWakerVTable, Waker},
  thread::JoinHandle,
  time::Duration,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum TaskHandlingResult {
  Halt,
  Continue,
}

pub struct MessageDispatcher<'a> {
  index:      usize,
  free_queue: &'a MTLLFIFOQueue16<Job>,
  job_queue:  &'a MTLLFIFOQueue16<Job>,
  retries:    usize,
}

impl<'a> MessageDispatcher<'a> {
  #[track_caller]
  pub fn dispatch<T: FnOnce(&Thread) + Send + Sync + 'static>(mut self, task: T) {
    unsafe {
      if let Some(job) = self.free_queue.pop_front() {
        let j = &mut (*job);

        j.task = Task::Closure(Box::new(task));

        self.job_queue.push_back(job);

        return;
      } else if self.retries > 3 {
        panic!("Out of free jobs!");
      }
      self.retries += 1;
      self.dispatch(task)
    }
  }

  pub fn index(&self) -> usize {
    self.index
  }
}

pub struct BroadcastIterator<'a> {
  pub(super) threads: Vec<(&'a MTLLFIFOQueue16<Job>, &'a MTLLFIFOQueue16<Job>)>,
  pub(super) index:   usize,
}

impl<'a> Iterator for BroadcastIterator<'a> {
  type Item = MessageDispatcher<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.index >= self.threads.len() {
      None
    } else {
      let (free_queue, job_queue) = self.threads[self.index];
      self.index += 1;
      Some(MessageDispatcher { index: self.index - 1, free_queue, job_queue, retries: 0 })
    }
  }
}

pub trait ThreadHost {
  /// Allows a unique message to be sent directly to every thread reachable by
  /// this host
  #[track_caller]
  fn broadcast_message<'a>(&'a self) -> BroadcastIterator<'a>;

  fn __add_global_task_base(&self, task: Task, fence: bool) -> Option<Fence>;

  fn __add_specialized_task_base<Specialization: Into<usize>>(
    &self,
    specialization: Specialization,
    task: Task,
  );

  fn add_task<T: FnOnce(&Thread) + Send + Sync + 'static>(&self, task: T);

  fn add_task_specialized<S: Into<usize>, T: FnOnce(&Thread) + Send + Sync + 'static>(
    &self,
    specialization: S,
    task: T,
  );

  /// Adds a task that will only run after all copes of the returned fence value
  /// are dropped or waited on.
  fn add_fenced_task<T: FnOnce(&Thread) + Send + Sync + 'static>(&self, task: T) -> Fence;

  fn add_async_task<T: RumFuture>(&self, task: T);

  /// Submit a task to the job pool, and return a LandingZone which will contain
  /// the task's return result when it completes.
  fn add_boxed_lz_task<Data: Sized, T: (FnOnce(&Thread) -> Data) + Send + Sync + 'static>(
    &self,
    create_fence: bool,
    task: T,
  ) -> (Option<Fence>, Box<super::LandingZone<Data>>);

  /// Submit a task to the job pool, and bind to a Signal which will contain the
  /// task's return result when it completes.
  ///
  /// # Safety
  ///
  /// The `Signal` object relies on a stable address to allow it wait for and
  /// receive data from another thread. As such, if the signal is allowed to go
  /// out of scope, there are behaviors in place to prevent its cleanup from
  /// causing undefined behavior. However, if the signal is allowed to
  /// pass into another scope, such from being returned from a function or being
  /// moved into a closure, then the `move` that may occur will lead to data
  /// corruption, undefined behavior, mostly likely deadlock.
  ///
  /// It is up to the user to ensure that the signal is waited before it is
  /// allowed to be moved into another scope. Use `add_boxed_signalled_task` if
  /// this cannot be guaranteed.
  unsafe fn add_lz_task<Data: Sized, T: (FnOnce(&Thread) -> Data) + Send + Sync + 'static>(
    &self,
    signal: &mut LandingZone<Data>,
    create_fence: bool,
    task: T,
  ) -> Option<Fence>;

  /// Submit a future task to the job pool, and bind to a Signal which will
  /// contain the task's return result when it completes.
  ///
  /// # Safety
  ///
  /// The `Signal` object relies on a stable address to allow it wait for and
  /// receive data from another thread. As such, if the signal is allowed to go
  /// out of scope, there are behaviors in place to prevent its cleanup from
  /// causing undefined behavior. However, if the signal is allowed to
  /// pass into another scope, such from being returned from a function or being
  /// moved into a closure, then the `move` that may occur will lead to data
  /// corruption, undefined behavior, and mostly likely deadlock.
  unsafe fn add_lz_async_task<Data: Sized, F: Future<Output = Data> + Send + 'static>(
    &self,
    signal: &mut LandingZone<Data>,
    create_fence: bool,
    task: F,
  ) -> Option<Fence>;

  /// Submit a task to the job pool, and return a Signal which will contain the
  /// task's return result when it completes.
  fn add_boxed_lz_async_task<Data: Sized, F: Future<Output = Data> + Send + 'static>(
    &self,
    create_fence: bool,
    task: F,
  ) -> (Option<Fence>, Box<super::LandingZone<Data>>);

  fn num_of_threads(&self) -> usize;
}

/// Communications from the main thread, or another worker thread, to a
/// worker.
#[derive(Clone, Copy, Debug)]
pub enum ThreadDo {
  /// Command issued when the thread pool scheduled to close. This command puts
  /// the thread in exit state, where it will process all jobs in all queues
  /// until it receives a halt command on the global queue.
  HaltQueued,
  /// Command issued when the thread pool is dropped. Causes the receiving
  /// thread to exit it's event loop and drop as well.
  Halt,
  /// Command issued to make the recipient thread exclusive receive tasks that
  /// are labeled with the same_exclusive ID. All other threads will ignore
  /// such jobs, and likewise, the recipient thread will ignore all other jobs.
  MakeSpecialist {
    policy:         SpecializationPolicy,
    specialization: usize,
    visited:        usize,
    tries:          usize,
    max_tries:      usize,
  },
  /// Called by another thread to wake a future owned by this thread by id.
  WakeFuture(usize),
}

/// Communications from a worker thread to the main thread.
#[derive(Clone, Copy)]
pub enum ThreadSays {
  /// Initialized
  Initialized(usize),
  /// The thread has parked itself due to a lack of jobs.
  Parked(usize),
  /// The thread has halted due to some type of exception.
  Halted(usize),
  ///
  Exited(usize),
}

enum FeatureParkingSpot {
  Parked(RumBoxedFuture),
  Free(Option<usize>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ThreadId(pub usize);

impl ThreadId {
  pub const MAIN_THREAD_ID: usize = 0x0123_4567_78AB_CDEF;

  /// Creates a range at the offset of thread id with the given `size`.
  /// This can be used to create global tables with series of columns that are
  /// exclusive to each thread.
  pub fn range(&self, size: usize) -> std::ops::Range<usize> {
    let off = self.0 * size;
    self.0..self.0 + size
  }

  pub fn is_main(&self) -> bool {
    self.0 == Self::MAIN_THREAD_ID
  }
}

impl Display for ThreadId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Debug::fmt(self, f)
  }
}

pub struct Thread {
  pub(crate) id: ThreadId,
  pub(crate) global_free_queue: MTLLFIFOQueue16<Job>,
  pub(crate) global_job_queue: MTLLFIFOQueue16<Job>,
  pub(crate) local_free_queue: MTLLFIFOQueue16<Job>,
  pub(crate) local_job_queue: MTLLFIFOQueue16<Job>,
  /// Commination channel from the worker thread to the main thread.
  /// Used to communicate thread state, such as when the worker theread parks
  /// itself.
  pub(crate) thread_comm: Sender<ThreadSays>,
  futures: Vec<(FeatureParkingSpot)>,
  first_free: Option<usize>,
  specialization_lut: *mut dyn super::specialists::SpecializationTable,
  specialization_policy: SpecializationPolicy,
  /// Indicates the thread pool is about to close and preventes the
  /// thread from  ignoring the global queue
  halt_pending: bool,
}

unsafe impl Send for Thread {}
unsafe impl Sync for Thread {}

impl ThreadHost for Thread {
  fn broadcast_message<'a>(&'a self) -> BroadcastIterator<'a> {
    BroadcastIterator {
      threads: vec![(&self.local_free_queue, &self.local_job_queue)],
      index:   0,
    }
  }

  fn num_of_threads(&self) -> usize {
    1
  }

  #[track_caller]
  fn __add_global_task_base(&self, task: Task, fence: bool) -> Option<Fence> {
    debug_assert!(task.is_active());
    unsafe {
      let mut retries = 0;
      loop {
        if let Some(job) = self.global_free_queue.pop_front() {
          let j = &mut (*job);

          j.task = task;

          let fence = if fence {
            let fence = Some(Fence::new(j.fence));
            // Ensure the stored reference count represents the copy of the fence
            // attached to the task and the copy returned to the caller.
            (*j.fence).store(2, Release);
            fence
          } else {
            (*j.fence).store(0, Relaxed);
            None
          };

          self.global_job_queue.push_back(job);

          break fence;
        } else if retries > 3 {
          panic!("Out of free jobs!");
        }
        retries += 1;
      }
    }
  }

  #[track_caller]
  fn __add_specialized_task_base<Specialization: Into<usize>>(
    &self,
    specialization: Specialization,
    task: Task,
  ) {
    debug_assert!(task.is_active());
    let lut = unsafe { &mut *self.specialization_lut };
    if let Some(task) = lut.post_job(task, specialization.into()) {
      self.__add_global_task_base(task, false);
    }
  }

  fn add_task<T: FnOnce(&Thread) + Send + Sync + 'static>(&self, task: T) {
    self.__add_global_task_base(Task::Closure(Box::new(task)), false);
  }

  fn add_task_specialized<S: Into<usize>, T: FnOnce(&Thread) + Send + Sync + 'static>(
    &self,
    specialization: S,
    task: T,
  ) {
    self.__add_specialized_task_base(specialization, Task::Closure(Box::new(task)));
  }

  fn add_boxed_lz_task<Data: Sized, T: (FnOnce(&Thread) -> Data) + Send + Sync + 'static>(
    &self,
    create_fence: bool,
    task: T,
  ) -> (Option<Fence>, Box<super::LandingZone<Data>>) {
    let mut signal = Box::new(LandingZone::new());
    unsafe { (self.add_lz_task(signal.as_mut(), create_fence, task), signal) }
  }

  unsafe fn add_lz_task<Data: Sized, T: (FnOnce(&Thread) -> Data) + Send + Sync + 'static>(
    &self,
    signal: &mut LandingZone<Data>,
    create_fence: bool,
    task: T,
  ) -> Option<Fence> {
    let ptr = signal as *mut _ as *mut () as usize;

    let task: Task = Task::Closure(Box::new(move |t: &Thread| {
      let signal = &mut *(ptr as *mut () as *mut LandingZone<Data>);

      signal.data = Some(task(t));
      signal.end();
    }));

    signal.start();

    self.__add_global_task_base(task, create_fence)
  }

  unsafe fn add_lz_async_task<Data: Sized, F: Future<Output = Data> + Send + 'static>(
    &self,
    signal: &mut LandingZone<Data>,
    create_fence: bool,
    task: F,
  ) -> Option<Fence> {
    let ptr = signal as *mut _ as *mut () as usize;

    let task = Task::Future(UnsafeCell::new(Box::pin(async move {
      let result = task.await;
      let signal = &mut *(ptr as *mut () as *mut LandingZone<Data>);
      signal.data = Some(result);
      signal.end();
      Ok(())
    })));

    signal.start();

    self.__add_global_task_base(task, create_fence)
  }

  fn add_boxed_lz_async_task<Data: Sized, F: Future<Output = Data> + Send + 'static>(
    &self,
    create_fence: bool,
    task: F,
  ) -> (Option<Fence>, Box<super::LandingZone<Data>>) {
    let mut signal = Box::new(LandingZone::new());
    let fence = unsafe { self.add_lz_async_task(signal.as_mut(), create_fence, task) };
    (fence, signal)
  }

  fn add_fenced_task<T: FnOnce(&Thread) + Send + Sync + 'static>(&self, task: T) -> Fence {
    let task = Task::Closure(Box::new(task));
    self.__add_global_task_base(task, true).unwrap()
  }

  fn add_async_task<T: RumFuture>(&self, task: T) {
    let task = Task::Future(UnsafeCell::new(Box::pin(task)));
    self.__add_global_task_base(task, false);
  }
}

impl Thread {
  thread_local! {
    static THREAD: UnsafeCell<*const ()> = UnsafeCell::new(std::ptr::null());
  }

  /// Returns the ThreadId of the caller's execution context
  pub fn get_id() -> ThreadId {
    match Self::get_thread() {
      Some(thread) => thread.id,
      None => ThreadId(ThreadId::MAIN_THREAD_ID),
    }
  }

  /// Returns the the {ThreadId} of this thread.
  pub fn id(&self) -> ThreadId {
    self.id
  }

  pub(super) fn new(
    global_free_queue: MTLLFIFOQueue16<Job>,
    global_job_queue: MTLLFIFOQueue16<Job>,
    local_free_queue: MTLLFIFOQueue16<Job>,
    local_job_queue: MTLLFIFOQueue16<Job>,
    thread_comm: Sender<ThreadSays>,
    id: usize,
    specialization_lut: *mut dyn SpecializationTable,
  ) -> Thread {
    Thread {
      global_free_queue,
      global_job_queue,
      local_free_queue,
      local_job_queue,
      thread_comm,
      id: ThreadId(id as usize),
      futures: Vec::with_capacity(32),
      first_free: None,
      specialization_lut,
      specialization_policy: Default::default(),
      halt_pending: false,
    }
  }

  pub(super) fn send_message(&mut self, message: ThreadSays) -> RumResult<()> {
    match self.thread_comm.send(message) {
      Err(send_error) => Err(crate::error::ConcurrentError::InterthreadCommunicationError),
      _ => Ok(()),
    }
  }

  pub fn add_future_task<T: Send + Clone>(
    &self,
    task: impl (FnOnce(&Thread) -> RumResult<T>) + Send + Sync + 'static,
  ) -> ThreadFuture<T> {
    ThreadFuture::<T>::new(task)
  }

  /// Returns the {Thread} object representing the current OS thread.
  pub fn get_thread<'a: 'static>() -> Option<&'a Self> {
    let mut global_thread: *const () = std::ptr::null();

    unsafe {
      let thread = Thread::THREAD.with(|thread| {
        let ptr = *thread.get();
        if !ptr.is_null() {
          global_thread = ptr;
        }
      });
    }

    if global_thread.is_null() {
      None
    } else {
      unsafe { Some(&*(global_thread as *const _ as *const Self)) }
    }
  }

  /// Wake's a future job.
  ///
  /// Since this can be called from any thread that has a reference to the
  /// waker, this only adds a `WakeFuture` task to the owning threads local
  /// queue. The actual process of polling the awoken future is done within
  /// the owning thread's job loop.
  ///
  /// Warning: This may be called from a different thread
  pub(super) unsafe fn add_future_wake_task(other: &Self, future_id: usize) {
    if let Some(local_job_ptr) = other.local_free_queue.pop_front() {
      // Re queue job
      debug_assert!(!local_job_ptr.is_null());
      let l_job = unsafe { &mut *local_job_ptr };
      l_job.task = Task::Command(ThreadDo::WakeFuture(future_id));
      other.local_job_queue.push_back(local_job_ptr);
    } else {
      panic!("Thread [{}] - No Free Job When Attempting to Create Awake Task", other.id);
    }
  }

  /// Parks this thread indefinitely. Requires the owner of the thread's
  /// JoinHandle to call `std::thread::wake` to reactivate this thread.
  fn park(&mut self) {
    //self.send_message(ThreadSays::Parked(self.id.0 as usize));
    std::thread::sleep(Duration::from_nanos(500));
    // todo std::thread::park()
  }

  fn wake_future(&mut self, future_id: usize) {
    debug_assert!(self.futures.len() > future_id);

    let empty_spot = &mut self.futures[future_id];

    let mut data = FeatureParkingSpot::Free(self.first_free);

    std::mem::swap(&mut data, empty_spot);

    self.first_free = Some(future_id);

    match data {
      FeatureParkingSpot::Parked(future) => {
        if let Some(local_job_ptr) = self.local_free_queue.pop_front() {
          // Re queue job
          debug_assert!(!local_job_ptr.is_null());
          let l_job = unsafe { &mut *local_job_ptr };
          l_job.task = Task::Future(UnsafeCell::new(future));
          self.local_job_queue.push_back(local_job_ptr);
        } else {
          panic!("Thread [{}] - No Free Jobs", self.id);
        }
        // Add future to local queue
      }
      _ => panic!("Thread [{}] - Future Not Found!", self.id),
    }
  }

  /// Returns `TaskHandlingResult::Halt` if the task was `ThreadDo::Halt`.
  /// Otherwise processes task and returns `TaskHandlingResult::Continue`.
  fn handle_task(&mut self, task: Task) -> TaskHandlingResult {
    match task {
      Task::Future(mut future) => {
        self.handle_future_task(future);
        TaskHandlingResult::Continue
      }

      Task::Closure(task) => {
        (task)(self);
        TaskHandlingResult::Continue
      }

      Task::Command(command) => match command {
        ThreadDo::HaltQueued => {
          println!("Thread {} acknowledges pending halt", self.id);
          self.halt_pending = true;
          TaskHandlingResult::Continue
        }

        ThreadDo::Halt => TaskHandlingResult::Halt,

        ThreadDo::MakeSpecialist { max_tries, policy, specialization, tries, visited } => {
          self.attempt_specialization(specialization, policy, tries, max_tries, visited);
          TaskHandlingResult::Continue
        }

        ThreadDo::WakeFuture(future_id) => {
          self.wake_future(future_id);
          TaskHandlingResult::Continue
        }
      },
      Task::None => TaskHandlingResult::Halt,
    }
  }

  fn handle_future_task(&mut self, future: UnsafeCell<Pin<Box<dyn RumFuture>>>) {
    let mut future = unsafe { future.into_inner() };

    let index = match self.first_free.take() {
      Some(index) => {
        match self.futures[index] {
          FeatureParkingSpot::Free(next) => {
            self.first_free = next;
          }
          _ => unreachable!(),
        }
        index
      }
      None => {
        let len = self.futures.len();
        self.futures.push(FeatureParkingSpot::Free(None));
        len
      }
    };

    let waker = FutureJobWaker::new(index, self);

    let mut ctx = Context::from_waker(&waker);

    match future.as_mut().poll(&mut ctx) {
      std::task::Poll::Pending => {
        debug_assert!(matches!(self.futures[index], FeatureParkingSpot::Free(_)));
        self.futures[index] = FeatureParkingSpot::Parked(future);
      }
      std::task::Poll::Ready(result) => {
        self.futures[index] = FeatureParkingSpot::Free(self.first_free);
        self.first_free = Some(index);
        match result {
          Err(err) => println!("TODO: Place in logger: {err}"),
          Ok(_) => {}
        }
      }
    }
  }

  fn attempt_specialization(
    &mut self,
    specialization: usize,
    policy: SpecializationPolicy,
    tries: usize,
    max_tries: usize,
    visited: usize,
  ) {
    let visited_flag = 1 << self.id.0;
    let has_visited = visited ^ visited_flag;
    let tries = tries + 1;
    let repost = false;

    if has_visited != visited {
      if self.specialization_policy.can_specialize(specialization, policy) {
        let specialization_lut = unsafe { &mut *self.specialization_lut };

        if specialization_lut.register(self, specialization) {
          println!("Thread {} registered as a specialist in {specialization}", self.id);
          self.specialization_policy.merge(policy);
        }
        return;
      }
    }

    if tries < max_tries {
      self.__add_global_task_base(
        Task::Command(ThreadDo::MakeSpecialist {
          policy,
          specialization,
          visited,
          tries,
          max_tries,
        }),
        false,
      );
      /// Give other threads a chance to pick up the specialization
      std::thread::sleep(Duration::from_micros(200));
    } else {
      println!("Sepecialization request for a {} specialist has failed", specialization);
    }
  }

  /// Similar to `run`, except this intended to to be utilized on the main
  /// thread to facility progression of work while during spin up of new
  /// threads. As such, this should only be used when an app if first starting
  /// up.
  pub(super) fn local_run(&mut self) {
    loop {
      let Self {
        id,
        global_free_queue,
        global_job_queue,
        local_free_queue,
        local_job_queue,
        thread_comm: channel,
        ..
      } = self;

      if let Some(job_ptr) = self.global_job_queue.pop_front() {
        debug_assert!(!job_ptr.is_null());

        let job = unsafe { &mut *job_ptr };

        if let Some(dependency) = unsafe { job.fence.as_ref() } {
          if dependency.load(Relaxed) > 0 {
            // Put the dependency back onto the queue

            debug_assert!(job.task.is_active());

            self.global_job_queue.push_back(job_ptr);
            continue;
          }
        }

        let task = job.task.take();

        job.clear();
        self.global_free_queue.push_back(job_ptr);
        self.handle_task(task);
      }
      break;
    }
  }

  pub(super) fn run(&mut self) {
    if let Err(err) = self.send_message(ThreadSays::Initialized(self.id.0 as usize)) {
      /// Comm error. Something serious happened to the Main thread.
      /// need to halt.
      println!("Thread {} failed to register communication with main thread.", self.id);
      return;
    }

    /// Initialize thread-local global thread.
    Thread::THREAD.with(|thread| unsafe {
      *(thread.get()) = (&*self) as *const _ as *const ();
    });

    'job_loop: loop {
      /// --------------------------------------------------------
      /// Handle local jobs
      /// --------------------------------------------------------
      let Self {
        id,
        global_free_queue,
        global_job_queue,
        local_free_queue,
        local_job_queue,
        ..
      } = self;
      if let Some(job_ptr) = local_job_queue.pop_front() {
        debug_assert!(!job_ptr.is_null());

        let job = unsafe { &mut *job_ptr };

        let should_process_job = if let Some(dependency) = unsafe { job.fence.as_ref() } {
          if dependency.load(Relaxed) > 0 {
            local_job_queue.push_back(job_ptr);
            debug_assert!(job.task.is_active());
            false
          } else {
            true
          }
        } else {
          true
        };

        if should_process_job {
          let task = job.task.take();
          job.clear();
          self.local_free_queue.push_back(job_ptr);

          match self.handle_task(task) {
            TaskHandlingResult::Continue => {
              if !self.halt_pending {
                // Allows the thread to prioritize local jobs
                continue 'job_loop;
              }
            }
            TaskHandlingResult::Halt => break 'job_loop,
          }
        }
      }

      if !self.specialization_policy.is_exclusive() || self.halt_pending {
        /// --------------------------------------------------------
        /// Handle global jobs
        /// --------------------------------------------------------
        if let Some(job_ptr) = self.global_job_queue.pop_front() {
          debug_assert!(!job_ptr.is_null());

          let job = unsafe { &mut *job_ptr };

          if let Some(dependency) = unsafe { job.fence.as_ref() } {
            if dependency.load(Acquire) > 0 {
              if let Some(local_job_ptr) = self.local_free_queue.pop_front() {
                debug_assert!(!local_job_ptr.is_null());

                let l_job = unsafe { &mut *local_job_ptr };

                l_job.task = job.task.take();

                std::mem::swap(&mut job.fence, &mut l_job.fence);

                debug_assert!(
                  l_job.task.is_active(),
                  "Received empty task --- l:{:#?} {:#?}",
                  l_job.task,
                  job.task
                );

                job.clear();

                self.global_free_queue.push_back(job_ptr);

                unsafe { (*l_job.fence).fetch_sub(1, SeqCst) };

                self.local_job_queue.push_back(local_job_ptr);

                continue 'job_loop;
              } else {
                panic!("No Free Jobs");
              }
            }
          }
          let task = job.task.take();
          job.clear();
          self.global_free_queue.push_back(job_ptr);

          match self.handle_task(task) {
            TaskHandlingResult::Continue => continue 'job_loop,
            TaskHandlingResult::Halt => break 'job_loop,
          }
        }
      }

      if !self.specialization_policy.is_realtime() {
        // Nothing happened in this iteration of the loop. Allow the thread to sleep.
        self.park();
      }
    }

    self.send_message(ThreadSays::Halted(self.id.0));
  }

  pub fn sleep_ms(ms: u64) {
    std::thread::sleep(Duration::from_millis(ms))
  }

  pub fn sleep_micros(micros_seconds: u64) {
    std::thread::sleep(Duration::from_micros(micros_seconds))
  }

  pub fn sleep_ns(ns: u64) {
    std::thread::sleep(Duration::from_nanos(ns))
  }

  pub fn sleep_sec(seconds: u64) {
    std::thread::sleep(Duration::from_secs(seconds))
  }
}
