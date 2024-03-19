use super::{job::Task, AppThreadPool, Thread, ThreadHost};
use std;

/// A lookup table used to register threads as specialists and post jobs to
/// register specialists
pub trait SpecializationTable {
  /// Get a specialist thread
  fn get_specialist(&self, specialty: usize) -> Option<&Thread>;
  /// Allow a thread to post a job to a specialists. On success None is
  /// returned, indicating the job was accepted by the specialist. Otherwise
  /// the task is returned back to the caller.
  fn post_job(&self, task: Task, specialty: usize) -> Option<Task>;
  /// Allow a thread to unregister itself as a specialist
  fn register(&mut self, thread: &mut Thread, specialty: usize) -> bool;
  /// Allow a thread to attempt to register as a specialist
  fn deregister(&mut self, thread: &mut Thread, specialty: usize) -> bool;
}

pub struct ThreadSpecializationTable<const COLUMNS: usize, const ROWS: usize> {
  pub(crate) lut:  [[*mut Thread; COLUMNS]; ROWS],
  pub(crate) lock: std::sync::Mutex<()>,
}

unsafe impl<const COLUMNS: usize, const ROWS: usize> Send
  for ThreadSpecializationTable<COLUMNS, ROWS>
{
}
unsafe impl<const COLUMNS: usize, const ROWS: usize> Sync
  for ThreadSpecializationTable<COLUMNS, ROWS>
{
}

impl<const COLUMNS: usize, const ROWS: usize> ThreadSpecializationTable<COLUMNS, ROWS> {
  pub(super) fn new() -> Self {
    Self {
      lut:  [[std::ptr::null_mut(); COLUMNS]; ROWS],
      lock: Default::default(),
    }
  }
}

impl<const COLUMNS: usize, const ROWS: usize> SpecializationTable
  for ThreadSpecializationTable<COLUMNS, ROWS>
{
  #[track_caller]
  fn get_specialist(&self, specialty: usize) -> Option<&Thread> {
    debug_assert!(COLUMNS > 0 && ROWS > 0, "Thread specialization is disabled");

    if COLUMNS == 0 || ROWS == 0 {
      return None;
    }

    let row = specialty;

    debug_assert!(
      row < ROWS,
      "Thread tried to post job with specialty {row}, which exceeds the number of global thread specialties {ROWS}",
    );

    if row >= ROWS {
      return None;
    }

    let specialists = &self.lut[row];

    if let Some(specialist) = specialists.iter().find(|i| !(**i).is_null()) {
      return Some(unsafe { &**specialist });
    }

    None
  }

  #[track_caller]
  fn post_job(&self, task: Task, specialty: usize) -> Option<Task> {
    debug_assert!(COLUMNS > 0 && ROWS > 0, "Thread specialization is disabled");

    if COLUMNS == 0 || ROWS == 0 {
      return Some(task);
    }

    let row = specialty;

    debug_assert!(
      row < ROWS,
      "Thread tried to post job with specialty {row}, which exceeds the number of global thread specialties {ROWS}",
    );

    if row >= ROWS {
      return Some(task);
    }

    let specialists = &self.lut[row];

    if let Some(specialist) = specialists.iter().find(|i| !(**i).is_null()) {
      let specialist = unsafe { &mut **specialist };

      if let Some(local_job_ptr) = specialist.local_free_queue.pop_front() {
        debug_assert!(!local_job_ptr.is_null());

        let l_job = unsafe { &mut *local_job_ptr };

        l_job.task = task;

        debug_assert!(l_job.task.is_active());

        specialist.local_job_queue.push_back(local_job_ptr);

        return None;
      }
    }

    Some(task)
  }

  #[track_caller]
  fn register(&mut self, thread: &mut Thread, specialty: usize) -> bool {
    debug_assert!(COLUMNS > 0 && ROWS > 0, "Thread specialization is disabled");

    if COLUMNS == 0 || ROWS == 0 {
      return false;
    }

    let identity = thread as *mut Thread;

    let row = specialty;

    debug_assert!(
      row < ROWS,
      "Thread {} tried to register specialty {row}, which exceeds the number of global thread specialties {ROWS}",
      thread.id
    );

    if row >= ROWS {
      return false;
    }

    let specialists = &mut self.lut[row];

    if let Some((index, _)) = specialists.iter().enumerate().find(|(_, i)| (**i).is_null()) {
      let column = index;

      match self.lock.lock() {
        Err(err) => {
          eprintln!("{err}");
        }
        Ok(_) => {
          let mut j = 0;

          for i in 0..COLUMNS {
            let specialist = specialists[i];
            if specialist.is_null() {
              specialists[i] = identity;
              return true;
            }
          }
        }
      }
    }

    return false;
  }

  #[track_caller]
  fn deregister(&mut self, thread: &mut Thread, specialty: usize) -> bool {
    debug_assert!(COLUMNS > 0 && ROWS > 0, "Thread specialization is disabled");

    if COLUMNS == 0 || ROWS == 0 {
      return false;
    }

    let identity = thread as *mut Thread;

    let row = specialty;

    debug_assert!(
      row < ROWS,
      "Thread {} tried to deregister specialty {row}, which exceeds the number of global thread specialties {ROWS}",
      thread.id
    );

    if row >= ROWS {
      return false;
    }

    let specialists = &mut self.lut[row];

    if let Some((index, _)) = specialists.iter().enumerate().find(|(_, i)| **i == identity) {
      let column = index;

      todo!("Implement locking for table updates!");

      let new_specialists = [std::ptr::null_mut(); COLUMNS];

      let mut j = 0;

      for i in 0..COLUMNS {
        let specialist = specialists[i];
        if specialist != identity {
          new_specialists[j] = specialist;
          j += 1;
        }
      }

      *specialists = new_specialists;

      return true;
    } else {
      debug_assert!(
        false,
        "Thread tried to deregister as a {specialty} Specialist before registering"
      );
      return false;
    }
  }
}

pub trait Specialty: Into<usize> {}
impl<T: Into<usize>> Specialty for T {}

impl<const JOB_POOL_SIZE: usize, const SPECIALTY_COUNT: usize, const MAX_SPECIALISTS: usize>
  AppThreadPool<JOB_POOL_SIZE, SPECIALTY_COUNT, MAX_SPECIALISTS>
{
  /// Assigns a specialization to a thread.
  pub fn create_specialist<T: Into<usize>>(
    &self,
    specialization: T,
    mut policy: SpecializationPolicy,
  ) {
    // Thread specialization role policies
    // Exclusive - A thread can only have one specialization.
    // Family - A thread can only be a specialized in a group of specialties.
    // Unrestricted - A thread can be any type of specialist.

    // Thread specialization priority
    // Sole - A specialized thread only receives jobs from it's particular
    // specialization
    // Default - A thread prioritizes jobs for its specialization

    let specialization: usize = specialization.into();

    policy.extend(specialization);

    self.__add_global_task_base(
      Task::Command(super::ThreadDo::MakeSpecialist {
        max_tries: self.thread_count() << 1,
        tries: 0,
        visited: usize::MAX,
        policy,
        specialization,
      }),
      false,
    );
  }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SpecializationPriority {
  /// A specialized thread prioritizes its jobs in its specializations, but
  /// otherwise works on any job available to it.
  #[default]
  Default,
  /// A specialized thread only works on jobs from its particular
  /// specializations
  Exclusive,
  /// A specialized thread only works on jobs from its particular
  /// specializations and does not sleep.
  RealTime,
}

/// Configuration for how a thread can be registered as a specialist.
#[derive(Default, Debug, Clone, Copy)]
pub struct SpecializationPolicy {
  specializations: usize,
  priority:        SpecializationPriority,
}

impl SpecializationPolicy {
  pub fn build<T: Into<usize> + Copy>(priority: SpecializationPriority, family: &[T]) -> Self {
    let mut specializations = family.iter().fold(0, |a: usize, b| (a | (1usize << ((*b).into()))));

    Self { specializations, priority }
  }

  pub fn extend(&mut self, specialization: usize) {
    self.specializations |= 1 << specialization;
  }

  pub fn is_exclusive(&self) -> bool {
    self.priority > SpecializationPriority::Default
  }

  pub fn is_realtime(&self) -> bool {
    self.priority > SpecializationPriority::Exclusive
  }

  /// True if the current policy is compatible with the givin policy
  pub fn can_specialize(&self, specialization: usize, other: Self) -> bool {
    let is_not_specialized = self.specializations == 0;

    let compatible_specializations = (self.specializations & other.specializations) > 0;

    let already_specialized_as_other = (self.specializations & (1 << specialization)) > 0;

    let has_higher_priority = self.priority > other.priority;

    is_not_specialized
      || (compatible_specializations && !already_specialized_as_other && !has_higher_priority)
  }

  pub fn merge(&mut self, other: Self) {
    self.specializations |= other.specializations;
    self.priority = self.priority.max(other.priority);
  }
}

#[cfg(test)]
mod test {

  enum TestSpecialty {
    Drummer   = 1,
    Guitarist = 2,
    Harpist   = 3,
    Pianist   = 4,
  }

  impl Into<usize> for TestSpecialty {
    fn into(self) -> usize {
      match self {
        Self::Drummer => 1,
        Self::Guitarist => 2,
        Self::Harpist => 3,
        Self::Pianist => 4,
      }
    }
  }

  use std::time::Duration;

  use crate::{error::RumResult, AppThreadPool, ThreadHost};
  #[test]
  fn creates_specialists_threads() -> RumResult<()> {
    let mut pool = AppThreadPool::<8, 5, 1>::new(4)?;

    pool.create_specialist(TestSpecialty::Harpist, Default::default());
    pool.create_specialist(TestSpecialty::Pianist, Default::default());
    pool.create_specialist(TestSpecialty::Drummer, Default::default());
    pool.create_specialist(TestSpecialty::Guitarist, Default::default());

    pool.await_startup();

    std::thread::sleep(Duration::from_millis(1));

    pool.add_task_specialized(TestSpecialty::Drummer, |t| println!("Drummer: Crash!, {}", t.id()));
    pool.add_task_specialized(TestSpecialty::Guitarist, |t| {
      println!("Guitarist: PLUCK!, {}", t.id())
    });
    pool
      .add_task_specialized(TestSpecialty::Harpist, |t| println!("Harpist: Strum..., {}", t.id()));
    pool.add_task_specialized(TestSpecialty::Pianist, |t| {
      println!("Pianist: TRLRLRLRLLR!, {}", t.id())
    });

    pool.await_graceful_exit(1);

    Ok(())
  }
}
