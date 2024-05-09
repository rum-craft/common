use crate::Dur;

pub fn initialize_moments() {}

#[cfg(target_os = "linux")]
#[derive(Debug)]
#[repr(C)]
struct TimeSpec {
  tv_sec:  libc::time_t, /* seconds */
  tv_nsec: libc::c_long, /* nanoseconds */
}

#[cfg(target_os = "linux")]
extern "C" {
  /// Note: Most systems require the program be linked with the librt library to
  /// use this function.
  fn clock_gettime(ty: libc::clockid_t, timer: *mut TimeSpec) -> u32;
}

#[derive(Debug, Clone, Copy, Default)]
// A specific point in time
pub struct Moment(
  /// Moment in time as measured from some fixed point, which may either be the
  /// unix epoch or some undefined point in the past.
  u64,
);

impl Moment {
  /// The time since the 1970 epoch
  pub fn since_epoch() -> Moment {
    #[cfg(target_os = "linux")]
    unsafe {
      let mut timespec = TimeSpec { tv_nsec: 0, tv_sec: 0 };

      if clock_gettime(libc::CLOCK_REALTIME, &mut timespec) != 0 {
        panic!("Failed to acquire time stamp")
      }

      Self(timespec.tv_nsec as u64 + timespec.tv_sec as u64 * 1_000_000_000)
    }

    #[cfg(target_os = "win32")]
    {
      todo!("Use a windows function to get the current time stamp")
    }
  }

  /// Alias of `monotonic`
  pub fn now() -> Moment {
    Moment::monotonic()
  }

  /// An arbitrary point in time guaranteed to have occurred during or after the
  /// previous call to this method
  pub fn monotonic() -> Moment {
    #[cfg(target_os = "linux")]
    unsafe {
      let mut timespec = TimeSpec { tv_nsec: 0, tv_sec: 0 };

      if clock_gettime(libc::CLOCK_MONOTONIC, &mut timespec) != 0 {
        panic!("Failed to acquire time stamp")
      }

      Self(timespec.tv_nsec as u64 + timespec.tv_sec as u64 * 1_000_000_000)
    }

    #[cfg(target_os = "win32")]
    {
      todo!("Use a windows function to get the current time stamp")
    }
  }

  /// Duration elapsed since the start of the Monotonic system clock
  pub fn to_dur(&self) -> Dur {
    Dur(self.0)
  }

  /// Return the duration that has elapsed since this moment was created.
  pub fn since(&self) -> Dur {
    Moment::now() - *self
  }
}

impl std::ops::Sub<Moment> for Moment {
  type Output = Dur;

  fn sub(self, rhs: Moment) -> Self::Output {
    Dur(self.0 - rhs.0)
  }
}

#[test]
fn calculate_now() {
  crate::initialize_timers();

  #[cfg(target_os = "linux")]
  {
    let now = crate::Cycles::new();

    let m_now = Moment::now();

    let end = crate::Cycles::new();
    println!(
      "{}:{:0>2}:{:0>2}:{:0>2}.{:0>3} {}",
      m_now.to_dur().days(),
      m_now.to_dur().hours_comp(),
      m_now.to_dur().minutes_comp(),
      m_now.to_dur().sec_comp(),
      m_now.to_dur().ms_comp(),
      (end - now).ns()
    );

    while now.mark().sec() < 2 {
      std::thread::sleep(std::time::Duration::from_nanos(20000000));
    }

    let m_now = Moment::now();

    let end = crate::Cycles::new();
    println!(
      "{}:{:0>2}:{:0>2}:{:0>2}.{:0>3} {}",
      m_now.to_dur().days(),
      m_now.to_dur().hours_comp(),
      m_now.to_dur().minutes_comp(),
      m_now.to_dur().sec_comp(),
      m_now.to_dur().ms_comp(),
      (end - now).ns()
    );
  }
}
