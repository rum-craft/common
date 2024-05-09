#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dur(
  /// Length of duration in nanoseconds
  pub(super) u64,
);

impl std::ops::Add<Dur> for Dur {
  type Output = Dur;

  #[inline(always)]
  fn add(self, rhs: Dur) -> Self::Output {
    Dur(self.0 + rhs.0)
  }
}

impl std::ops::Sub<Dur> for Dur {
  type Output = Dur;

  #[inline(always)]
  fn sub(self, rhs: Dur) -> Self::Output {
    Dur(self.0 - rhs.0)
  }
}

impl Dur {
  #[inline(always)]
  pub fn as_short_ms(&self) -> ShortDur {
    let ms = self.ms();

    if ms > 59999 {
      ShortDur(u16::MAX)
    } else {
      ShortDur(ms as u16)
    }
  }

  #[inline(always)]
  pub fn days(&self) -> u64 {
    self.minutes() / 24
  }

  /// The hours component of the duration
  #[inline(always)]
  pub fn hours_comp(&self) -> u64 {
    self.hours() % 24
  }

  #[inline(always)]
  pub fn hours(&self) -> u64 {
    self.minutes() / 60
  }

  /// The minutes component of the duration
  #[inline(always)]
  pub fn minutes_comp(&self) -> u64 {
    self.minutes() % 60
  }

  #[inline(always)]
  pub fn minutes(&self) -> u64 {
    self.sec() / 60
  }

  /// The seconds component of the duration
  #[inline(always)]
  pub fn sec_comp(&self) -> u64 {
    self.sec() % 60
  }

  #[inline(always)]
  pub fn sec(&self) -> u64 {
    self.ns() / 1_000_000_000
  }

  /// The milliseconds component of the duration
  #[inline(always)]
  pub fn ms_comp(&self) -> u64 {
    self.ms() % 1000
  }

  #[inline(always)]
  pub fn ms(&self) -> u64 {
    self.ns() / 1_000_000
  }

  /// The microseconds component of the duration
  #[inline(always)]
  pub fn us_comp(&self) -> u64 {
    self.ms() % 1000
  }

  #[inline(always)]
  pub fn us(&self) -> u64 {
    self.ns() / 1_000
  }

  /// The nanoseconds component of the duration
  #[inline(always)]
  pub fn ns_comp(&self) -> u64 {
    self.ms().min(999)
  }

  #[inline(always)]
  pub fn ns(&self) -> u64 {
    self.0
  }

  #[inline(always)]
  pub fn sec_f64(&self) -> f64 {
    self.ns_f64() / 1_000_000_000.0
  }

  #[inline(always)]
  pub fn ms_f64(&self) -> f64 {
    self.ns_f64() / 1_000_000.0
  }

  #[inline(always)]
  pub fn us_f64(&self) -> f64 {
    self.ns_f64() / 1_000.0
  }

  #[inline(always)]
  pub fn ns_f64(&self) -> f64 {
    self.ns() as f64
  }

  #[inline(always)]
  pub fn sec_f32(&self) -> f32 {
    self.ns_f32() / 1_000_000_000.0
  }

  #[inline(always)]
  pub fn ms_f32(&self) -> f32 {
    self.ns_f32() / 1_000_000.0
  }

  #[inline(always)]
  pub fn us_f32(&self) -> f32 {
    self.ns_f32() / 1_000.0
  }

  #[inline(always)]
  pub fn ns_f32(&self) -> f32 {
    self.ns() as f32
  }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// An time interval up to 60 seconds in length, at millisecond resolution
pub struct ShortDur(u16);

impl ShortDur {
  /// The value of the duration is out of the range which it can store. In other
  /// words, all we know is this duration >= 1 min.
  pub fn out_of_range(&self) -> bool {
    self.0 > 59999
  }

  /// The seconds component of the duration
  #[inline(always)]
  pub fn sec_comp(&self) -> u64 {
    self.sec() % 60
  }

  #[inline(always)]
  pub fn sec(&self) -> u64 {
    self.ms() / 1_000
  }

  /// The milliseconds component of the duration
  #[inline(always)]
  pub fn ms_comp(&self) -> u64 {
    self.ms() % 1000
  }

  #[inline(always)]
  pub fn ms(&self) -> u64 {
    self.0 as u64
  }
}
