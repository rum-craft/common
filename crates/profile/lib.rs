static mut CYCLES_PER_SECOND: u64 = 1_000_000_000;
static mut INITIALIZED: bool = false;
static INITIALIZE_TIME_MS: u64 = 100;

/// Needs to be called before any timer functions are used to ensure a correct
/// value for CYCLES_PER_SECOND is calculated.
pub fn initialize_timers() {
  if !unsafe { INITIALIZED } {
    unsafe { INITIALIZED = true };
    let start_ts = std::time::Instant::now();
    let mut end_ts;

    let start = get_rdtsc_64();
    let end;

    loop {
      end_ts = std::time::Instant::now();

      if (end_ts - start_ts).as_millis() as u64 >= INITIALIZE_TIME_MS {
        end = get_rdtsc_64();
        break;
      }
    }

    let dur = end_ts - start_ts;
    let total_ms = dur.as_millis();
    unsafe { CYCLES_PER_SECOND = (end - start) * (1000 / total_ms as u64) };
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cycles {
  count: i64,
}

impl std::ops::Sub<Cycles> for Cycles {
  type Output = Dur;

  fn sub(self, rhs: Cycles) -> Self::Output {
    Dur { dur: self.count - rhs.count }
  }
}

impl Default for Cycles {
  #[inline(always)]
  fn default() -> Self {
    Self { count: get_rdtsc_64() as i64 }
  }
}

impl Cycles {
  #[inline(always)]
  pub fn new() -> Self {
    Cycles::default()
  }

  #[inline(always)]
  pub fn count(&self) -> u64 {
    self.count as u64
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dur {
  dur: i64,
}

impl std::ops::Add<Dur> for Dur {
  type Output = Dur;

  #[inline(always)]
  fn add(self, rhs: Dur) -> Self::Output {
    Dur { dur: self.dur + rhs.dur }
  }
}

impl std::ops::Sub<Dur> for Dur {
  type Output = Dur;

  #[inline(always)]
  fn sub(self, rhs: Dur) -> Self::Output {
    Dur { dur: self.dur - rhs.dur }
  }
}

impl Dur {
  pub fn sec(&self) -> i64 {
    self.dur as i64 / unsafe { CYCLES_PER_SECOND as i64 }
  }

  pub fn ms(&self) -> i64 {
    (self.dur as i64 * 1_000) / unsafe { CYCLES_PER_SECOND as i64 }
  }

  pub fn us(&self) -> i64 {
    (self.dur as i64 * 1_000_000) / unsafe { CYCLES_PER_SECOND as i64 }
  }

  pub fn ns(&self) -> i64 {
    (self.dur as i64 * 1_000_000_000) / unsafe { CYCLES_PER_SECOND as i64 }
  }

  pub fn sec_f64(&self) -> f64 {
    self.dur as f64 / unsafe { CYCLES_PER_SECOND as f64 }
  }

  pub fn ms_f64(&self) -> f64 {
    (self.dur as f64 * 1_000.0) / unsafe { CYCLES_PER_SECOND as f64 }
  }

  pub fn us_f64(&self) -> f64 {
    (self.dur as f64 * 1_000_000.0) / unsafe { CYCLES_PER_SECOND as f64 }
  }

  pub fn ns_f64(&self) -> f64 {
    (self.dur as f64 * 1_000_000_000.0) / unsafe { CYCLES_PER_SECOND as f64 }
  }

  pub fn sec_f32(&self) -> f32 {
    self.dur as f32 / unsafe { CYCLES_PER_SECOND as f32 }
  }

  pub fn ms_f32(&self) -> f32 {
    (self.dur as f32 * 1_000.0) / unsafe { CYCLES_PER_SECOND as f32 }
  }

  pub fn us_f32(&self) -> f32 {
    (self.dur as f32 * 1_000_000.0) / unsafe { CYCLES_PER_SECOND as f32 }
  }

  pub fn ns_f32(&self) -> f32 {
    (self.dur as f32 * 1_000_000_000.0) / unsafe { CYCLES_PER_SECOND as f32 }
  }
}

#[test]
fn test() {
  initialize_timers();

  let start_ts = std::time::Instant::now();

  let now = Cycles::default();

  while (Cycles::default() - now).sec_f64() < 1.5 {}

  let result = Cycles::default() - now;
  let other_result = std::time::Instant::now() - start_ts;
  let result2 = Cycles::default() - now;

  let result2 = result2 - result;

  println!(
    "Dur {} {} : Duration {} CPS {}",
    result.sec_f32(),
    result2.us_f32(),
    other_result.as_secs_f32(),
    unsafe { CYCLES_PER_SECOND }
  );
}

pub struct NSReporter {
  name:  &'static str,
  start: Cycles,
}

impl NSReporter {
  pub fn new(name: &'static str) -> Self {
    Self { name, start: Cycles::new() }
  }

  pub fn report(&self) {
    let dur = Cycles::new() - self.start;
    println!("{} -- {}ns", self.name, dur.ns());
  }
}

impl Drop for NSReporter {
  fn drop(&mut self) {
    //self.report()
  }
}

use std::arch::asm;
#[test]
fn maidn() {
  let start_ts = std::time::Instant::now();
  let mut end_ts;

  let ms = 50;

  let start = get_rdtsc_64();
  let end;
  loop {
    end_ts = std::time::Instant::now();

    if (end_ts - start_ts).as_millis() as u64 >= ms {
      end = get_rdtsc_64();
      break;
    }
  }

  let dur = end_ts - start_ts;
  let total_ms = dur.as_millis();
  let counts_per_second = (end - start) * (1000 / total_ms as u64);

  println!(
    "
elapsed ms : {}
rdtsc      : {}
csps       : {} // Clock ticks per second
GHz        : {} // CPU Frequency",
    total_ms,
    (end - start),
    counts_per_second,
    (end - start) as f64 / 1_000_000_000.0 * (1000.0 / total_ms as f64)
  );

  let end_ts;

  let rdtsc = counts_per_second * 10;

  let mut end;
  let start_ts = std::time::Instant::now();
  let start = get_rdtsc_64();
  loop {
    end = get_rdtsc_64();
    if (end - start) >= rdtsc {
      end_ts = std::time::Instant::now();
      break;
    }
  }

  let seconds: f64 = ((end - start) as f64) / counts_per_second as f64 * 1_000_000_000.0;

  println!("ns {seconds} Instant {}", (end_ts - start_ts).as_nanos());
}

#[inline]
#[cfg(all(target_arch = "x86_64"))]
/// note: Roughly `10`-`40ns` overhead
pub fn get_rdtsc_64() -> u64 {
  let mut val;
  unsafe {
    // x86-64: EDX + EAX are set with program counter information
    // EDX has high 32
    // EAX has low 32
    asm!("rdtsc", "shl rdx, 32", "or rax, rdx", "mov {0}, rax", out(reg) val);
  }

  val
}
/// note: Roughly `10`-`40ns` overhead
#[inline]
#[cfg(all(target_arch = "x86_64"))]
pub fn get_rdtsc() -> u64 {
  let mut val;
  unsafe {
    // x86-64: EDX + EAX are set with program counter information
    // EDX has high 32
    // EAX has low 32
    asm!("rdtsc", "mov {0}, rax", out(reg) val);
  }
  val
}
