pub struct NSReporter {
  name:  &'static str,
  start: std::time::Instant,
}

impl NSReporter {
  pub fn new(name: &'static str) -> Self {
    Self { name, start: std::time::Instant::now() }
  }

  pub fn report(&self) {
    let now = std::time::Instant::now();
    let dur = now - self.start;
    println!("{} -- {}ns", self.name, dur.as_nanos());
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

  let ms = 10;

  let start = get_rdtsc_64();
  let end;
  loop {
    end_ts = std::time::Instant::now();

    if (end_ts - start_ts).as_millis() as u64 >= ms {
      end = get_rdtsc_64();
      break;
    }
  }

  let dur = (end_ts - start_ts);

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
