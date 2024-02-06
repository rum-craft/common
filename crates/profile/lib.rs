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
