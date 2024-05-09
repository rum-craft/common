#![feature(alloc_layout_extra)]
#![feature(linkage)]

mod cycles;
mod duration;
mod engine;
mod moment;

pub use cycles::*;
pub use duration::*;
pub use engine::*;
pub use moment::*;

/// Call this during app startup to establish baselines for various timer types.
pub fn initialize_timers() {
  initialize_cycles();
  initialize_moments();
}
