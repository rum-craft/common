extern crate rum_profile_macro;
pub use rum_profile_macro::{profile_block, profile_block_droppable};
use std::{fmt::Debug, sync::atomic::Ordering::*, time::Duration};

use crate::Cycles;

static mut ENGINE: ProfileEngine = ProfileEngine::new();

pub struct ProfileBlock {
  pub profile_id:  u64,
  pub cycle:       Cycles,
  pub identifier:  &'static str,
  pub source_path: &'static str,
  pub line_number: usize,
}

impl Drop for ProfileBlock {
  fn drop(&mut self) {
    let end = Cycles::new();
    unsafe { ENGINE.add_entry(self, end) }
  }
}

impl ProfileBlock {
  pub fn new(
    id: u64,
    identifier: &'static str,
    source_path: &'static str,
    line_number: usize,
  ) -> Self {
    ProfileBlock {
      profile_id: id,
      cycle: Cycles::new(),
      identifier,
      source_path,
      line_number,
    }
  }
}

pub static GLOBAL_ID_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

#[repr(align(64))]
#[derive(Clone, Copy)]
struct BlockId {
  iterations:  u64,
  avg_time:    f64,
  min:         f64,
  max:         f64,
  identifier:  &'static str,
  source:      &'static str,
  line_number: usize,
}

impl Debug for BlockId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut s = f.debug_struct(self.identifier);
    s.field("avg(ns)", &(self.avg_time));
    s.field("avg(us)", &(self.avg_time / 1_000.0));
    s.field("avg(ms)", &(self.avg_time / 1_000_000.0));
    s.field("path", &self.source);
    s.field("iterations", &self.iterations);
    s.finish()
  }
}

static DEFAULT_STR: &'static str = "";

impl Default for BlockId {
  fn default() -> Self {
    Self {
      iterations:  0,
      avg_time:    0.0,
      min:         f64::MAX,
      max:         f64::MIN,
      identifier:  DEFAULT_STR,
      source:      DEFAULT_STR,
      line_number: 0,
    }
  }
}

pub struct ProfileEngine {
  len:     std::sync::atomic::AtomicU64,
  entries: *mut BlockId,
}

unsafe impl Sync for ProfileEngine {}

impl ProfileEngine {
  pub fn report() {
    for (id, entry) in unsafe { ENGINE.slice().iter().enumerate() } {
      if id > 0 && entry.identifier.as_ptr() == DEFAULT_STR.as_ptr() {
        break;
      } else if id == 0 {
        continue;
      }

      eprintln!("[{id}] = {entry:#?}")
    }
  }

  const fn new() -> Self {
    Self {
      entries: std::ptr::null_mut(),
      len:     std::sync::atomic::AtomicU64::new(0),
    }
  }

  unsafe fn slice(&self) -> &[BlockId] {
    let len = self.len.load(Acquire);
    let own_ptr = self.entries;
    std::slice::from_raw_parts_mut(own_ptr, len as usize)
  }

  #[inline]
  fn add_entry(&mut self, block: &mut ProfileBlock, end: Cycles) {
    let len = self.len.load(Acquire);

    if len == u64::MAX {
      std::thread::sleep(Duration::from_nanos(1500));
      return self.add_entry(block, end);
    } else if len <= block.profile_id {
      match self.len.compare_exchange_weak(len, u64::MAX, Acquire, Relaxed) {
        Err(_) => {
          // Failed to obtain lock. Wait and retry.
          std::thread::sleep(Duration::from_nanos(500));
          self.add_entry(block, end);
        }
        Ok(old_len) => unsafe {
          // Increase the size of the entries pool;
          let new_len = (block.profile_id << 1).max(old_len << 1).max(512);

          let own_ptr = self.entries;

          let (layout, _) = std::alloc::Layout::new::<BlockId>()
            .repeat(new_len as usize)
            .expect("Could not build ProfileEngine Entries");

          let new_buffer: *mut BlockId = std::alloc::alloc(layout) as _;

          let old_data = if old_len > 0 {
            ::std::ptr::copy_nonoverlapping(own_ptr, new_buffer, old_len as usize);

            for entry in std::slice::from_raw_parts_mut(
              new_buffer.offset(old_len as isize),
              (new_len - old_len) as usize,
            ) {
              *entry = BlockId::default();
            }

            (own_ptr, old_len as usize)
          } else {
            for entry in std::slice::from_raw_parts_mut(new_buffer, new_len as usize) {
              *entry = BlockId::default();
            }

            (std::ptr::null_mut(), 0)
          };

          self.entries = new_buffer;

          if let Err(err) = self.len.compare_exchange_weak(u64::MAX, new_len, Release, Relaxed) {
            panic!("len atomic has been corrupted! {err}");
          }

          if old_data.1 > 0 {
            let (layout, _) = std::alloc::Layout::new::<BlockId>()
              .repeat(old_data.1 as usize)
              .expect("Could not build ProfileEngine Entries");

            std::alloc::dealloc(old_data.0 as _, layout)
          }

          self.add_entry(block, end);
        },
      }
    } else {
      unsafe {
        let ptr: *mut BlockId = self.entries.offset(block.profile_id as isize);
        let entry = &mut *ptr;

        let dur = end - block.cycle;

        let ns = dur.ns_f64();

        entry.min = entry.min.min(ns);
        entry.max = entry.max.max(ns);

        entry.iterations += 1;

        let e_f64 = entry.iterations as f64;
        let p1_w = (e_f64 - 1.0) / e_f64;
        let p2_w = 1.0 / e_f64;

        entry.avg_time = entry.avg_time * p1_w + ns * p2_w;

        if entry.identifier.as_ptr() == DEFAULT_STR.as_ptr() {
          entry.identifier = block.identifier;
          entry.source = block.source_path;
          entry.line_number = block.line_number;
        }
      }
    }
  }
}
