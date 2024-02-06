use rum_profile::NSReporter;

use super::{block_record::BlockRecord, Allocator as BlockAllocator};
use crate::bit_record_allocator::allocator::BitState;

#[test]
pub fn block() {
  let mut block = BlockRecord::<u64>::default();
  block.set_nibble(0, BitState::Partial);
  assert_eq!(block.iter_blocks().next().unwrap().0, BitState::Partial);

  let mut block = BlockRecord::<u64>::default();
  block.set_nibble(0, BitState::Full);
  assert_eq!(block.iter_blocks().next().unwrap().0, BitState::Full);

  let mut block = BlockRecord::<u64>::default();
  block.set_nibble(0, BitState::Sub);
  assert_eq!(block.iter_blocks().next().unwrap().0, BitState::Sub);

  let mut block = BlockRecord::<u64>::default();
  block.set_nibble(0, BitState::Empty);
  assert_eq!(block.iter_blocks().next().unwrap().0, BitState::Empty);

  let mut block = BlockRecord::<u64>::default();
  for bit in 0..block.len() {
    block.set_nibble(bit, BitState::Full);
  }
  assert_eq!(block.is_full(), true);

  let mut block = BlockRecord::<u64>::default();
  for bit in 0..block.len() {
    block.set_nibble(bit, BitState::Sub);
  }
  assert_eq!(block.is_full(), true);

  let mut block = BlockRecord::<u64>::default();
  for bit in 0..block.len() {
    block.set_nibble(bit, BitState::Partial);
  }
  assert_eq!(block.is_full(), false);

  let mut block = BlockRecord::<u64>::default();
  for bit in 0..block.len() {
    block.set_nibble(bit, BitState::Empty);
  }
  assert_eq!(block.is_full(), false);

  let mut block = BlockRecord::<u64>::default();
  for bit in 0..block.len() {
    block.set_nibble(bit, BitState::Full);
  }

  for bit in 10..block.len() {
    block.set_nibble(bit, BitState::Partial);
  }

  dbg!(block);

  assert_eq!(block.iter_blocks().collect::<Vec<_>>()[0].0, BitState::Full);
}

#[test]
pub fn basic_allocations() {
  let data = BlockAllocator::<1, u8, _>::create(128).expect("Should be fine!");

  unsafe {
    *data.alloc(1).expect("should have space") = 'h' as u8;
    *data.alloc(1).expect("should have space") = 'e' as u8;
    dbg!(&data);
    *data.alloc(1).expect("should have space") = 'l' as u8;
    *data.alloc(1).expect("should have space") = 'l' as u8;
    dbg!(&data);
    *data.alloc(1).expect("should have space") = 'o' as u8;
    *data.alloc(1).expect("should have space") = ' ' as u8;
    dbg!(&data);
    *data.alloc(1).expect("should have space") = 'w' as u8;
    *data.alloc(1).expect("should have space") = 'o' as u8;
    dbg!(&data);
    *data.alloc(1).expect("should have space") = 'r' as u8;
    *data.alloc(1).expect("should have space") = 'l' as u8;

    let penult = data.alloc(1).expect("should have space");
    *penult = 'd' as u8;

    dbg!(&data);

    let last = data.alloc(1).expect("should have space");
    *last = 'd' as u8;

    let allocatted_string =
      String::from_utf8(std::slice::from_raw_parts(data.data(), ("hello world".len())).to_vec()).expect("should be utf8 (ASCII)");

    debug_assert_eq!(allocatted_string, "hello world");

    data.free(penult).expect("Corrupted pointer!");
    dbg!(&data);
    data.free(last).expect("Corrupted pointer!");

    dbg!(&data);
  }
}

#[test]
fn unfulfilled_allocation_results_in_none() {
  let allocator = BlockAllocator::<32, u16, _>::create(1024).expect("Should be fine!");
  allocator.alloc(512).expect("Should have space");
  allocator.alloc(512).expect("Should have space");
  assert!(allocator.alloc(512).is_none());

  let allocator = BlockAllocator::<32, u32, _>::create(1024).expect("Should be fine!");
  allocator.alloc(512).expect("Should have space");
  allocator.alloc(512).expect("Should have space");
  assert!(allocator.alloc(512).is_none());
}

#[test]
pub fn test() {
  let data = 0b1111_0011_0110_1011u16;
  let mut x = data;

  let len = 2;
  for _ in 0..(len - 1) {
    x = x & (x << 1);
  }

  let leading = x.leading_zeros();
  println!("{data:0>16b} {x:0>16b} {}", 16 - leading)
}

#[test]
pub fn inter_block_allocations() {
  let allocator = BlockAllocator::<1, u32, _>::create(1024).expect("Should be fine!");
  dbg!(&allocator);
  let r = NSReporter::new("alloc");
  let ptr = allocator.alloc(25).expect("should have space");
  r.report();
  dbg!(&allocator);
  let r = NSReporter::new("alloc");
  let ptr = allocator.alloc(8).expect("should have space");
  r.report();
  dbg!(&allocator);
  let r = NSReporter::new("alloc");
  allocator.free(ptr).unwrap();
  r.report();
  dbg!(&allocator);
}

#[test]
pub fn massive_allocation_1GB() {
  const _1GB: usize = 1024 * 1024 * 1024;
  let r = NSReporter::new("create");
  let allocator = BlockAllocator::<1024, u32, _>::create(_1GB).expect("Should be fine!");

  r.report();
  let r = NSReporter::new("alloc");
  let ptr = allocator.alloc(_1GB).expect("should have space");
  r.report();

  let r = NSReporter::new("free");
  assert!(allocator.alloc(_1GB).is_none());
  r.report();
  allocator.free(ptr);
  let r = NSReporter::new("alloc");
  let ptr = allocator.alloc(_1GB >> 1).expect("Should allocate");
  r.report();
  let r = NSReporter::new("alloc");
  let ptr = allocator.alloc(_1GB >> 1).expect("Should allocate");
  r.report();
}

#[test]
pub fn multi_block_allocations() {
  let allocator = BlockAllocator::<4, u16, _>::create(512).expect("Should be fine!");

  let ptr = allocator.alloc(1).expect("should have space");
  dbg!(&allocator);
  let ptr_a = allocator.alloc(3).expect("should have space");
  dbg!(&allocator);
  let ptr_b = allocator.alloc(8).expect("should have space");
  dbg!(&allocator);
  let ptr_c = allocator.alloc(3).expect("should have space");
  dbg!(&allocator);
  let ptr_c = allocator.alloc(3).expect("should have space");
  dbg!(&allocator);
  let ptr_c = allocator.alloc(64).expect("should have space");
  dbg!(&allocator);
  allocator.alloc(1).expect("should have space");
  dbg!(&allocator);
  allocator.free(ptr_a).expect("Corrupted pointer!");
  dbg!(&allocator);
  allocator.free(ptr_b).expect("Corrupted pointer!");
  dbg!(&allocator);
  allocator.free(ptr_c).expect("Corrupted pointer!");
  dbg!(&allocator);
}
