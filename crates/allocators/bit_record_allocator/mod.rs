use std::fmt::Debug;

mod allocator;
mod bit_block_bit_type;
mod block_record;

#[cfg(test)]
mod test;

pub use allocator::{BlockRecordAllocator as AllocatorBase, RcBlockAllocator as Allocator};
pub use bit_block_bit_type::BlockBits;
