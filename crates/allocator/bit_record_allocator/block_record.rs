use super::{
  allocator::{BitState, BitState::*},
  bit_block_bit_type::BlockBits,
};
use std::fmt::Debug;

#[derive(Default, Clone, Copy)]
pub(crate) struct BlockRecord<BitType: BlockBits> {
  /// If a particular bit is set, then the corresponding memory block contains
  /// one or more allocations.
  pub(super) alloc_bits_l:     BitType,
  /// - If set, and the corresponding bit in `alloc_bits` is set, the
  /// allocation if "fully" allocated, and there is no free space in the
  /// block.
  ///
  /// - If set and the corresponding bit in `alloc_bits` is not set, the
  ///   allocation
  /// is part of a of "full" allocation, with the head block located in a
  /// proceeding pair of `alloc_bit`  and `sub_alloc_bit` that are both set.
  ///
  /// - If not set, and the corresponding bit in `alloc_bits` is set, then this
  ///   is a single partial allocation, and the corresponding sub-block header
  ///   must be
  /// investigated to see if there is free space available.
  pub(super) sub_alloc_bits_h: BitType,
}

impl<BitType: BlockBits> Debug for BlockRecord<BitType> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    //f.write_fmt(format_args!("Rec<{}>", BitType::name()))?;

    //  f.write_str(" [ ")?;
    f.write_str(" ")?;

    for (ty, index) in self.iter_blocks() {
      if index > 0 && (index % 4) == 0 {
        f.write_str("_")?;
      }
      match ty {
        Empty => f.write_str("0")?,
        Partial => f.write_str("p")?,
        Full => f.write_str("F")?,
        Sub => f.write_str("S")?,
      }
    }
    f.write_str(" ")?;

    //   f.write_str(" ] ")?;

    Ok(())
  }
}

impl<BitType: BlockBits> BlockRecord<BitType> {
  pub fn iter_blocks(&self) -> impl Iterator<Item = (BitState, usize)> {
    let copy = *self;
    (0..BitType::bit_count() as usize).into_iter().map(move |i| {
      let offset = i;
      let nibble = copy.get_nibble(offset);

      (BitState::from(nibble), offset)
    })
  }

  #[inline(always)]
  pub(crate) fn get_nibble(&self, offset: usize) -> BitState {
    let l = unsafe {
      ((self.alloc_bits_l.unsigned_shr(offset as u32)) & BitType::one()).to_u8().unwrap_unchecked()
    };
    let h = unsafe {
      ((self.sub_alloc_bits_h.unsigned_shr(offset as u32)) & BitType::one())
        .to_u8()
        .unwrap_unchecked()
    };
    let nibble = l as u8 | ((h as u8) << 1);
    BitState::from(nibble)
  }

  #[inline(always)]
  pub fn set_nibble(&mut self, bit: usize, state: BitState) {
    debug_assert!(bit < BitType::bit_count());
    unsafe {
      let lower = BitType::from((state as u8) & 0b1).unwrap_unchecked() << bit;
      let lower_mask = !(BitType::one() << bit);
      let upper = BitType::from(((state as u8) & 0b10) >> 1).unwrap_unchecked() << bit;
      let upper_mask = !(BitType::one() << bit);

      self.alloc_bits_l = (self.alloc_bits_l & lower_mask) | lower;
      self.sub_alloc_bits_h = (self.sub_alloc_bits_h & upper_mask) | upper;
    }
  }

  #[inline(always)]
  pub fn clear(&mut self) {
    self.alloc_bits_l = BitType::zero();
    self.sub_alloc_bits_h = BitType::zero();
  }

  #[inline(always)]
  pub fn free_bits(&self) -> BitType {
    (!self.alloc_bits_l) & (!self.sub_alloc_bits_h)
  }

  #[inline(always)]
  pub fn is_full(&self) -> bool {
    (self.alloc_bits_l ^ self.sub_alloc_bits_h) == BitType::max_value()
  }

  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    (self.alloc_bits_l | self.sub_alloc_bits_h) == BitType::zero()
  }

  /// Returns the state of this block as it would appear in a higher order
  /// block.
  #[inline(always)]
  pub fn get_super_state(&self) -> BitState {
    self
      .is_full()
      .then_some(Full)
      .unwrap_or_else(|| self.is_empty().then_some(Empty).unwrap_or(Partial))
  }

  #[allow(unused)]
  pub fn len(&self) -> usize {
    BitType::bit_count()
  }
}
