use num_traits::{PrimInt, Unsigned};
use std::fmt::Binary;

pub(crate) const fn get_sub_table_start(depth: usize, pow_shift: usize) -> usize {
  if depth == 0 {
    0
  } else {
    let mut offset = 1;
    let mut i = 1;

    loop {
      if i >= depth {
        break;
      }
      offset += 1 << (pow_shift * i);
      i += 1;
    }
    offset
  }
}

const fn create_block_offset_lookup_table<const POW_SHIFTS: usize>() -> [u32; 8] {
  [
    0u32,
    1u32,
    get_sub_table_start(2, POW_SHIFTS) as u32,
    get_sub_table_start(3, POW_SHIFTS) as u32,
    get_sub_table_start(4, POW_SHIFTS) as u32,
    get_sub_table_start(5, POW_SHIFTS) as u32,
    get_sub_table_start(6, POW_SHIFTS) as u32,
    get_sub_table_start(7, POW_SHIFTS) as u32,
  ]
}

const fn create_power_shift_lut<const POW_SHIFTS: usize>() -> [usize; 8] {
  [POW_SHIFTS * 0, POW_SHIFTS * 1, POW_SHIFTS * 2, POW_SHIFTS * 3, POW_SHIFTS * 4, POW_SHIFTS * 5, POW_SHIFTS * 6, POW_SHIFTS * 7]
}

const fn create_sub_block_table_lookup_table<const POW_SHIFTS: usize>() -> [usize; 8] {
  [
    1usize,
    1 << (POW_SHIFTS),
    1 << (POW_SHIFTS * 2),
    1 << (POW_SHIFTS * 3),
    1 << (POW_SHIFTS * 4),
    1 << (POW_SHIFTS * 5),
    1 << (POW_SHIFTS * 6),
    1 << (POW_SHIFTS * 7),
  ]
}

pub trait BlockBits: Unsigned + PrimInt + Binary {
  /// Total number of bits used by this type
  fn bit_count() -> usize;

  /// Total number of shifts to need to raise binary 1 to the bit count power.
  fn pow_shifts() -> usize;

  fn name() -> &'static str;

  /// Lookup table of block set offsets
  fn block_group_offset_lut() -> &'static [u32; 8];

  /// Lookup table of block group table sizes
  fn block_group_size_lut() -> &'static [usize; 8];

  /// Lookup table for powers shift values
  fn power_shift_lut() -> &'static [usize; 8];

  // Shift left unchecked
  fn shl_unchecked(&self, other: u32) -> Self;

  fn sub_unchecked(&self, other: Self) -> Self;
}

macro_rules! block_bit_type {
  ($primitive:ty, $primitive_name_str:literal, $bit_count:literal, $pow_shifts:literal) => {
    impl BlockBits for $primitive {
      #[inline(always)]
      fn bit_count() -> usize {
        $bit_count
      }

      #[inline(always)]
      fn pow_shifts() -> usize {
        $pow_shifts
      }

      #[inline(always)]
      fn name() -> &'static str {
        $primitive_name_str
      }

      #[inline(always)]
      fn block_group_offset_lut() -> &'static [u32; 8] {
        const LUT: [u32; 8] = create_block_offset_lookup_table::<$pow_shifts>();
        &LUT
      }

      #[inline(always)]
      fn block_group_size_lut() -> &'static [usize; 8] {
        const LUT: [usize; 8] = create_sub_block_table_lookup_table::<$pow_shifts>();
        &LUT
      }

      #[inline(always)]
      fn power_shift_lut() -> &'static [usize; 8] {
        const LUT: [usize; 8] = create_power_shift_lut::<$pow_shifts>();
        &LUT
      }

      #[inline(always)]
      fn shl_unchecked(&self, other: u32) -> Self {
        unsafe { self.unchecked_shl(other) }
      }

      #[inline(always)]
      fn sub_unchecked(&self, other: Self) -> Self {
        unsafe { self.unchecked_sub(other) }
      }
    }
  };
}

block_bit_type!(u8, "u8", 8, 3);
block_bit_type!(u16, "u16", 16, 4);
block_bit_type!(u32, "u32", 32, 5);
block_bit_type!(u64, "u64", 64, 6);
block_bit_type!(u128, "u128", 128, 7);

#[test]
pub fn evaluate_lut() {
  assert_eq!(get_sub_table_start(0, u8::pow_shifts()), 0);
  assert_eq!(get_sub_table_start(1, u8::pow_shifts()), 1);
  assert_eq!(get_sub_table_start(2, u8::pow_shifts()), 9);
  assert_eq!(get_sub_table_start(3, u8::pow_shifts()), 73);

  assert_eq!(u8::block_group_offset_lut()[0], 0);
  assert_eq!(u8::block_group_offset_lut()[1], 1);
  assert_eq!(u8::block_group_offset_lut()[2], 9);
  assert_eq!(u8::block_group_offset_lut()[3], 73);

  assert_eq!(get_sub_table_start(0, u64::pow_shifts()), 0);
  assert_eq!(get_sub_table_start(1, u64::pow_shifts()), 1);
  assert_eq!(get_sub_table_start(2, u64::pow_shifts()), 65);
  assert_eq!(get_sub_table_start(3, u64::pow_shifts()), 4161);

  assert_eq!(u64::block_group_offset_lut()[0], 0);
  assert_eq!(u64::block_group_offset_lut()[1], 1);
  assert_eq!(u64::block_group_offset_lut()[2], 65);
  assert_eq!(u64::block_group_offset_lut()[3], 4161);

  assert_eq!(u64::block_group_size_lut()[0], 1);
  assert_eq!(u64::block_group_size_lut()[1], 64);
  assert_eq!(u64::block_group_size_lut()[2], 64 * 64);
  assert_eq!(u64::block_group_size_lut()[3], 64 * 64 * 64);

  assert_eq!(u32::block_group_size_lut()[0], 1);
  assert_eq!(u32::block_group_size_lut()[1], 32);
  assert_eq!(u32::block_group_size_lut()[2], 32 * 32);
  assert_eq!(u32::block_group_size_lut()[3], 32 * 32 * 32);

  assert_eq!(u8::block_group_size_lut()[0], 1);
  assert_eq!(u8::block_group_size_lut()[1], 8);
  assert_eq!(u8::block_group_size_lut()[2], 8 * 8);
  assert_eq!(u8::block_group_size_lut()[3], 8 * 8 * 8);
}
