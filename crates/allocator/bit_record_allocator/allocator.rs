use std::{
  alloc::{Allocator, Global},
  fmt::Debug,
  marker::PhantomData,
  ptr::NonNull,
};

use super::{bit_block_bit_type::BlockBits, block_record::BlockRecord};

pub(crate) struct BlockIter<BitType: BlockBits> {
  pub(crate) header: BlockRecord<BitType>,
  pub(crate) mode:   usize,
  pub(crate) index:  usize,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
#[repr(u8)]
pub enum BitState {
  /// The data range defined by this bit is free to be allocated.
  /// All free space.
  Empty   = 0b00,
  /// The data range defined by this bit is fully allocated.
  /// No Free space
  Full    = 0b01,
  /// The data range defined by this bit is a member of a full allocation.
  /// No  Free space
  Sub     = 0b10,
  /// 0b11 = The data range defined by this bit is partially allocated.
  /// May free space.
  Partial = 0b11,
}

impl From<u8> for BitState {
  fn from(value: u8) -> Self {
    match value {
      0b00 => Self::Empty,
      0b10 => Self::Sub,
      0b01 => Self::Full,
      0b11 => Self::Partial,
      _ => unreachable!(),
    }
  }
}

/// Returns the number of records for a given `level`
pub(crate) fn get_record_len<BitType: BlockBits>(level: usize) -> usize {
  let mut block_count = 0;
  for level in 0..level {
    block_count += BitType::bit_count().pow(level as u32);
  }
  block_count
}

#[allow(dead_code)]
pub(crate) const fn const_assert_is_power_of_2(val: usize) {
  assert!(val.is_power_of_two(), "Expected power of 2.");
}

impl<BitType: BlockBits> Iterator for BlockIter<BitType> {
  type Item = (BitState, usize);

  fn next(&mut self) -> Option<Self::Item> {
    let val = if self.index < BitType::bit_count() { Some((self.header.get_nibble(self.index), self.index)) } else { None };

    self.index += 1;

    val
  }
}

pub(crate) struct AllocResult {
  pub(crate) ptr_offset:    usize,
  pub(crate) is_full_block: bool,
  pub(crate) adjacent:      Option<bool>,
}

pub struct RcBlockAllocator<
  const BASE_ALLOC_SIZE: usize,
  BitType: BlockBits,
  A: Allocator = Global,
  const MANAGER_ALLOCATOR: bool = false,
>(pub(crate) *mut BlockRecordAllocator<BASE_ALLOC_SIZE, BitType, MANAGER_ALLOCATOR>, PhantomData<A>);

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits> RcBlockAllocator<BASE_ALLOC_SIZE, BitType, Global, false> {
  #[inline(always)]
  pub fn new(size: usize) -> Result<RcBlockAllocator<BASE_ALLOC_SIZE, BitType, Global, false>, std::alloc::AllocError> {
    BlockRecordAllocator::new(size, Global)
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, A: Allocator> RcBlockAllocator<BASE_ALLOC_SIZE, BitType, A, false> {
  #[inline(always)]
  pub fn from_allocator(size: usize, allocator: A) -> Result<Self, std::alloc::AllocError> {
    BlockRecordAllocator::new(size, allocator)
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits> RcBlockAllocator<BASE_ALLOC_SIZE, BitType, Global, true> {
  #[inline(always)]
  pub fn new_managed(
    block_head: *mut u8,
    data_len: usize,
  ) -> Result<RcBlockAllocator<BASE_ALLOC_SIZE, BitType, Global, true>, std::alloc::AllocError> {
    BlockRecordAllocator::new_managed(block_head, data_len, Global)
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, A: Allocator, const MANAGER_ALLOCATOR: bool>
  RcBlockAllocator<BASE_ALLOC_SIZE, BitType, A, MANAGER_ALLOCATOR>
{
  #[inline(always)]
  pub fn base_allocation_size(size: usize) -> usize {
    0
  }

  #[inline(always)]
  pub fn base_header_size(size: usize) -> usize {
    0
  }

  #[inline(always)]
  pub(crate) fn data(&self) -> *mut u8 {
    unsafe { self.0.as_mut().unwrap_unchecked().data }
  }

  #[inline(always)]
  pub fn alloc(&self, size: usize) -> Option<*mut u8> {
    unsafe { self.0.as_mut().unwrap_unchecked().alloc(size) }
  }

  #[inline(always)]
  pub fn free(&self, ptr: *mut u8) -> Result<(), String> {
    unsafe { self.0.as_mut().unwrap_unchecked().free(ptr) }
  }

  #[inline(always)]
  pub fn is_full(&self) -> bool {
    unsafe { self.0.as_ref().unwrap_unchecked().is_full() }
  }

  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    !self.is_full()
  }
}

unsafe impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, A: Allocator> Allocator
  for RcBlockAllocator<BASE_ALLOC_SIZE, BitType, A>
{
  fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
    let size = layout.size();
    match unsafe { self.alloc(size) } {
      Some(ptr) => Ok(unsafe { std::ptr::NonNull::<[u8]>::new_unchecked(std::ptr::slice_from_raw_parts_mut(ptr, size)) }),
      None => Err(std::alloc::AllocError),
    }
  }

  unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, _: std::alloc::Layout) {
    let ptr = ptr.as_ptr();
    self.free(ptr).expect("Could not free pointer");
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, A: Allocator, const M: bool> Debug
  for RcBlockAllocator<BASE_ALLOC_SIZE, BitType, A, M>
{
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    unsafe { self.0.as_ref().unwrap_unchecked().fmt(f) }
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, A: Allocator> Clone for RcBlockAllocator<BASE_ALLOC_SIZE, BitType, A> {
  fn clone(&self) -> Self {
    unsafe { self.0.as_mut().unwrap_unchecked().references += 1 };
    Self(self.0, self.1)
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, A: Allocator, const MANAGER_ALLOCATOR: bool> Drop
  for RcBlockAllocator<BASE_ALLOC_SIZE, BitType, A, MANAGER_ALLOCATOR>
{
  fn drop(&mut self) {
    unsafe {
      let allocator = self.0.as_mut().unwrap_unchecked();
      allocator.references -= 1;
      if allocator.references == 0 {
        allocator.std_free::<A>();
      }
    };
  }
}

pub struct BlockRecordAllocator<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, const MANAGER_ALLOCATOR: bool = false> {
  pub(crate) records:     *mut BlockRecord<BitType>,
  pub(crate) data:        *mut u8,
  pub(crate) records_len: usize,
  pub(crate) data_len:    usize,
  pub(crate) base_level:  usize,
  pub(crate) block_size:  usize,
  pub(crate) references:  usize,
  offsets:                [u32; 8],
  lengths:                [usize; 8],
  split_allocation:       bool,
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits> BlockRecordAllocator<BASE_ALLOC_SIZE, BitType, true> {
  /// Allocates memory from an externally owned memory block.
  ///
  /// # Safety
  ///
  /// The lifetime of pointers allocated from this allocator should not outlive
  /// the lifetime of the allocator, which in turn should not
  /// outlive the lifetime of `block_head`
  pub fn new_managed<A: Allocator>(
    block_head: *mut u8,
    data_len: usize,
    base_allocator: A,
  ) -> Result<RcBlockAllocator<BASE_ALLOC_SIZE, BitType, A, true>, std::alloc::AllocError> {
    match Self::create_bit_record_allocator(data_len) {
      Some((records_len, base_level, offsets, sizes)) => {
        let Ok((alloc_struct, par_allocator, record_layout, ..)) = Self::get_layouts::<A>(records_len, data_len) else {
          return Err(std::alloc::AllocError);
        };

        let root_layout = alloc_struct.extend(par_allocator).unwrap().0.extend(record_layout).unwrap().0;

        let ptr = base_allocator.allocate_zeroed(root_layout)?.as_ptr() as *mut u8;

        let root = unsafe { &mut *(ptr as *mut Self) };

        let alloc_offset = alloc_struct.size() + alloc_struct.padding_needed_for(par_allocator.align());
        let records_offset = alloc_offset + par_allocator.size() + par_allocator.padding_needed_for(record_layout.align());

        let mut allocator = Some(base_allocator);
        unsafe { std::mem::swap(&mut *(ptr.offset(alloc_offset as isize) as *mut _), &mut allocator) };
        std::mem::forget(allocator);

        root.records = unsafe { ptr.offset(records_offset as isize) as *mut _ };
        root.data = block_head;
        root.records_len = records_len;
        root.data_len = data_len;
        root.base_level = base_level;
        root.block_size = BASE_ALLOC_SIZE;
        root.references = 1;
        root.lengths = sizes;
        root.offsets = offsets;
        root.split_allocation = true;

        Self::reserve_out_of_range_allocations(root);

        Ok(RcBlockAllocator(ptr as *mut _, PhantomData::default()))
      }
      None => Err(std::alloc::AllocError),
    }
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits> BlockRecordAllocator<BASE_ALLOC_SIZE, BitType, true> {
  /// Allocates memory from internally owned memory block.
  ///
  /// # Safety
  ///
  /// The lifetime of pointers allocated from this allocator should not outlive
  /// the lifetime of the allocator
  pub fn new<A: Allocator>(
    data_len: usize,
    base_allocator: A,
  ) -> Result<RcBlockAllocator<BASE_ALLOC_SIZE, BitType, A>, std::alloc::AllocError> {
    match Self::create_bit_record_allocator(data_len) {
      Some((records_len, base_level, offsets, sizes)) => {
        let Ok((alloc_struct, par_allocator, record_layout, data_layout)) = Self::get_layouts::<A>(records_len, data_len) else {
          return Err(std::alloc::AllocError);
        };

        let root_layout =
          alloc_struct.extend(par_allocator).unwrap().0.extend(record_layout).unwrap().0.extend(data_layout).unwrap().0;

        let ptr = base_allocator.allocate_zeroed(root_layout)?.as_ptr() as *mut u8;

        let root = unsafe { &mut *(ptr as *mut Self) };

        let alloc_offset = alloc_struct.size() + alloc_struct.padding_needed_for(par_allocator.align());
        let records_offset = alloc_offset + par_allocator.size() + par_allocator.padding_needed_for(record_layout.align());
        let data_offset = records_offset + record_layout.size() + record_layout.padding_needed_for(data_layout.align());

        let mut allocator = Some(base_allocator);
        unsafe { std::mem::swap(&mut *(ptr.offset(alloc_offset as isize) as *mut _), &mut allocator) };
        std::mem::forget(allocator);

        root.records = unsafe { ptr.offset(records_offset as isize) as *mut _ };
        root.data = unsafe { ptr.offset(data_offset as isize) as *mut _ };
        root.records_len = records_len;
        root.data_len = data_len;
        root.base_level = base_level;
        root.block_size = BASE_ALLOC_SIZE;
        root.references = 1;
        root.lengths = sizes;
        root.offsets = offsets;
        root.split_allocation = false;

        Self::reserve_out_of_range_allocations(root);

        Ok(RcBlockAllocator(ptr as *mut _, PhantomData::default()))
      }
      None => Err(std::alloc::AllocError),
    }
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, const MANAGER_ALLOCATOR: bool>
  BlockRecordAllocator<BASE_ALLOC_SIZE, BitType, MANAGER_ALLOCATOR>
{
  pub(crate) fn record_snapshot(&self) -> Box<[u8]> {
    self.get_data().into()
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, const MANAGER_ALLOCATOR: bool>
  BlockRecordAllocator<BASE_ALLOC_SIZE, BitType, MANAGER_ALLOCATOR>
{
  pub unsafe fn std_free<A: Allocator>(&self) {
    let (alloc_struct, par_allocator, record_layout, data_layout) =
      Self::get_layouts::<A>(self.records_len, self.data_len).unwrap_unchecked();

    // A Manager allocator does not own its data pointer, so it does not free
    // it when destroyerd
    let base_layout = if MANAGER_ALLOCATOR {
      alloc_struct.extend(par_allocator).unwrap().0.extend(record_layout).unwrap().0
    } else {
      alloc_struct.extend(par_allocator).unwrap().0.extend(record_layout).unwrap().0.extend(data_layout).unwrap().0
    };

    let ptr = (self as *const _ as *mut u8);

    let alloc_offset = alloc_struct.size() + alloc_struct.padding_needed_for(par_allocator.align());

    let allocator = std::mem::take(&mut *(ptr.offset(alloc_offset as isize) as *mut Option<A>)).unwrap_unchecked();

    allocator.deallocate(NonNull::<u8>::new_unchecked(ptr), base_layout);
  }

  #[inline(always)]
  pub(crate) fn get_layouts<A: Allocator>(
    records_len: usize,
    data_block_size: usize,
  ) -> Result<(std::alloc::Layout, std::alloc::Layout, std::alloc::Layout, std::alloc::Layout), std::alloc::LayoutError> {
    let alloc_struct = std::alloc::Layout::new::<BlockRecordAllocator<BASE_ALLOC_SIZE, BitType>>();
    let par_allocator = std::alloc::Layout::new::<Option<A>>();
    let header_layout = std::alloc::Layout::array::<BlockRecord<BitType>>(records_len)?;
    let data_layout = std::alloc::Layout::array::<u8>(data_block_size)?.align_to(128)?;

    Ok((alloc_struct, par_allocator, header_layout, data_layout))
  }

  fn create_bit_record_allocator(size: usize) -> Option<(usize, usize, [u32; 8], [usize; 8])> {
    const_assert_is_power_of_2(BASE_ALLOC_SIZE);

    let block_count = ((size as f32) / (BASE_ALLOC_SIZE as f32)).ceil();

    let level = block_count.log(BitType::bit_count() as f32).ceil() as usize;

    let max_size = BASE_ALLOC_SIZE * ((BitType::bit_count()).pow(level as u32));

    if max_size < size {
      return None;
    }

    let records_len = get_record_len::<BitType>(level);

    let block_size: usize = Self::get_block_size_at_level(level - 1);

    let end_bit = size / block_size;

    if end_bit < BitType::bit_count() {
      let partial = (size % block_size) > 0;
      let diff = BitType::bit_count() - (end_bit - partial as usize);

      let mut sizes = *BitType::block_group_size_lut();
      let mut offsets = *BitType::block_group_offset_lut();

      let mut off = 1;
      for i in 1..8 {
        sizes[i] = sizes[i] - (diff << BitType::power_shift_lut()[i - 1]);
        offsets[i] = off;
        off += sizes[i] as u32;
      }

      Some((offsets[level] as usize, level, offsets, sizes))
    } else {
      Some((records_len, level, *BitType::block_group_offset_lut(), *BitType::block_group_size_lut()))
    }
  }

  /// "Allocate" all memory blocks that are outside the actual allocatable
  /// range.
  pub(crate) fn reserve_out_of_range_allocations(
    allocator: &mut BlockRecordAllocator<BASE_ALLOC_SIZE, BitType, MANAGER_ALLOCATOR>,
  ) {
    let base_level = allocator.base_level;
    let mut data_len = allocator.data_len;

    let blocks = allocator.mut_records();
    let mut block_offset = 0;
    let mut inter_block_index = 0;
    let mut block_index = block_offset + inter_block_index;
    let max_size = Self::get_block_size_at_level(base_level);

    if data_len < max_size {
      for depth in 0..(base_level) {
        let level = base_level - depth;
        let block_size: usize = Self::get_block_size_at_level(level - 1);

        let end_bit = data_len / block_size;
        data_len = data_len % block_size;

        let partially_set = data_len > 1 && level > 1;
        let shift_amount = end_bit;

        blocks[block_index].alloc_bits_l = BitType::max_value().unsigned_shl(shift_amount as u32);
        blocks[block_index].sub_alloc_bits_h =
          unsafe { BitType::from(partially_set as usize).unwrap_unchecked() } << shift_amount;

        if !partially_set {
          break;
        }

        block_offset =
          BitType::block_group_offset_lut()[depth + 1] as usize + BitType::block_group_size_lut()[depth] * inter_block_index;
        inter_block_index = end_bit;
        block_index = block_offset + inter_block_index;
      }
    }
  }

  pub fn is_empty(&self) -> bool {
    self.records()[0].is_empty()
  }

  pub fn is_full(&self) -> bool {
    self.records()[0].is_full()
  }

  #[inline(always)]
  pub(crate) fn records(&self) -> &[BlockRecord<BitType>] {
    unsafe { std::slice::from_raw_parts(self.records, self.records_len) }
  }

  #[inline(always)]
  pub(crate) fn mut_records<'b>(&self) -> &'b mut [BlockRecord<BitType>] {
    unsafe { std::slice::from_raw_parts_mut(self.records, self.records_len) }
  }

  pub(crate) fn allocate_inner(
    &self,
    sub_table_block_index: usize,
    current_level: usize,
    request_size: usize,
    can_borrow: bool,
  ) -> Option<AllocResult> {
    use BitState::*;
    let current_depth = self.base_level - current_level;
    let block_index = self.offsets[current_depth] as usize + sub_table_block_index;

    let block = self.records()[block_index];

    if block.is_full() {
      return None;
    }

    let current_block_size = Self::get_block_size_at_level(current_level);
    let current_bit_size = Self::get_block_size_at_level(current_level - 1);

    if current_bit_size > request_size && current_level > 1 {
      let child_sub_field_offset = BitType::bit_count() * sub_table_block_index;

      for (state, bit_index) in block.iter_blocks() {
        if state == Empty || state == Partial {
          let adjacent_bit_in_another_block = (bit_index + 1) >= BitType::bit_count();

          if adjacent_bit_in_another_block {
            let adjacent_block = &mut self.mut_records()[block_index + 1];

            let can_borrow = {
              can_borrow && sub_table_block_index < (self.lengths[current_depth] - 1) && {
                let nibble = adjacent_block.get_nibble(0);
                nibble == BitState::Empty || nibble == BitState::Partial
              }
            };

            match self.allocate_inner(child_sub_field_offset + bit_index, current_level - 1, request_size, can_borrow) {
              Some(AllocResult { ptr_offset, is_full_block: full_block, adjacent }) => {
                let block = &mut self.mut_records()[block_index];

                block.set_nibble(bit_index, full_block.then_some(Full).unwrap_or(Partial));

                let is_full_block = block.is_full();

                match adjacent {
                  Some(adjacent_is_full) => {
                    // Adjacent sub-block is in another block

                    adjacent_block.set_nibble(0, adjacent_is_full.then_some(Full).unwrap_or(Partial));

                    return Some(AllocResult { adjacent: Some(adjacent_block.is_full()), is_full_block, ptr_offset });
                  }
                  None => {
                    return Some(AllocResult { is_full_block, ptr_offset, adjacent: None });
                  }
                }
              }
              None => {}
            }
          } else {
            let can_borrow = {
              let nibble = block.get_nibble(bit_index + 1);
              nibble == BitState::Empty || nibble == BitState::Partial
            };

            match self.allocate_inner(child_sub_field_offset + bit_index, current_level - 1, request_size, can_borrow) {
              Some(AllocResult { ptr_offset, is_full_block: full_block, adjacent }) => {
                let block = &mut self.mut_records()[block_index];

                block.set_nibble(bit_index, full_block.then_some(Full).unwrap_or(Partial));

                match adjacent {
                  Some(adjacent_is_full) => {
                    block.set_nibble(bit_index + 1, adjacent_is_full.then_some(Full).unwrap_or(Partial));
                    return Some(AllocResult { is_full_block: block.is_full(), ptr_offset, adjacent: None });
                  }
                  None => {
                    return Some(AllocResult { is_full_block: block.is_full(), ptr_offset, adjacent: None });
                  }
                }
              }
              None => {}
            }
          }
        }
      }

      None
    } else {
      let block = &mut self.mut_records()[block_index];

      pub(crate) fn fill_block<const SET_HEAD: bool, BitType: BlockBits>(
        block: &mut BlockRecord<BitType>,
        bit_offset: usize,
        num_of_bits: usize,
      ) {
        let _1: BitType = BitType::one();

        let mask = if num_of_bits < BitType::bit_count() {
          ((_1.shl_unchecked(num_of_bits as u32)).sub_unchecked(_1)) << bit_offset
        } else {
          BitType::max_value()
        };

        if SET_HEAD {
          let head = (_1) << bit_offset;
          block.sub_alloc_bits_h = block.sub_alloc_bits_h | (mask ^ head);
          block.alloc_bits_l = block.alloc_bits_l | head;
        } else {
          block.sub_alloc_bits_h = block.sub_alloc_bits_h | mask;
        }
      }

      let needed_blocks = request_size.div_ceil(current_bit_size);

      if needed_blocks > 1 {
        // search for minimum sized nodes;
        let ff: BitType = block.free_bits();

        let bit_index = find_range_offset(needed_blocks, ff.reverse_bits());

        if bit_index < BitType::bit_count() {
          let k = needed_blocks;

          fill_block::<true, _>(block, bit_index, k);

          if current_level > 1 {
            let child_sub_field_offset =
              self.offsets[current_depth + 1] as usize + (BitType::bit_count() * sub_table_block_index);

            self.mut_records()[bit_index + child_sub_field_offset].clear();
          }

          let ptr_offset = (sub_table_block_index * current_block_size) + (bit_index * current_bit_size);

          Some(AllocResult { is_full_block: block.is_full(), ptr_offset, adjacent: None })
        } else if can_borrow {
          // Try allocating between this block and its neighbor to the left.

          let other_index = self.offsets[current_depth] as usize + sub_table_block_index + 1;
          let other_block = &mut self.mut_records()[other_index];

          let half_shift = BitType::bit_count() >> 1;
          let upper_half = ff >> half_shift;

          let off = other_block.free_bits();
          let lower_half = off << half_shift;

          let ff = upper_half | lower_half;

          let bit_index = find_range_offset(needed_blocks, ff.reverse_bits());

          if bit_index < half_shift {
            let our_offset = bit_index + half_shift;
            let our_block_count = BitType::bit_count() - our_offset;
            let their_offset = 0;
            let their_bit_count = needed_blocks - our_block_count;

            fill_block::<true, _>(block, our_offset, our_block_count);
            fill_block::<false, _>(other_block, their_offset, their_bit_count);

            let ptr_offset = (sub_table_block_index * current_block_size) + (our_offset * current_bit_size);

            Some(AllocResult {
              is_full_block: block.is_full(),
              ptr_offset,
              adjacent: Some(other_block.is_full()),
            })
          } else {
            None
          }
        } else {
          None
        }
      } else {
        // Try direct single block allocation.
        for (state, bit_index) in block.iter_blocks() {
          if state == Empty {
            block.set_nibble(bit_index, Full);

            let ptr_offset = (sub_table_block_index * current_block_size) + (bit_index * current_bit_size);

            return Some(AllocResult { is_full_block: block.is_full(), ptr_offset, adjacent: None });
          }
        }

        None
      }
    }
  }

  pub fn alloc(&self, size: usize) -> Option<*mut u8> {
    match self.allocate_inner(0, self.base_level, size, false) {
      Some(AllocResult { ptr_offset, .. }) => {
        let ptr = unsafe { self.data.offset(ptr_offset as isize) };

        Some(ptr)
      }
      None => None,
    }
  }

  pub(crate) fn free_inner(
    &self,
    ptr_offset: usize,
    current_level: usize,
    sub_table_block_index: usize,
    base_ptr_offset: usize,
  ) -> (BitState, Option<BitState>) {
    use BitState::*;

    let current_depth = self.base_level - current_level;
    let block_index = self.offsets[current_depth] as usize + sub_table_block_index;
    let block = &mut self.mut_records()[block_index];

    if self.mut_records()[block_index].is_empty() {
      return (BitState::Empty, None);
    }

    let current_bit_size = Self::get_block_size_at_level(current_level - 1);

    let mut bit_index = 0;
    let mut adjusted_ptr = ptr_offset;

    while adjusted_ptr >= current_bit_size {
      bit_index += 1;
      adjusted_ptr -= current_bit_size;
    }

    match &mut block.get_nibble(bit_index) {
      Empty => {
        panic!("This bit should be allocated {block_index}{bit_index}")
      }
      Sub => {
        panic!("This block should be head start")
      }
      Full => {
        let (val, adjacent_bit_state) = if current_level > 1 {
          self.free_inner(
            adjusted_ptr,
            current_level - 1,
            bit_index + sub_table_block_index * BitType::bit_count(),
            base_ptr_offset,
          )
        } else {
          (Empty, None)
        };

        let block = &mut self.mut_records()[block_index];
        let mut outer_adjacent_state = None;

        let adjacent_bit_index = bit_index + 1;

        match adjacent_bit_state {
          Some(adjacent_state) => {
            if adjacent_bit_index >= BitType::bit_count() {
              let block = &mut self.mut_records()[block_index + 1];
              block.set_nibble(0, adjacent_state);
              outer_adjacent_state = Some(block.get_super_state());
            } else {
              block.set_nibble(adjacent_bit_index, adjacent_state);
            }
          }
          None => {}
        }

        match val {
          Empty => {
            {
              // Unset the full bit
              block.set_nibble(bit_index, Empty);
              let mut next_bit: usize = bit_index;
              'return_val: loop {
                next_bit += 1;
                if next_bit >= BitType::bit_count() {
                  // Check the adjacent block for sub bits
                  if sub_table_block_index < (self.lengths[current_depth] - 1) {
                    let adj_block: &mut BlockRecord<BitType> = &mut self.mut_records()[block_index + 1];

                    next_bit = 0;

                    loop {
                      if adj_block.get_nibble(next_bit) == Sub {
                        adj_block.set_nibble(next_bit, Empty);
                      } else if next_bit == 0 {
                        // No change occurred
                        break 'return_val (block.get_super_state(), outer_adjacent_state);
                      } else {
                        break 'return_val (block.get_super_state(), Some(adj_block.get_super_state()));
                      }

                      next_bit += 1;

                      if next_bit >= BitType::bit_count() {
                        break 'return_val (block.get_super_state(), Some(adj_block.get_super_state()));
                      }
                    }
                  } else {
                    break 'return_val (block.get_super_state(), outer_adjacent_state);
                  }
                } else if block.get_nibble(next_bit) == Sub {
                  block.set_nibble(next_bit, Empty);
                } else {
                  break 'return_val (block.get_super_state(), outer_adjacent_state);
                }
              }
            }
          }
          Partial => {
            block.set_nibble(bit_index, Partial);
            (Partial, outer_adjacent_state)
          }
          _ => unreachable!(),
        }
      }
      Partial => {
        debug_assert!(current_level > 0, "Can't have a partial block on the leaf level");

        let (bit_state, adjacent_bit_state) = self.free_inner(
          adjusted_ptr,
          current_level - 1,
          bit_index + sub_table_block_index * BitType::bit_count(),
          base_ptr_offset,
        );

        let block = &mut self.mut_records()[block_index];

        block.set_nibble(bit_index, bit_state);

        let mut outer_adjacent_state = None;

        match adjacent_bit_state {
          Some(adjacent_state) => {
            if (bit_index + 1) >= BitType::bit_count() {
              let block = &mut self.mut_records()[block_index + 1];
              block.set_nibble(0, adjacent_state);
              outer_adjacent_state = Some(block.get_super_state());
            } else {
              block.set_nibble(bit_index + 1, adjacent_state);
            }
          }
          None => {}
        }

        if block.is_empty() {
          (Empty, outer_adjacent_state)
        } else {
          (Partial, outer_adjacent_state)
        }
      }
    }
  }

  pub fn free(&self, ptr: *mut u8) -> Result<(), String> {
    // convert pointer to offset
    let ptr_offset = ptr as isize - self.data as isize;

    if ptr_offset < 0 || ptr_offset as usize > self.data_len {
      return Err(format!(
        "Pointer [0x{:0>16x}] not in range (0x{:0>16x} .. 0x{:0>16x})",
        ptr as usize,
        self.data as usize,
        self.data as usize + self.data_len
      ));
    }

    self.free_inner(ptr_offset as usize, self.base_level, 0, ptr_offset as usize);

    Ok(())
  }

  #[inline(always)]
  fn get_block_size_at_level(base_level: usize) -> usize {
    BASE_ALLOC_SIZE << BitType::power_shift_lut()[base_level]
  }
}

// Debug Implementation
impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, const B: bool> BlockRecordAllocator<BASE_ALLOC_SIZE, BitType, B> {
  pub(super) fn get_data<'this>(&'this self) -> &'this [u8] {
    unsafe { std::slice::from_raw_parts(self.data, self.data_len) }
  }
}

impl<const BASE_ALLOC_SIZE: usize, BitType: BlockBits, const B: bool> Debug
  for BlockRecordAllocator<BASE_ALLOC_SIZE, BitType, B>
{
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_fmt(format_args!("\nBlockHeaderRoot<{},{}> ----------------", BASE_ALLOC_SIZE, BitType::name()))?;

    f.write_fmt(format_args!("\nrecords len (recs): {}", self.records_len))?;
    f.write_fmt(format_args!("\n   record size (b): {}", std::mem::size_of::<BlockRecord<BitType>>()))?;
    f.write_fmt(format_args!("\n  records size (b): {}", self.records_len * std::mem::size_of::<BlockRecord<BitType>>()))?;
    f.write_fmt(format_args!("\n      data len (b): {}", self.data_len))?;
    f.write_fmt(format_args!("\n     base size (b): {}", self.block_size))?;
    f.write_fmt(format_args!("\n        base level: {}", self.base_level))?;

    let mut i = 0;
    let headers = self.records();

    for k in 0..self.base_level {
      let len = self.lengths[k];

      f.write_fmt(format_args!(
        "\n\nLevel {k} -- record byte coverage(b): {: <11} -- block size(b): {: <11} --:\n",
        self.block_size << (BitType::pow_shifts() * (self.base_level - k)),
        self.block_size << (BitType::pow_shifts() * (self.base_level - (k + 1)))
      ))?;

      for j in 0..len {
        let r = i + j;
        let block = headers[r];
        if j % 4 == 0 {
          f.write_str("\n")?;
          if j > 8 {
            f.write_fmt(format_args!("... {} more\n", len - j))?;
            break;
          }
        }
        f.write_fmt(format_args!("{r:0>4}:{block:?}"))?;
      }

      i += len;
    }

    f.write_fmt(format_args!("\n-------------------------------------------"))?;

    Ok(())
  }
}

/// Finds the offset of the first string of set bits (`1111...`) of length
/// `len`

pub(crate) fn find_range_offset<BitType: BlockBits>(len: usize, mut free_bits: BitType) -> usize {
  let val = len - 1;

  for _ in 0..(val >> 3) {
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
  }

  let count_4 = val & 4;
  if count_4 > 0 {
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
  }

  let count_2 = val & 2;
  if count_2 > 0 {
    free_bits = free_bits & (free_bits.shl_unchecked(1));
    free_bits = free_bits & (free_bits.shl_unchecked(1));
  }

  let count_1 = val & 1;
  if count_1 > 0 {
    free_bits = free_bits & (free_bits << 1);
  }

  free_bits.leading_zeros() as usize
}

#[inline(always)]
pub(crate) fn select_child_field<BitType: BlockBits>(current_depth: usize, in_field_block_index: usize) -> usize {
  let child_depth = current_depth + 1;
  BitType::block_group_offset_lut()[child_depth] as usize + (BitType::block_group_size_lut()[child_depth] * in_field_block_index)
}
