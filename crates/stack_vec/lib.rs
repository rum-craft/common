#![allow(unused)]
#[cfg(test)]
mod test;

#[derive(Default)]
enum StackData<const STACK_SIZE: usize, T: Sized> {
  StackData([T; STACK_SIZE]),
  VecData(Vec<T>),
  #[default]
  None,
}

/// A vector which derives its initial capacity from the stack. The data is
/// moved to the heap if the number of elements pushed to the vector exceed the
/// stack capacity.
///
/// Since the data is stored on the stack, care should be given to prevent stack
/// overflow. Generally, a limited number of items in that do not exceed 1kb in
/// total allocated space should be safe to store on the stack.
struct StackVec<const STACK_SIZE: usize, T: Sized> {
  stack_buffer: StackData<STACK_SIZE, T>,
  allocations:  usize,
}

impl<const STACK_SIZE: usize, T> Drop for StackVec<STACK_SIZE, T> {
  fn drop(&mut self) {
    match core::mem::take(&mut self.stack_buffer) {
      StackData::StackData(data) => {
        for i in 0..self.allocations {
          drop(unsafe { core::mem::transmute_copy::<T, T>(&data[i]) });
        }
        core::mem::forget(data);
      }
      StackData::VecData(vec) => drop(vec),
      StackData::None => {}
    }
  }
}

impl<const STACK_SIZE: usize, T: Sized> StackVec<STACK_SIZE, T> {
  #[inline(always)]
  pub fn new() -> Self {
    Self {
      stack_buffer: StackData::StackData(unsafe { core::mem::zeroed() }),
      allocations:  0,
    }
  }

  pub fn push(&mut self, element: T) {
    match &mut self.stack_buffer {
      StackData::StackData(data) => {
        if self.allocations < (STACK_SIZE - 1) {
          let mut e = element;
          core::mem::swap(&mut data[self.allocations], &mut e);
          core::mem::forget(e);
          self.allocations += 1;
        } else {
          unsafe {
            let mut vec = Vec::<T>::with_capacity(STACK_SIZE << 1);
            core::ptr::copy(data.as_ptr(), vec.as_mut_ptr(), self.allocations);
            vec.set_len(self.allocations);
            vec.push(element);
            let mut data = StackData::VecData(vec);
            core::mem::swap(&mut self.stack_buffer, &mut data);
            core::mem::forget(data);
          }
        }
      }
      StackData::VecData(vec_data) => vec_data.push(element),
      StackData::None => {}
    }
  }

  pub fn pop(&mut self) -> Option<T> {
    match &mut self.stack_buffer {
      StackData::None => None,
      StackData::StackData(data) => {
        if self.allocations > 0 {
          self.allocations -= 1;
          let data = unsafe { core::mem::transmute_copy(&data[self.allocations]) };
          Some(data)
        } else {
          None
        }
      }
      StackData::VecData(vec_data) => vec_data.pop(),
    }
  }

  #[inline(always)]
  pub fn data_is_on_stack(&mut self) -> bool {
    !matches!(self.stack_buffer, StackData::VecData(..))
  }

  #[inline(always)]
  pub fn as_slice(&self) -> &[T] {
    match &self.stack_buffer {
      StackData::StackData(data) => unsafe { core::slice::from_raw_parts(data.as_ptr(), self.allocations) },
      StackData::VecData(vec) => vec.as_slice(),
      StackData::None => unsafe { core::slice::from_raw_parts(core::ptr::null(), 0) },
    }
  }

  #[inline(always)]
  pub fn as_mut_slice(&mut self) -> &mut [T] {
    match &mut self.stack_buffer {
      StackData::StackData(data) => unsafe { core::slice::from_raw_parts_mut(data.as_mut_ptr(), self.allocations) },
      StackData::VecData(vec) => vec.as_mut_slice(),
      StackData::None => unsafe { core::slice::from_raw_parts_mut(core::ptr::null_mut(), 0) },
    }
  }
}
