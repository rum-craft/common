use core::ops::{Index, IndexMut};

#[derive(Default)]
pub(crate) enum StackData<const STACK_SIZE: usize, T: Sized> {
  StackData([T; STACK_SIZE]),
  VecData(Vec<T>),
  #[default]
  None,
}

/// A vector which derives its initial capacity from the stack. The data is
/// moved to the heap if the number of elements pushed to the vector exceed
/// the stack capacity.
///
/// Since the data is stored on the stack, care should be given to prevent
/// stack overflow. Generally, a limited number of items in that do not
/// exceed 1kb in total allocated space should be safe to store on the
/// stack.
pub struct StackVec<const STACK_SIZE: usize, T: Sized> {
  pub(crate) inner:       StackData<STACK_SIZE, T>,
  pub(crate) allocations: usize,
}

impl<const STACK_SIZE: usize, T> Index<usize> for StackVec<STACK_SIZE, T> {
  type Output = T;

  fn index(&self, index: usize) -> &Self::Output {
    if index >= self.len() {
      panic!("Index {index} is out of range of 0..{}", self.len());
    }

    match &self.inner {
      StackData::StackData(data) => &data[index],
      StackData::VecData(vec) => &vec[index],
      StackData::None => unreachable!(),
    }
  }
}

impl<const STACK_SIZE: usize, T> IndexMut<usize> for StackVec<STACK_SIZE, T> {
  fn index_mut(&mut self, index: usize) -> &mut Self::Output {
    if index >= self.len() {
      panic!("Index {index} is out of range of 0..{}", self.len());
    }

    match &mut self.inner {
      StackData::StackData(data) => &mut data[index],
      StackData::VecData(vec) => &mut vec[index],
      StackData::None => unreachable!(),
    }
  }
}

impl<const STACK_SIZE: usize, T> AsRef<[T]> for StackVec<STACK_SIZE, T> {
  fn as_ref(&self) -> &[T] {
    self.as_slice()
  }
}

impl<const STACK_SIZE: usize, T> AsMut<[T]> for StackVec<STACK_SIZE, T> {
  fn as_mut(&mut self) -> &mut [T] {
    self.as_mut_slice()
  }
}

impl<const STACK_SIZE: usize, T> Drop for StackVec<STACK_SIZE, T> {
  fn drop(&mut self) {
    match core::mem::take(&mut self.inner) {
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
  /// Converts the stack vec into a regular vector, consuming the stack vec in
  /// the process.
  pub fn to_vec(mut self) -> Vec<T> {
    match core::mem::take(&mut self.inner) {
      StackData::None => vec![],
      StackData::StackData(data) => {
        let mut vec = Vec::<T>::with_capacity(STACK_SIZE << 1);
        unsafe {
          core::ptr::copy(data.as_ptr(), vec.as_mut_ptr(), self.allocations);
          vec.set_len(self.allocations);
        };
        core::mem::forget(data);
        vec
      }
      StackData::VecData(vec) => vec,
    }
  }

  #[inline(always)]
  pub fn new() -> Self {
    Self {
      inner:       StackData::StackData(unsafe { core::mem::zeroed() }),
      allocations: 0,
    }
  }

  pub fn len(&self) -> usize {
    match &self.inner {
      StackData::None => 0,
      StackData::StackData(data) => self.allocations,
      StackData::VecData(vec) => vec.len(),
    }
  }

  pub fn iter<'stack>(&'stack self) -> StackVecIterator<'stack, STACK_SIZE, T> {
    StackVecIterator { inner: self, tracker: 0, len: self.len() }
  }

  pub fn push(&mut self, element: T) {
    match &mut self.inner {
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
            core::mem::swap(&mut self.inner, &mut data);
            core::mem::forget(data);
          }
        }
      }
      StackData::VecData(vec_data) => vec_data.push(element),
      StackData::None => {}
    }
  }

  pub fn pop(&mut self) -> Option<T> {
    match &mut self.inner {
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
  pub fn data_is_on_stack(&self) -> bool {
    !matches!(self.inner, StackData::VecData(..))
  }

  #[inline(always)]
  pub fn as_slice(&self) -> &[T] {
    match &self.inner {
      StackData::StackData(data) => unsafe {
        core::slice::from_raw_parts(data.as_ptr(), self.allocations)
      },
      StackData::VecData(vec) => vec.as_slice(),
      StackData::None => unsafe { core::slice::from_raw_parts(core::ptr::null(), 0) },
    }
  }

  #[inline(always)]
  pub fn as_mut_slice(&mut self) -> &mut [T] {
    match &mut self.inner {
      StackData::StackData(data) => unsafe {
        core::slice::from_raw_parts_mut(data.as_mut_ptr(), self.allocations)
      },
      StackData::VecData(vec) => vec.as_mut_slice(),
      StackData::None => unsafe { core::slice::from_raw_parts_mut(core::ptr::null_mut(), 0) },
    }
  }
}

pub struct StackVecIterator<'stack, const STACK_SIZE: usize, T> {
  inner:   &'stack StackVec<STACK_SIZE, T>,
  tracker: usize,
  len:     usize,
}

impl<'stack, const STACK_SIZE: usize, T> Iterator for StackVecIterator<'stack, STACK_SIZE, T> {
  type Item = &'stack T;

  fn next(&mut self) -> Option<Self::Item> {
    if self.tracker < self.len {
      let index = self.tracker;
      self.tracker += 1;
      match &self.inner.inner {
        StackData::StackData(data) => Some(&data[index]),
        StackData::VecData(vec) => Some(&vec[index]),
        StackData::None => None,
      }
    } else {
      None
    }
  }
}
