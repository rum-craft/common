use crate::StackVec;

#[test]
pub fn allocates_on_stack_only() {
  let mut vec = StackVec::<1024, u32>::new();

  vec.push(1);
  vec.push(2);
  vec.push(3);
  vec.push(4);

  assert_eq!(vec.as_slice(), [1, 2, 3, 4]);

  assert!(vec.data_is_on_stack());

  assert_eq!(vec.pop(), Some(4));
  assert_eq!(vec.pop(), Some(3));
  assert_eq!(vec.pop(), Some(2));
  assert_eq!(vec.pop(), Some(1));
  assert_eq!(vec.pop(), None);
}

#[test]
pub fn over_allocates_are_moved_into_vector() {
  let mut vec = StackVec::<3, u32>::new();

  vec.push(1);
  vec.push(2);
  vec.push(3);
  vec.push(4);

  assert_eq!(vec.as_slice(), [1, 2, 3, 4]);

  assert!(!vec.data_is_on_stack());

  assert_eq!(vec.pop(), Some(4));
  assert_eq!(vec.pop(), Some(3));
  assert_eq!(vec.pop(), Some(2));
  assert_eq!(vec.pop(), Some(1));
  assert_eq!(vec.pop(), None);
}

#[test]
pub fn over_allocates_are_moved_into_vector_large_stack_allocation() {
  let mut vec = StackVec::<30000, _>::new();

  vec.push(1);
  vec.push(2);
  vec.push(3);
  vec.push(4);

  assert_eq!(vec.as_slice(), [1, 2, 3, 4]);

  assert!(vec.data_is_on_stack());

  assert_eq!(vec.pop(), Some(4));
  assert_eq!(vec.pop(), Some(3));
  assert_eq!(vec.pop(), Some(2));
  assert_eq!(vec.pop(), Some(1));
  assert_eq!(vec.pop(), None);
}

#[test]
pub fn data_with_drop_trait_is_properly_handle_from_vec() {
  static mut DROPPED: isize = 0;

  #[derive(Debug, Clone, PartialEq, Eq)]
  struct Data(u32);

  impl Drop for Data {
    fn drop(&mut self) {
      unsafe { DROPPED += 1 };
    }
  }

  let mut vec = StackVec::<1, _>::new();

  vec.push(Data(1));
  vec.push(Data(2));
  vec.push(Data(3));
  vec.push(Data(4));

  assert!(!vec.data_is_on_stack());

  assert_eq!(vec.pop(), Some(Data(4)));
  assert_eq!(vec.pop(), Some(Data(3)));
  assert_eq!(vec.pop(), Some(Data(2)));
  assert_eq!(vec.pop(), Some(Data(1)));

  drop(vec);

  assert_eq!(unsafe { DROPPED }, 8);
}

#[test]
pub fn data_with_drop_trait_is_properly_handled_on_stack() {
  static mut DROPPED: isize = 0;

  #[derive(Debug, Clone, PartialEq, Eq)]
  struct Data(u32);

  impl Drop for Data {
    fn drop(&mut self) {
      unsafe { DROPPED += 1 };
    }
  }

  let mut vec = StackVec::<40, _>::new();

  vec.push(Data(1));
  vec.push(Data(2));
  vec.push(Data(3));
  vec.push(Data(4));

  assert!(vec.data_is_on_stack());

  assert_eq!(vec.pop(), Some(Data(4)));
  assert_eq!(vec.pop(), Some(Data(3)));
  assert_eq!(vec.pop(), Some(Data(2)));
  assert_eq!(vec.pop(), Some(Data(1)));

  drop(vec);

  assert_eq!(unsafe { DROPPED }, 8);
}
