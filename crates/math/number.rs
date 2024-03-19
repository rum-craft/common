use std::fmt::Debug;

use num_traits::{Float, Num};

pub trait DefaultNum {
  fn usize(num: usize) -> Self;
  fn f64(num: f64) -> Self;
  fn f32(num: f32) -> Self;
  fn _0() -> Self;
  fn _1() -> Self;
  fn _2() -> Self;
  fn _half() -> Self;
  fn _qtr() -> Self;
}
macro_rules! derive_default_num {
  ($type:ident) => {
    impl DefaultNum for $type {
      #[inline]
      fn usize(num: usize) -> Self {
        num as $type
      }

      #[inline]
      fn f64(num: f64) -> Self {
        num as $type
      }

      #[inline]
      fn f32(num: f32) -> Self {
        num as $type
      }

      #[inline]
      fn _0() -> Self {
        0 as $type
      }

      #[inline]
      fn _1() -> Self {
        1 as $type
      }

      #[inline]
      fn _2() -> Self {
        2 as $type
      }

      #[inline]
      fn _half() -> Self {
        Self::f64(0.5)
      }

      #[inline]
      fn _qtr() -> Self {
        Self::f64(0.25)
      }
    }
  };
}
derive_default_num!(u64);
derive_default_num!(u32);
derive_default_num!(u16);
derive_default_num!(u8);
derive_default_num!(i64);
derive_default_num!(i32);
derive_default_num!(i16);
derive_default_num!(i8);
derive_default_num!(f64);
derive_default_num!(f32);

pub trait Scalar: Debug + Default + Num + Copy + PartialOrd + DefaultNum + 'static {}
pub trait ScalarFloat: Scalar + Float {}

impl Scalar for i8 {}
impl Scalar for i16 {}
impl Scalar for i32 {}
impl Scalar for i64 {}
impl Scalar for u8 {}
impl Scalar for u16 {}
impl Scalar for u32 {}
impl Scalar for u64 {}
impl Scalar for f32 {}
impl Scalar for f64 {}
impl ScalarFloat for f32 {}
impl ScalarFloat for f64 {}
