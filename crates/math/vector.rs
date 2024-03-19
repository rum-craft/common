use super::number::*;
use num_traits::{Num, NumOps};
use std::{
  fmt::Debug,
  hash::Hash,
  ops::{Add, Div, Index, IndexMut, Mul, Neg, Rem, Sub},
};

pub trait Vector<T: Scalar, const S: usize>: Copy + NumOps {
  const T: usize = S;

  fn slice_mut(&mut self) -> &mut [T; S];

  fn slice(&self) -> &[T; S];

  fn empty() -> Self;

  fn from_array(array: [T; S]) -> Self;

  fn dot(&self, rhs: Self) -> T;

  fn len(&self) -> usize;

  fn sum(&self) -> T {
    let mut sum: T = T::zero();
    for v in self.slice() {
      sum = sum + *v;
    }
    sum
  }
}

#[macro_export]
macro_rules! vector_struct {

  ($(#[$($attrss:tt)+])* $vector_type:ident $count:literal $($name:ident)+ ) => {
    $(#[$($attrss)+])*
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Clone, Copy)]
    pub struct $vector_type<T: Scalar> {
      $(pub $name: T,)+
    }

    //unsafe impl<T: Scalar> Zeroable for $vector_type<T> {}
    //unsafe impl<T: Scalar> Pod for $vector_type<T> {}

    impl<T: Scalar> Vector<T, $count> for $vector_type<T>
      where T: NumOps + Num + Copy + Default
    {
      fn slice_mut(&mut self) -> &mut [T; $count] {
        unsafe {
          &mut *std::mem::transmute::<*mut $vector_type<T>, *mut [T; $count]>(self)
        }
      }
      fn slice(&self) -> &[T; $count] {
        unsafe {
          &*std::mem::transmute::<*const $vector_type<T>, *const [T; $count]>(self)
        }
      }

      fn len(&self) -> usize {
        $count
      }

      fn empty() -> Self {
        Self::default()
      }

      fn from_array(array: [T; $count]) -> Self {
        Self::from(&array[0..$count])
      }

      #[inline]
      fn dot(&self, rhs: $vector_type<T>) -> T {
        let pair_mul = *self * rhs;
        pair_mul.sum()
      }
    }
  };
}

#[macro_export]
macro_rules! vector_ops {
  ($op:tt) => {
    T
  };

  ($l:expr, $r:expr, $op:tt) => {
    $l $op $r
  };

  ($l:expr) => {
    $l
  };

  ($index:literal, $name:ident) => {
    #[inline]
    pub fn $name (&self) -> T { self.$name.clone() }
  };



  ($vector_type:ident $($index:literal $name:ident)+ ) => {
    impl<T:Scalar> From<&[T]> for $vector_type<T>
    where
      T: Clone + Copy,
    {
      #[inline]
      fn from(texel: &[T]) -> Self {
        Self { $($name: texel[$index]),+ }
      }
    }

    impl<T:Scalar> $vector_type<T> {
      #[inline]
      pub fn new($($name : T),+) -> Self {
        Self { $($name),+ }
      }

      $(
        vector_ops!($index, $name);
      )+
    }

    impl<T: Scalar> Index<usize> for $vector_type<T> {
      type Output = T;
      fn index(&self, index: usize) -> &Self::Output {
          debug_assert!(index < self.len());
          &self.slice()[index]
      }
    }


    impl<T: Scalar> IndexMut<usize> for $vector_type<T> {
      fn index_mut(&mut self, index: usize) -> &mut Self::Output {
          debug_assert!(index < self.len());
          &mut self.slice_mut()[index]
      }
    }


    impl<T: Mul<Output = T> + Scalar> Mul for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn mul(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, *)),+ }
      }
    }

    impl<T: Mul<Output = T> + Scalar> Mul for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn mul(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, *)),+ }
      }
    }

    impl<T: Div<Output = T> + Scalar> Div for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn div(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, /)),+ }
      }
    }

    impl<T: Div<Output = T> + Scalar> Div for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn div(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, /)),+ }
      }
    }

    impl<T: Add<Output = T> + Scalar> Add for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn add(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, +)),+ }
      }
    }

    impl<T: Add<Output = T> + Scalar> Add for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn add(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, +)),+ }
      }
    }

    impl<T: Sub<Output = T> + Scalar> Sub for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn sub(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, -)),+ }
      }
    }

    impl<T: Sub<Output = T> + Scalar> Sub for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn sub(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, -)),+ }
      }
    }

    impl<T: Neg<Output = T> + Scalar> Neg for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn neg(self) -> Self::Output {
        $vector_type { $($name: -self.$name),+ }
      }
    }

    impl<T: Neg<Output = T> + Scalar> Neg for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn neg(self) -> Self::Output {
        $vector_type { $($name: -self.$name),+ }
      }
    }

    impl<T: Rem<Output = T> + Scalar> Rem for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn rem(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, %)),+ }
      }
    }

    impl<T: Rem<Output = T> + Scalar> Rem for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn rem(self, rhs: Self) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs.$name, %)),+ }
      }
    }

    // Scalars

    impl<T: Add<Output = T> + Scalar> Add<T> for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn add(self, rhs: T) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs, +)),+ }
      }
    }

    impl<T: Add<Output = T> + Scalar> Add<T> for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn add(self, rhs: T) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs, +)),+ }
      }
    }

    impl<T: Div<Output = T> + Scalar> Div<T> for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn div(self, rhs: T) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs, /)),+ }
      }
    }

    impl<T: Div<Output = T> + Scalar> Div<T> for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn div(self, rhs: T) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs, /)),+ }
      }
    }

    impl<T: Mul<Output = T> + Scalar> Mul<T> for $vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn mul(self, rhs: T) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs, *)),+ }
      }
    }

    impl<T: Mul<Output = T> + Scalar> Mul<T> for &$vector_type<T> {
      type Output = $vector_type<T>;
      #[inline]
      fn mul(self, rhs: T) -> Self::Output {
        $vector_type { $($name: vector_ops!(self.$name, rhs, *)),+ }
      }
    }
  };
}

#[macro_export]
macro_rules! vector_impl {
  ( $op:expr) => (
    $op
  );

  ($l:expr,$r:expr, $op:tt) => {
    $l $op $r
  };

  ($vector_type:ident $($index:tt)+) => {

    impl<T: Scalar> $vector_type<T> {

      #[inline]
      pub fn sum(&self) -> T {
        let mut sum: T = T::zero();
        for v in self.slice() {
          sum = sum + *v;
        }
        sum
      }
    }

    impl<T: Scalar> $vector_type<T> {

      #[inline]
      pub fn magnitude_squared(&self) -> T {
        self.dot(*self)
      }
      #[inline]
      pub fn divided(&self, scalar: T) -> Self {
        self / scalar
      }
    }

    impl<T: Mul<Output = T> + Scalar> $vector_type<T> {
      pub fn scaled(&self, scalar: T) -> Self {
        self * scalar
      }
    }

    impl<T: ScalarFloat + Div<Output = T>> $vector_type<T> {

      #[inline]
      pub fn magnitude(&self) -> T {
        let m_squared = self.dot(*self);
        T::sqrt(m_squared.into())
      }

      #[inline]
      pub fn unit(&self) -> Self {
        self.normalize()
      }

      #[inline]
      pub fn normalize(&self) -> Self {
        self / self.magnitude()
      }

      #[inline]
      pub fn lerp(&self, rhs:&Self, scalar: T) -> Self {
        *self + (*rhs - *self).scaled(scalar)
      }
    }
  };
}

// Vector 2 Base -----------------------
vector_struct!(#[repr(C)] Vec2 2 x y);
vector_ops!(Vec2 0 x 1 y);
vector_impl!(Vec2 0 x 1 y);

impl<T: Scalar> From<(T, T)> for Vec2<T> {
  fn from(value: (T, T)) -> Self {
    Vec2::new(value.0, value.1)
  }
}

impl<T: Scalar> Into<(T, T)> for Vec2<T> {
  fn into(self) -> (T, T) {
    (self.x(), self.y())
  }
}

// Vector 3 Base -----------------------
vector_struct!(#[repr(C)] Vec3 3 x y z);
vector_ops!(Vec3 0 x 1 y 2 z);
vector_impl!(Vec3 0 x 1 y 2 z);

impl<T: Scalar> From<(T, T, T)> for Vec3<T> {
  fn from(value: (T, T, T)) -> Self {
    Vec3::new(value.0, value.1, value.2)
  }
}

impl<T: Scalar> Into<(T, T, T)> for Vec3<T> {
  fn into(self) -> (T, T, T) {
    (self.x(), self.y(), self.z())
  }
}

// Vector 4 Base -----------------------
vector_struct!(#[repr(C)] Vec4 4 x y z w);
vector_ops!(Vec4 0 x 1 y 2 z 3 w);
vector_impl!(Vec4 0 x 1 y 2 z 3 w);

impl<T: Scalar> From<(T, T, T, T)> for Vec4<T> {
  fn from(value: (T, T, T, T)) -> Self {
    Vec4::new(value.0, value.1, value.2, value.3)
  }
}

impl<T: Scalar> Into<(T, T, T, T)> for Vec4<T> {
  fn into(self) -> (T, T, T, T) {
    (self.x(), self.y(), self.z(), self.w())
  }
}

#[cfg(test)]
mod test {

  use crate::Vector;

  use super::Vec2;

  #[test]
  fn test() {
    let a: Vec2<f32> = Vec2::new(10.0, 20.0);
    let b = Vec2::new(1f32, 1.0);

    let c = b + a;

    assert_eq!((-c / 2.).slice(), &[-5.5, -10.5])
  }
}
