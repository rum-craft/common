pub use num_traits::Num;

pub use super::ScalarFloat;

pub trait VectorSum: Clone + Copy {
  type Output: Clone + Copy;
  fn sum(self) -> Self::Output;
}

pub trait VectorCross<T>: Clone + Copy {
  type Output: Clone + Copy;
  fn cross(self, rhs: T) -> Self::Output;
}

pub trait SquareRoot<T>: Clone + Copy {
  type Output: Clone + Copy;
  fn sqrt(self) -> Self::Output;
}

pub trait ToPower<T>: Clone + Copy {
  type Output: Clone + Copy;
  fn pow(self, power: T) -> Self::Output;
}

pub trait VectorMagnitude<S>: VectorDot<Self, S> + VectorSum<Output = S> + Clone + Copy
where
  S: Num + ScalarFloat,
{
  /// The scalar magnitude (or length) of the vector.
  fn magnitude(self) -> S {
    self.dot(self).sqrt()
  }

  /// The scalar length (or magnitude) of the vector.
  fn length(self) -> S {
    self.magnitude()
  }
}

pub trait VectorDot<V, S>: std::ops::Mul<V, Output = V> + Clone + Copy
where
  V: VectorSum<Output = S>,
{
  fn dot(self, rhs: V) -> S {
    (self * rhs).sum()
  }
}

impl<T, S> VectorDot<T, S> for T where T: VectorSum<Output = S> + std::ops::Mul<T, Output = T> {}

impl<T, S> VectorMagnitude<S> for T
where
  T: VectorDot<T, S> + VectorSum<Output = S> + Clone + Copy,
  S: Num + ScalarFloat,
{
}
