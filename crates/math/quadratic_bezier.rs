use super::{matrix::*, number::*, vector::*, Rectangle};
use std::ops::{Add, Div, Mul, Sub};

/// Simple tuple form of a Quadratic Bezier Curve
#[derive(Debug, Clone, Copy)]
pub struct QBezierCurve2D<T: ScalarFloat> {
  p1: Vec2<T>,
  p2: Vec2<T>,
  p3: Vec2<T>,
}

impl<T: ScalarFloat> Add<Vec2<T>> for QBezierCurve2D<T> {
  type Output = QBezierCurve2D<T>;

  fn add(self, rhs: Vec2<T>) -> Self::Output {
    Self { p1: self.p1 + rhs, p2: self.p2 + rhs, p3: self.p3 + rhs }
  }
}

impl<T: ScalarFloat> Sub<Vec2<T>> for QBezierCurve2D<T> {
  type Output = QBezierCurve2D<T>;

  fn sub(self, rhs: Vec2<T>) -> Self::Output {
    Self { p1: self.p1 - rhs, p2: self.p2 - rhs, p3: self.p3 - rhs }
  }
}

impl<T: ScalarFloat> Div<Vec2<T>> for QBezierCurve2D<T> {
  type Output = QBezierCurve2D<T>;

  fn div(self, rhs: Vec2<T>) -> Self::Output {
    Self { p1: self.p1 / rhs, p2: self.p2 / rhs, p3: self.p3 / rhs }
  }
}

impl<T: ScalarFloat> Mul<Vec2<T>> for QBezierCurve2D<T> {
  type Output = QBezierCurve2D<T>;

  fn mul(self, rhs: Vec2<T>) -> Self::Output {
    Self { p1: self.p1 * rhs, p2: self.p2 * rhs, p3: self.p3 * rhs }
  }
}

impl<T: ScalarFloat> Mul<Mat22<T>> for QBezierCurve2D<T> {
  type Output = QBezierCurve2D<T>;

  fn mul(self, rhs: Mat22<T>) -> Self::Output {
    let p1 = rhs * self.p1;
    let p2 = rhs * self.p2;
    let p3 = rhs * self.p3;
    (p1, p2, p3).into()
  }
}

impl<T: ScalarFloat> Mul<T> for QBezierCurve2D<T> {
  type Output = QBezierCurve2D<T>;

  fn mul(self, rhs: T) -> Self::Output {
    let p1 = self.p1 * rhs;
    let p2 = self.p2 * rhs;
    let p3 = self.p3 * rhs;
    (p1, p2, p3).into()
  }
}

impl<T: ScalarFloat> Div<T> for QBezierCurve2D<T> {
  type Output = QBezierCurve2D<T>;

  fn div(self, rhs: T) -> Self::Output {
    let p1 = self.p1 / rhs;
    let p2 = self.p2 / rhs;
    let p3 = self.p3 / rhs;
    (p1, p2, p3).into()
  }
}

impl<T: ScalarFloat> From<(Vec2<T>, Vec2<T>, Vec2<T>)> for QBezierCurve2D<T> {
  fn from(value: (Vec2<T>, Vec2<T>, Vec2<T>)) -> Self {
    let (p1, p2, p3) = value;
    Self { p1, p2, p3 }
  }
}

impl<T: ScalarFloat> From<QBezierCurve2D<T>> for (Vec2<T>, Vec2<T>, Vec2<T>) {
  fn from(value: QBezierCurve2D<T>) -> Self {
    (value.p1, value.p2, value.p3)
  }
}

pub enum QuadraticSolutions<T> {
  One(T),
  Two(T, T),
  None,
}

impl<T> QBezierCurve2D<T>
where
  T: ScalarFloat,
{
  /// Create a new instance of a Self from a Quadratic Bezier Tuple
  pub fn from_tuple(curve: (Vec2<T>, Vec2<T>, Vec2<T>)) -> Self {
    Self::from(curve)
  }

  pub fn to_tuple(&self) -> (Vec2<T>, Vec2<T>, Vec2<T>) {
    (self.p1, self.p2, self.p3)
  }

  /// Create an array from the curve
  pub fn as_slice(&self) -> &[Vec2<T>; 3] {
    unsafe { &*std::mem::transmute::<*const QBezierCurve2D<T>, *const [Vec2<T>; 3]>(self) }
  }

  /// Reverses the point order of the curve.
  pub fn reverse(&self) -> Self {
    let (a, b, c) = self.to_tuple();
    Self::from((c, b, a))
  }

  /// Create a curve from a three element array
  pub fn from_array(array: [Vec2<T>; 3]) -> Self {
    Self { p1: array[0], p2: array[1], p3: array[2] }
  }

  /// Reverses the point order of the curve.
  pub fn tangent(&self, t: T) -> Vec2<T> {
    let (a, b, c) = self.to_tuple();
    (b - a) * (T::one() - t) + (c - b) * t
  }

  /// The the intersections of the glyph and the line segment defined by two
  /// points.
  pub fn intersections(&self, p1: Vec2<T>, p2: Vec2<T>) -> QuadraticSolutions<T> {
    let diff = p2 - p1;
    let angle_h = -diff.y.atan2(diff.x);
    let rot_mat_h = Mat22::rot(angle_h);

    let curve = *self - p1;
    let curve_a = (curve * rot_mat_h) / diff.magnitude();

    //return curve_a.x_intercept(T::zero());

    match curve_a.x_intercept(T::zero()) {
      crate::QuadraticSolutions::One(x1) => {
        if x1 >= T::zero() && x1 <= T::one() {
          crate::QuadraticSolutions::One(x1)
        } else {
          crate::QuadraticSolutions::None
        }
      }
      crate::QuadraticSolutions::Two(x1, x2) => {
        let a = x1 >= T::zero() && x1 <= T::one();
        let b = x2 >= T::zero() && x2 <= T::one();
        match (a, b) {
          (true, true) => crate::QuadraticSolutions::Two(x1, x2),
          (true, false) => crate::QuadraticSolutions::One(x1),
          (false, true) => crate::QuadraticSolutions::One(x2),
          _ => crate::QuadraticSolutions::None,
        }
      }
      s => s,
    }
  }

  /// Returns The y-axis intercept of the curve given an x-axis offset.
  pub fn y_intercept(&self, x_offset: T) -> QuadraticSolutions<T> {
    let (p1, p2, p3) = self.to_tuple();

    let one = T::one();
    let two: T = one + one;
    let four: T = two + two;

    let a = p1.x - two * p2.x + p3.x;
    let b = two * (p2.x - p1.x);
    let c = p1.x - x_offset;

    let t1;
    let mut t2 = T::infinity();

    if a.abs() <= T::epsilon() {
      t1 = -c / b;
    } else {
      let base = ((b * b) - (four * a * c)).sqrt();
      let d = one / (two * a);
      t1 = (-b + base) * d;
      t2 = (-b - base) * d;
    }

    if t1 >= T::zero() && t1 <= T::one() {
      if t2 >= T::zero() && t2 <= T::one() {
        QuadraticSolutions::Two(self.y_point(t1), self.y_point(t2))
      } else {
        QuadraticSolutions::One(self.y_point(t1))
      }
    } else if t2 >= T::zero() && t2 <= T::one() {
      QuadraticSolutions::One(self.y_point(t2))
    } else {
      QuadraticSolutions::None
    }
  }

  /// Returns The x-axis intercept of the curve given a y-axis offset.
  pub fn x_intercept(&self, y_offset: T) -> QuadraticSolutions<T> {
    let (p1, p2, p3) = self.to_tuple();

    let one = T::one();
    let two: T = one + one;
    let four: T = two + two;

    let a = p1.y - two * p2.y + p3.y;
    let b = two * (p2.y - p1.y);
    let c = p1.y - y_offset;

    let t1;
    let mut t2 = T::infinity();

    if a.abs() <= T::epsilon() {
      t1 = -c / b;
    } else {
      let term = (b * b) - (four * a * c);

      if term < T::epsilon() {
        return QuadraticSolutions::None;
      }

      let base = (term).sqrt();
      let d = one / (two * a);
      t1 = (-b + base) * d;
      t2 = (-b - base) * d;
    }

    if t1 >= T::zero() && t1 <= T::one() {
      if t2 >= T::zero() && t2 <= T::one() {
        QuadraticSolutions::Two(self.x_point(t1), self.x_point(t2))
      } else {
        QuadraticSolutions::One(self.x_point(t1))
      }
    } else if t2 >= T::zero() && t2 <= T::one() {
      QuadraticSolutions::One(self.x_point(t2))
    } else {
      QuadraticSolutions::None
    }
  }

  /// The point on the curve at `t`
  pub fn point(&self, t: T) -> Vec2<T> {
    let (p1, p2, p3) = self.to_tuple();
    let ti = T::one() - t;
    p1 * ti * ti + p2 * (T::one() + T::one()) * ti * t + p3 * t * t
  }

  /// The value of the curve on the y axis at `t`
  pub fn y_point(&self, t: T) -> T {
    let (p1, p2, p3) = self.to_tuple();
    let ti = T::one() - t;
    p1.y * ti * ti + p2.y * (T::one() + T::one()) * ti * t + p3.y * t * t
  }

  /// The value of the curve on the x axis at `t`
  pub fn x_point(&self, t: T) -> T {
    let (p1, p2, p3) = self.to_tuple();
    let ti = T::one() - t;
    p1.x * ti * ti + p2.x * (T::one() + T::one()) * ti * t + p3.x * t * t
  }

  pub fn scale(&self, scalar: T) -> Self {
    let (a, b, c) = self.to_tuple();
    (a * scalar, b * scalar, c * scalar).into()
  }

  pub fn split(&self, t: T) -> (Self, Self) {
    let (p1, p3, p5) = self.to_tuple();

    let ti = T::one() - t;

    let p2 = p1 * ti + p3 * t;
    let p4 = p3 * ti + p5 * t;
    let pc = p2 * ti + p4 * t;

    ((p1, p2, pc).into(), (pc, p4, p5).into())
  }

  pub fn aa_bounding_box(&self) -> Rectangle<T> {
    let (p1, mut p2, p3) = self.to_tuple();

    let px1 = p2 - p1;
    let px2 = p3 - p2;
    let pt = (-px1) / (px2 - px1);

    if pt.x >= T::zero() && pt.x <= T::one() {
      p2.x = self.point(pt.x).x;
    }

    if pt.y >= T::zero() && pt.y <= T::one() {
      p2.y = self.point(pt.y).y;
    }

    let min_x = p1.x.min(p2.x.min(p3.x));
    let max_x = p1.x.max(p2.x.max(p3.x));

    let min_y = p1.y.min(p2.y.min(p3.y));
    let max_y = p1.y.max(p2.y.max(p3.y));

    Rectangle { bottom_left: (min_x, min_y).into(), top_right: (max_x, max_y).into() }
  }
}
