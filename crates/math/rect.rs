use super::number::*;
use std::{
  fmt::{Debug, Display},
  ops::{Add, Div, Mul, Neg, Sub},
};

use super::*;

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
/// A rectangular area in 2D space
pub struct Rectangle<T: Scalar> {
  /// Placement of the top right corner of the rectangle
  /// within cartesian space
  pub bottom_left: Vec2<T>,

  /// Placement of the bottom left corner of the rectangle
  /// within cartesian space
  pub top_right: Vec2<T>,
}

impl<T: Scalar> Debug for Rectangle<T>
where
  T: Mul<Output = T> + Copy + Sub<Output = T> + Default + PartialOrd + Debug + Display + Copy,
{
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_fmt(format_args!(
      "Rect2D{{ x: {}, y: {}, w: {}, h: {} }}",
      self.top_right.x(),
      self.top_right.y(),
      self.width(),
      self.height()
    ))
  }
}

/// Position of the cartesian origin in relation to the Rectangles's corners.
pub enum Origin {
  Center,
  BottomLeft,
  BottomRight,
  TopLeft,
  TopRight,
}

impl<T: Scalar> Rectangle<T>
where
  T: Copy + Clone + Default + Sub<Output = T> + Div<T, Output = T> + Neg<Output = T> + DefaultNum,
{
  /// Creates a Rect2D of size [width, height] with
  /// the top left corner centered on the origin
  pub fn from_dimensions(width: T, height: T, origin: Origin) -> Self {
    use Origin::*;
    match origin {
      Center => {
        let hw = width / T::f64(2.0);
        let hh = height / T::f64(2.0);
        Self { bottom_left: Vec2::new(-hw, -hh), top_right: Vec2::new(hw, hh) }
      }
      BottomLeft => Self {
        top_right:   Vec2::new(width, height),
        bottom_left: Vec2::new(Default::default(), Default::default()),
      },
      BottomRight => Self {
        top_right:   Vec2::new(Default::default(), height),
        bottom_left: Vec2::new(-width, Default::default()),
      },
      TopLeft => Self {
        top_right:   Vec2::new(width, Default::default()),
        bottom_left: Vec2::new(Default::default(), -height),
      },
      TopRight => Self {
        top_right:   Vec2::new(Default::default(), Default::default()),
        bottom_left: Vec2::new(-width, -height),
      },
    }
  }

  pub fn with_flipped_y(&self) -> Self {
    Self {
      top_right:   Vec2::new(self.top_right.x(), -self.top_right.y()),
      bottom_left: Vec2::new(self.bottom_left.x(), -self.bottom_left.y()),
    }
  }
}

impl<T> Rectangle<T>
where
  T: Scalar + Ord,
{
  /// Returns the smallest rectangle that contains both rectangles
  /// # Example
  /// ```
  /// use rum_keg::Rectangle;
  /// let a = Rectangle::new(0, 0, 10, 10);
  /// let b = Rectangle::new(5, 5, 20, 20);
  /// let c = a.union(b);
  /// assert_eq!(c, Rectangle::new(0, 0, 25, 25));
  /// ```
  pub fn union(&self, other: &Self) -> Self {
    let min_x = self.bottom_left.x.min(other.bottom_left.x);
    let min_y = self.bottom_left.y.min(other.bottom_left.y);
    let max_x = self.top_right.x.max(other.top_right.x);
    let max_y = self.top_right.y.max(other.top_right.y);

    Self {
      bottom_left: Vec2::new(min_x, min_y),
      top_right:   Vec2::new(max_x, max_y),
    }
  }
}

impl<T> Rectangle<T>
where
  T: Scalar + Debug + Display,
{
  pub fn new(sw: Vec2<T>, ne: Vec2<T>) -> Self {
    Self { bottom_left: sw, top_right: ne }
  }

  /// Create a rectangle with the South East (Bottom Left) corner of the
  /// rectangle centered on the origin.
  pub fn from_origin(width: T, height: T) -> Self {
    Self {
      bottom_left: Vec2::new(Default::default(), Default::default()),
      top_right:   Vec2::new(width, height),
    }
  }

  #[inline]
  pub fn width(&self) -> T {
    self.top_right.x - self.bottom_left.x
  }

  #[inline]
  pub fn height(&self) -> T {
    self.top_right.y - self.bottom_left.y
  }

  #[inline]
  /// Returns the vertices of the quad in the following order:
  /// - \[0] = north west
  /// - \[1] = north east
  /// - \[2] = south east
  /// - \[3] = south west
  pub fn vertices(&self) -> [Vec2<T>; 4] {
    let Self { top_right: se, bottom_left: nw } = self;
    [nw.clone(), Vec2::new(nw.x, se.y), se.clone(), Vec2::new(se.x, nw.y)]
  }

  #[inline]
  /// Get a vector representing the absolute size of the rectangle;
  pub fn size(&self) -> Vec2<T> {
    let a = self.bottom_left;
    let b = self.top_right;
    b - a
  }

  #[inline]
  /// Get the South-West (Bottom Left) corner of the rectangle;
  pub fn center(&self) -> Vec2<T> {
    let a = self.bottom_left;
    let b = self.top_right;
    a + ((b - a) / (T::one() + T::one()))
  }

  #[inline]
  /// Get the South-East (Bottom Right) corner of the rectangle;
  pub fn se(&self) -> Vec2<T> {
    Vec2::new(self.top_right.x, self.bottom_left.y)
  }

  #[inline]
  /// Get the Bottom Right corner of the rectangle;
  pub fn br(&self) -> Vec2<T> {
    self.se()
  }

  #[inline]
  /// Get the Right Bottom corner of the rectangle;
  pub fn rb(&self) -> Vec2<T> {
    self.se()
  }

  #[inline]
  /// Get the South-West (Bottom Left) corner of the rectangle;
  pub fn bottom_left(&self) -> Vec2<T> {
    self.bottom_left
  }

  #[inline]
  /// Get the Bottom Left corner of the rectangle;
  pub fn bl(&self) -> Vec2<T> {
    self.bottom_left
  }

  #[inline]
  /// Get the Left Bottom corner of the rectangle;
  pub fn lb(&self) -> Vec2<T> {
    self.bottom_left
  }

  #[inline]
  /// Get the North-West (Top Left) corner of the rectangle;
  pub fn nw(&self) -> Vec2<T> {
    Vec2::new(self.bottom_left.x, self.top_right.y)
  }

  #[inline]
  // Get the Top Left corner of the rectangle;
  pub fn tl(&self) -> Vec2<T> {
    self.nw()
  }

  #[inline]
  /// Get the Left Top corner of the rectangle;
  pub fn lt(&self) -> Vec2<T> {
    self.nw()
  }

  #[inline]
  /// Get the North-East (Bottom Right) corner of the rectangle;
  pub fn ne(&self) -> Vec2<T> {
    self.top_right
  }

  #[inline]
  /// Get the Top Right corner of the rectangle;
  pub fn tr(&self) -> Vec2<T> {
    self.top_right
  }

  #[inline]
  /// Get the Right Top corner of the rectangle;
  pub fn rt(&self) -> Vec2<T> {
    self.top_right
  }

  #[inline]
  /// Calculate the area of the rectangle
  pub fn area(&self) -> T {
    self.width() * self.height()
  }

  pub fn fits(&self, rhs: &Self) -> bool {
    return (self.width() >= rhs.width()) && (self.height() >= rhs.height());
  }

  pub fn contains(&self, rhs: &Self) -> bool {
    return self.bottom_left.y <= rhs.bottom_left.y
      && self.bottom_left.x <= rhs.bottom_left.x
      && self.top_right.y >= rhs.top_right.y
      && self.top_right.x >= rhs.top_right.x;
  }

  #[inline]
  pub fn overlaps(&self, rhs: &Self) -> bool {
    return self.bl().x <= rhs.tr().x
      && self.bl().y <= rhs.tr().y
      && self.tr().x >= rhs.bl().x
      && self.tr().y >= rhs.bl().y;
  }

  pub fn moved(&self, pos: Vec2<T>) -> Self {
    Rectangle { bottom_left: self.bottom_left + pos, top_right: self.top_right + pos }
  }
}

impl<T> Add<Vec2<T>> for Rectangle<T>
where
  T: Add<T, Output = T> + Scalar,
{
  type Output = Self;

  fn add(self, rhs: Vec2<T>) -> Self::Output {
    Self { top_right: self.top_right + rhs, bottom_left: self.bottom_left + rhs }
  }
}

impl<T> Sub<Vec2<T>> for Rectangle<T>
where
  T: Sub<T, Output = T> + Scalar,
{
  type Output = Self;

  fn sub(self, rhs: Vec2<T>) -> Self::Output {
    Self { top_right: self.top_right - rhs, bottom_left: self.bottom_left - rhs }
  }
}

impl<T> Mul<Vec2<T>> for Rectangle<T>
where
  T: Mul<T, Output = T> + Scalar,
{
  type Output = Self;

  fn mul(self, rhs: Vec2<T>) -> Self::Output {
    Self { top_right: self.top_right * rhs, bottom_left: self.bottom_left * rhs }
  }
}

impl<T> Div<Vec2<T>> for Rectangle<T>
where
  T: Div<T, Output = T> + Scalar,
{
  type Output = Self;

  fn div(self, rhs: Vec2<T>) -> Self::Output {
    Self { top_right: self.top_right / rhs, bottom_left: self.bottom_left / rhs }
  }
}

impl<T> Mul<T> for Rectangle<T>
where
  T: Mul<T, Output = T> + Scalar,
{
  type Output = Self;

  fn mul(self, rhs: T) -> Self::Output {
    Self { top_right: self.top_right * rhs, bottom_left: self.bottom_left * rhs }
  }
}

impl<T> Div<T> for Rectangle<T>
where
  T: Div<T, Output = T> + Scalar,
{
  type Output = Self;

  fn div(self, rhs: T) -> Self::Output {
    Self { top_right: self.top_right / rhs, bottom_left: self.bottom_left / rhs }
  }
}

#[cfg(test)]
mod test {

  use crate::{Origin, Rectangle, Vec2};

  #[test]
  fn from_dimensions() {
    let rec = Rectangle::from_dimensions(1024i32, 1024i32, Origin::Center);
    assert_eq!(rec.top_right, Vec2::new(512, 512), "Center: Top Right");
    assert_eq!(rec.bottom_left, Vec2::new(-512, -512), "Center: Bottom Left");

    let rec = Rectangle::from_dimensions(1024i32, 1024i32, Origin::TopLeft);
    assert_eq!(rec.top_right, Vec2::new(1024, 0), "TopLeft: Top Right");
    assert_eq!(rec.bottom_left, Vec2::new(0, -1024), "TopLeft: Bottom Left");

    let rec = Rectangle::from_dimensions(1024i32, 1024i32, Origin::TopRight);
    assert_eq!(rec.top_right, Vec2::new(0, 0), "TopRight: Top Right");
    assert_eq!(rec.bottom_left, Vec2::new(-1024, -1024), "TopRight: Bottom Left");

    let rec = Rectangle::from_dimensions(1024i32, 1024i32, Origin::BottomLeft);
    assert_eq!(rec.top_right, Vec2::new(1024, 1024), "BottomLeft: Top Right");
    assert_eq!(rec.bottom_left, Vec2::new(0, 0), "BottomLeft: Bottom Left");

    let rec = Rectangle::from_dimensions(1024i32, 1024i32, Origin::BottomRight);
    assert_eq!(rec.top_right, Vec2::new(0, 1024), "BottomRight: Top Right");
    assert_eq!(rec.bottom_left, Vec2::new(-1024, 0), "BottomRight: Bottom Left");
  }

  #[test]
  fn area() {
    assert_eq!(100.0, Rectangle::from_dimensions(10f32, 10f32, Origin::Center).area());
    assert_eq!(100.0, Rectangle::from_dimensions(10f32, 10f32, Origin::BottomRight).area());
    assert_eq!(100.0, Rectangle::from_dimensions(10f32, 10f32, Origin::BottomLeft).area());
    assert_eq!(100.0, Rectangle::from_dimensions(10f32, 10f32, Origin::TopLeft).area());
    assert_eq!(100.0, Rectangle::from_dimensions(10f32, 10f32, Origin::TopRight).area());
  }

  #[test]
  fn fits() {
    assert!(Rectangle::from_origin(10, 10).fits(&Rectangle::from_origin(2, 2)));
    assert!(!(Rectangle::from_origin(10, 10).fits(&Rectangle::from_origin(2, 20))));
  }

  #[test]
  fn se_nw() {
    let rec = Rectangle::from_origin(10, 10);
    assert_eq!(rec.nw(), Vec2::new(0, 10), "BottomRight: Top Right");
    assert_eq!(rec.se(), Vec2::new(10, 0), "BottomRight: Bottom Left");
  }
}
