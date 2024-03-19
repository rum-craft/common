use num_traits::Float;

//use bytemuck::{Pod, Zeroable};
use super::{number::ScalarFloat, Vec4, Vector, *};
use std::{
  fmt::Debug,
  marker::PhantomData,
  ops::{Index, IndexMut, Mul},
};

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Matrix<const COLUMN_COUNT: usize, const ROW_COUNT: usize, M, T>(
  [T; ROW_COUNT],
  PhantomData<M>,
)
where
  M: ScalarFloat,
  T: Vector<M, COLUMN_COUNT>;

//unsafe impl<const COLUMN_COUNT: usize, const ROW_COUNT: usize, M, T> Zeroable
// for Matrix<COLUMN_COUNT, ROW_COUNT, M, T> where
//  M: ScalarFloat,
//  T: Vector<M, COLUMN_COUNT>,
//{
//}

//unsafe impl<const COLUMN_COUNT: usize, const ROW_COUNT: usize, M, T> Pod for
// Matrix<COLUMN_COUNT, ROW_COUNT, M, T> where
//M: ScalarFloat + Pod,
//T: Vector<M, COLUMN_COUNT> + Pod + Copy,
//{
//}

impl<const COLUMN_COUNT: usize, const ROW_COUNT: usize, M, T> Matrix<COLUMN_COUNT, ROW_COUNT, M, T>
where
  M: ScalarFloat,
  T: Vector<M, COLUMN_COUNT>,
{
  pub fn from_rows(rows: [T; ROW_COUNT]) -> Self {
    Self(rows, PhantomData)
  }

  pub fn new() -> Self {
    Self([T::empty(); ROW_COUNT], PhantomData)
  }

  pub fn identity() -> Self {
    if COLUMN_COUNT == ROW_COUNT {
      let mut a = Self::new();
      for index in 0..ROW_COUNT {
        a.0[index].slice_mut()[index] = M::one();
      }
      a
    } else {
      Self::new()
    }
  }

  pub fn transpose(&self) -> Self {
    if ROW_COUNT == COLUMN_COUNT {
      let mut transposed = Self::new();
      for index in 0..ROW_COUNT {
        let data = transposed.0[index].slice_mut();
        for i in 0..ROW_COUNT {
          data[i] = self.0[i].slice()[index];
        }
      }
      transposed
    } else {
      self.clone()
    }
  }

  /// Returns the nth row of the matrix.
  /// # Example
  /// ```
  /// use rum_keg::primitives::Matrix;
  /// let matrix = Matrix::<3, 3, f32, Vec3<f32>>::identity();
  /// let row0 = matrix.row(0);
  /// let row1 = matrix.row(1);
  /// let row2 = matrix.row(2);
  ///
  /// assert_eq!(row0, Vec3::new(1.0, 0.0, 0.0));
  /// assert_eq!(row1, Vec3::new(0.0, 1.0, 0.0));
  /// assert_eq!(row2, Vec3::new(0.0, 0.0, 1.0));
  /// ```
  pub fn row(&self, row_index: usize) -> T {
    self.0[row_index]
  }

  /// Returns the nth column of the matrix.
  /// This is slower than row() because it has to do a partial transpose of the
  /// matrix. # Example
  /// ```
  /// use rum_keg::primitives::Matrix;
  /// let a = Matrix::<3, 3, f32, Vec3<f32>>::from_rows([
  ///   Vec3::new(1.0, 2.0, 3.0),
  ///   Vec3::new(4.0, 5.0, 6.0),
  ///   Vec3::new(7.0, 8.0, 9.0),
  /// ]);
  /// assert_eq!(a.column(0), Vec3::new(1.0, 4.0, 7.0));
  /// assert_eq!(a.column(1), Vec3::new(2.0, 5.0, 8.0));
  /// assert_eq!(a.column(2), Vec3::new(3.0, 6.0, 9.0));
  /// ```
  pub fn column(&self, col_index: usize) -> T {
    let mut column = T::empty();
    for row in 0..ROW_COUNT {
      column.slice_mut()[row] = self.0[row].slice()[col_index];
    }
    column
  }
}

impl<M> Mat44<M>
where
  M: ScalarFloat,
{
  pub fn top_left_ortho(width: M, height: M, near: M, far: M) -> Self {
    let _0 = M::zero();
    Self::ortho(width, _0, height, _0, near, far)
  }

  pub fn bottom_left_ortho(width: M, height: M, near: M, far: M) -> Self {
    let _0 = M::zero();
    Self::ortho(_0, -width, height, _0, near, far)
  }

  pub fn center_ortho(width: M, height: M, near: M, far: M) -> Self {
    let _0 = M::zero();
    let h_width = width / M::_2();
    let h_height = height / M::_2();
    Self::ortho(h_width, -h_width, h_height, -h_height, near, far)
  }

  /// Create an orthographic projection matrix.
  /// # Example
  /// ```
  /// use rum_keg::primitives::Matrix;
  /// let matrix = Matrix::<4, 4, f32, Vec4>::ortho(1.0, 0.0, 1.0, 0.0, 0.0, 1.0);
  /// ```
  ///
  /// # See also
  /// [top_left_ortho](Matrix::top_left_ortho)
  /// [bottom_left_ortho](Matrix::bottom_left_ortho)
  pub fn ortho(right: M, left: M, top: M, bottom: M, near: M, far: M) -> Self {
    let f_min_n = far - near;
    let f_sum_n = far + near;
    let t_min_b = top - bottom;
    let t_sum_b = top + bottom;
    let r_min_l = right - left;
    let r_sum_l = left + right;
    let _1 = M::one();
    let _0 = M::zero();
    let _2 = _1 + _1;

    let mut mat = Self::new();

    mat[0][0] = _2 / r_min_l;
    mat[1][1] = _2 / t_min_b;
    mat[2][2] = -_2 / f_min_n;
    mat[3][3] = _1;

    mat[3][0] = (-r_sum_l) / r_min_l;
    mat[3][1] = (-t_sum_b) / t_min_b;
    mat[3][2] = (-f_sum_n) / f_min_n;

    mat
  }

  /// Create a perspective projection matrix.
  /// # Example
  /// ```
  /// use rum_keg::primitives::Matrix;
  /// let matrix = Matrix::<4, 4, f32, Vec4>::perspective(1.0, 1.0, 0.0, 1.0);
  /// ```
  pub fn perspective(
    fov_radians: M,
    right: M,
    left: M,
    top: M,
    bottom: M,
    near: M,
    far: M,
  ) -> Self {
    let s = fov_radians.tan();
    let f_m_n = far - near;
    let f_p_n = far + near;
    let t_m_b = top - bottom;
    let t_p_b = top + bottom;
    let r_m_l = left - right;
    let r_p_l = left + right;
    let _1 = M::one();
    let _0 = M::zero();
    let _2 = _1 + _1;

    let mut mat = Self::new();

    mat[0][0] = ((_2 * near) / r_m_l) * s;
    mat[0][2] = r_p_l / r_m_l;

    mat[1][1] = ((_2 * near) / t_m_b) * s;
    mat[1][2] = t_p_b / t_m_b;

    mat[2][2] = -f_p_n / f_m_n;
    mat[2][3] = -((_2 * far * near) / f_m_n);

    mat[3][2] = -_1;

    mat
  }
}

impl<const L_ROW: usize, T: ScalarFloat, V1: Vector<T, L_ROW>> Mul for Matrix<L_ROW, L_ROW, T, V1> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let mut new = Self::new();
    let transposed = rhs.transpose();

    for i in 0..L_ROW {
      let row = new.0[i].slice_mut();
      for j in 0..L_ROW {
        let row_a = transposed.0[j];
        let row_b = self.0[i];
        row[j] = row_a.dot(row_b);
      }
    }

    new
  }
}

impl<
    const L_COL: usize,
    const L_ROW: usize,
    T: ScalarFloat,
    V: Vector<T, L_COL> + Default + Debug,
  > Mul<V> for Matrix<L_COL, L_ROW, T, V>
{
  type Output = V;

  fn mul(self, rhs: V) -> Self::Output {
    let mut new = V::default();

    let row = new.slice_mut();

    for j in 0..L_ROW {
      let row_a = rhs;
      let row_b: V = self.0[j];
      row[j] = row_a.dot(row_b);
    }

    new
  }
}

impl<T, M> Matrix<2, 2, M, T>
where
  M: ScalarFloat,
  T: Vector<M, 2>,
{
  ///
  /// Creates a 2x2 rotation matrix from the given angle.
  ///
  /// - `angle_rad` - angle of rotation in radians
  #[allow(unused)]
  pub fn rot(angle_rad: M) -> Self {
    let (s, c) = angle_rad.sin_cos();
    Self::from_rows([T::from_array([c, -s]), T::from_array([s, c])])
  }
}

pub type Mat44<T> = Matrix<4, 4, T, Vec4<T>>;
pub type Mat33<T> = Matrix<3, 3, T, Vec3<T>>;
pub type Mat22<T> = Matrix<2, 2, T, Vec2<T>>;

impl<const X: usize, const Y: usize, M, T> Index<usize> for Matrix<X, Y, M, T>
where
  M: ScalarFloat,
  T: Vector<M, X>,
{
  type Output = T;

  fn index(&self, index: usize) -> &Self::Output {
    debug_assert!(index < Y);
    &self.0[index]
  }
}

impl<const X: usize, const Y: usize, M, T> IndexMut<usize> for Matrix<X, Y, M, T>
where
  M: ScalarFloat,
  T: Vector<M, X>,
{
  fn index_mut(&mut self, index: usize) -> &mut Self::Output {
    debug_assert!(index < Y);
    &mut self.0[index]
  }
}

/// Projections matrices
impl<T: ScalarFloat> Mat44<T> {
  pub fn orthogonal_projection_mat(fov_radians: T, near: T, far: T) -> Self {
    let s = T::one() / T::tan(fov_radians);

    let near_plane = T::neg(far / (far - near));

    let far_plane = T::neg((far * near) / (far - near));

    let mut mat = Mat44::new();

    mat[0][0] = s;
    mat[1][1] = s;
    mat[2][2] = near_plane;
    mat[2][3] = T::neg(T::one());
    mat[3][2] = far_plane;
    mat
  }

  pub fn perspective_project_mat(fov_radians: T, aspect_ratio: T, near: T, far: T) -> Self {
    let s = T::one() / T::tan(fov_radians);

    let _2: T = T::_2();
    let _1: T = T::_1();

    let t = near * T::tan(fov_radians);
    let b = -t;

    let r = t * aspect_ratio;
    let l = -r;

    let mut mat = Mat44::new();
    mat[0][0] = (near * _2) / (r - l);

    mat[1][1] = (near * _2) / (t - b);

    mat[2][0] = (r + l) / (r - l);
    mat[2][1] = (t + b) / (t - b);
    mat[2][2] = T::neg((far + near)) / (far - near);
    mat[2][3] = T::neg(_1);

    mat[3][2] = (T::neg(_2) * far * near) / (far - near);

    mat
  }
}

impl Mat44<f64> {}

#[allow(unused)]
pub type Mat44f32 = Mat44<f32>;
#[allow(unused)]
pub type Mat44f64 = Mat44<f64>;
#[allow(unused)]
pub type Mat33f32 = Mat33<f32>;
#[allow(unused)]
pub type Mat33f64 = Mat33<f64>;
#[allow(unused)]
pub type Mat22f32 = Mat22<f32>;
#[allow(unused)]
pub type Mat22f64 = Mat22<f64>;

#[test]
fn test_mat44_projections() {
  let mat = Mat44::perspective_project_mat(90.0f32, 2.0, 0.001, 100.0);
  dbg!(mat);
}

#[test]
fn test_mat44() {
  let mat = Mat44::from_rows([
    (1., 2., 3., 4.).into(),
    (5., 6., 7., 8.).into(),
    (9., 10., 11., 12.).into(),
    (13., 14., 15., 16.).into(),
  ]);
  let mut ident = Mat44::identity();

  ident.0[1].slice_mut()[1] = 2.0;

  let vec = mat * Vec4::new(1., 2., 3., 4.);

  print!("{:?}", vec);
}

#[test]
fn _2d_rotation() {
  use std::f64::consts::PI as PI_f64;
  let vec = Vec2::new(1f64, 0.0);
  // 90 Degree rotation
  let _90dm22 = Mat22::rot(PI_f64 / 2.0);
  let _180dm22 = Mat22::rot(PI_f64);
  let _270dm22 = Mat22::rot(PI_f64 / 2.0 * 3.0);

  dbg!(_90dm22);

  let rot_vec = _90dm22 * vec;
  //let rot_vec = _180dm22 * vec;
  //let rot_vec = _270dm22 * vec;

  assert_eq!(rot_vec.slice(), &[0.0, 1.0]);
}
