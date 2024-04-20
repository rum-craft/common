pub mod cubic_bezier;
pub mod matrix;
pub mod number;
pub mod quadratic_bezier;
pub mod rect;
pub mod traits;
pub mod vector;

pub use cubic_bezier::*;
pub use matrix::*;
pub use number::*;
pub use quadratic_bezier::*;
pub use rect::*;
pub use traits::*;
pub use vector::*;

pub type Vec2f32 = Vec2<f32>;
pub type Vec2f64 = Vec2<f64>;
