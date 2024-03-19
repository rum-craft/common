use super::{number::*, vector::Vector};
use std::marker::PhantomData;

pub struct CubicBezierTuple<T: ScalarFloat, const S: usize, V: Vector<T, S>>(pub V, pub V, pub V, pub V, PhantomData<T>);
