#![allow(non_camel_case_types, non_snake_case, unused)]
use crate::compiler::parser::type_Value;
use rum_istring::IString;
use std::{collections::BTreeMap, fmt::Debug, hash::Hash};

use BitSize::*;

#[derive(Debug)]
struct LLContext {
  variable_type:  BTreeMap<IString, type_Value>,
  variable_value: BTreeMap<IString, LLVal>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PtrData {
  pub ptr:      PtrType,
  pub bits:     BitSize,
  pub elements: usize,
}

impl Debug for PtrData {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.elements == 0 {
      f.write_fmt(format_args!("{:?}(b{:?}[?])", self.ptr, self.bits as u8))
    } else {
      f.write_fmt(format_args!("{:?}(b{:?}[{}])", self.ptr, self.bits as u8, self.elements))
    }
  }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PtrType {
  #[default]
  Unallocated,
  Stack(usize),
  Heap,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct IntData {
  pub val:    IntVal,
  pub bits:   BitSize,
  pub signed: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntVal {
  Undefined,
  Static(i64),
  SSA(usize),
}
impl IntVal {
  pub fn static_val(&self) -> Option<i64> {
    if let IntVal::Static(val) = self {
      Some(*val)
    } else {
      None
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitSize {
  b8   = 8,
  b16  = 16,
  b32  = 32,
  b64  = 64,
  b128 = 128,
  b256 = 256,
  b512 = 512,
}

impl BitSize {
  pub fn mask(&self) -> u64 {
    use BitSize::*;
    match self {
      b8 => 0xFF,
      b16 => 0xFFFF,
      b32 => 0xFFFF_FFFF,
      b64 => 0xFFFF_FFFF_FFFF_FFFF,
      b128 => 0,
      b256 => 0,
      b512 => 0,
    }
  }

  pub fn byte_count(&self) -> u64 {
    use BitSize::*;
    match self {
      b8 => 1,
      b16 => 2,
      b32 => 4,
      b64 => 8,
      b128 => 16,
      b256 => 32,
      b512 => 64,
    }
  }
}

#[derive(Clone, Copy)]
#[allow(non_camel_case_types)]
pub enum LLVal {
  Und,
  Ptr(PtrData),
  Int(IntData),
  F32(f32),
  F64(f64),
  PtrBits(BitSize),
}

impl Hash for LLVal {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    let bytes: [u8; 32] = unsafe { std::mem::transmute(*self) };
    bytes.hash(state)
  }
}

impl PartialEq for LLVal {
  fn eq(&self, other: &Self) -> bool {
    let bytes_a: [u8; 32] = unsafe { std::mem::transmute(*self) };
    let bytes_b: [u8; 32] = unsafe { std::mem::transmute(*other) };
    bytes_a.eq(&bytes_b)
  }
}

impl Eq for LLVal {}

impl Debug for LLVal {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      LLVal::F32(val) => f.write_fmt(format_args!("f32({val})")),
      LLVal::F64(val) => f.write_fmt(format_args!("f64({val})")),
      LLVal::Ptr(val) => f.write_fmt(format_args!("{val:?}")),
      LLVal::PtrBits(val) => f.write_fmt(format_args!("{val:?}")),
      LLVal::Int(int) => match int.val {
        IntVal::SSA(val) => f.write_fmt(format_args!("i{}(${})", int.bits as u8, val)),
        IntVal::Static(val) => f.write_fmt(format_args!("i{}({})", int.bits as u8, val)),
        IntVal::Undefined => f.write_fmt(format_args!("i{}(?)", int.bits as u8)),
      },
      LLVal::Und => f.write_str("undefined"),
    }
  }
}

impl LLVal {
  pub fn bit_size(&self) -> BitSize {
    use LLVal::*;
    match self {
      F32(_) => b32,
      F64(_) => b64,
      Int(int) => int.bits,
      Ptr(_) => b64,
      PtrBits(b) => *b,
      Und => b64,
    }
  }

  pub fn default_ptr(bits: BitSize) -> Self {
    LLVal::Ptr(PtrData { ptr: Default::default(), bits, elements: 0 })
  }

  pub fn default_int(bits: BitSize) -> Self {
    LLVal::Int(IntData { val: IntVal::Undefined, bits, signed: true })
  }

  pub fn default_uint(bits: BitSize) -> Self {
    LLVal::Int(IntData { val: IntVal::Undefined, bits, signed: false })
  }

  pub fn to_f64(&self) -> f64 {
    use LLVal::*;
    match *self {
      F32(val) => val as f64,
      F64(val) => val,
      Int(IntData { mut val, bits, signed }) => {
        if let IntVal::Static(val) = val {
          if signed {
            match bits {
              b8 => val as u8 as i8 as f64,
              b16 => val as u16 as u16 as f64,
              b32 => val as u32 as u32 as f64,
              _ => val as i64 as f64,
            }
          } else {
            match bits {
              b8 => val as u8 as f64,
              b16 => val as u16 as f64,
              b32 => val as u32 as f64,
              _ => val as u64 as f64,
            }
          }
        } else {
          0.0
        }
      }
      _ => 0.0,
    }
  }

  pub fn to_f32(&self) -> f32 {
    use LLVal::*;
    match *self {
      F32(val) => val,
      F64(val) => val as f32,
      Int(IntData { mut val, bits, signed }) => {
        if let IntVal::Static(val) = val {
          if signed {
            match bits {
              b8 => val as u8 as i8 as f32,
              b16 => val as u16 as u16 as f32,
              b32 => val as u32 as u32 as f32,
              _ => val as i64 as f32,
            }
          } else {
            match bits {
              b8 => val as u8 as f32,
              b16 => val as u16 as f32,
              b32 => val as u32 as f32,
              _ => val as u64 as f32,
            }
          }
        } else {
          0.0
        }
      }
      _ => 0.0,
    }
  }

  pub fn to_int(&self, bit_size: BitSize) -> IntData {
    use BitSize::*;
    use LLVal::*;
    match *self {
      PtrBits(..) | Und | Ptr(..) => {
        IntData { val: IntVal::Undefined, bits: bit_size, signed: false }
      }
      Int(IntData { mut val, bits, signed }) => {
        if let IntVal::Static(val) = val {
          IntData {
            val:    IntVal::Static((val as u64 & bit_size.mask()) as i64),
            bits:   bit_size,
            signed: false,
          }
        } else {
          IntData { val, bits: bit_size, signed: false }
        }
      }
      F32(val) => {
        let val = match bit_size {
          b8 => val as u8 as i64,
          b16 => val as u16 as i64,
          b32 => val as u32 as i64,
          b64 => val as i64 as i64,
          _ => val as i64,
        };

        IntData { val: IntVal::Static(val), bits: bit_size, signed: false }
      }
      F64(val) => {
        let val = match bit_size {
          b8 => val as u8 as i64,
          b16 => val as u16 as i64,
          b32 => val as u32 as i64,
          b64 => val as i64 as i64,
          _ => val as i64,
        };

        IntData { val: IntVal::Static(val), bits: bit_size, signed: false }
      }
    }
  }
}

fn temp() {
  let input = r###"  
  "###;
}
