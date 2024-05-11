use crate::compiler::{
  self,
  parser::{
    arithmetic_Value,
    assignment_group_1_Value,
    assignment_group_Value,
    block_list_Value,
    logical_Value,
    match_list_Value,
    mem_expr_Value,
    pointer_offset_group_Value,
    primitive_ptr_type_Value,
    primitive_type_Value,
    type_Value,
    LL_MemLocation,
    LL_PointerCast,
    LL_function,
    Type_128BitPointer,
    Type_f32,
    Type_f64,
    Type_i16,
    Type_i32,
    Type_i64,
    Type_i8,
    Type_u16,
    Type_u32,
    Type_u64,
    Type_u8,
  },
};
use radlr_rust_runtime::types::Token;
use rum_istring::{CachedString, IString};
use std::collections::BTreeMap;

pub fn interpret_ll_function(funct: &LL_function<Token>, args: &[LLValue]) -> LLValue {
  let mut context: LLContext =
    LLContext { variable_type: Default::default(), variable_value: Default::default() };

  assert!(args.len() == funct.params.len());

  for (param, arg_value) in funct.params.iter().zip(args.iter()) {
    let ty = param.ty.clone();

    let name = param.id.id.intern();
    context.variable_type.entry(name).or_insert(param.ty.clone());

    use type_Value::*;

    // Assert arguments are compatible with the function's parameters

    let val_type = match (ty, arg_value) {
      // Pointers
      (Type_128BitPointer(..), val @ LLValue::ptr128(..)) => val,
      (Type_64BitPointer(..), val @ LLValue::ptr64(..)) => val,
      (Type_32BitPointer(..), val @ LLValue::ptr32(..)) => val,
      (Type_16BitPointer(..), val @ LLValue::ptr16(..)) => val,
      (Type_8BitPointer(..), val @ LLValue::ptr8(..)) => val,
      // Integers
      (Type_i8(..), val @ LLValue::i8(..)) => val,
      (Type_i16(..), val @ LLValue::i16(..)) => val,
      (Type_i32(..), val @ LLValue::i32(..)) => val,
      (Type_i64(..), val @ LLValue::i64(..)) => val,
      // Unsigned Integers
      (Type_u8(..), val @ LLValue::u8(..)) => val,
      (Type_u16(..), val @ LLValue::u16(..)) => val,
      (Type_u32(..), val @ LLValue::u32(..)) => val,
      (Type_u64(..), val @ LLValue::u64(..)) => val,
      // Floating Point
      (Type_f32(..), val @ LLValue::f32(..)) => val,
      (Type_f64(..), val @ LLValue::f64(..)) => val,
      // Floating Point Vectors
      // todo
      (Type_f32v2(..), val) => todo!("Support floating point vectors"),
      (Type_f32v3(..), val) => todo!("Support floating point vectors"),
      (Type_f32v4(..), val) => todo!("Support floating point vectors"),
      (Type_f32v8(..), val) => todo!("Support floating point vectors"),

      (Type_f64v2(..), val) => todo!("Support floating point vectors"),
      (Type_f64v4(..), val) => todo!("Support floating point vectors"),

      (a, b) => {
        panic!("incombatible argument for {a:?} {b:?}")
      }
    };

    context.variable_value.entry(name).or_insert(*val_type);
  }

  // Interpret statements

  process_statements(&funct.block.statements, &mut context);

  dbg!(&context);

  let ret = &funct.block.ret;

  interprete_ll_expression(&ret.expression, &context, funct.return_type.clone())
}

fn interprete_ll_logical_expression(
  expr: &logical_Value<Token>,
  context: &LLContext,
  val: type_Value,
) -> LLValue {
  match &expr {
    logical_Value::LL_Member(mem) => {
      interprete_ll_expression(&arithmetic_Value::LL_Member(mem.clone()), context, val)
    }
    logical_Value::LL_Num(num) => {
      interprete_ll_expression(&arithmetic_Value::LL_Num(num.clone()), context, val)
    }
    logical_Value::GR(and) => {
      let left_val = interprete_ll_logical_expression(&and.left, context, type_Value::None);
      let right_val =
        interprete_ll_logical_expression(&and.right, context, type_from_value(&left_val));

      let bool = match (left_val, right_val) {
        (LLValue::u32(l), LLValue::u32(r)) => l > r,
        _ => panic!("cannot compare values!"),
      };

      LLValue::u32(bool as u32)
    }
    _ => LLValue::undefined,
  }
}

fn type_from_value(val: &LLValue) -> type_Value {
  match val {
    LLValue::u64(..) => type_Value::Type_u64(Type_u64 {}),
    LLValue::f32(..) => type_Value::Type_f32(Type_f32 {}),
    LLValue::f64(..) => type_Value::Type_f64(Type_f64 {}),
    LLValue::i8(..) => type_Value::Type_i8(Type_i8 {}),
    LLValue::i16(..) => type_Value::Type_i16(Type_i16 {}),
    LLValue::i32(..) => type_Value::Type_i32(Type_i32 {}),
    LLValue::i64(..) => type_Value::Type_i64(Type_i64 {}),
    LLValue::u8(..) => type_Value::Type_u8(Type_u8 {}),
    LLValue::u16(..) => type_Value::Type_u16(Type_u16 {}),
    LLValue::u32(..) => type_Value::Type_u32(Type_u32 {}),
    _ => type_Value::None,
  }
}

fn process_statements(stmts: &[block_list_Value<Token>], context: &mut LLContext) -> bool {
  for statement in stmts {
    match statement {
      block_list_Value::LL_Continue(_) => return true,

      block_list_Value::LL_Match(m) => {
        let expression_val =
          interprete_ll_logical_expression(&m.expression, context, type_Value::None);

        for stmt in &m.statements {
          match stmt {
            match_list_Value::LL_Block(block) => {
              return process_statements(&block.statements, context);
            }
            match_list_Value::LL_MatchCase(case) => {
              if match &case.primitive_value {
                compiler::parser::primitive_value_Value::LL_True(_) => match &expression_val {
                  LLValue::u32(val) => *val > 0,
                  _ => false,
                },
                compiler::parser::primitive_value_Value::LL_False(_) => match &expression_val {
                  LLValue::u32(val) => *val == 0,
                  _ => false,
                },
                _ => false,
              } {
                return process_statements(&case.block.statements, context);
              }
            }
            _ => {}
          }
        }
      }

      block_list_Value::LL_Loop(loop_) => while process_statements(&loop_.statements, context) {},

      block_list_Value::LL_Var_Binding(assign) => {
        let name: IString = assign.id.id.intern();
        let ty = &assign.ty;

        if let Some(old) = context.variable_type.insert(name, ty.clone()) {
          panic!("Redefined variable")
        } else {
          let val = match ty {
            type_Value::Type_128BitPointer(_) => LLValue::ptr128(std::ptr::null_mut(), 0),
            type_Value::Type_64BitPointer(_) => LLValue::ptr64(std::ptr::null_mut(), 0),
            type_Value::Type_32BitPointer(_) => LLValue::ptr32(std::ptr::null_mut(), 0),
            type_Value::Type_16BitPointer(_) => LLValue::ptr16(std::ptr::null_mut(), 0),
            type_Value::Type_8BitPointer(_) => LLValue::ptr8(std::ptr::null_mut(), 0),
            type_Value::Type_u32(_) => LLValue::u32(0),
            ty => panic!("Operation for this type is not supported: {ty:?}"),
          };

          context.variable_value.insert(name, val);
        }
      }

      block_list_Value::LL_HeapAllocate(alloc) => {
        let ref_name = alloc.id.id.to_token();

        if let Some(ptr_val) = context.variable_value.get(&ref_name) {
          if let Some((ptr, cast_size, element_count)) = get_ptr_and_its_size(ptr_val) {
            if element_count > 0 {
              panic!("ptr space has already been allocated!");
            }

            let val = match &alloc.byte_count {
              assignment_group_1_Value::LL_Uint(int) => int.val as usize,
              assignment_group_1_Value::Id(id) => {
                let ref_name = alloc.id.id.to_token();
                if let Some(val) = context.variable_value.get(&ref_name) {
                  match val {
                    LLValue::f32(val) => *val as usize,
                    LLValue::f64(val) => *val as usize,
                    LLValue::u64(val) => *val as usize,
                    LLValue::u32(val) => *val as usize,
                    _ => panic!("Invalid value!"),
                  }
                } else {
                  panic!("Reference not found!");
                }
              }
              _ => 0,
            } as usize;

            let layout = std::alloc::Layout::array::<u8>((((cast_size as usize) / 8) * val))
              .expect("Could not create layout");

            let ptr = unsafe { std::alloc::alloc(layout) };

            if ptr.is_null() {
              panic!("could not allocate space!");
            }

            let ptr = match ptr_val {
              LLValue::ptr128(..) => LLValue::ptr128(ptr, val),
              LLValue::ptr64(..) => LLValue::ptr64(ptr, val),
              LLValue::ptr32(..) => LLValue::ptr32(ptr, val),
              LLValue::ptr8(..) => LLValue::ptr8(ptr, val),
              _ => unreachable!(),
            };

            context.variable_value.insert(ref_name, ptr);
          }
        } else {
          panic!("Variable is not defined! {}", alloc.id.tok.blame(1, 1, "", None));
        }
      }

      block_list_Value::LL_Assign(assign) => match &assign.location {
        assignment_group_Value::Id(id) => {
          let key = id.id.to_token();
          if let Some(ty) = context.variable_type.get(&key) {
            let new_val = interprete_ll_expression(&assign.expression, &*context, ty.clone());

            if !match (&new_val, ty) {
              (LLValue::u32(_), type_Value::Type_u32(..))
              | (LLValue::f32(_), type_Value::Type_f32(..))
              | (LLValue::f64(_), type_Value::Type_f64(..))
              | (LLValue::i8(_), type_Value::Type_i8(..))
              | (LLValue::i16(_), type_Value::Type_i16(..))
              | (LLValue::i32(_), type_Value::Type_i32(..))
              | (LLValue::i64(_), type_Value::Type_i64(..))
              | (LLValue::u8(_), type_Value::Type_u8(..))
              | (LLValue::u16(_), type_Value::Type_u16(..))
              | (LLValue::u64(_), type_Value::Type_u64(..)) => true,
              _ => false,
            } {
              panic!("Value type mismatch! {new_val:?} | {ty:?}")
            }
            context.variable_value.insert(key, new_val);
          }
        }
        assignment_group_Value::LL_MemLocation(location) => {
          if let Some((ptr, cast_size, _)) = interprete_ll_mem_location(&location, &*context) {
            let default_type = match cast_size {
              64 => type_Value::Type_u64(Type_u64 {}),
              32 => type_Value::Type_u32(Type_u32 {}),
              16 => type_Value::Type_u16(Type_u16 {}),
              8 => type_Value::Type_u8(Type_u8 {}),
              _ => unreachable!(),
            };

            match interprete_ll_expression(&assign.expression, &*context, default_type) {
              LLValue::f32(val) => {
                unsafe { *(ptr as *mut f32) = val };
              }
              _ => {}
            }
          } else {
            panic!("Could not interpret memory location {}", location.tok.blame(1, 1, "", None))
          }
        }
        assignment_group_Value::None => {}
        _ => {}
      },
      _ => {}
    }
  }

  false
}

fn resolve_pointer_cast(
  pointer_cast: &LL_PointerCast<Token>,
  context: &LLContext,
) -> Option<(*mut u8, u32, usize)> {
  let name = pointer_cast.id.id.to_token();

  if let Some(val) = context.variable_value.get(&name) {
    let cast_size = match &pointer_cast.ty {
      primitive_ptr_type_Value::Type_128BitPointer(_) => 128,
      primitive_ptr_type_Value::Type_64BitPointer(_) => 64,
      primitive_ptr_type_Value::Type_32BitPointer(_) => 32,
      primitive_ptr_type_Value::Type_16BitPointer(_) => 16,
      primitive_ptr_type_Value::Type_8BitPointer(_) => 8,
      _ => return None,
    };

    match val {
      LLValue::ptr128(ptr, size) => Some((*ptr, cast_size, *size)),
      LLValue::ptr64(ptr, size) => Some((*ptr, cast_size, *size)),
      LLValue::ptr32(ptr, size) => Some((*ptr, cast_size, *size)),
      LLValue::ptr8(ptr, size) => Some((*ptr, cast_size, *size)),
      _ => None,
    }
  } else {
    None
  }
}

fn interprete_ll_mem_location(
  node: &LL_MemLocation<Token>,
  context: &LLContext,
) -> Option<(*mut u8, usize, u32)> {
  if let Some((ptr, cast_size, element_count)) = {
    match &node.base_ptr {
      pointer_offset_group_Value::LL_PointerCast(cast) => resolve_pointer_cast(&cast, context),
      pointer_offset_group_Value::Id(id) => {
        if let Some(val) = context.variable_value.get(&id.id.to_token()) {
          get_ptr_and_its_size(val)
        } else {
          None
        }
      }

      _ => return None,
    }
  } {
    let offset_size = cast_size as isize / 8;

    let offset = interpret_ll_mem_expression(&node.expression, context) * offset_size;

    Some(unsafe { (ptr.offset(offset), cast_size as usize, element_count as u32) })
  } else {
    None
  }
}

fn get_ptr_and_its_size(val: &LLValue) -> Option<(*mut u8, u32, usize)> {
  match val {
    LLValue::ptr128(ptr, element_count) => Some((*ptr, 128, *element_count)),
    LLValue::ptr64(ptr, element_count) => Some((*ptr, 64, *element_count)),
    LLValue::ptr32(ptr, element_count) => Some((*ptr, 32, *element_count)),
    LLValue::ptr8(ptr, element_count) => Some((*ptr, 8, *element_count)),
    _ => None,
  }
}

fn interpret_ll_mem_expression(expr: &mem_expr_Value<Token>, context: &LLContext) -> isize {
  use mem_expr_Value::*;
  match expr {
    mem_expr_Value::LL_MemMul(mul) => {
      let l = interpret_ll_mem_expression(&mul.left, context);
      let r = interpret_ll_mem_expression(&mul.right, context);
      l * r
    }
    mem_expr_Value::LL_MemAdd(add) => {
      let l = interpret_ll_mem_expression(&add.left, context);
      let r = interpret_ll_mem_expression(&add.right, context);
      l + r
    }
    mem_expr_Value::Id(id) => {
      let name = id.id.to_token();

      if let Some(val) = context.variable_value.get(&name) {
        match val {
          LLValue::f32(val) => *val as isize,
          LLValue::u32(val) => *val as isize,
          v => panic!(
            "value of {v:?} is incompatible with this operation \n {}",
            id.tok.blame(1, 1, "", Option::None)
          ),
        }
      } else {
        panic!("{}", id.tok.blame(1, 1, "value has not been declared", Option::None));
      }
    }
    mem_expr_Value::LL_Int(int) => int.val as isize,
    None => 0,
  }
}

fn interprete_ll_expression(
  expr: &arithmetic_Value<Token>,
  context: &LLContext,
  expected_val: type_Value,
) -> LLValue {
  match &expr {
    arithmetic_Value::LL_PrimitiveCast(cast) => {
      let ty = cast.ty.clone();
      let val = interprete_ll_expression(&cast.expression, context, ty.into());
      val
    }
    arithmetic_Value::LL_MemLocation(location) => {
      if let Some((ptr, ..)) = interprete_ll_mem_location(&location, context) {
        LLValue::f32(unsafe { *(ptr as *mut f32) })
      } else {
        LLValue::undefined
      }
    }
    arithmetic_Value::LL_Member(mem) => {
      let id = mem.root.id.intern();

      if let Some(val) = context.variable_value.get(&id) {
        *val
      } else {
        LLValue::undefined
      }
    }
    arithmetic_Value::LL_Num(num) => match expected_val {
      type_Value::Type_u32(_) => LLValue::u32(num.val as u32),
      type_Value::Type_u16(_) => LLValue::u16(num.val as u16),
      type_Value::Type_u64(_) => LLValue::u64(num.val as u64),
      type_Value::Type_u8(_) => LLValue::u8(num.val as u8),
      type_Value::Type_i32(_) => LLValue::i32(num.val as i32),
      type_Value::Type_i16(_) => LLValue::i16(num.val as i16),
      type_Value::Type_i64(_) => LLValue::i64(num.val as i64),
      type_Value::Type_i8(_) => LLValue::i8(num.val as i8),
      type_Value::Type_f32(_) => LLValue::f32(num.val as f32),
      type_Value::Type_f64(_) => LLValue::f64(num.val as f64),
      _ => LLValue::f32(num.val as f32),
    },
    arithmetic_Value::Add(add) => {
      let left_val = interprete_ll_expression(&add.left, context, expected_val.clone());
      let right_val = interprete_ll_expression(&add.right, context, expected_val);

      use LLValue::*;

      match (left_val, right_val) {
        (f32(left), f32(right)) => f32(left + right),
        _ => unreachable!("Could not resolve expression"),
      }
    }
    arithmetic_Value::Sub(add) => {
      let left_val = interprete_ll_expression(&add.left, context, expected_val.clone());
      let right_val = interprete_ll_expression(&add.right, context, expected_val);

      use LLValue::*;
      match (left_val, right_val) {
        (f32(left), f32(right)) => f32(left - right),
        (u32(left), u32(right)) => u32(left - right),
        _ => unreachable!("Could not resolve expression"),
      }
    }
    arithmetic_Value::Mul(mul) => {
      let left_val = interprete_ll_expression(&mul.left, context, expected_val.clone());
      let right_val = interprete_ll_expression(&mul.right, context, expected_val);

      use LLValue::*;

      match (left_val, right_val) {
        (f32(left), f32(right)) => f32(left * right),
        _ => unreachable!("Could not resolve expression"),
      }
    }
    _ => LLValue::undefined,
  }
}

#[derive(Debug)]
struct LLContext {
  variable_type:  BTreeMap<IString, type_Value>,
  variable_value: BTreeMap<IString, LLValue>,
}

#[derive(Debug, Clone, Copy)]
struct PtrData {
  ptr:        *mut u8,
  bit_size:   usize,
  byte_size:  usize,
  allocation: usize,
}

struct IntData {
  val:      u64,
  bit_size: usize,
  signed:   bool,
}

enum BitSize



#[derive(Debug, Clone, Copy)]
#[allow(non_camel_case_types)]
pub enum LLValue {
  undefined,
  ptr(PtrData),
  int(IntData),
  ptr8(*mut u8, usize),
  ptr16(*mut u8, usize),
  ptr32(*mut u8, usize),
  ptr64(*mut u8, usize),
  ptr128(*mut u8, usize),
  f32(f32),
  f64(f64),
  i8(i8),
  i16(i16),
  i32(i32),
  i64(i64),
  u8(u8),
  u16(u16),
  u32(u32),
  u64(u64),
}

fn temp() {
  let input = r###"
  

  
  "###;
}
