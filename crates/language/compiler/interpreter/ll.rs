use crate::compiler::parser::{
  self,
  LL_MemLocation,
  LL_PointerCast,
  LL_function,
  Mem_exprValues,
  Primitive_typeValues,
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

    use Primitive_typeValues::*;

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

  dbg!(&context);

  // Interpret statements

  let mut out_val = LLValue::undefined;

  for statement in &funct.block.statements {
    match statement {
      parser::AssignmentValues::LL_Var_Binding(binding) => {
        let name = binding.id.id.intern();
        let ty = &binding.ty;

        if let Some(old) = context.variable_type.insert(name, ty.clone()) {
          panic!("Redefined variable")
        } else {
          let val = match ty {
            Primitive_typeValues::Type_128BitPointer(_) => LLValue::ptr128(std::ptr::null_mut(), 0),
            Primitive_typeValues::Type_64BitPointer(_) => LLValue::ptr64(std::ptr::null_mut(), 0),
            Primitive_typeValues::Type_32BitPointer(_) => LLValue::ptr32(std::ptr::null_mut(), 0),
            Primitive_typeValues::Type_16BitPointer(_) => LLValue::ptr16(std::ptr::null_mut(), 0),
            Primitive_typeValues::Type_8BitPointer(_) => LLValue::ptr8(std::ptr::null_mut(), 0),
            ty => panic!("Operation for this type is not supported: {ty:?}"),
          };

          context.variable_value.insert(name, val);
        }
      }

      parser::AssignmentValues::LL_HeapAllocate(alloc) => {
        let ref_name = alloc.id.id.to_token();

        if let Some(ptr_val) = context.variable_value.get(&ref_name) {
          if let Some((ptr, cast_size, element_count)) = get_ptr_and_its_size(ptr_val) {
            if element_count > 0 {
              panic!("ptr space has already been allocated!");
            }

            let val = match &alloc.byte_count {
              parser::Assignment_group_1Values::LL_UnsignedInteger(int) => int.val as usize,
              parser::Assignment_group_1Values::Id(id) => {
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

      parser::AssignmentValues::LL_Assign(assign) => {
        let val: LLValue = interprete_ll_expression(&assign.expression, &context);
        match &assign.location {
          parser::Assignment_groupValues::Id(_) => {}
          parser::Assignment_groupValues::LL_MemLocation(location) => {
            if let Some(ptr) = interprete_ll_mem_location(&location, &context) {
              match interprete_ll_expression(&assign.expression, &context) {
                LLValue::f32(val) => {
                  unsafe { *(ptr as *mut f32) = val };
                }
                _ => {}
              }
            } else {
              panic!("Could not interpret memory location {}", location.tok.blame(1, 1, "", None))
            }
          }
          parser::Assignment_groupValues::None => {}
          _ => {}
        }
      }
      _ => {}
    }
  }

  let ret = &funct.block.ret;

  let ret_val = interprete_ll_expression(&ret.expression, &context);

  out_val
}

fn resolve_pointer_cast(
  pointer_cast: &LL_PointerCast<Token>,
  context: &LLContext,
) -> Option<(*mut u8, u32, usize)> {
  let name = pointer_cast.id.id.to_token();

  if let Some(val) = context.variable_value.get(&name) {
    let cast_size = match &pointer_cast.ty {
      Primitive_typeValues::Type_128BitPointer(_) => 128,
      Primitive_typeValues::Type_64BitPointer(_) => 64,
      Primitive_typeValues::Type_32BitPointer(_) => 32,
      Primitive_typeValues::Type_16BitPointer(_) => 16,
      Primitive_typeValues::Type_8BitPointer(_) => 8,
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
) -> Option<*mut u8> {
  if let Some((ptr, cast_size, element_count)) = {
    match &node.base_ptr {
      parser::Pointer_offset_groupValues::LL_PointerCast(cast) => {
        resolve_pointer_cast(&cast, context)
      }
      parser::Pointer_offset_groupValues::Id(id) => {
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

    dbg!(offset_size);

    let offset = interpret_ll_mem_expression(&node.expression, context) * offset_size;

    Some(unsafe { ptr.offset(offset) })
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

fn interpret_ll_mem_expression(expr: &Mem_exprValues<Token>, context: &LLContext) -> isize {
  use Mem_exprValues::*;
  match expr {
    LL_MemMul(mul) => {
      let l = interpret_ll_mem_expression(&mul.left, context);
      let r = interpret_ll_mem_expression(&mul.right, context);
      l * r
    }
    LL_MemAdd(add) => {
      let l = interpret_ll_mem_expression(&add.left, context);
      let r = interpret_ll_mem_expression(&add.right, context);
      l * r
    }
    Id(id) => {
      let name = id.id.to_token();

      if let Some(val) = context.variable_value.get(&name) {
        match val {
          LLValue::f32(val) => *val as isize,
          v => panic!(
            "value of {v:?} is incompatible with this operation \n {}",
            id.tok.blame(1, 1, "", Option::None)
          ),
        }
      } else {
        panic!("{}", id.tok.blame(1, 1, "value has not been declared", Option::None));
      }
    }
    LL_Integer(int) => int.val as isize,
    None => 0,
  }
}

fn interprete_ll_expression(expr: &parser::LogicalValues<Token>, context: &LLContext) -> LLValue {
  match &expr {
    parser::LogicalValues::LL_MemLocation(location) => {
      if let Some(ptr) = interprete_ll_mem_location(&location, context) {
        LLValue::f32(unsafe { *(ptr as *mut f32) })
      } else {
        LLValue::undefined
      }
    }
    parser::LogicalValues::LL_Member(mem) => {
      let id = mem.root.id.intern();

      if let Some(val) = context.variable_value.get(&id) {
        *val
      } else {
        LLValue::undefined
      }
    }
    parser::LogicalValues::LL_Number(num) => LLValue::f32(num.val as f32),
    parser::LogicalValues::Add(add) => {
      let left_val = interprete_ll_expression(&add.left, context);
      let right_val = interprete_ll_expression(&add.right, context);

      use LLValue::*;

      match (left_val, right_val) {
        (f32(left), f32(right)) => f32(left + right),
        _ => unreachable!("Could not resolve expression"),
      }
    }
    parser::LogicalValues::Mul(mul) => {
      let left_val = interprete_ll_expression(&mul.left, context);
      let right_val = interprete_ll_expression(&mul.right, context);

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
  variable_type:  BTreeMap<IString, parser::Primitive_typeValues>,
  variable_value: BTreeMap<IString, LLValue>,
}

#[derive(Debug, Clone, Copy)]
#[allow(non_camel_case_types)]
pub enum LLValue {
  undefined,
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
