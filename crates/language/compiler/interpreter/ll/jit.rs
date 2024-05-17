#![allow(unused)]

use super::interpreter::{BitSize, IntVal, LLVal, PtrType};
use crate::compiler::{
  self,
  interpreter::{
    error::RumResult,
    ll::interpreter::{IntData, PtrData},
  },
  parser::{
    arithmetic_Value,
    assignment_Value,
    assignment_group_1_Value,
    assignment_group_Value,
    block_list_Value,
    logical_Value,
    match_group_Value,
    match_list_1_Value,
    mem_expr_Value,
    pointer_offset_group_Value,
    primitive_ptr_type_Value,
    primitive_type_Value,
    table_type_Value,
    type_Value,
    LL_Block,
    LL_MemLocation,
    LL_PointerCast,
    LL_Var_Binding,
    LL_function,
    Type_128BitPointer,
    Type_16BitPointer,
    Type_32BitPointer,
    Type_64BitPointer,
    Type_8BitPointer,
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
use rum_logger::todo_note;
use std::{
  collections::{BTreeMap, BTreeSet, VecDeque},
  fmt::{Debug, Write},
};
use BitSize::*;
use OpVal::*;

pub fn optimize_ssa_function(funct: &LL_SSA_function<()>) -> LL_SSA_function<()> {
  LL_SSA_function { blocks: funct.blocks.clone() }
}

pub fn compile_ll_function(funct: &LL_function<Token>) -> RumResult<LL_SSA_function<()>> {
  let mut ctx = LL_context::default();
  let block = ctx.push_block(None);

  // Process function parameters

  if let Err(err) = process_params(&funct.params, block) {
    panic!("{err:>?}");
  }

  let active_block = match process_block(&funct.block, block, 0) {
    Err(err) => {
      panic!("failed {err:?}");
    }
    Ok(block) => block,
  };

  match &funct.block.ret.expression {
    arithmetic_Value::None => {}
    expr => {
      let ty = ty_to_ll_value(&funct.return_type)?;
      let val = Some(process_arithmetic_expression(&expr, active_block, ty)?);
      ctx.get_head_block().return_val = val;
    }
  }

  dbg!(&ctx);

  Ok(LL_SSA_function {
    blocks: ctx.blocks.into_iter().map(|b| unsafe { Box::from_raw(b) }).collect(),
  })
}

fn process_params(
  params: &Vec<Box<LL_Var_Binding<Token>>>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<()> {
  for (index, param) in params.iter().enumerate() {
    let ty = ty_to_ll_value(&param.ty)?;
    let name = param.id.id.intern();

    if let LLVal::Und = ty {
      return Err(
        format!("Invalid function parameter: \n{}", param.tok.blame(1, 1, "", None)).into(),
      );
    }

    match exe_block.get_id(name) {
      Some(e) => {
        return Err(
          format!(
            "Error: the binding [ {} ] has already been declared\nFirst Declared:\n{}\nRedeclared:\n{}",
            name.to_string(),
            e.2.blame(1, 1, "", None),
            param.tok.blame(1, 1, "", None)
          )
          .into(),
        );
      }
      None => {
        let offset = exe_block.get_stack_offset(1);
        exe_block.decls.insert(
          name,
          (
            PtrData { bits: ty.bit_size(), elements: 1, ptr: PtrType::Stack(offset) },
            ty,
            param.tok.clone(),
          ),
        );
      }
    }
  }

  Ok(())
}

fn process_block<'a>(
  block: &LL_Block<Token>,
  exe_block: &'a mut ExeBlock<()>,
  loop_block_id: usize,
) -> RumResult<&'a mut ExeBlock<()>> {
  let mut exe_block = exe_block;
  for stmt in &block.statements {
    exe_block = process_statements(stmt, exe_block, loop_block_id)?;
  }
  Ok(exe_block)
}

fn process_statements<'a>(
  statement: &block_list_Value<Token>,
  exe_block: &'a mut ExeBlock<()>,
  loop_block_id: usize,
) -> RumResult<&'a mut ExeBlock<()>> {
  match statement {
    block_list_Value::LL_Continue(_) => {
      exe_block.branch_unconditional = Some(loop_block_id);
      exe_block.push_unary_op(Op::JUMP, LLVal::Und, OpVal::BLOCK(loop_block_id));
      exe_block.ctx().get_block_mut(loop_block_id).unwrap().predecessors.insert(exe_block.id);
      return Ok(exe_block);
    }
    block_list_Value::LL_Match(m) => {
      match process_match_expression(&m.expression, exe_block, LLVal::Und)? {
        LogicalExprType::Arithmatic(arithmatic_opval, _) => {
          todo!("Arithmetic based matching")
        }
        LogicalExprType::Boolean(bool_block) => {
          let mut default_case = None;
          let mut bool_success_case = None;

          for match_block in &m.statements {
            match match_block {
              match_list_1_Value::LL_Block(block) => {
                let start_block = bool_block.create_successor();
                let start_block_id = start_block.id;
                start_block.predecessors.insert(bool_block.id);
                let end_block = process_block(&block, start_block, loop_block_id)?;
                default_case = Some((start_block_id, end_block));
              }

              match_list_1_Value::LL_MatchCase(case) => {
                let start_block = bool_block.create_successor();
                let start_block_id = start_block.id;
                start_block.predecessors.insert(bool_block.id);
                let end_block = process_block(&case.block, start_block, loop_block_id)?;

                match &case.val {
                  compiler::parser::match_case_Value::LL_False(_) => {
                    default_case = Some((start_block_id, end_block));
                  }
                  compiler::parser::match_case_Value::LL_True(_) => {
                    bool_success_case = Some((start_block_id, end_block));
                  }
                  compiler::parser::match_case_Value::LL_Num(val) => {
                    panic!("Incorrect expression for logical type");
                  }
                  _ => unreachable!(),
                }
              }
              _ => unreachable!(),
            }
          }

          let join_block = bool_block.create_successor();

          if let Some((start_block_id, end_block)) = default_case {
            dbg!(&end_block);
            bool_block.branch_fail = Some(start_block_id);
            if end_block.branch_unconditional.is_none() && end_block.branch_fail.is_none() {
              end_block.branch_unconditional = Some(join_block.id);
              join_block.predecessors.insert(end_block.id);
            }
          } else {
            bool_block.branch_fail = Some(join_block.id);
            join_block.predecessors.insert(bool_block.id);
          }

          if let Some((start_block_id, end_block)) = bool_success_case {
            bool_block.branch_succeed = Some(start_block_id);
            if end_block.branch_unconditional.is_none() && end_block.branch_fail.is_none() {
              end_block.branch_unconditional = Some(join_block.id);
              join_block.predecessors.insert(end_block.id);
            }
          } else {
            bool_block.branch_succeed = Some(join_block.id);
            join_block.predecessors.insert(bool_block.id);
          }

          return Ok(join_block);
        }
      };
    }
    block_list_Value::LL_Loop(loop_) => {
      let predecessor = exe_block.create_successor();
      predecessor.predecessors.insert(exe_block.id);
      let id = predecessor.id;
      return Ok(process_block(&loop_.block, predecessor, id)?);
    }
    block_list_Value::LL_Var_Binding(binding) => {
      let decl = &binding.id;
      let decl_name = decl.id.intern();
      let mut ty = ty_to_ll_value(&binding.ty)?;

      process_output_value(&mut ty, exe_block);

      let offset = exe_block.get_stack_offset(1);
      if let Some(_) = exe_block.decls.insert(
        decl_name,
        (
          PtrData { bits: ty.bit_size(), elements: 0, ptr: PtrType::Unallocated },
          ty,
          binding.tok.clone(),
        ),
      ) {
        panic!("Aliased a value!");
      }
    }
    block_list_Value::LL_StackAllocate(alloc) => {
      let target = &alloc.id;
      let target_name = target.id.to_token();
      let ptr_type = PtrType::Stack(0);
      let byte_count = &alloc.byte_count;
      create_allocation(exe_block, target_name, ptr_type, byte_count);
    }
    block_list_Value::LL_HeapAllocate(alloc) => {
      let target = &alloc.id;
      let target_name = target.id.to_token();
      let ptr_type = PtrType::Heap;
      let byte_count = &alloc.byte_count;
      create_allocation(exe_block, target_name, ptr_type, byte_count);
    }
    block_list_Value::LL_Assign(assign) => match &assign.location {
      assignment_Value::Id(binding) => {
        let name = binding.id.intern();

        if let Some((mut ptr_data, val, tok)) = exe_block.get_id(name).cloned() {
          let value = process_arithmetic_expression(&assign.expression, exe_block, val)?;

          if let PtrType::Unallocated = ptr_data.ptr {
            let offset = exe_block.get_stack_offset(1);
            ptr_data.ptr = PtrType::Stack(offset);
            ptr_data.elements = 1;
            exe_block.get_id_mut(name).unwrap().0 = ptr_data;
          }

          match (value) {
            (Lit(lit)) => {
              exe_block.push_binary_op(Op::STORE, LLVal::Und, OpVal::REF(ptr_data), value);
            }
            _ => {
              exe_block.push_binary_op(Op::STORE, LLVal::Und, OpVal::REF(ptr_data), value);
            }
          }
        } else {
          panic!("{}", binding.tok.blame(1, 1, "not found", None))
        }
      }
      assignment_Value::LL_MemLocation(location) => {
        let base_ptr = resolve_base_ptr(&location.base_ptr, exe_block);
        let offset = resolve_mem_offset(&location.expression, exe_block);

        if let ref_val @ OpVal::REF(mut ptr) = base_ptr {
          let expression =
            process_arithmetic_expression(&assign.expression, exe_block, LLVal::Und)?;

          match (offset) {
            (Lit(lit)) if ptr.elements > 0 => {
              if let IntVal::Static(offset_val) = lit.to_int(b64).val {
                if offset_val > ptr.elements as i64 {
                  panic!("Out of bounds access");
                }

                ptr.elements = (ptr.elements as i64 - offset_val) as usize;

                let ptr_location =
                  exe_block.push_binary_op(Op::ADD, LLVal::Ptr(ptr), base_ptr, offset);

                exe_block.push_binary_op(Op::STORE, LLVal::Und, ptr_location, expression);
              } else {
                panic!("should have data")
              }
            }
            _ => {
              ptr.elements = 0; // Unknown number of elements left

              let ptr_location =
                exe_block.push_binary_op(Op::ADD, LLVal::Ptr(ptr), base_ptr, offset);

              exe_block.push_binary_op(Op::STORE, LLVal::Und, ptr_location, expression);
            }
          }
        } else {
          unreachable!()
        }
      }
      assignment_Value::None => {
        todo!()
      }
      val => {
        todo!("{val:#?}")
      }
    },
    val => {
      todo!("{val:#?}")
    }
  }

  Ok(exe_block)
}

fn create_allocation(
  exe_block: &mut ExeBlock<()>,
  target_name: IString,
  ptr_type: PtrType,
  byte_count: &assignment_group_1_Value<Token>,
) {
  match exe_block.get_id(target_name).cloned() {
    Some((mut ptr, val, tok)) => {
      if ptr.elements != 0 || ptr.ptr != PtrType::Unallocated {
        panic!("Already allocated! {}", tok.blame(1, 1, "", None))
      }

      ptr.ptr = ptr_type;

      let byte_size = ptr.bits.byte_count() as i64;

      let op_val = match byte_count {
        assignment_group_1_Value::LL_Uint(int) => {
          ptr.elements = int.val as usize;
          OpVal::Lit(LLVal::Int(IntData {
            val:    IntVal::Static(int.val),
            bits:   b64,
            signed: false,
          }))
        }

        assignment_group_1_Value::Id(id) => {
          if let Some((ptr, mut val, _)) = exe_block.get_id(id.id.to_token()).cloned() {
            match &mut val {
              LLVal::Int(data @ IntData { val: IntVal::Undefined, .. }) => {
                data.val = IntVal::SSA(exe_block.get_current_ssa_id())
              }
              _ => {}
            }

            exe_block.push_unary_op(Op::LOAD, val, OpVal::REF(ptr))
          } else {
            panic!()
          }
        }

        val => unreachable!("{val:?}"),
      };

      exe_block.decls.get_mut(&target_name).unwrap().0 = ptr;
      exe_block.outputs.insert(target_name, val);

      exe_block.push_binary_op(Op::ALLOC, LLVal::Ptr(ptr), OpVal::REF(ptr), op_val);
    }
    None => {
      panic!("decleration not found")
    }
  }
}

fn resolve_mem_offset(expr: &mem_expr_Value<Token>, exe_block: &mut ExeBlock<()>) -> OpVal<()> {
  match expr {
    mem_expr_Value::Id(id) => {
      if let Some((ptr, mut val, _)) = exe_block.get_id(id.id.to_token()).cloned() {
        match &mut val {
          LLVal::Int(data @ IntData { val: IntVal::Undefined, .. }) => {
            data.val = IntVal::SSA(exe_block.get_current_ssa_id())
          }
          _ => {}
        }

        exe_block.push_unary_op(Op::LOAD, val, OpVal::REF(ptr))
      } else {
        panic!()
      }
    }
    mem_expr_Value::LL_Int(int) => OpVal::Lit(LLVal::Int(IntData {
      val:    IntVal::Static(int.val),
      bits:   b64,
      signed: false,
    })),
    mem_expr_Value::LL_MemAdd(add) => {
      let left = resolve_mem_offset(&add.left, exe_block);
      let right = resolve_mem_offset(&add.right, exe_block);

      match (left, right) {
        (
          OpVal::Lit(LLVal::Int(IntData { val: IntVal::Static(left), .. })),
          OpVal::Lit(LLVal::Int(IntData { val: IntVal::Static(right), .. })),
        ) => {
          let val = right + left;

          OpVal::Lit(LLVal::Int(IntData {
            val:    IntVal::Static(val),
            bits:   b64,
            signed: false,
          }))
        }
        _ => exe_block.push_binary_op(
          Op::ADD,
          LLVal::Int(IntData {
            val:    IntVal::SSA(exe_block.get_current_ssa_id()),
            bits:   b64,
            signed: false,
          }),
          left,
          right,
        ),
      }
    }
    mem_expr_Value::LL_MemMul(mul) => {
      let left = resolve_mem_offset(&mul.left, exe_block);
      let right = resolve_mem_offset(&mul.right, exe_block);

      match (left, right) {
        (
          OpVal::Lit(LLVal::Int(IntData { val: IntVal::Static(left), .. })),
          OpVal::Lit(LLVal::Int(IntData { val: IntVal::Static(right), .. })),
        ) => {
          let val = right * left;

          OpVal::Lit(LLVal::Int(IntData {
            val:    IntVal::Static(val),
            bits:   b64,
            signed: false,
          }))
        }
        _ => exe_block.push_binary_op(
          Op::MUL,
          LLVal::Int(IntData {
            val:    IntVal::SSA(exe_block.get_current_ssa_id()),
            bits:   b64,
            signed: false,
          }),
          left,
          right,
        ),
      }
    }
    _ => unreachable!(),
  }
}

fn resolve_base_ptr(
  base_ptr: &pointer_offset_group_Value<Token>,
  exe_block: &mut ExeBlock<()>,
) -> OpVal<()> {
  match base_ptr {
    pointer_offset_group_Value::Id(id) => {
      if let Some((ptr, val, tok)) = exe_block.get_id(id.id.to_token()).cloned() {
        OpVal::REF(ptr)
      } else {
        panic!("Couldn't find base pointer");
      }
    }
    pointer_offset_group_Value::LL_PointerCast(cast) => todo!(),
    pointer_offset_group_Value::None => unreachable!(),
  }
}

enum LogicalExprType<'a> {
  /// Index of the boolean expression block.
  Boolean(&'a mut ExeBlock<()>),
  Arithmatic(OpVal<()>, &'a mut ExeBlock<()>),
}

impl<'a> LogicalExprType<'a> {
  pub fn map_arith_result(
    result: RumResult<OpVal<()>>,
    exe_block: &'a mut ExeBlock<()>,
  ) -> RumResult<Self> {
    match result {
      Err(err) => Err(err),
      Ok(opval) => Ok(Self::Arithmatic(opval, exe_block)),
    }
  }
}

fn process_match_expression<'b, 'a: 'b>(
  expression: &match_group_Value<Token>,
  exe_block: &'a mut ExeBlock<()>,
  e_val: LLVal,
) -> RumResult<LogicalExprType<'a>> {
  use LogicalExprType as LET;

  match expression {
    match_group_Value::EQ(val) => handle_eq(val, exe_block),
    match_group_Value::LE(val) => handle_le(val, exe_block),
    match_group_Value::LS(val) => handle_ls(val, exe_block),
    match_group_Value::GR(val) => handle_gr(val, exe_block),
    match_group_Value::GE(val) => handle_ge(val, exe_block, e_val),
    match_group_Value::NE(val) => handle_ne(val, exe_block),
    match_group_Value::AND(val) => handle_and(val, exe_block),
    match_group_Value::OR(val) => handle_or(val, exe_block),
    match_group_Value::XOR(val) => handle_xor(val, exe_block),
    match_group_Value::NOT(val) => handle_not(val, exe_block),
    match_group_Value::LL_Member(mem) => {
      LET::map_arith_result(handle_member(mem, exe_block), exe_block)
    }
    match_group_Value::LL_SelfMember(mem) => {
      LET::map_arith_result(handle_self_member(mem, exe_block), exe_block)
    }
    match_group_Value::LL_MemLocation(mem) => {
      LET::map_arith_result(handle_mem_location(mem, exe_block), exe_block)
    }
    match_group_Value::LL_Call(val) => {
      LET::map_arith_result(handle_call(val, exe_block), exe_block)
    }
    match_group_Value::LL_PrimitiveCast(prim) => {
      LET::map_arith_result(handle_primitive_cast(prim, exe_block), exe_block)
    }
    match_group_Value::LL_Str(..) => todo!(),
    match_group_Value::LL_Num(val) => LET::map_arith_result(handle_num(val, e_val), exe_block),
    match_group_Value::Add(val) => LET::map_arith_result(handle_add(val, exe_block), exe_block),
    match_group_Value::Div(val) => LET::map_arith_result(handle_div(val, exe_block), exe_block),
    match_group_Value::Log(val) => LET::map_arith_result(handle_log(val, exe_block), exe_block),
    match_group_Value::Mul(val) => LET::map_arith_result(handle_mul(val, exe_block), exe_block),
    match_group_Value::Mod(val) => LET::map_arith_result(handle_mod(val, exe_block), exe_block),
    match_group_Value::Pow(val) => LET::map_arith_result(handle_pow(val, exe_block), exe_block),
    match_group_Value::Sub(val) => {
      LET::map_arith_result(handle_sub(val, exe_block, e_val), exe_block)
    }
    match_group_Value::Root(..) => todo!(),
    match_group_Value::None => unreachable!(),
  }
}

fn process_arithmetic_expression(
  expression: &arithmetic_Value<Token>,
  exe_block: &mut ExeBlock<()>,
  e_val: LLVal,
) -> RumResult<OpVal<()>> {
  match expression {
    arithmetic_Value::LL_Member(mem) => handle_member(mem, exe_block),
    arithmetic_Value::LL_SelfMember(mem) => handle_self_member(mem, exe_block),
    arithmetic_Value::LL_MemLocation(mem) => handle_mem_location(mem, exe_block),
    arithmetic_Value::LL_Call(val) => handle_call(val, exe_block),
    arithmetic_Value::LL_PrimitiveCast(prim) => handle_primitive_cast(prim, exe_block),
    arithmetic_Value::LL_Str(..) => todo!(),
    arithmetic_Value::LL_Num(val) => handle_num(val, e_val),
    arithmetic_Value::Add(val) => handle_add(val, exe_block),
    arithmetic_Value::Div(val) => handle_div(val, exe_block),
    arithmetic_Value::Log(val) => handle_log(val, exe_block),
    arithmetic_Value::Mul(val) => handle_mul(val, exe_block),
    arithmetic_Value::Mod(val) => handle_mod(val, exe_block),
    arithmetic_Value::Pow(val) => handle_pow(val, exe_block),
    arithmetic_Value::Sub(val) => handle_sub(val, exe_block, e_val),
    arithmetic_Value::Root(..) => todo!(),
    arithmetic_Value::None => unreachable!(),
  }
}

fn convert_val(c_val: OpVal<()>, e_val: LLVal, exe_block: &mut ExeBlock<()>) -> OpVal<()> {
  match (c_val, e_val) {
    // Floating point conversions
    (c_op @ OpVal::SSA(_, LLVal::F32(c)), e_val @ LLVal::F64(e)) => {
      exe_block.push_unary_op(Op::CONVERT, e_val, c_op)
    }
    (c_op @ OpVal::SSA(_, LLVal::F64(c)), e_val @ LLVal::F32(e)) => {
      exe_block.push_unary_op(Op::CONVERT, e_val, c_op)
    }
    (c_op @ OpVal::SSA(_, LLVal::Int(int)), e_val @ LLVal::F32(e)) => {
      exe_block.push_unary_op(Op::CONVERT, e_val, c_op)
    }
    (c_op @ OpVal::SSA(_, LLVal::Int(int)), e_val @ LLVal::F64(e)) => {
      exe_block.push_unary_op(Op::CONVERT, e_val, c_op)
    }

    // Integer conversions
    (c_op @ OpVal::SSA(_, LLVal::F32(c)), e_val @ LLVal::Int(int)) => {
      exe_block.push_unary_op(Op::CONVERT, e_val, c_op)
    }
    (c_op @ OpVal::SSA(_, LLVal::F64(c)), e_val @ LLVal::Int(int)) => {
      exe_block.push_unary_op(Op::CONVERT, e_val, c_op)
    }

    (c_op @ OpVal::SSA(_, LLVal::Int(c_int)), e_val @ LLVal::Int(int)) => {
      if c_int.signed != int.signed || c_int.bits != int.bits {
        exe_block.push_unary_op(Op::CONVERT, e_val, c_op)
      } else {
        c_op
      }
    }

    // Literal Conversions
    (OpVal::Lit(LLVal::F32(c)), LLVal::F64(..)) => OpVal::Lit(LLVal::F64((c as f64))),
    (OpVal::Lit(LLVal::F64(c)), LLVal::F32(..)) => OpVal::Lit(LLVal::F32((c as f32))),
    (OpVal::Lit(LLVal::Int(c_int)), LLVal::F32(..)) => {
      OpVal::Lit(LLVal::F32(fp_from_int_val(c_int)))
    }
    (OpVal::Lit(LLVal::Int(c_int)), LLVal::F64(..)) => {
      OpVal::Lit(LLVal::F64(fp_from_int_val(c_int)))
    }
    (OpVal::Lit(LLVal::F32(c)), LLVal::Int(mut int)) => {
      set_int_val_from_fp(&mut int, c);
      OpVal::Lit(LLVal::Int(int))
    }
    (OpVal::Lit(LLVal::F64(c)), LLVal::Int(mut int)) => {
      set_int_val_from_fp(&mut int, c);
      OpVal::Lit(LLVal::Int(int))
    }

    _ => c_val,
  }
}

fn fp_from_int_val<F: num_traits::Float>(int: IntData) -> F {
  if int.signed {
    match int.bits {
      b128 => F::from(int.val.static_val().unwrap() as i128).unwrap(),
      b64 => F::from(int.val.static_val().unwrap() as i64).unwrap(),
      b32 => F::from(int.val.static_val().unwrap() as i32).unwrap(),
      b16 => F::from(int.val.static_val().unwrap() as i16).unwrap(),
      _ | b8 => F::from(int.val.static_val().unwrap() as i8).unwrap(),
    }
  } else {
    match int.bits {
      b128 => F::from(int.val.static_val().unwrap() as u128).unwrap(),
      b64 => F::from(int.val.static_val().unwrap() as u64).unwrap(),
      b32 => F::from(int.val.static_val().unwrap() as u32).unwrap(),
      b16 => F::from(int.val.static_val().unwrap() as u16).unwrap(),
      _ | b8 => F::from(int.val.static_val().unwrap() as u8).unwrap(),
    }
  }
}

fn set_int_val_from_fp<T: num_traits::Float + num_traits::Num>(int: &mut IntData, c: T) {
  if int.signed {
    match int.bits {
      b128 => int.val = IntVal::Static(c.to_i128().unwrap() as i64),
      b64 => int.val = IntVal::Static(c.to_i64().unwrap() as i64),
      b32 => int.val = IntVal::Static(c.to_i32().unwrap() as i32 as i64),
      b16 => int.val = IntVal::Static(c.to_i16().unwrap() as i16 as i64),
      _ | b8 => int.val = IntVal::Static(c.to_i8().unwrap() as i8 as i64),
    };
  } else {
    match int.bits {
      b128 => int.val = IntVal::Static(c.to_u128().unwrap() as i64),
      b64 => int.val = IntVal::Static(c.to_u64().unwrap() as i64),
      b32 => int.val = IntVal::Static(c.to_u32().unwrap() as i32 as i64),
      b16 => int.val = IntVal::Static(c.to_u16().unwrap() as i16 as i64),
      _ | b8 => int.val = IntVal::Static(c.to_u8().unwrap() as i8 as i64),
    };
  }
}

fn handle_primitive_cast(
  val: &compiler::parser::LL_PrimitiveCast<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  let ty = val.ty.clone().into();
  let ty = ty_to_ll_value(&ty)?;

  let val = process_arithmetic_expression(&val.expression, exe_block, ty)?;

  match val {
    OpVal::Lit(lit) => match (lit, ty) {
      _ => Ok(val),
    },
    OpVal::REF(r) => todo!(),
    OpVal::SSA(..) => todo!(),
    OpVal::BLOCK(..) => todo!(),
    OpVal::REG(..) => todo!(),
  }
}

fn handle_call(
  val: &compiler::parser::LL_Call<Token>,

  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle LL_Call Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_mem_location(
  val: &compiler::parser::LL_MemLocation<Token>,

  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  panic!("Handle Mem Location Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_add(
  val: &compiler::parser::Add<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle Add Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_div(
  val: &compiler::parser::Div<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle Div Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_mul(
  val: &compiler::parser::Mul<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle Mul Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_mod(
  val: &compiler::parser::Mod<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle Mod Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_log(
  val: &compiler::parser::Log<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle Log Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_pow(
  val: &compiler::parser::Pow<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle Pow Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_self_member(
  val: &compiler::parser::LL_SelfMember<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle Self Member Expression");
  Ok(exe_block.create_ssa_id(LLVal::Und))
}

fn handle_member(
  val: &compiler::parser::LL_Member<Token>,
  exe_block: &mut ExeBlock<()>,
) -> RumResult<OpVal<()>> {
  todo_note!("Handle Member Expression - Multi Level Case");
  match exe_block.get_id(val.root.id.to_token()).cloned() {
    Some((ptr, mut val, _)) => {
      match &mut val {
        LLVal::Int(data @ IntData { val: IntVal::Undefined, .. }) => {
          data.val = IntVal::SSA(exe_block.get_current_ssa_id())
        }
        _ => {}
      }

      Ok(exe_block.push_unary_op(Op::LOAD, val, OpVal::REF(ptr)))
    }
    None => {
      panic!(
        "Undeclared variable {exe_block:#?}[{}]:\n{}",
        val.root.id,
        val.root.tok.blame(1, 1, "", None)
      )
    }
  }
}

fn handle_num(val: &compiler::parser::LL_Num, expected_val: LLVal) -> RumResult<OpVal<()>> {
  let val = match expected_val {
    LLVal::F64(..) | LLVal::Und => Lit(LLVal::F64(val.val)),
    LLVal::F32(..) => Lit(LLVal::F32(val.val as f32)),
    LLVal::Int(mut int) => {
      int.val = IntVal::Static(val.val as i64);
      Lit(LLVal::Int(int))
    }
    LLVal::Ptr(PtrData { bits, .. }) => {
      Lit(LLVal::Int(IntData { val: IntVal::Static(val.val as u64 as i64), bits, signed: false }))
    }
    LLVal::PtrBits(bits) => {
      Lit(LLVal::Int(IntData { val: IntVal::Static(val.val as u64 as i64), bits, signed: false }))
    }
  };

  Ok(val)
}

fn handle_ge<'a>(
  val: &compiler::parser::GE<Token>,
  exe_block: &'a mut ExeBlock<()>,
  e_val: LLVal,
) -> RumResult<LogicalExprType<'a>> {
  let left = process_arithmetic_expression(&val.left, exe_block, e_val)?;
  let right = process_arithmetic_expression(&val.right, exe_block, e_val)?;
  let right = convert_val(right, left.ll_val(), exe_block);
  // If both left and right are literal values, we perform the calculation and
  // return a literal u64 of the result.
  // Otherwise, we return a SSE reference val

  let mut e_val = IntData {
    val:    IntVal::SSA(exe_block.get_current_ssa_id()),
    bits:   b32,
    signed: false,
  };

  let opval = if left.is_ssa() || right.is_ssa() {
    exe_block.push_binary_op(Op::GE, LLVal::Int(e_val), left, right)
  } else {
    match (left, right) {
      (OpVal::Lit(LLVal::F32(l)), OpVal::Lit(r)) => {
        e_val.val = IntVal::Static((l >= r.to_f32()) as i64);
        Lit(LLVal::Int(e_val))
      }
      (OpVal::Lit(LLVal::F64(l)), OpVal::Lit(r)) => {
        e_val.val = IntVal::Static((l >= r.to_f64()) as i64);
        Lit(LLVal::Int(e_val))
      }
      (OpVal::Lit(LLVal::Int(l)), OpVal::Lit(r)) => {
        let r = r.to_int(l.bits);
        e_val.val = IntVal::Static((l.val >= r.val) as i64);
        Lit(LLVal::Int(e_val))
      }
      val => unreachable!("{val:?}"),
    }
  };

  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_sub(
  sub: &compiler::parser::Sub<Token>,

  exe_block: &mut ExeBlock<()>,
  mut expected_val: LLVal,
) -> RumResult<OpVal<()>> {
  let left = process_arithmetic_expression(&sub.left, exe_block, expected_val)?;

  let right = convert_val(
    process_arithmetic_expression(&sub.right, exe_block, expected_val)?,
    left.ll_val(),
    exe_block,
  );

  process_output_value(&mut expected_val, exe_block);

  if left.is_ssa() || right.is_ssa() {
    Ok(exe_block.push_binary_op(Op::SUB, expected_val, left, right))
  } else {
    match (left, right) {
      (
        OpVal::Lit(LLVal::Int(IntData { val: IntVal::Static(left), .. })),
        OpVal::Lit(LLVal::Int(IntData { val: IntVal::Static(right), .. })),
      ) => {}
      _ => {}
    }

    Err(compiler::interpreter::error::RumScriptError::StaticText("todo"))
  }
}

fn process_output_value(expected_val: &mut LLVal, exe_block: &mut ExeBlock<()>) {
  match expected_val {
    LLVal::Int(data @ IntData { val: IntVal::Undefined, .. }) => {
      data.val = IntVal::SSA(exe_block.get_current_ssa_id())
    }
    _ => {}
  }
}

fn handle_le<'a>(
  val: &compiler::parser::LE<Token>,
  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle LE Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_ls<'a>(
  val: &compiler::parser::LS<Token>,

  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle LS Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_gr<'a>(
  val: &compiler::parser::GR<Token>,
  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle GR Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_eq<'a>(
  val: &compiler::parser::EQ<Token>,

  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle EQ Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_ne<'a>(
  val: &compiler::parser::NE<Token>,

  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle NE Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_not<'a>(
  val: &compiler::parser::NOT<Token>,
  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle NOT Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_and<'a>(
  val: &compiler::parser::AND<Token>,

  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle AND Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_xor<'a>(
  val: &compiler::parser::XOR<Token>,

  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle AND Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn handle_or<'a>(
  val: &compiler::parser::OR<Token>,

  exe_block: &'a mut ExeBlock<()>,
) -> RumResult<LogicalExprType<'a>> {
  todo_note!("Handle OR Expression");
  Ok(LogicalExprType::Boolean(exe_block))
}

fn ty_to_ll_value(val: &type_Value) -> RumResult<LLVal> {
  use BitSize::*;
  use LLVal::*;
  let val = match val {
    type_Value::Type_u64(..) => {
      Int(IntData { val: IntVal::Undefined, bits: b64, signed: false })
    }
    type_Value::Type_u32(..) => {
      Int(IntData { val: IntVal::Undefined, bits: b32, signed: false })
    }
    type_Value::Type_u16(..) => {
      Int(IntData { val: IntVal::Undefined, bits: b16, signed: false })
    }
    type_Value::Type_u8(..) => {
      Int(IntData { val: IntVal::Undefined, bits: b8, signed: false })
    }
    type_Value::Type_i64(..) => {
      Int(IntData { val: IntVal::Undefined, bits: b64, signed: true })
    }
    type_Value::Type_i32(..) => {
      Int(IntData { val: IntVal::Undefined, bits: b32, signed: true })
    }
    type_Value::Type_i16(..) => {
      Int(IntData { val: IntVal::Undefined, bits: b16, signed: true })
    }
    type_Value::Type_i8(..) => Int(IntData { val: IntVal::Undefined, bits: b8, signed: true }),
    type_Value::Type_f32(..) => F32(0.0),
    type_Value::Type_f64(..) => F64(0.0),
    type_Value::Type_8BitPointer(..) => PtrBits(b8),
    type_Value::Type_16BitPointer(..) => PtrBits(b16),
    type_Value::Type_32BitPointer(..) => PtrBits(b32),
    type_Value::Type_64BitPointer(..) => PtrBits(b64),
    type_Value::Type_128BitPointer(..) => PtrBits(b128),
    _ => LLVal::Und,
  };

  Ok(val)
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum OpVal<R: Debug> {
  /// A static value that is fully defined; can be used to to perform compiler
  /// operations
  Lit(LLVal),
  SSA(usize, LLVal),
  REF(PtrData),
  BLOCK(usize),
  REG(R, LLVal),
}

impl<R: Debug> Debug for OpVal<R> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      OpVal::Lit(val) => f.write_fmt(format_args!("{:?}", val)),
      OpVal::REF(lit) => f.write_fmt(format_args!("&({:?})", lit)),
      OpVal::SSA(id, val) => f.write_fmt(format_args!("${id}({val:?})")),
      OpVal::REG(id, val) => f.write_fmt(format_args!("{id:?}({val:?})")),
      OpVal::BLOCK(val) => f.write_fmt(format_args!("BLOCK({val})")),
    }
  }
}

impl<R: Debug> OpVal<R> {
  pub fn is_ssa(&self) -> bool {
    matches!(self, OpVal::SSA(..))
  }

  pub fn undefined(&self) -> bool {
    matches!(self, OpVal::Lit(LLVal::Und))
  }

  pub fn is_reg(&self) -> bool {
    matches!(self, OpVal::REG(..))
  }

  pub fn ll_val(&self) -> LLVal {
    match *self {
      Self::Lit(l) => l,
      Self::SSA(_, l) => l,
      Self::REG(_, l) => l,
      Self::REF(ptr) => LLVal::Ptr(ptr),
      Self::BLOCK(_) => LLVal::Und,
    }
  }
}

#[derive(Clone, Copy)]
pub enum OpExpr<R: Debug> {
  NullOp(Op, OpVal<R>),
  UnaryOp(Op, OpVal<R>, OpVal<R>),
  BinaryOp(Op, OpVal<R>, OpVal<R>, OpVal<R>),
}

impl<R: Debug> OpExpr<R> {
  pub fn name(&self) -> Op {
    match self {
      OpExpr::BinaryOp(op, ..) | OpExpr::UnaryOp(op, ..) | OpExpr::NullOp(op, ..) => *op,
    }
  }
}

impl<R: Debug> Debug for OpExpr<R> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      OpExpr::BinaryOp(op, c, a, b) => f.write_fmt(format_args!("{c: >16?} = {op:?} {a:?} {b:?}")),
      OpExpr::UnaryOp(op, c, a) => f.write_fmt(format_args!("{c: >16?} = {op:?} {a:?}")),
      OpExpr::NullOp(op, c) => f.write_fmt(format_args!("{c: >16?} = {op:?}")),
    }
  }
}

#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy)]
pub enum Op {
  ADD,
  SUB,
  MUL,
  DIV,
  LOG,
  POW,
  GR,
  LE,
  GE,
  LS,
  OR,
  XOR,
  AND,
  NOT,
  LOAD,
  STORE,
  CALL,
  CONVERT,
  /// Allocate heap memory and return pointer.
  ALLOC,
  RETURN,
  CALL_BLOCK,
  EXIT_BLOCK,
  JUMP,
  JUMP_ZE,
  JUMP_NZ,
  JUMP_EQ,
}

struct PtrRef(PtrData, LLVal, Token);

#[derive(Debug)]
pub struct LL_SSA_function<R: Debug + Default + Copy> {
  pub(crate) blocks: Vec<Box<ExeBlock<R>>>,
}

#[derive(Debug)]
pub struct LL_context<R: Debug> {
  name:         BTreeMap<IString, (PtrData, LLVal, Token)>,
  blocks:       Vec<*mut ExeBlock<R>>,
  ssa_index:    isize,
  stack_offset: isize,
  block_top:    usize,
}

impl<R: Debug> Default for LL_context<R> {
  fn default() -> Self {
    Self {
      name:         Default::default(),
      blocks:       Default::default(),
      ssa_index:    -1,
      stack_offset: -1,
      block_top:    0,
    }
  }
}

impl<R: Debug + Default + Copy> LL_context<R> {
  pub fn create_ssa_id(&mut self, val: LLVal) -> OpVal<R> {
    OpVal::SSA(self.get_ssa_id(), val)
  }

  pub fn push_block<'a>(&mut self, predecessor: Option<usize>) -> &'a mut ExeBlock<R> {
    self.block_top = self.blocks.len();

    let mut block = Box::new(ExeBlock::default());

    block.id = self.block_top as usize;
    block.ctx = self;

    if let Some(predecessor) = predecessor {
      block.scope_parent = Some(self.blocks[predecessor])
    }

    self.blocks.push(Box::into_raw(block));

    unsafe { &mut *self.blocks[self.block_top] }
  }

  pub fn get_current_ssa_id(&self) -> usize {
    self.ssa_index as usize
  }

  fn get_ssa_id(&mut self) -> usize {
    let ssa = &mut self.ssa_index;
    (*ssa) += 1;
    (*ssa) as usize
  }

  pub fn get_stack_offset(&mut self) -> usize {
    let so = &mut self.stack_offset;
    (*so) += 1;
    (*so) as usize
  }

  pub fn next_block_id(&self) -> usize {
    (self.block_top + 1) as usize
  }

  pub fn get_block_mut(&mut self, block_id: usize) -> Option<&mut ExeBlock<R>> {
    self.blocks.get_mut(block_id).map(|b| unsafe { &mut **b })
  }

  pub fn get_head_block(&mut self) -> &mut ExeBlock<R> {
    self.get_block_mut(self.block_top).unwrap()
  }
}

#[derive(Clone)]
pub struct ExeBlock<R: Debug> {
  pub id:                   usize,
  pub scope_parent:         Option<*mut ExeBlock<R>>,
  pub ctx:                  *mut LL_context<R>,
  pub predecessors:         BTreeSet<usize>,
  pub ops:                  Vec<OpExpr<R>>,
  pub decls:                BTreeMap<IString, (PtrData, LLVal, Token)>,
  pub outputs:              BTreeMap<IString, LLVal>,
  pub return_val:           Option<OpVal<R>>,
  pub branch_unconditional: Option<usize>,
  pub branch_succeed:       Option<usize>,
  pub branch_fail:          Option<usize>,
}

impl<R: Debug + Default + Copy> Debug for ExeBlock<R> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut s = f.debug_struct("Exeblock");
    s.field("id", &self.id);
    s.field("scope_parent", &self.scope_parent);
    s.field("predecessors", &self.predecessors);
    s.field("ops", &self.ops);
    s.field("decls", &self.decls);
    s.field("outputs", &self.outputs);
    s.field("return_val", &self.return_val);
    s.field("branch_unconditional", &self.branch_unconditional);
    s.field("branch_succeed", &self.branch_succeed);
    s.field("branch_fail", &self.branch_fail);
    s.finish()
  }
}

impl<R: Debug + Default + Copy> Default for ExeBlock<R> {
  fn default() -> Self {
    Self {
      id:                   Default::default(),
      scope_parent:         Default::default(),
      ctx:                  std::ptr::null_mut(),
      predecessors:         Default::default(),
      ops:                  Default::default(),
      decls:                Default::default(),
      outputs:              Default::default(),
      return_val:           Default::default(),
      branch_succeed:       Default::default(),
      branch_unconditional: Default::default(),
      branch_fail:          Default::default(),
    }
  }
}

impl<R: Debug + Default + Copy> ExeBlock<R> {
  pub fn push_binary_op(
    &mut self,
    op: Op,
    out_val: LLVal,
    left: OpVal<R>,
    right: OpVal<R>,
  ) -> OpVal<R> {
    let out_val = self.ctx().create_ssa_id(out_val);
    self.ops.push(OpExpr::BinaryOp(op, out_val, left, right));
    out_val
  }

  pub fn push_unary_op(&mut self, op: Op, out_val: LLVal, val: OpVal<R>) -> OpVal<R> {
    let out_val = self.ctx().create_ssa_id(out_val);
    self.ops.push(OpExpr::UnaryOp(op, out_val, val));
    out_val
  }

  pub fn push_null_op(&mut self, op: Op, out_val: LLVal) -> OpVal<R> {
    let out_val = self.ctx().create_ssa_id(out_val);
    self.ops.push(OpExpr::NullOp(op, out_val));
    out_val
  }

  fn ctx(&self) -> &mut LL_context<R> {
    unsafe { &mut *self.ctx }
  }

  pub(super) fn create_ssa_id(&self, val: LLVal) -> OpVal<R> {
    if self.ctx.is_null() {
      OpVal::SSA(usize::MAX, val)
    } else {
      self.ctx().create_ssa_id(val)
    }
  }

  pub(super) fn get_current_ssa_id(&self) -> usize {
    if self.ctx.is_null() {
      usize::MAX
    } else {
      self.ctx().get_current_ssa_id()
    }
  }

  pub fn get_id(&mut self, id: IString) -> Option<&(PtrData, LLVal, Token)> {
    if let Some(decl) = self.decls.get(&id) {
      Some(decl)
    } else if let Some(par) = self.scope_parent {
      unsafe { par.as_mut().unwrap().get_id(id) }
    } else {
      None
    }
  }

  pub fn get_id_mut(&mut self, id: IString) -> Option<&mut (PtrData, LLVal, Token)> {
    if let Some(decl) = self.decls.get_mut(&id) {
      Some(decl)
    } else if let Some(par) = self.scope_parent {
      unsafe { par.as_mut().unwrap().get_id_mut(id) }
    } else {
      None
    }
  }

  pub fn get_stack_offset(&mut self, increment: usize) -> usize {
    0
  }

  fn create_successor<'a>(&self) -> &'a mut ExeBlock<R> {
    let id = self.ctx().push_block(Some(self.id)).id;
    unsafe { &mut *self.ctx().blocks[id] }
  }
}
