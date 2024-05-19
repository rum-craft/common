use super::types::*;
use crate::compiler::interpreter::ll::{
  ssa_block_compiler::{from_flt, from_int, from_uint},
  types::{BitSize, LLType, LLVal, OpArg, SSABlock, SSAExpr, SSAFunction, SSAOp},
  x86::{encoder::*, push_bytes},
};
use rum_container::get_aligned_value;
use rum_logger::todo_note;
use std::collections::HashMap;

const PAGE_SIZE: usize = 4096;

struct Register {
  index: usize,
  val:   Option<LLVal>,
}

impl Register {
  pub fn name(&self) -> x86Reg {
    const NAMES: [x86Reg; 10] = [
      x86Reg::RAX,
      x86Reg::RCX,
      x86Reg::RDX,
      x86Reg::RBX,
      x86Reg::R8,
      x86Reg::R9,
      x86Reg::R10,
      x86Reg::R11,
      //x86Reg::R12,
      //x86Reg::R13,
      x86Reg::R14,
      x86Reg::R15,
    ];

    NAMES[self.index]
  }
}

#[derive(Debug)]
struct JumpResolution {
  /// The binary offset the first instruction of each block.
  block_offset: Vec<usize>,
  /// The binary offset and block id target of jump instructions.
  jump_points:  Vec<(usize, usize)>,
}

impl JumpResolution {
  fn add_jump(&mut self, binary: &mut Vec<u8>, block_id: usize) {
    self.jump_points.push((binary.len(), block_id));
  }
}

struct RegisterAllocator {
  registers:  Vec<Register>,
  allocation: HashMap<LLVal, usize>,
}

impl RegisterAllocator {
  pub fn modify_register(&mut self, from: &OpArg<x86Reg>, to: &OpArg<()>) -> OpArg<x86Reg> {
    match from {
      OpArg::REG(register_name, old_val) => {
        let val = to.ll_val();

        if let Some((index, _)) =
          self.registers.iter().enumerate().find(|i| i.1.name() == *register_name)
        {
          self.allocation.insert(val, index);
          self.allocation.remove(old_val);
          OpArg::REG(*register_name, val)
        } else {
          *from
        }
      }
      op => *op,
    }
  }

  pub fn set(&mut self, size: BitSize, op: LLVal) -> x86Reg {
    if let Some(index) = self.allocation.get(&op) {
      return self.registers[*index].name();
    }

    for register in &mut self.registers {
      if let None = &register.val {
        register.val = Some(op);
        self.allocation.insert(op, register.index);
        return register.name();
      }
    }

    // Evict the youngest register first
    for register in &mut self.registers {
      todo_note!("Handle register eviction: {:?}", register.name());

      let op = register.val.unwrap();

      self.allocation.remove(&op);

      register.val = Some(op);

      self.allocation.insert(op, register.index);

      return register.name();
    }

    // Resolve jumps

    panic!("Could not acquire register")
  }
}

pub fn compile_from_ssa_fn(funct: &SSAFunction<()>) {
  const MALLOC: unsafe extern "C" fn(usize) -> *mut libc::c_void = libc::malloc;
  const FREE: unsafe extern "C" fn(*mut libc::c_void) = libc::free;

  let mut binary = Vec::<u8>::with_capacity(PAGE_SIZE);
  // store pointers to free and malloc at base binaries

  let mut offset = 0;
  push_bytes(&mut binary, MALLOC);
  push_bytes(&mut binary, FREE);

  // Move stack by needed bytes to allocate memory for our stack elements
  // and local pointer references

  let mut register = RegisterAllocator {
    allocation: Default::default(),
    registers:  [
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
      Register { index: 0, val: None },
    ]
    .into_iter()
    .enumerate()
    .map(|(i, mut r)| {
      r.index = i;
      r
    })
    .collect(),
  };

  dbg!(funct);

  let mut jmp_resolver =
    JumpResolution { block_offset: Default::default(), jump_points: Default::default() };

  // Create area on the stack for local declarations

  let mut total_area = 0;

  let mut offsets = Vec::with_capacity(funct.declarations);
  offsets.resize_with(funct.declarations, || 0);

  for block in &funct.blocks {
    for decl in &block.decls {
      let ty = decl.ty;
      if let Some(byte_size) = ty.info.total_byte_size() {
        if let Some(id) = ty.info.stack_id() {
          total_area = get_aligned_value(total_area, ty.info.alignment() as u64);
          offsets.insert(id, total_area as usize);
          total_area += byte_size as u64;
        }
      }
    }
  }

  for block in &funct.blocks {
    jmp_resolver.block_offset.push(binary.len());

    println!("START_BLOCK {} ---------------- \n", block.id);
    for op_expr in &block.ops {
      let new_op = match op_expr {
        SSAExpr::BinaryOp(op, out, left, right) => {
          let right = convert_ssa_to_reg(right, &mut register);
          let left = convert_ssa_to_reg(left, &mut register);

          match op {
            SSAOp::ADD | SSAOp::MUL => {
              if left.is_reg() && !out.undefined() {
                let out = register.modify_register(&left, out);
                SSAExpr::BinaryOp(*op, out, left, right)
              } else if right.is_reg() && !out.undefined() {
                let out = register.modify_register(&right, out);
                SSAExpr::BinaryOp(*op, out, right, left)
              } else {
                panic!("Invalid operands for {op:?} op  - l:{left:?} r:{right:?} ")
              }
            }
            SSAOp::SUB | SSAOp::DIV => {
              if left.is_reg() && !out.undefined() {
                let out = register.modify_register(&left, out);
                SSAExpr::BinaryOp(*op, out, left, right)
              } else {
                panic!("Invalid operands for {op:?} op  - l:{left:?} r:{right:?} ")
              }
            }
            SSAOp::GE | SSAOp::LE | SSAOp::LS | SSAOp::GR | SSAOp::EQ | SSAOp::NE => {
              // The outgoing operand is not used.
              SSAExpr::BinaryOp(*op, OpArg::Undefined, left, right)
            }
            _ => {
              let out = convert_ssa_to_reg(out, &mut register);
              SSAExpr::BinaryOp(*op, out, left, right)
            }
          }
        }
        SSAExpr::UnaryOp(op, out, left) => match op {
          SSAOp::CONVERT => {
            let left = convert_ssa_to_reg(left, &mut register);
            let out = register.modify_register(&left, out);
            SSAExpr::UnaryOp(*op, out, left)
          }
          SSAOp::LOAD => {
            let left = convert_ssa_to_reg(left, &mut register);
            let mut out = convert_ssa_to_reg(out, &mut register);
            SSAExpr::UnaryOp(*op, out, left)
          }
          _ => {
            let left = convert_ssa_to_reg(left, &mut register);
            let out = convert_ssa_to_reg(out, &mut register);
            SSAExpr::UnaryOp(*op, out, left)
          }
        },

        SSAExpr::NullOp(op, out) => {
          let out = convert_ssa_to_reg(out, &mut register);
          SSAExpr::NullOp(*op, out)
        }

        SSAExpr::Debug(tok) => SSAExpr::Debug(tok.clone()),
      };

      match &new_op {
        dbg @ SSAExpr::Debug(_) => {
          println!("########\n\n  {dbg:?}")
        }
        new_op => {
          println!("## {:<80} {:} \n", format!("{:?}", new_op), format!("{:?}", op_expr));
        }
      }

      let old_offset = binary.len();
      compile_op(&new_op, &block, &mut binary, &mut jmp_resolver, &offsets);
      offset = print_instructions(&binary[old_offset..], offset);
      println!("\n")
    }

    if let Some(return_value) = &block.return_val {
      println!("RETURN {:?} \n\n", convert_ssa_to_reg(return_value, &mut register))
    }
  }

  for (instruction_index, block_id) in &jmp_resolver.jump_points {
    let block_address = jmp_resolver.block_offset[*block_id];
    let instruction_end_point = *instruction_index;
    let relative_offset = block_address as i32 - instruction_end_point as i32;
    let ptr = binary[instruction_end_point - 4..].as_mut_ptr();
    unsafe { ptr.copy_from(&(relative_offset) as *const _ as *const u8, 4) }
  }

  dbg!(jmp_resolver);

  offset = print_instructions(&binary[16..], offset);

  todo!("Compile function")
}

impl OpArg<x86Reg> {
  pub fn to_reg_arg(&self) -> Arg {
    use Arg::*;
    match self {
      Self::Lit(literal) => match literal.info.ty() {
        LLType::Float => Imm_Int(from_flt(*literal) as u64),
        LLType::Integer => Imm_Int(from_int(*literal) as u64),
        LLType::Unsigned => Imm_Int(from_uint(*literal) as u64),
        _ => unreachable!(),
      },
      Self::REG(reg, l_val) => Reg(*reg),
      _ => unreachable!(),
    }
  }

  pub fn to_mem_arg(&self) -> Arg {
    use Arg::*;
    match self {
      Self::Lit(literal) => match literal.info.ty() {
        LLType::Float => Imm_Int(from_flt(*literal) as u64),
        LLType::Integer => Imm_Int(from_int(*literal) as u64),
        LLType::Unsigned => Imm_Int(from_uint(*literal) as u64),
        _ => unreachable!(),
      },
      Self::REG(reg, l_val) => match l_val {
        _ => Reg(*reg),
      },
      _ => unreachable!(),
    }
  }
}

pub fn compile_op(
  op_expr: &SSAExpr<x86Reg>,
  block: &SSABlock<()>,
  bin: &mut Vec<u8>,
  jmp_resolver: &mut JumpResolution,
  so: &[usize],
) {
  use Arg::*;
  use BitSize::*;
  match op_expr.name() {
    SSAOp::ADD => {
      if let SSAExpr::BinaryOp(op, val, op1, op2) = op_expr {
        let bit_size = op1.ll_val().info.into();
        encode(bin, &add, bit_size, op1.arg(so), op2.arg(so), None);
      } else {
        panic!()
      }
    }
    SSAOp::SUB => {
      if let SSAExpr::BinaryOp(op, val, op1, op2) = op_expr {
        let bit_size = op1.ll_val().info.into();
        encode(bin, &sub, bit_size, op1.arg(so), op2.arg(so), None);
      } else {
        panic!()
      }
    }
    SSAOp::MUL => todo!("TODO: {op_expr:?}"),
    SSAOp::DIV => todo!("TODO: {op_expr:?}"),
    SSAOp::LOG => todo!("TODO: {op_expr:?}"),
    SSAOp::POW => todo!("TODO: {op_expr:?}"),
    SSAOp::GR => todo!("SSAOp::GR"),
    SSAOp::LS => todo!("SSAOp::LS"),
    SSAOp::LE => {
      if let SSAExpr::BinaryOp(_, _, op1, op2) = op_expr {
        let bit_size = op1.ll_val().info.into();
        if let (Some(pass), Some(fail)) = (block.branch_succeed, block.branch_fail) {
          encode(bin, &cmp, bit_size, op1.arg(so), op2.arg(so), None);
          if pass == block.id + 1 {
            encode(bin, &jg, b32, Imm_Int(fail as u64), None, None);
            jmp_resolver.add_jump(bin, fail);
            println!("JL BLOCK({fail})");
          } else if fail == block.id + 1 {
            encode(bin, &jle, b32, Imm_Int(pass as u64), None, None);
            jmp_resolver.add_jump(bin, pass);
            println!("JGE BLOCK({pass})");
          } else {
            encode(bin, &jle, b32, Imm_Int(pass as u64), None, None);
            jmp_resolver.add_jump(bin, pass);
            encode(bin, &jmp, b32, Imm_Int(fail as u64), None, None);
            jmp_resolver.add_jump(bin, fail);
            println!("JGE BLOCK({pass})");
            println!("JMP BLOCK({fail})");
          }
        }
      } else {
        panic!()
      }
    }
    SSAOp::GE => {
      if let SSAExpr::BinaryOp(_, _, op1, op2) = op_expr {
        let bit_size = op1.ll_val().info.into();
        if let (Some(pass), Some(fail)) = (block.branch_succeed, block.branch_fail) {
          encode(bin, &cmp, bit_size, op1.arg(so), op2.arg(so), None);
          if pass == block.id + 1 {
            encode(bin, &jl, b32, Imm_Int(fail as u64), None, None);
            jmp_resolver.add_jump(bin, fail);
            println!("JL BLOCK({fail})");
          } else if fail == block.id + 1 {
            encode(bin, &jge, b32, Imm_Int(pass as u64), None, None);
            jmp_resolver.add_jump(bin, pass);
            println!("JGE BLOCK({pass})");
          } else {
            encode(bin, &jge, b32, Imm_Int(pass as u64), None, None);
            jmp_resolver.add_jump(bin, pass);
            encode(bin, &jmp, b32, Imm_Int(fail as u64), None, None);
            jmp_resolver.add_jump(bin, fail);
            println!("JGE BLOCK({pass})");
            println!("JMP BLOCK({fail})");
          }
        }
      } else {
        panic!()
      }
    }
    SSAOp::OR => todo!("SSAOp::OR"),
    SSAOp::XOR => todo!("SSAOp::XOR"),
    SSAOp::AND => todo!("SSAOp::AND"),
    SSAOp::NOT => todo!("SSAOp::NOT"),
    SSAOp::CALL => todo!("SSAOp::CALL"),
    SSAOp::CONVERT => {
      todo_note!("TODO: {op_expr:?}");
    }
    SSAOp::CALL_BLOCK => todo!("TODO: {op_expr:?}"),
    SSAOp::EXIT_BLOCK => todo!("TODO: {op_expr:?}"),
    SSAOp::JUMP => {
      if let SSAExpr::UnaryOp(..) = op_expr {
        // Requires RAX to be set to int_val;
        if let Some(target_id) = block.branch_unconditional {
          encode(bin, &jmp, b32, Imm_Int(target_id as u64), None, None);
          jmp_resolver.add_jump(bin, target_id);
        }
      } else {
        panic!()
      }
    }
    SSAOp::JUMP_ZE => todo!("TODO: {op_expr:?}"),
    SSAOp::NE => todo!("TODO: {op_expr:?}"),
    SSAOp::EQ => todo!("TODO: {op_expr:?}"),
    SSAOp::LOAD => {
      if let SSAExpr::UnaryOp(op, val, op1) = op_expr {
        debug_assert!(op1.ll_val().info.stack_id().is_some());
        let bit_size = op1.ll_val().info.deref().into();
        if op1.ll_val().info.is_ptr() {
          encode(bin, &mov, bit_size, val.arg(so), op1.arg(so).to_mem(), None);
        } else {
          let stack_id =
            op1.ll_val().info.stack_id().expect("Loads should have an associated stack id");

          let offset = so[stack_id] as isize;

          encode(bin, &mov, bit_size, val.arg(so), Mem(x86Reg::RSP_REL(offset as u64)), None);
        }
      } else {
        panic!()
      }
    }
    SSAOp::STORE => {
      if let SSAExpr::BinaryOp(op, val, op1, op2) = op_expr {
        debug_assert!(op1.ll_val().info.stack_id().is_some());
        let bit_size = op1.ll_val().info.deref().into();
        if op1.ll_val().info.is_ptr() {
          encode(bin, &mov, bit_size, op1.arg(so).to_mem(), op2.arg(so), None);
        } else {
          let stack_id =
            op1.ll_val().info.stack_id().expect("Loads should have an associated stack id");

          let offset = (so[stack_id] as isize);

          encode(bin, &mov, bit_size, Mem(x86Reg::RSP_REL(offset as u64)), op2.arg(so), None);
        }
      } else {
        panic!()
      }
    }
    SSAOp::ALLOC => {
      if let SSAExpr::BinaryOp(op, val, op1, op2) = op_expr {
        debug_assert!(op1.ll_val().info.is_ptr());

        match op1.ll_val().info.location() {
          crate::compiler::interpreter::ll::types::DataLocation::Heap => {
            // todo: Preserve and restore RAX & RDI if it they have been allocated. Ideally,
            // RAX and RDI are reserved for duties such as calls, and other
            // registers are used for more general operations.

            // Also preserve active caller registers

            // Location of the allocate function address.

            encode(bin, &mov, b64, Reg(x86Reg::RDI), op2.arg(so), None);
            encode(bin, &call, b64, Mem(x86Reg::RIP_REL(0)), None, None).displace_too(0);
            encode(bin, &mov, b64, op1.arg(so).to_mem(), Reg(x86Reg::RAX), None);

            todo_note!("Handle errors if pointer is 0");
          }
          _ => {}
        }
      } else {
        panic!()
      }
    }

    SSAOp::RETURN => {
      encode(bin, &ret, b64, None, None, None);
    }
    SSAOp::NOOP => {}
  }
}

fn convert_ssa_to_reg(op: &OpArg<()>, register: &mut RegisterAllocator) -> OpArg<x86Reg> {
  match *op {
    OpArg::SSA(index, val) => {
      if val.info.is_undefined() {
        return OpArg::SSA(index, val);
      }

      OpArg::REG(register.set(val.info.into(), val), val)
    }
    OpArg::STACK(i, reference) => OpArg::STACK(i, reference),
    OpArg::BLOCK(block) => OpArg::BLOCK(block),
    OpArg::Lit(literal) => OpArg::Lit(literal),
    OpArg::Undefined => OpArg::Undefined,
    OpArg::REG(..) => unreachable!(),
  }
}

fn print_instructions(binary: &[u8], mut offset: u64) -> u64 {
  use iced_x86::{Decoder, DecoderOptions, Formatter, MasmFormatter};

  let mut decoder = Decoder::with_ip(64, &binary, offset, DecoderOptions::NONE);
  let mut formatter = MasmFormatter::new();

  formatter.options_mut().set_digit_separator("_");
  formatter.options_mut().set_number_base(iced_x86::NumberBase::Decimal);
  formatter.options_mut().set_add_leading_zero_to_hex_numbers(true);
  formatter.options_mut().set_first_operand_char_index(2);
  formatter.options_mut().set_always_show_scale(true);
  formatter.options_mut().set_rip_relative_addresses(true);

  for instruction in decoder {
    let mut output = String::default();
    formatter.format(&instruction, &mut output);
    print!("{:016} ", instruction.ip());
    println!(" {}", output);

    offset = instruction.ip() + instruction.len() as u64
  }

  offset
}
