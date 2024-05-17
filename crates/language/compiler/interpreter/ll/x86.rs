use std::{
  collections::{BTreeMap, HashMap},
  ops::Range,
};

use rum_logger::todo_note;

use crate::compiler::interpreter::ll::{
  interpreter::{IntData, IntVal, LLVal, PtrData, PtrType},
  jit::{OpExpr, OpVal},
};

use super::{
  interpreter::BitSize,
  jit::{ExeBlock, LL_SSA_function, Op},
};

const PAGE_SIZE: usize = 4096;

struct Register {
  index: usize,
  val:   Option<LLVal>,
}

/// Operations that a register can perform.
enum RegOperations {
  MemPtr  = 0b1,
  Integer = 0b10,
  FLoat   = 0b100,
  b8      = 0b1000,
  b16     = 0b10000,
  b32     = 0b100000,
  b64     = 0b1000000,
  b128    = 0b10000000,
  b256    = 0b100000000,
  b512    = 0b1000000000,
}

impl Register {
  pub fn name(&self) -> GeneralRegisterName {
    const NAMES: [GeneralRegisterName; 10] = [
      GeneralRegisterName::RAX,
      GeneralRegisterName::RCX,
      GeneralRegisterName::RDX,
      GeneralRegisterName::RBX,
      GeneralRegisterName::R8,
      GeneralRegisterName::R9,
      GeneralRegisterName::R10,
      GeneralRegisterName::R11,
      //GeneralRegisterName::R12,
      //GeneralRegisterName::R13,
      GeneralRegisterName::R14,
      GeneralRegisterName::R15,
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
  pub fn modify_register(
    &mut self,
    from: &OpVal<GeneralRegisterName>,
    to: &OpVal<()>,
  ) -> OpVal<GeneralRegisterName> {
    match from {
      OpVal::REG(register_name, old_val) => {
        let val = to.ll_val();

        if let Some((index, _)) =
          self.registers.iter().enumerate().find(|i| i.1.name() == *register_name)
        {
          self.allocation.insert(val, index);
          self.allocation.remove(old_val);
          OpVal::REG(*register_name, val)
        } else {
          *from
        }
      }
      op => *op,
    }
  }

  pub fn set(&mut self, size: BitSize, op: LLVal) -> GeneralRegisterName {
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

pub fn compile_from_ssa_fn(funct: &LL_SSA_function<()>) {
  const MALLOC: unsafe extern "C" fn(usize) -> *mut libc::c_void = libc::malloc;
  const FREE: unsafe extern "C" fn(*mut libc::c_void) = libc::free;

  let mut binary = Vec::<u8>::with_capacity(PAGE_SIZE);
  // store pointers to free and malloc at base binaries

  let mut offset = 0;
  push_bytes(&mut binary, MALLOC);
  push_bytes(&mut binary, FREE);

  debug_assert!(!funct.blocks.is_empty());

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

  offset = print_instructions(&binary[0..], offset);
  dbg!(funct);

  let mut jmp_resolver =
    JumpResolution { block_offset: Default::default(), jump_points: Default::default() };

  for block in &funct.blocks {
    jmp_resolver.block_offset.push(binary.len());

    println!("START_BLOCK {} ---------------- \n", block.id);
    for op in &block.ops {
      let new_op = match op {
        OpExpr::BinaryOp(op, out, left, right) => {
          let right = convert_ssa_to_reg(right, &mut register);
          let left = convert_ssa_to_reg(left, &mut register);

          match op {
            Op::ADD => {
              if left.is_reg() && !out.undefined() {
                let out = register.modify_register(&left, out);
                OpExpr::BinaryOp(*op, out, left, right)
              } else if right.is_reg() && !out.undefined() {
                let out = register.modify_register(&right, out);
                OpExpr::BinaryOp(*op, out, right, left)
              } else {
                panic!("Invalid operands for {op:?} op  - l:{left:?} r:{right:?} ")
              }
            }
            Op::GE => {
              // The outgoing operand is not used.
              OpExpr::BinaryOp(*op, OpVal::Lit(LLVal::Und), left, right)
            }
            _ => {
              let out = convert_ssa_to_reg(out, &mut register);
              OpExpr::BinaryOp(*op, out, left, right)
            }
          }
        }
        OpExpr::UnaryOp(op, out, left) => {
          let left = convert_ssa_to_reg(left, &mut register);
          let out = convert_ssa_to_reg(out, &mut register);
          OpExpr::UnaryOp(*op, out, left)
        }

        OpExpr::NullOp(op, out) => {
          let out = convert_ssa_to_reg(out, &mut register);
          OpExpr::NullOp(*op, out)
        }
      };

      println!("## {:<80} {:} \n", format!("{:?}", new_op), format!("{:?}", op));

      let old_offset = binary.len();
      compile_op(&new_op, &block, &mut binary, &mut jmp_resolver);
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
    let relative_offset = (block_address as i32 - instruction_end_point as i32);
    dbg!((instruction_index, block_id, relative_offset));
    let ptr = binary[instruction_end_point - 4..].as_mut_ptr();
    unsafe { ptr.copy_from(&(relative_offset) as *const _ as *const u8, 4) }
  }

  dbg!(jmp_resolver);

  offset = print_instructions(&binary[16..], offset);

  todo!("Compile function")
}

impl OpVal<GeneralRegisterName> {
  pub fn to_reg_arg(&self) -> Arg {
    use Arg::*;
    match self {
      Self::Lit(literal) => match literal {
        LLVal::Int(IntData { val: IntVal::Static(val), bits, signed }) => Imm(*val as u64),
        _ => unreachable!(),
      },
      Self::REG(reg, l_val) => Reg(*reg),
      _ => unreachable!(),
    }
  }

  pub fn to_mem_arg(&self) -> Arg {
    use Arg::*;
    match self {
      Self::Lit(literal) => match literal {
        LLVal::Int(IntData { val: IntVal::Static(val), bits, signed }) => Imm(*val as u64),
        _ => unreachable!(),
      },
      Self::REG(reg, l_val) => match l_val {
        LLVal::Ptr(..) => Mem(*reg),
        _ => Reg(*reg),
      },
      _ => unreachable!(),
    }
  }
}

#[inline]
/// Pushes an arbitrary number of bytes to into a binary buffer.
fn push_bytes<T: Sized>(mut binary: &mut Vec<u8>, data: T) {
  let byte_size = std::mem::size_of::<T>();
  let data_as_bytes = &data as *const _ as *const u8;
  binary.extend(unsafe { std::slice::from_raw_parts(data_as_bytes, byte_size) });
}

pub fn compile_op(
  op: &OpExpr<GeneralRegisterName>,
  block: &ExeBlock<()>,
  binary: &mut Vec<u8>,
  jmp_resolver: &mut JumpResolution,
) {
  use Arg::*;
  use BitSize::*;
  use GeneralRegisterName as GR;
  match op.name() {
    Op::ADD => {
      if let OpExpr::BinaryOp(_, dest, left_val, right_val) = op {
        // Requires RAX to be set to int_val;
        if dest.ll_val() != left_val.ll_val() {
          println!("need to convert, {left_val:?} to {dest:?}")
        }

        add(binary, left_val.ll_val().bit_size(), right_val.to_reg_arg(), left_val.to_reg_arg());
        println!("ADD {dest:?}, {right_val:?}");
        println!("")
      }
    }
    Op::SUB => {
      if let OpExpr::BinaryOp(_, dest, left_val, right_val) = op {
        // Requires RAX to be set to int_val;
        if dest.ll_val() != left_val.ll_val() {
          println!("need to convert, {left_val:?} to {dest:?}")
        }
        println!("SUB {dest:?}, {right_val:?}");
        println!("")
      }
    }
    Op::MUL => {
      if let OpExpr::BinaryOp(_, dest, left_val, right_val) = op {
        // Requires RAX to be set to int_val;
        if dest.ll_val() != left_val.ll_val() {
          println!("need to convert, {left_val:?} to {dest:?}")
        }
        println!("MUL {dest:?}, {right_val:?}");
        println!("")
      }
    }
    Op::DIV => {
      if let OpExpr::BinaryOp(_, dest, left_val, right_val) = op {
        // Requires RAX to be set to int_val;
        if dest.ll_val() != left_val.ll_val() {
          println!("need to convert, {left_val:?} to {dest:?}")
        }
        println!("DIV {dest:?}, {right_val:?}");
        println!("")
      }
    }
    Op::LOG => {
      if let OpExpr::BinaryOp(_, dest, left_val, right_val) = op {
        // Requires RAX to be set to int_val;
        if dest.ll_val() != left_val.ll_val() {
          println!("need to convert, {left_val:?} to {dest:?}")
        }
        println!("LOG {dest:?}, {right_val:?}");
        println!("")
      }
    }
    Op::POW => {
      if let OpExpr::BinaryOp(_, dest, left_val, right_val) = op {
        // Requires RAX to be set to int_val;
        if dest.ll_val() != left_val.ll_val() {
          println!("need to convert, {left_val:?} to {dest:?}")
        }
        println!("POW {dest:?}, {right_val:?}");
        println!("")
      }
    }
    Op::GR => todo!("Op::GR"),
    Op::LE => todo!("Op::LE"),
    Op::GE => {
      if let OpExpr::BinaryOp(_, _, left_val, right_val) = op {
        // Requires RAX to be set to int_val;

        if let (Some(pass), Some(fail)) = (block.branch_succeed, block.branch_fail) {
          println!("CMP {left_val:?} {right_val:?}");
          cmp(binary, left_val.ll_val().bit_size(), left_val.to_reg_arg(), right_val.to_reg_arg());

          if pass == block.id + 1 {
            jmp(binary, b32, JumpOps::Less, Imm(fail as u64));
            jmp_resolver.add_jump(binary, fail);
            println!("JL BLOCK({fail})");
          } else if fail == block.id + 1 {
            jmp(binary, b32, JumpOps::GreaterOrEqual, Imm(pass as u64));
            jmp_resolver.add_jump(binary, pass);
            println!("JGE BLOCK({pass})");
          } else {
            jmp(binary, b32, JumpOps::GreaterOrEqual, Imm(pass as u64));
            jmp_resolver.add_jump(binary, pass);
            jmp(binary, b32, JumpOps::Jump, Imm(fail as u64));
            jmp_resolver.add_jump(binary, fail);
            println!("JGE BLOCK({pass})");
            println!("JMP BLOCK({fail})");
          }
        } else {
          panic!("Ill formed block")
        }
      }
    }
    Op::LS => todo!("Op::LS"),
    Op::OR => todo!("Op::OR"),
    Op::XOR => todo!("Op::XOR"),
    Op::AND => todo!("Op::AND"),
    Op::NOT => todo!("Op::NOT"),
    Op::LOAD => {
      if let OpExpr::UnaryOp(_, dest_reg, source_reg) = op {
        // Requires RAX to be set to int_val;

        match source_reg.ll_val() {
          LLVal::Ptr(PtrData { ptr: PtrType::Stack(index), bits, elements }) => {
            let bit_size = source_reg.ll_val().bit_size();
            println!("MOV {dest_reg:?} [{source_reg:?}] {bit_size:?}");
            mov(binary, bit_size, source_reg.to_mem_arg(), dest_reg.to_reg_arg())
          }
          LLVal::Ptr(PtrData { ptr: PtrType::Heap, bits, elements }) => {}
          ty => panic!("invalid type for load op: {ty:?}"),
        }

        println!("")
      }
    }
    Op::STORE => {
      if let OpExpr::BinaryOp(_, _, ptr_val, int_val) = op {
        // Requires RAX to be set to int_val;

        if let OpVal::REG(ptr_name, _) = ptr_val {
          match int_val {
            OpVal::REG(int_name, _) => {
              println!("MOV {ptr_name:?} {int_name:?}");
            }
            OpVal::Lit(val) => {
              match val {
                LLVal::F32(val) => {
                  let imm = Imm(unsafe { std::mem::transmute::<_, u32>(*val) } as u64);
                  mov(binary, b32, imm, Mem(*ptr_name));
                }
                LLVal::F64(val) => {
                  let imm = Imm(unsafe { std::mem::transmute(*val) });
                  mov(binary, b64, imm, Mem(*ptr_name));
                }
                LLVal::Int(IntData { val: IntVal::Static(imm), .. }) => {
                  mov(binary, val.bit_size(), Imm(*imm as u64), Mem(*ptr_name));
                  println!("MOV [ {ptr_name:?}] {imm}");
                }
                _ => unreachable!(),
              };
            }
            _ => unreachable!(),
          }
        } else {
          panic!("Not a register");
        }
        println!("")
      }
    }
    Op::CALL => todo!("Op::CALL"),
    Op::CONVERT => todo!("Op::CONVERT"),
    Op::ALLOC => {
      if let OpExpr::BinaryOp(_, ptr_val, _, int_val) = op {
        // Requires RAX to be set to int_val;

        if let OpVal::REG(ptr_name, _) = ptr_val {
          match int_val {
            OpVal::REG(int_name, _) => {
              mov(binary, b64, Reg(*int_name), Reg(GR::RDI));
              mov(binary, b64, Reg(GR::RAX), Reg(*ptr_name));
              println!("MOV RDI {int_name:?}");
              println!("CALL %malloc%");
              println!("MOV {ptr_name:?} RAX");
            }
            OpVal::Lit(val) => {
              let imm = match val {
                LLVal::F32(val) => *val as i64,
                LLVal::F64(val) => *val as i64,
                LLVal::Int(IntData { val: IntVal::Static(val), .. }) => *val,
                _ => unreachable!(),
              } as u64;

              mov(binary, b64, Imm(imm), Reg(GR::RDI));
              call(binary, b64, Mem(GR::R8));
              if *ptr_name != GR::RAX {
                mov(binary, b64, Reg(GR::RAX), Reg(*ptr_name));
              }

              println!("MOV  RDI {imm}");
              println!("CALL %malloc%");
              println!("MOV  {ptr_name:?} RAX");
            }
            _ => unreachable!(),
          }
        } else {
          panic!("Not a register");
        }
        println!("")
      }
    }
    Op::RETURN => todo!("Op::RETURN"),
    Op::CALL_BLOCK => todo!("Op::CALL_BLOCK"),
    Op::EXIT_BLOCK => todo!("Op::EXIT_BLOCK"),
    Op::JUMP => {
      if let OpExpr::UnaryOp(..) = op {
        // Requires RAX to be set to int_val;
        if let Some(target_id) = block.branch_unconditional {
          jmp(binary, b32, JumpOps::Jump, Imm(target_id as u64));
          jmp_resolver.add_jump(binary, target_id);
          println!("JMP BLOCK({target_id}) ");
        }
      }
    }
    Op::JUMP_ZE => todo!("Op::JUMP_ZE"),
    Op::JUMP_NZ => todo!("Op::JUMP_NZ"),
    Op::JUMP_EQ => todo!("Op::JUMP_EQ"),
  }
}

fn print_instructions(binary: &[u8], mut offset: u64) -> u64 {
  use iced_x86::{Decoder, DecoderOptions, Formatter, Instruction, MasmFormatter};

  let mut decoder = Decoder::with_ip(64, &binary, offset, DecoderOptions::NONE);
  let mut formatter = MasmFormatter::new();

  formatter.options_mut().set_digit_separator("_");
  formatter.options_mut().set_number_base(iced_x86::NumberBase::Decimal);
  formatter.options_mut().add_leading_zero_to_hex_numbers();
  formatter.options_mut().set_first_operand_char_index(2);

  for instruction in decoder {
    let mut output = String::default();
    formatter.format(&instruction, &mut output);
    print!("{:016} ", instruction.ip());
    println!(" {}", output);

    offset = instruction.ip() + instruction.len() as u64
  }

  offset
}

#[derive(Clone, Copy, Debug)]
enum Arg {
  Reg(GeneralRegisterName),
  Mem(GeneralRegisterName),
  Imm(u64),
  OpExt(u8),
  RSP_OFF(usize),
}

impl Arg {
  pub fn is_reg(&self) -> bool {
    matches!(self, Arg::Reg(..))
  }

  pub fn reg_index(&self) -> u8 {
    match self {
      Arg::Reg(reg) | Arg::Mem(reg) => reg.register_index(),
      Self::OpExt(index) => *index,
      _ | Arg::Imm(_) => unreachable!(),
    }
  }

  pub fn is_64_extended(&self) -> bool {
    match self {
      Arg::Reg(reg) | Arg::Mem(reg) => reg.is_64_extended(),
      _ => false,
    }
  }
}

/// https://www.felixcloutier.com/x86/add
fn add(binary: &mut Vec<u8>, bit_size: BitSize, right: Arg, left: Arg) {
  use Arg::*;
  use BinaryOpEncoding::*;
  use BitSize::*;
  match (right, left) {
    (right @ Imm(..), left @ Reg(reg)) if (!reg.is_64_extended() && reg.register_index() == 0) => {
      match bit_size {
        b8 => encode_binary_op(binary, 0x04, bit_size, I, left, right, 0),
        bit_size => encode_binary_op(binary, 0x05, bit_size, I, left, right, 0),
      }
    }
    (right @ Imm(imm), left @ Mem(..)) | (right @ Imm(imm), left @ Reg(..)) => {
      if bit_size > b8 && (imm as i8) as i64 == imm as i64 {
        encode_binary_op(binary, 0x83, b8, MI, left, right, 0)
      } else {
        match bit_size {
          b8 => encode_binary_op(binary, 0x80, bit_size, MI, left, right, 0),
          bit_size => encode_binary_op(binary, 0x81, bit_size, MI, left, right, 0),
        }
      }
    }
    (right @ Reg(..), left @ Reg(..)) | (right @ Mem(..), left @ Reg(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0x02, bit_size, RM, left, right, 0),
      bit_size => encode_binary_op(binary, 0x03, bit_size, RM, left, right, 0),
    },
    (right @ Reg(..), left @ Mem(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0x00, bit_size, MR, left, right, 0),
      bit_size => encode_binary_op(binary, 0x01, bit_size, MR, left, right, 0),
    },
    (right, left) => panic!("Invalid:  mov left:{left:?}, right:{right:?}"),
  }
}

/// https://www.felixcloutier.com/x86/cmp
fn cmp(binary: &mut Vec<u8>, bit_size: BitSize, left: Arg, right: Arg) {
  use Arg::*;
  use BinaryOpEncoding::*;
  use BitSize::*;
  match (right, left) {
    (right @ Imm(..), left @ Reg(..)) | (right @ Imm(..), left @ Mem(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0x80, bit_size, MI, left, right, 7),
      bit_size => encode_binary_op(binary, 0x81, bit_size, MI, left, right, 7),
    },
    (right @ Reg(..), left @ Reg(..)) | (right @ Mem(..), left @ Reg(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0x3A, bit_size, RM, left, right, 0),
      bit_size => encode_binary_op(binary, 0x3B, bit_size, RM, left, right, 0),
    },
    (right @ Reg(..), left @ Mem(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0x38, bit_size, MR, left, right, 0),
      bit_size => encode_binary_op(binary, 0x39, bit_size, MR, left, right, 0),
    },
    (right, left) => panic!("Invalid:  mov left:{left:?}, right:{right:?}"),
  }
}

/// https://www.felixcloutier.com/x86/mov
fn mov(binary: &mut Vec<u8>, bit_size: BitSize, from: Arg, to: Arg) {
  use Arg::*;
  use BinaryOpEncoding::*;
  use BitSize::*;
  match (from, to) {
    (from @ Imm(..), to @ Reg(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0xB0, bit_size, OI, to, from, 0),
      bit_size => encode_binary_op(binary, 0xB8, bit_size, OI, to, from, 0),
    },
    (from @ Imm(..), to @ Mem(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0xC6, bit_size, MI, to, from, 0),
      bit_size => encode_binary_op(binary, 0xC7, bit_size, MI, to, from, 0),
    },
    (from @ Reg(..), to @ Reg(..)) | (from @ Mem(..), to @ Reg(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0x8A, bit_size, RM, to, from, 0),
      bit_size => encode_binary_op(binary, 0x8B, bit_size, RM, to, from, 0),
    },
    (from @ Reg(..), to @ Mem(..)) => match bit_size {
      b8 => encode_binary_op(binary, 0x88, bit_size, MR, to, from, 0),
      bit_size => encode_binary_op(binary, 0x89, bit_size, MR, to, from, 0),
    },
    (from, to) => panic!("Invalid:  mov to:{to:?}, from:{from:?}"),
  }
}

#[repr(u8)]
#[derive(Debug)]
pub enum JumpOps {
  /// AKA OF == 1
  Overflow       = 0x00,
  /// AKA OF == 0
  NoOverflow     = 0x01,
  /// AKA CF == 1
  Below          = 0x02,
  /// AKA CF == 0
  AboveOrEqual   = 0x03,
  /// AKA ZF == 1
  Equal          = 0x04,
  /// AKA ZF == 0
  NotEqual       = 0x05,
  /// AKA ZF == 1 || CF == 1
  BelowOrEqual   = 0x06,
  /// AKA ZF == 0 && CF == 0
  Above          = 0x07,
  /// AKA SF == 1
  Signed         = 0x08,
  /// AKA SF == 0
  Unsigned       = 0x09,
  /// AKA PF == 1
  EvenParity     = 0x0A,
  /// AKA PF == 0
  OddParity      = 0x0B,
  /// AKA SF != OF
  Less           = 0x0C,
  /// AKA SF != OF
  GreaterOrEqual = 0x0D,
  /// AKA ZF == 1 || SF != OF
  LessOrEqual    = 0x0E,
  /// AKA ZF == 0 && SF == OF
  Greater        = 0x0F,
  /// General jump to offset
  Jump           = 0xFF,
  __JShort__     = 0x70,
  __JLong___     = 0x80,
}

fn jmp(binary: &mut Vec<u8>, bit_size: BitSize, op: JumpOps, arg: Arg) {
  use Arg::*;
  use BitSize::*;
  match (bit_size, arg) {
    (b8, Imm(pos)) => match op {
      JumpOps::Jump => push_bytes(binary, (0xEBu8, pos as i8)),
      op => push_bytes(binary, (op as u8 + JumpOps::__JShort__ as u8, pos as i8)),
    },
    (b32, Imm(pos)) => match op {
      JumpOps::Jump => {
        push_bytes(binary, 0xE9u8);
        push_bytes(binary, pos as i32);
      }
      op => {
        push_bytes(binary, (0x0Fu8, op as u8 | JumpOps::__JLong___ as u8));
        push_bytes(binary, pos as u32);
      }
    },
    (b8, arg @ Reg(..)) | (b8, arg @ Mem(..)) => todo!(),
    (b32, arg @ Reg(..)) | (b32, arg @ Mem(..)) => todo!(),
    (b64, arg @ Reg(..)) | (b64, arg @ Mem(..)) => todo!(),
    combo => panic!("Invalid operations for jump {op:?} {combo:?} "),
  }
}

fn call(binary: &mut Vec<u8>, bit_size: BitSize, op: Arg) {
  encode_unary_op(binary, 0xFF, bit_size, UnaryOpEncoding::M, op, 2);
}

#[derive(Debug)]
enum UnaryOpEncoding {
  /// ### Register to Memory/Register
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op         | offset        |               |
  D,
  /// ### Memory/Register Value
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op         | mod:reg(w)    |               |
  M,
}

#[derive(Debug)]
enum BinaryOpEncoding {
  /// ### Register to Memory/Register
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op         | mod:rm(w)     | mod:reg(r)    |
  MR,
  /// ### Memory/Register to Register
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op         | mod:reg(w)    | mod:rm(r)     |
  RM,
  /// ### SEG/OFFSET to Register
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op         | RAX/EAX/AX/AL | Moffs         |
  FD,
  /// ### Register to SEG/OFFSET
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op         | Moffs(w)      | RAX/EAX/AX/AL |
  TD,
  /// ### Immediate to Register
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op + rd(2) | imm           |
  OI,
  /// ### Immediate to Memory
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op         | mod:rm(w)     | imm           |
  MI,
  /// ### Immediate to Register
  ///
  /// | opcode     | operand1      | operand2      |
  /// | ------     | ------        | ------        |
  /// | op         | Reg           | imm           |
  I,
}
const REX_W_64B: u8 = 0b0100_1000;
const REX_R_REG_EX: u8 = 0b0100_0100;
const REX_X_SIP: u8 = 0b0100_0010;
const REX_B_MEM_REG_EX: u8 = 0b0100_0001;

const MEM_MOD: u8 = 0b00;
const D8__MOD: u8 = 0b01;
const D32_MOD: u8 = 0b10;
const REG_MOD: u8 = 0b11;

/// | mod: 7-6 | reg: 5-3 | r_m: 2-0 |
fn push_mod_rm_reg_op(binary: &mut Vec<u8>, r_m: Arg, reg: Arg) {
  let mod_bits = match r_m {
    Arg::Mem(_) => 0b00,
    Arg::Reg(_) => 0b11,
    op => panic!("Invalid r_m operand {op:?}"),
  };

  binary.push(((mod_bits & 0x3) << 6) | ((reg.reg_index() & 0x7) << 3) | (r_m.reg_index() & 0x7));
}

fn insert_rex_if_required(binary: &mut Vec<u8>, bit_size: BitSize, r_m: Arg, reg: Arg) {
  let mut rex = 0;
  rex |= (bit_size == BitSize::b64).then_some(REX_W_64B).unwrap_or(0);
  rex |= (r_m.is_64_extended()).then_some(REX_B_MEM_REG_EX).unwrap_or(0);
  rex |= (reg.is_64_extended()).then_some(REX_R_REG_EX).unwrap_or(0);
  if rex > 0 {
    binary.push(rex);
  }
}

pub fn encode_unary_op(
  binary: &mut Vec<u8>,
  op_code: u8,
  bit_size: BitSize,
  enc: UnaryOpEncoding,
  op1: Arg,
  ext: u8,
) {
  use Arg::*;
  use UnaryOpEncoding::*;

  match enc {
    M => {
      insert_rex_if_required(binary, bit_size, op1, OpExt(ext));
      push_bytes(binary, op_code);
      push_mod_rm_reg_op(binary, op1, OpExt(ext));
    }
    D => {
      push_bytes(binary, op_code);
      todo!()
    }
    enc => panic!("{enc:?} not valid for unary operations"),
  }
}

pub fn encode_binary_op(
  binary: &mut Vec<u8>,
  op_code: u8,
  bit_size: BitSize,
  enc: BinaryOpEncoding,
  op1: Arg,
  op2: Arg,
  ext: u8,
) {
  use Arg::*;
  use BinaryOpEncoding::*;

  match enc {
    MR => {
      insert_rex_if_required(binary, bit_size, op1, op2);
      push_bytes(binary, op_code);
      push_mod_rm_reg_op(binary, op1, op2);
    }
    RM => {
      insert_rex_if_required(binary, bit_size, op2, op1);
      push_bytes(binary, op_code);
      push_mod_rm_reg_op(binary, op2, op1);
    }
    MI => match op2 {
      Imm(imm) => {
        insert_rex_if_required(binary, bit_size, op1, OpExt(ext));
        push_bytes(binary, op_code);
        push_mod_rm_reg_op(binary, op1, OpExt(ext));
        match bit_size {
          BitSize::b8 => push_bytes(binary, imm as u8),
          _ => push_bytes(binary, imm as u32),
        }
      }
      imm => panic!("Invalid immediate arg op2 of {imm:?} for MI encoding"),
    },
    OI => match op2 {
      Imm(imm) => {
        insert_rex_if_required(binary, bit_size, op1, OpExt(ext));
        push_bytes(binary, op_code | op1.reg_index());
        match bit_size {
          BitSize::b8 => push_bytes(binary, imm as u8),
          BitSize::b32 => push_bytes(binary, imm as u32),
          BitSize::b64 => push_bytes(binary, imm as u64),
          size => panic!("Invalid immediate size {size:?} for OI encoding"),
        }
      }
      imm => panic!("Invalid immediate arg op2 of {imm:?} for MI encoding"),
    },
    I => match op2 {
      Imm(imm) => {
        insert_rex_if_required(binary, bit_size, OpExt(0), OpExt(ext));
        push_bytes(binary, (op_code));
        match bit_size {
          BitSize::b8 => push_bytes(binary, imm as u8),
          BitSize::b64 | BitSize::b32 => push_bytes(binary, 3 as u32),
          size => panic!("Invalid immediate size {size:?} for OI encoding"),
        }
      }
      imm => panic!("Invalid immediate arg op2 of {imm:?} for MI encoding"),
    },
    enc => panic!("{enc:?} not valid for binary operations on {op1:?} on {op2:?}"),
  }
}

fn convert_ssa_to_reg(
  op: &OpVal<()>,
  register: &mut RegisterAllocator,
) -> OpVal<GeneralRegisterName> {
  match *op {
    OpVal::SSA(index, val) => {
      if let LLVal::Und = val {
        return OpVal::SSA(index, val);
      }
      match val {
        LLVal::Und => OpVal::REG(register.set(BitSize::b64, val), val),
        LLVal::Ptr(_) => OpVal::REG(register.set(BitSize::b64, val), val),
        LLVal::PtrBits(_) => OpVal::REG(register.set(BitSize::b64, val), val),
        LLVal::F32(_) => OpVal::REG(register.set(BitSize::b64, val), val),
        LLVal::F64(_) => OpVal::REG(register.set(BitSize::b64, val), val),
        LLVal::Int(int) => match int.bits {
          BitSize::b8 => OpVal::REG(register.set(BitSize::b64, val), val),
          BitSize::b16 => OpVal::REG(register.set(BitSize::b64, val), val),
          BitSize::b32 => OpVal::REG(register.set(BitSize::b64, val), val),
          BitSize::b64 => OpVal::REG(register.set(BitSize::b64, val), val),
          _ => OpVal::REG(GeneralRegisterName::R8, val),
        },
      }
    }
    OpVal::BLOCK(block) => OpVal::BLOCK(block),
    OpVal::Lit(literal) => OpVal::Lit(literal),
    OpVal::REF(reference) => {
      OpVal::REG(register.set(BitSize::b64, LLVal::Ptr(reference)), LLVal::Ptr(reference))
    }
    _ => unreachable!(),
  }
}

/* #[test]
pub fn run_x86() {
  let prot = libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC;
  let flags: i32 = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;

  let allocation_size = 4096;
  let ptr =
    unsafe { libc::mmap(std::ptr::null_mut(), allocation_size, prot, flags, -1, 0) as *mut u8 };

  let data = unsafe { std::slice::from_raw_parts_mut(ptr, allocation_size) };

  for entry in data.iter_mut() {
    *entry = 0;
  }

  // Move instruction
  let offset = mov_imm(GeneralRegisterName::EAX, 2024, 0, data);
  let offset = mov_imm(GeneralRegisterName::R8W, 2024, offset, data);
  let offset = fill_with_noop(offset, 20, data);
  ret_short(offset, data);

  let funct: fn() -> u64 = unsafe { std::mem::transmute(ptr) };

  dbg!((funct)());

  unsafe {
    let result = libc::munmap(ptr as *mut _, allocation_size);
    dbg!(result);
  }
} */

pub enum Mod {
  RegAddress = 0b00,
  Displace8  = 0b01,
  Displace16 = 0b10,
  Register   = 0b11,
}

pub enum RM {
  //
  BX_SI = 0b000,
  BX_DI = 0b001,
  BP_SI = 0b010,
  BP_DI = 0b011,
  SI    = 0b100,
  DI    = 0b101,
  BP    = 0b110,
  BX    = 0b111,
}

pub fn create_mod_rm(m: Mod, reg: u8, rm: RM) -> u8 {
  let m = m as u8;
  let rm = rm as u8;
  (m & 0x3) << 5 | (reg & 0x7) << 3 | (rm & 0x7)
}

pub struct GeneralRegisterAllocation {
  name: GeneralRegisterName,
  size: BitSize,
}

#[allow(non_camel_case_types, unused)]
pub enum RegisterName {
  GeneralRegisterName(GeneralRegisterName),
  AVX_64,
  AVX_128,
  AVX_512,
}

#[allow(non_camel_case_types, unused)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralRegisterName {
  FLAGS = 0,
  EIP   = 1,
  //
  AL    = 0x00 | 0x0_00 | 0x10_00,
  CL    = 0x01 | 0x0_00 | 0x10_00,
  DL    = 0x02 | 0x0_00 | 0x10_00,
  BL    = 0x03 | 0x0_00 | 0x10_00,
  //
  AH    = 0x04 | 0x0_00 | 0x10_00,
  CH    = 0x05 | 0x0_00 | 0x10_00,
  DH    = 0x06 | 0x0_00 | 0x10_00,
  BH    = 0x07 | 0x0_00 | 0x10_00,
  //
  AX    = 0x00 | 0x0_00 | 0x30_00,
  CX    = 0x01 | 0x0_00 | 0x30_00,
  DX    = 0x02 | 0x0_00 | 0x30_00,
  BX    = 0x03 | 0x0_00 | 0x30_00,
  //
  EAX   = 0x00 | 0x0_00 | 0x70_00,
  ECX   = 0x01 | 0x0_00 | 0x70_00,
  EDX   = 0x02 | 0x0_00 | 0x70_00,
  EBX   = 0x03 | 0x0_00 | 0x70_00,
  //
  RAX   = 0x00 | 0x0_00 | 0xF0_00,
  RCX   = 0x01 | 0x0_00 | 0xF0_00,
  RDX   = 0x02 | 0x0_00 | 0xF0_00,
  RBX   = 0x03 | 0x0_00 | 0xF0_00,
  //
  SP    = 0x04 | 0x0_00 | 0x30_00,
  BP    = 0x05 | 0x0_00 | 0x30_00,
  SI    = 0x06 | 0x0_00 | 0x30_00,
  DI    = 0x07 | 0x0_00 | 0x30_00,
  //
  ESP   = 0x04 | 0x0_00 | 0x70_00,
  EBP   = 0x05 | 0x0_00 | 0x70_00,
  ESI   = 0x06 | 0x0_00 | 0x70_00,
  EDI   = 0x07 | 0x0_00 | 0x70_00,
  //
  RSP   = 0x04 | 0x0_00 | 0xF0_00,
  RBP   = 0x05 | 0x0_00 | 0xF0_00,
  RSI   = 0x06 | 0x0_00 | 0xF0_00,
  RDI   = 0x07 | 0x0_00 | 0xF0_00,
  //
  R8B   = 0x00 | 0x1_00 | 0x10_00,
  R9B   = 0x01 | 0x1_00 | 0x10_00,
  R10B  = 0x02 | 0x1_00 | 0x10_00,
  R11B  = 0x03 | 0x1_00 | 0x10_00,
  R12B  = 0x04 | 0x1_00 | 0x10_00,
  R13B  = 0x05 | 0x1_00 | 0x10_00,
  R14B  = 0x06 | 0x1_00 | 0x10_00,
  R15B  = 0x07 | 0x1_00 | 0x10_00,
  //
  R8W   = 0x00 | 0x1_00 | 0x30_00,
  R9W   = 0x01 | 0x1_00 | 0x30_00,
  R10W  = 0x02 | 0x1_00 | 0x30_00,
  R11W  = 0x03 | 0x1_00 | 0x30_00,
  R12W  = 0x04 | 0x1_00 | 0x30_00,
  R13W  = 0x05 | 0x1_00 | 0x30_00,
  R14W  = 0x06 | 0x1_00 | 0x30_00,
  R15W  = 0x07 | 0x1_00 | 0x30_00,
  //
  R8D   = 0x00 | 0x1_00 | 0x70_00,
  R9D   = 0x01 | 0x1_00 | 0x70_00,
  R10D  = 0x02 | 0x1_00 | 0x70_00,
  R11D  = 0x03 | 0x1_00 | 0x70_00,
  R12D  = 0x04 | 0x1_00 | 0x70_00,
  R13D  = 0x05 | 0x1_00 | 0x70_00,
  R14D  = 0x06 | 0x1_00 | 0x70_00,
  R15D  = 0x07 | 0x1_00 | 0x70_00,
  //
  R8    = 0x00 | 0x1_00 | 0xF0_00,
  R9    = 0x01 | 0x1_00 | 0xF0_00,
  R10   = 0x02 | 0x1_00 | 0xF0_00,
  R11   = 0x03 | 0x1_00 | 0xF0_00,
  R12   = 0x04 | 0x1_00 | 0xF0_00,
  R13   = 0x05 | 0x1_00 | 0xF0_00,
  R14   = 0x06 | 0x1_00 | 0xF0_00,
  R15   = 0x07 | 0x1_00 | 0xF0_00,
}

impl GeneralRegisterName {
  pub fn size(&self) -> BitSize {
    let val = *self as u16;

    match (val & 0xF0_00) >> 12 {
      0x1 => BitSize::b8,
      0x3 => BitSize::b16,
      0x7 => BitSize::b32,
      0xF => BitSize::b64,
      _ => unreachable!(),
    }
  }

  pub fn register_index(&self) -> u8 {
    ((*self as u16) & 0x0F) as u8
  }

  /// The register is one of R8-R15
  pub fn is_64_extended(&self) -> bool {
    ((*self as u16) & 0x1_00) > 0
  }
}

pub enum VectorRegistor {
  XMM1,
  XMM2,
  XMM3,
  XMM4,
  XMM5,
  XMM6,
  XMM7,
  XMM8,
  SSE1,
  SSE2,
  SSE3,
  SSE4,
  SSE5,
  SSE6,
  SSE7,
  SSE8,
}
