#![allow(warnings)]

use std::{fs, rc::Rc};

use anyhow::Result;
// use goblin::pe::{section_table::SectionTable, PE};
use iced_x86::{Decoder, Instruction as x86Instruction, Mnemonic, Register};

fn main() -> Result<()> {
    // let exe = fs::read("./symb.exe")?;
    // let parsed = PE::parse(&exe)?;

    // let text_section = parsed
    //     .sections
    //     .iter()
    //     .find(|s| s.name == *b".text\0\0\0")
    //     .unwrap();

    // let mut offset = text_section.pointer_to_raw_data as usize;
    // let instructions = &exe[offset..text_section.size_of_raw_data as usize + offset];

    let bytes = b"\xF0\xF3\x01\x18".repeat(1_000_000);
    let start = std::time::Instant::now();

    let decoder = Decoder::with_ip(64, &bytes, 0x1234_5678, 0);

    let mut ast_builder = AstBuilder::new();

    // let decoder = iced_x86::Decoder::new(64, instructions, 0);
    for inst in decoder {
        ast_builder.add_instruction(inst);
    }

    let end = start.elapsed();
    println!("{:?}", end);

    // dbg!(ast_builder.instructions);
    // dbg!(SectionTable::parse(
    //     &exe,
    //     &mut offset,
    //     text_section.name_offset().unwrap().unwrap()
    // ))
    // .unwrap();

    Ok(())
}

struct AstBuilder {
    instructions: Vec<Instruction>,
}

impl AstBuilder {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
        }
    }

    pub fn add_instruction(&mut self, inst: x86Instruction) {
        match inst.mnemonic() {
            Mnemonic::Add => self.add_add(inst),
            m => todo!("{:?}", m),
        }
    }

    fn add_add(&mut self, inst: x86Instruction) {
        let dst = Self::get_operand_ast(inst, 0);
        let src = Self::get_operand_ast(inst, 1);

        let parent = Instruction {
            operands: Operands::two(dst.clone(), src.clone()),
            kind: InstructionKind::BvAdd,
        };

        // self.add_carry_flag(inst, Rc::clone(&parent), dst, src);

        self.instructions.push(parent)
    }

    fn add_carry_flag(
        &mut self,
        inst: x86Instruction,
        parent: Rc<Instruction>,
        op1: Operand,
        op2: Operand,
    ) {
        let low = Operand::Imm64(0);
        let high = Operand::Imm64(0);

        let bit_size = 1;

        // MSB((op1 & op2) ^ ((op1 ^ op2 ^ parent) & (op1 ^ op2)))

        // (op1 ^ op2)
        let a = Instruction::new(
            InstructionKind::BvXor,
            Operands::two(op1.clone(), op2.clone()),
        );
        // parent
        let b = Instruction::new(
            InstructionKind::Extract,
            Operands::three(low, high, Operand::Instruction(parent)),
        );

        // (op1 ^ op2 ^ parent)
        let c = Instruction::new(
            InstructionKind::BvXor,
            Operands::two(
                Operand::Instruction(Rc::new(a)),
                Operand::Instruction(Rc::new(b)),
            ),
        );
        // (op1 ^ op2)
        let d = Instruction::new(
            InstructionKind::BvXor,
            Operands::two(op1.clone(), op2.clone()),
        );

        // ((op1 ^ op2 ^ parent) & (op1 ^ op2))
        let e = Instruction::new(
            InstructionKind::BvAnd,
            Operands::two(
                Operand::Instruction(Rc::new(c)),
                Operand::Instruction(Rc::new(d)),
            ),
        );
        // (op1 & op2)
        let f = Instruction::new(InstructionKind::BvAnd, Operands::two(op1, op2));

        // (op1 & op2) ^ ((op1 ^ op2 ^ parent) & (op1 ^ op2))
        let g = Instruction::new(
            InstructionKind::BvXor,
            Operands::two(
                Operand::Instruction(Rc::new(e)),
                Operand::Instruction(Rc::new(f)),
            ),
        );

        let node = Instruction::new(
            InstructionKind::Extract,
            Operands::three(
                Operand::Imm64(bit_size - 1),
                Operand::Imm64(bit_size - 1),
                Operand::Instruction(Rc::new(g)),
            ),
        );

        self.instructions.push(node);
    }

    fn get_operand_ast(inst: x86Instruction, idx: u32) -> Operand {
        match inst.op_kind(idx) {
            iced_x86::OpKind::Register => Operand::Register(inst.op_register(idx) as u32),
            iced_x86::OpKind::NearBranch16 => todo!(),
            iced_x86::OpKind::NearBranch32 => todo!(),
            iced_x86::OpKind::NearBranch64 => todo!(),
            iced_x86::OpKind::FarBranch16 => todo!(),
            iced_x86::OpKind::FarBranch32 => todo!(),
            iced_x86::OpKind::Immediate8 => Operand::Imm8(inst.immediate8()),
            iced_x86::OpKind::Immediate8_2nd => todo!(),
            iced_x86::OpKind::Immediate16 => Operand::Imm16(inst.immediate16()),
            iced_x86::OpKind::Immediate32 => Operand::Imm32(inst.immediate32()),
            iced_x86::OpKind::Immediate64 => Operand::Imm64(inst.immediate64()),
            iced_x86::OpKind::Immediate8to16 => todo!(),
            iced_x86::OpKind::Immediate8to32 => todo!(),
            iced_x86::OpKind::Immediate8to64 => todo!(),
            iced_x86::OpKind::Immediate32to64 => todo!(),
            iced_x86::OpKind::MemorySegSI => todo!(),
            iced_x86::OpKind::MemorySegESI => todo!(),
            iced_x86::OpKind::MemorySegRSI => todo!(),
            iced_x86::OpKind::MemorySegDI => todo!(),
            iced_x86::OpKind::MemorySegEDI => todo!(),
            iced_x86::OpKind::MemorySegRDI => todo!(),
            iced_x86::OpKind::MemoryESDI => todo!(),
            iced_x86::OpKind::MemoryESEDI => todo!(),
            iced_x86::OpKind::MemoryESRDI => todo!(),
            iced_x86::OpKind::Memory => {
                let base_reg = inst.memory_base();
                let index = inst.memory_index();
                let seg = inst.memory_segment();

                let scale_value = inst.memory_index_scale();
                let displacement = inst.memory_displacement64();

                let byte_size = if base_reg != Register::None {
                    base_reg.info().size()
                } else if index != Register::None {
                    index.info().size()
                } else if inst.memory_displ_size() > 0 {
                    inst.memory_displ_size() as usize
                } else {
                    std::mem::size_of::<usize>()
                };

                let address = if base_reg != Register::None {
                    base_reg as u32
                } else if index != Register::None {
                    //     var offset = scaleValue == 1 ? new RegisterNode(index) : astCtxt.bvmul(astCtxt.bv(scaleValue, bitSize), new RegisterNode(index));
                    //     address = astCtxt.bvadd(address, offset);

                    todo!()
                } else if displacement != 0 {
                    //     address = astCtxt.bvadd(address, astCtxt.bv(dispValue, bitSize));
                    todo!()
                } else {
                    unreachable!()
                };

                Operand::Memory(address)
            }
        }
    }
}

#[derive(Debug)]
struct Instruction {
    operands: Operands,
    kind: InstructionKind,
}

impl Instruction {
    pub fn new(kind: InstructionKind, operands: Operands) -> Self {
        Self { operands, kind }
    }
}

#[derive(Debug)]
struct Operands([Operand; 3]);

impl Operands {
    pub fn one(op: Operand) -> Self {
        Self([op, Operand::None, Operand::None])
    }

    pub fn two(op1: Operand, op2: Operand) -> Self {
        Self([op1, op2, Operand::None])
    }

    pub fn three(op1: Operand, op2: Operand, op3: Operand) -> Self {
        Self([op1, op2, op3])
    }
}

#[derive(Debug, Clone)]
enum Operand {
    Instruction(Rc<Instruction>),
    Register(u32),
    Memory(u32),
    Imm8(u8),
    Imm16(u16),
    Imm32(u32),
    Imm64(u64),
    None,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum InstructionKind {
    /// Invalid node.
    Invalid = 0,

    /// BVADDx y)
    BvAdd = 5,

    /// (bvand x y)
    BvAnd = 7,

    /// (bvashr x y)
    BVASHR = 12,

    /// (bvlshr x y)
    BVLSHR = 17,

    /// (bvmul x y)
    BVMUL = 19,

    /// (bvnand x y)
    BVNAND = 23,

    /// (bvneg x)
    BVNEG = 29,

    /// (bvnor x y)
    BVNOR = 31,

    /// (bvnot x)
    BVNOT = 37,

    ///  (bvor x y)
    BVOR = 41,

    /// ((_ rotate_left x) y)
    BVROL = 43,

    /// ((_ rotate_right x) y)
    BVROR = 47,

    /// (bvsdiv x y)
    BVSDIV = 53,

    /// (bvsge x y)
    BVSGE = 59,

    ///  (bvsgt x y)
    BVSGT = 61,

    /// (bvshl x y)
    BVSHL = 67,

    /// (bvsle x y)
    BVSLE = 71,

    /// (bvslt x y)
    BVSLT = 73,

    /// (bvsmod x y)
    BVSMOD = 79,

    /// (bvsrem x y)
    BVSREM = 83,

    /// (bvsub x y)
    BVSUB = 89,

    /// (bvudiv x y)
    BVUDIV = 97,

    /// (bvuge x y)
    BVUGE = 101,

    /// (bvugt x y)
    BVUGT = 103,

    /// (bvule x y)
    BVULE = 107,

    /// (bvult x y)
    BVULT = 109,

    /// (bvurem x y)
    BVUREM = 113,

    /// (bvxnor x y)
    BVXNOR = 127,

    /// (bvxor x y)
    BvXor = 131,

    /// (_ bvx y)
    BV = 137,

    /// A compound of nodes
    COMPOUND = 139,

    /// (concat x y z ...)
    CONCAT = 149,

    /// (declare-fun <var_name> () (_ BitVec <var_size>))
    DECLARE = 151,

    /// (distinct x y)
    DISTINCT = 157,

    /// (= x y)
    EQUAL = 163,

    /// ((_ extract x y) z)
    Extract = 167,

    /// (forall ((x (_ BitVec <size>)), ...) body)
    FORALL = 173,

    /// (iff x y)
    IFF = 179,

    /// Integer node
    INTEGER = 181,

    /// (ite x y z)
    ITE = 191,

    /// (and x y)
    LAND = 193,

    /// (let ((x y)) z)
    LET = 197,

    /// (and x y)
    LNOT = 199,

    /// (or x y)
    LOR = 211,

    /// (xor x y)
    LXOR = 223,

    /// Reference node
    REFERENCE = 227,

    /// String node
    STRING = 229,

    /// ((_ sign_extend x) y)
    SX = 233,

    /// ((_ zero_extend x) y)
    ZX = 241,

    /// Undefined value
    UNDEF = 242,

    /// Memory address
    Memory = 243,

    /// Register
    REGISTER = 244,

    /// Temporary variable
    TEMPVAR = 245,

    /// SSA version of a variable node
    SSAVAR = 246,

    ZERO = 247,
    CARRY = 248,
    OVERFLOW = 249,
    SIGN = 250,
    PARITY = 251,
}
