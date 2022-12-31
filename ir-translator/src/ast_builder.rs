use std::cell::RefCell;

use iced_x86::{Decoder, Instruction as x86Instruction, Mnemonic, Register};

use ir::{u512, Instruction, InstructionIdx, InstructionKind, Operand, Operands};

pub struct AstBuilder {
    instructions: RefCell<Vec<Instruction>>,
}

impl AstBuilder {
    pub fn with_capacity(n: usize) -> Self {
        Self {
            instructions: RefCell::new(Vec::with_capacity(n * 4)),
        }
    }

    // pub fn add_instruction(&mut self, inst: x86Instruction) {
    //     self.build_semantics(inst)
    //     // match inst.mnemonic() {
    //     //     // Mnemonic::Add => self.insert_add(inst),
    //     //     // Mnemonic::Sub => self.insert_sub(inst),
    //     //     m => todo!("{:?}", m),
    //     // }
    // }

    fn intern_instruction(&self, inst: Instruction) -> InstructionIdx {
        let idx = self.instructions.borrow().len();
        self.instructions.borrow_mut().push(inst);
        InstructionIdx(idx as u32)
    }

    // fn insert_add(&mut self, inst: x86Instruction) {
    //     let dst = Self::get_operand_ast(inst, 0);
    //     let src = Self::get_operand_ast(inst, 1);

    //     let parent = self.intern_instruction(Instruction {
    //         operands: Operands::two(dst, src),
    //         kind: InstructionKind::BvAdd,
    //     });

    //     self.add_carry_flag(inst, parent, dst, src);
    // }
    // fn insert_sub(&mut self, inst: x86Instruction) {
    //     let dst = Self::get_operand_ast(inst, 0);
    //     let src = Self::get_operand_ast(inst, 1);

    //     let parent = self.intern_instruction(Instruction {
    //         operands: Operands::two(dst, src),
    //         kind: InstructionKind::BvSub,
    //     });

    //     self.add_carry_flag(inst, parent, dst, src);
    // }

    // fn add_carry_flag(
    //     &mut self,
    //     inst: x86Instruction,
    //     parent: InstructionIdx,
    //     op1: Operand,
    //     op2: Operand,
    // ) {
    //     self.instructions.reserve(8);

    //     let low = Operand::ImmU64(0);
    //     let high = Operand::ImmU64(0);

    //     let bit_size = 1;

    //     // MSB((op1 & op2) ^ ((op1 ^ op2 ^ parent) & (op1 ^ op2)))

    //     // (op1 ^ op2)
    //     let a = self.intern_instruction(Instruction::new(
    //         InstructionKind::BvXor,
    //         Operands::two(op1, op2),
    //     ));
    //     // parent
    //     let b = self.intern_instruction(Instruction::new(
    //         InstructionKind::Extract,
    //         Operands::three(low, high, Operand::Instruction(parent)),
    //     ));

    //     // (op1 ^ op2 ^ parent)
    //     let c = self.intern_instruction(Instruction::new(
    //         InstructionKind::BvXor,
    //         Operands::two(Operand::Instruction(a), Operand::Instruction(b)),
    //     ));
    //     // (op1 ^ op2)
    //     let d = self.intern_instruction(Instruction::new(
    //         InstructionKind::BvXor,
    //         Operands::two(op1, op2),
    //     ));

    //     // ((op1 ^ op2 ^ parent) & (op1 ^ op2))
    //     let e = self.intern_instruction(Instruction::new(
    //         InstructionKind::BvAnd,
    //         Operands::two(Operand::Instruction(c), Operand::Instruction(d)),
    //     ));
    //     // (op1 & op2)
    //     let f = self.intern_instruction(Instruction::new(
    //         InstructionKind::BvAnd,
    //         Operands::two(op1, op2),
    //     ));

    //     // (op1 & op2) ^ ((op1 ^ op2 ^ parent) & (op1 ^ op2))
    //     let g = self.intern_instruction(Instruction::new(
    //         InstructionKind::BvXor,
    //         Operands::two(Operand::Instruction(e), Operand::Instruction(f)),
    //     ));

    //     let node = self.intern_instruction(Instruction::new(
    //         InstructionKind::Extract,
    //         Operands::three(
    //             Operand::Imm(bit_size - 1),
    //             Operand::Imm(bit_size - 1),
    //             Operand::Instruction(g),
    //         ),
    //     ));
    //     // self.instructions.push(node);
    // }

    pub fn get_operand_ast(inst: x86Instruction, idx: u32) -> Operand {
        match inst.op_kind(idx) {
            iced_x86::OpKind::Register => Operand::Register(inst.op_register(idx)),
            iced_x86::OpKind::NearBranch16 => todo!(),
            iced_x86::OpKind::NearBranch32 => todo!(),
            iced_x86::OpKind::NearBranch64 => todo!(),
            iced_x86::OpKind::FarBranch16 => todo!(),
            iced_x86::OpKind::FarBranch32 => todo!(),
            iced_x86::OpKind::Immediate8 => Operand::Imm(inst.immediate8() as u64, 8),
            iced_x86::OpKind::Immediate8_2nd => todo!(),
            iced_x86::OpKind::Immediate16 => Operand::Imm(inst.immediate16() as u64, 16),
            iced_x86::OpKind::Immediate32 => Operand::Imm(inst.immediate32() as u64, 32),
            iced_x86::OpKind::Immediate64 => Operand::Imm(inst.immediate64() as u64, 64),
            iced_x86::OpKind::Immediate8to16 => todo!(),
            iced_x86::OpKind::Immediate8to32 => todo!(),
            iced_x86::OpKind::Immediate8to64 => Operand::Imm(inst.immediate8to64() as u64, 64),
            iced_x86::OpKind::Immediate32to64 => todo!(),
            iced_x86::OpKind::MemorySegSI
            | iced_x86::OpKind::MemorySegESI
            | iced_x86::OpKind::MemorySegRSI
            | iced_x86::OpKind::MemorySegDI
            | iced_x86::OpKind::MemorySegEDI
            | iced_x86::OpKind::MemorySegRDI
            | iced_x86::OpKind::MemoryESDI
            | iced_x86::OpKind::MemoryESEDI
            | iced_x86::OpKind::MemoryESRDI
            | iced_x86::OpKind::Memory => {
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

    pub fn equal(&self, expr1: Operand, expr2: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::Equal,
            Operands::two(expr1, expr2),
        ))
    }

    pub fn lor(&self, get_bit_size: InstructionIdx, bvtrue: InstructionIdx) -> InstructionIdx {
        todo!()
    }

    pub fn ite(&self, if_expr: Operand, then_expr: Operand, else_expr: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::BvAdd,
            Operands::three(if_expr, then_expr, else_expr),
        ))
    }

    pub fn bv(&self, value: u512, size: u32) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::Bv,
            Operands::two(Operand::Imm(value, 512), Operand::Imm(size as u64, 32)),
        ))
    }

    pub fn bvsub(&self, expr1: Operand, expr2: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::BvSub,
            Operands::two(expr1, expr2),
        ))
    }

    pub fn bvmul(&self, expr1: Operand, expr2: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::BvMul,
            Operands::two(expr1, expr2),
        ))
    }

    pub fn bvadd(&self, expr1: Operand, expr2: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::BvAdd,
            Operands::two(expr1, expr2),
        ))
    }

    pub fn extract(&self, high: u32, low: u32, expr: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::BvAdd,
            Operands::three(
                Operand::Imm(high as u64, 32),
                Operand::Imm(low as u64, 32),
                expr,
            ),
        ))
    }

    pub fn bvugt(&self, expr1: Operand, expr2: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::BvUgt,
            Operands::two(expr1, expr2),
        ))
    }

    pub fn bvand(&self, expr1: Operand, expr2: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::BvAnd,
            Operands::two(expr1, expr2),
        ))
    }

    pub fn bvxor(&self, expr1: Operand, expr2: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::BvXor,
            Operands::two(expr1, expr2),
        ))
    }

    pub fn bvtrue(&self) -> Operand {
        todo!()
    }

    pub fn zx(&self, size_ext: u32, expr: Operand) -> InstructionIdx {
        self.intern_instruction(Instruction::new(
            InstructionKind::Zx,
            Operands::two(Operand::Imm(size_ext as u64, 32), expr),
        ))
    }

    pub fn bvlshr(&self, op2: Operand, dqword: Operand) -> InstructionIdx {
        todo!()
    }
}
