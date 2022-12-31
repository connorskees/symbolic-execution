use crate::ast_builder::AstBuilder;

use iced_x86::{Instruction as x86Instruction, Mnemonic, Register};
use ir::Operand;

impl AstBuilder {
    pub fn build_semantics(&mut self, inst: x86Instruction) {
        match inst.mnemonic() {
            Mnemonic::Adc => self.adc(inst),
            Mnemonic::Add => self.add(inst),
            Mnemonic::Sub => self.sub(inst),
            m => todo!("{:?}", m),
        }
    }

    fn add(&mut self, inst: x86Instruction) {
        let op0 = AstBuilder::get_operand_ast(inst, 0);
        let op1 = AstBuilder::get_operand_ast(inst, 1);
        let node = self.bvadd(op0, op1);
    }

    fn sub(&mut self, inst: x86Instruction) {
        let op0 = AstBuilder::get_operand_ast(inst, 0);
        let op1 = AstBuilder::get_operand_ast(inst, 1);
        let node = self.bvsub(op0, op1);
    }

    fn adc(&mut self, inst: x86Instruction) {
        let op0 = AstBuilder::get_operand_ast(inst, 0);
        let op1 = AstBuilder::get_operand_ast(inst, 1);

        let x;

        let node = self.bvadd(
            Operand::Instruction({
                x = self.bvadd(op0, op1);
                x
            }),
            Operand::Instruction(self.zx(op0.get_bit_size() - 1, Operand::Register(Register::RAX))),
        );
    }
}
