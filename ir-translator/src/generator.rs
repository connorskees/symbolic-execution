use std::{collections::HashMap, fmt, io::Write};

use iced_x86::Mnemonic;

#[derive(Debug, Clone)]
pub enum Flag {
    Carry,
    Parity,
    Adjust,
    Zero,
    Sign,
    Trap,
    Direction,
    Overflow,
}

impl fmt::Display for Flag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Flag::Carry => write!(f, "CF"),
            Flag::Parity => write!(f, "PF"),
            Flag::Adjust => write!(f, "AF"),
            Flag::Zero => write!(f, "ZF"),
            Flag::Sign => write!(f, "SF"),
            Flag::Trap => write!(f, "TF"),
            Flag::Direction => write!(f, "DF"),
            Flag::Overflow => write!(f, "OF"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct InstDefinition {
    pub name: Mnemonic,
    pub implementations: HashMap<u8, InstSemantics>,
}

#[derive(Debug, Clone)]
pub struct InstSemantics {
    pub expr: Expr,
    pub interpolation: Option<String>,
    pub flags: Vec<Flag>,
}

#[derive(Debug, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Zx,
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    BitSize,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Paren(Box<Self>),
    Operand(u8),
    Int(i64),
    UnaryOp(UnaryOp, Box<Self>),
    BinaryOp {
        lhs: Box<Self>,
        op: BinOp,
        rhs: Box<Self>,
    },
    Ite {
        if_expr: Box<Self>,
        then_expr: Box<Self>,
        else_expr: Box<Self>,
    },
    Register(Flag),
    Interpolation(String),
}

impl Expr {
    pub fn is_literal(&self) -> bool {
        match self {
            Expr::Paren(e) => e.is_literal(),
            Expr::Operand(_) => false,
            Expr::Int(_) | Expr::Interpolation(..) => true,
            Expr::UnaryOp(UnaryOp::BitSize, _) => true,
            Expr::BinaryOp { lhs, op, rhs } => lhs.is_literal() && rhs.is_literal(),
            Expr::Ite {
                if_expr,
                then_expr,
                else_expr,
            } => todo!(),
            Expr::Register(_) => false,
        }
    }

    pub fn should_retain_parens(&self) -> bool {
        match self {
            Expr::Paren(e) => e.should_retain_parens(),
            Expr::Operand(_) => false,
            Expr::Int(_) => false,
            Expr::UnaryOp(UnaryOp::BitSize, _) => false,
            Expr::BinaryOp { .. } => self.is_literal(),
            Expr::Ite {
                if_expr,
                then_expr,
                else_expr,
            } => todo!(),
            Expr::Register(_) => false,
            Expr::Interpolation(..) => true,
        }
    }
}

pub(crate) struct TranslationBuilder {
    mnemonics: Vec<Mnemonic>,
    current_buffer: Vec<u8>,
    buffers: HashMap<Mnemonic, Vec<u8>>,
    in_function_call: bool,
    expr_counter: usize,
}

impl TranslationBuilder {
    pub fn new() -> Self {
        Self {
            mnemonics: Vec::new(),
            current_buffer: Vec::new(),
            buffers: HashMap::new(),
            in_function_call: false,
            expr_counter: 0,
        }
    }

    pub fn visit_tree(&mut self, tree: Vec<InstDefinition>) -> anyhow::Result<()> {
        for def in tree {
            let name = def.name;
            self.visit_definition(def)?;
            let buffer = self.current_buffer.clone();
            self.current_buffer.clear();
            self.buffers.insert(name, buffer);
        }

        Ok(())
    }

    pub fn finish(self) -> anyhow::Result<String> {
        let mut buffer = Vec::new();

        buffer.extend_from_slice(
            b"\
use crate::ast_builder::AstBuilder;

use iced_x86::{Instruction as x86Instruction, Mnemonic, Register};
use ir::Operand;

impl AstBuilder {
    pub fn build_semantics(&mut self, inst: x86Instruction) {
        match inst.mnemonic() {
",
        );

        for mnemonic in self.mnemonics {
            let lower = format!("{:?}", mnemonic).to_ascii_lowercase();
            writeln!(
                &mut buffer,
                "          Mnemonic::{:?} => self.{lower}(inst),",
                mnemonic
            )?;
        }

        buffer.extend_from_slice(b"          m => todo!(\"{:?}\", m),\n");
        buffer.extend_from_slice(b"        }\n    }\n");

        for (name, inst_buffer) in self.buffers {
            let name = format!("{:?}", name).to_ascii_lowercase();
            writeln!(
                &mut buffer,
                "\n    fn {name}(&mut self, inst: x86Instruction) {{"
            )?;
            buffer.extend_from_slice(b"        ");
            buffer.extend_from_slice(
                String::from_utf8(inst_buffer)?
                    .replace('\n', "\n        ")
                    .as_bytes(),
            );
            buffer.extend_from_slice(b"\n    }\n");
        }

        buffer.extend_from_slice(b"}\n");

        Ok(String::from_utf8(buffer)?)
    }

    fn visit_definition(&mut self, def: InstDefinition) -> anyhow::Result<()> {
        self.mnemonics.push(def.name);

        if def.implementations.len() == 1 {
            let (op_count, sem) = def.implementations.into_iter().next().unwrap();
            self.visit_semantics(op_count, sem)?;
        } else {
            todo!()
        }

        Ok(())
    }

    fn visit_semantics(&mut self, op_count: u8, sem: InstSemantics) -> anyhow::Result<()> {
        for i in 0..op_count {
            writeln!(
                &mut self.current_buffer,
                "let op{i} = AstBuilder::get_operand_ast(inst, {i});",
            )?;
            // self.current_buffer.extend_from_slice(format!("let "))
        }

        self.current_buffer.extend_from_slice(b"let node = ");
        self.visit_expr(sem.expr)?;
        self.current_buffer.push(b';');

        self.visit_flags(sem.flags)?;

        Ok(())
    }

    fn visit_expr(&mut self, expr: Expr) -> anyhow::Result<()> {
        match expr {
            Expr::Paren(e) => {
                let should_retain_parens = e.should_retain_parens();
                if should_retain_parens {
                    self.current_buffer.push(b'(');
                }
                self.visit_expr(*e)?;
                if should_retain_parens {
                    self.current_buffer.push(b')');
                }
            }
            Expr::Operand(n) => {
                self.current_buffer.extend_from_slice(b"op");
                self.current_buffer.push(n + b'0');
            }
            Expr::Int(n) => write!(&mut self.current_buffer, "{}", n)?,
            Expr::UnaryOp(op, expr) => self.visit_unary_op(*expr, op)?,
            Expr::BinaryOp { lhs, op, rhs } => self.visit_binary_op(*lhs, op, *rhs)?,
            Expr::Ite {
                if_expr,
                then_expr,
                else_expr,
            } => todo!(),
            Expr::Register(flag) => self.visit_flag_expression(flag)?,
            Expr::Interpolation(s) => self.current_buffer.extend_from_slice(s.as_bytes()),
        }

        Ok(())
    }

    fn visit_binary_op(&mut self, lhs: Expr, op: BinOp, rhs: Expr) -> anyhow::Result<()> {
        match op {
            BinOp::Add => {
                if lhs.is_literal() && rhs.is_literal() {
                    self.visit_literal_binary_op(lhs, '+', rhs)
                } else {
                    self.visit_function_call("self.bvadd", vec![lhs, rhs])
                }
            }
            BinOp::Sub => {
                if lhs.is_literal() && rhs.is_literal() {
                    self.visit_literal_binary_op(lhs, '-', rhs)
                } else {
                    self.visit_function_call("self.bvsub", vec![lhs, rhs])
                }
            }
            BinOp::Zx => self.visit_function_call("self.zx", vec![lhs, rhs]),
        }
    }

    fn visit_literal_binary_op(&mut self, lhs: Expr, op: char, rhs: Expr) -> anyhow::Result<()> {
        self.visit_expr(lhs)?;
        write!(&mut self.current_buffer, " {} ", op)?;
        self.visit_expr(rhs)?;
        Ok(())
    }

    fn visit_function_call(&mut self, name: &str, args: Vec<Expr>) -> anyhow::Result<()> {
        if self.in_function_call {
            self.current_buffer
                .extend_from_slice(b"Operand::Instruction(");
        }

        let was_in_function_call = self.in_function_call;
        self.in_function_call = true;

        write!(&mut self.current_buffer, "{}(", name)?;
        if let Some((first, rest)) = args.split_first() {
            self.visit_expr(first.clone())?;

            for expr in rest {
                self.current_buffer.extend_from_slice(b", ");
                self.visit_expr(expr.clone())?;
            }
        }

        self.current_buffer.push(b')');

        if was_in_function_call {
            self.current_buffer.push(b')');
        }

        self.in_function_call = was_in_function_call;

        Ok(())
    }

    fn visit_unary_op(&mut self, expr: Expr, op: UnaryOp) -> anyhow::Result<()> {
        match op {
            UnaryOp::BitSize => self.visit_bitsize(expr),
        }
    }

    fn visit_bitsize(&mut self, expr: Expr) -> anyhow::Result<()> {
        self.visit_expr(expr)?;
        self.current_buffer.extend_from_slice(b".get_bit_size()");
        Ok(())
    }

    fn visit_flags(&mut self, flags: Vec<Flag>) -> anyhow::Result<()> {
        for flag in flags {
            self.visit_flag(flag)?;
        }

        Ok(())
    }

    fn visit_flag_expression(&mut self, flag: Flag) -> anyhow::Result<()> {
        write!(
            &mut self.current_buffer,
            "Operand::Register(Register::RAX)",
            // flag
        )?;
        Ok(())
    }

    fn visit_flag(&mut self, flag: Flag) -> anyhow::Result<()> {
        todo!()
    }
}
