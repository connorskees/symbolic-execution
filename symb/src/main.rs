#![allow(warnings)]

use std::{collections::HashSet, fs, rc::Rc};

use anyhow::Result;
use goblin::pe::{section_table::SectionTable, PE};
use iced_x86::{Decoder, Instruction as x86Instruction, Mnemonic, Register};

use ir_translator::AstBuilder;

use crate::x86_semantics::{x86Semantics, Architecture};

mod x86_semantics;
// mod generator;

fn main() -> Result<()> {
    let exe = fs::read("./symb.exe")?;
    let parsed = PE::parse(&exe)?;

    let text_section = parsed
        .sections
        .iter()
        .find(|s| s.name == *b".text\0\0\0")
        .unwrap();

    let mut offset = text_section.pointer_to_raw_data as usize;
    let instructions = &exe[offset..text_section.size_of_raw_data as usize + offset];

    // let bytes = b"\xF0\xF3\x01\x18".repeat(1_000_000);
    let start = std::time::Instant::now();

    let decoder = Decoder::with_ip(64, instructions, 0, 0);

    let mut ast_builder = AstBuilder::with_capacity(instructions.len());

    let mut semantics = x86Semantics::new(Architecture::new(), ast_builder);
    // let decoder = iced_x86::Decoder::new(64, instructions, 0);
    for inst in decoder {
        semantics.build_semantics(inst);
        // ast_builder.build_semantics(inst);
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
