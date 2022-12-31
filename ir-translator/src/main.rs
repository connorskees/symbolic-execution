#![allow(unused)]

use std::fs;

use generator::TranslationBuilder;
use lalrpop_util::lalrpop_mod;

mod ast_builder;
mod generator;

lalrpop_mod!(pub semantics);

fn main() -> anyhow::Result<()> {
    let input = fs::read_to_string("ir-translator/src/semantics.txt")?;
    let semantics_tree = match semantics::InstDefinitionsParser::new().parse(&input) {
        Ok(inst) => inst,
        Err(e) => {
            println!("{}", e);
            anyhow::bail!("failed to parse input");
        }
    };

    let mut builder = TranslationBuilder::new();

    builder.visit_tree(semantics_tree)?;

    fs::write("ir-translator/src/translator.rs", builder.finish()?)?;

    Ok(())
}
