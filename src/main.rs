use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use anyhow::{anyhow, Result};
use logos::Logos;
use structopt::StructOpt;

pub mod ast;
pub mod builtins;
// pub mod codegen;
pub mod constant;
pub mod error_reporting;
pub mod fixed_types;
// pub mod global_symbols;
pub mod hir;
pub mod id_tracker;
pub mod lexer;
pub mod location_info;
pub mod parser;
pub mod semantic_analysis;
pub mod symbol_table;
pub mod typeinference;
pub mod types;

#[macro_use]
#[cfg(test)]
pub mod testutil;

use semantic_analysis::visit_entity;

#[derive(StructOpt)]
#[structopt(name = "spade", about = "Compiler for the spade language")]
struct Opt {
    #[structopt(name = "INPUT_FILE")]
    pub infile: PathBuf,
    #[structopt(short = "o")]
    pub outfile: PathBuf,
}

#[allow(dead_code, unused_variables, unused_mut)]
fn main() -> Result<()> {
    let opts = Opt::from_args();

    // Read the input file
    let mut file = File::open(&opts.infile)?;
    let mut file_content = String::new();
    file.read_to_string(&mut file_content)?;

    let mut parser = parser::Parser::new(lexer::TokenKind::lexer(&file_content));

    let entity_ast = match parser.entity() {
        Ok(v) => v,
        Err(e) => {
            error_reporting::report_parse_error(&opts.infile, &file_content, e);
            return Err(anyhow!("aborting due to previous error"));
        }
    };

    let mut symtab = symbol_table::SymbolTable::new();
    let mut idtracker = id_tracker::IdTracker::new();
    let hir = match visit_entity(&entity_ast.unwrap().inner, &mut symtab, &mut idtracker) {
        Ok(v) => v,
        Err(e) => {
            error_reporting::report_semantic_error(&opts.infile, &file_content, e);
            return Err(anyhow!("aborting due to previous error"));
        }
    };

    let mut type_state = typeinference::TypeState::new();

    match type_state.visit_entity(&hir) {
        Ok(()) => {}
        Err(e) => {
            error_reporting::report_typeinference_error(&opts.infile, &file_content, e);
            return Err(anyhow!("aborting due to previous error"));
        }
    }

    // let code = codegen::generate_entity(&hir, &type_state);

    // std::fs::write(opts.outfile, code.to_string())?;

    Ok(())
}
