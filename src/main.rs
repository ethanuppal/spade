use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use anyhow::{anyhow, Result};
use logos::Logos;
use structopt::StructOpt;

pub mod ast;
pub mod constant;
pub mod error_reporting;
pub mod hir;
pub mod lexer;
pub mod location_info;
pub mod parser;
pub mod semantic_analysis;
pub mod symbol_table;
pub mod types;

#[derive(StructOpt)]
#[structopt(name = "spade", about = "Compiler for the spade language")]
struct Opt {
    #[structopt(name = "INPUT_FILE")]
    pub infile: PathBuf,
}

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
    let hir = match semantic_analysis::visit_entity(entity_ast.inner, &mut symtab) {
        Ok(v) => v,
        Err(e) => {
            error_reporting::report_semantic_error(&opts.infile, &file_content, e);
            return Err(anyhow!("aborting due to previous error"));
        }
    };

    Ok(())
}
