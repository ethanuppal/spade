use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use anyhow::{anyhow, Result};
use logos::Logos;
use structopt::StructOpt;

use spade_ast_lowering::{id_tracker, symbol_table, visit_entity};
use spade_error_reporting as error_reporting;
pub use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference as typeinference;

#[derive(StructOpt)]
#[structopt(name = "spade", about = "Compiler for the spade language")]
struct Opt {
    #[structopt(name = "INPUT_FILE")]
    pub infile: PathBuf,
    #[structopt(short = "o")]
    pub outfile: PathBuf,
    /// Do not include color in the error report
    #[structopt(long = "no-color")]
    pub no_color: bool,
}

fn main() -> Result<()> {
    let opts = Opt::from_args();

    // Read the input file
    let mut file = File::open(&opts.infile)?;
    let mut file_content = String::new();
    file.read_to_string(&mut file_content)?;

    let mut parser = Parser::new(lexer::TokenKind::lexer(&file_content));

    let entity_ast = match parser.entity() {
        Ok(v) => v,
        Err(e) => {
            error_reporting::report_parse_error(&opts.infile, &file_content, e, opts.no_color);
            return Err(anyhow!("aborting due to previous error"));
        }
    };

    let mut symtab = symbol_table::SymbolTable::new();
    spade_builtins::populate_symtab(&mut symtab);
    let mut idtracker = id_tracker::IdTracker::new();
    let hir = match visit_entity(&entity_ast.unwrap(), &mut symtab, &mut idtracker) {
        Ok(v) => v,
        Err(e) => {
            error_reporting::report_semantic_error(&opts.infile, &file_content, e, opts.no_color);
            return Err(anyhow!("aborting due to previous error"));
        }
    };

    let mut type_state = typeinference::TypeState::new();

    match type_state.visit_entity(&hir) {
        Ok(()) => {}
        Err(e) => {
            error_reporting::report_typeinference_error(
                &opts.infile,
                &file_content,
                e,
                opts.no_color,
            );
            return Err(anyhow!("aborting due to previous error"));
        }
    }

    let mir = match spade_hir_lowering::generate_entity(&hir, &type_state) {
        Ok(val) => val,
        Err(e) => {
            error_reporting::report_hir_lowering_error(
                &opts.infile,
                &file_content,
                e,
                opts.no_color,
            );
            return Err(anyhow!("aborting due to previous error"));
        }
    };

    let code = spade_mir::codegen::entity_code(&mir);

    std::fs::write(opts.outfile, code.to_string())?;

    Ok(())
}
