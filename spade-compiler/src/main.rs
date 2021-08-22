use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use anyhow::{anyhow, Result};
use logos::Logos;
use structopt::StructOpt;

use spade_ast_lowering::{global_symbols, visit_module_body};
use spade_common::{error_reporting::CompilationError, id_tracker, name::Path};
use spade_hir::{symbol_table, ExecutableItem, ItemList};
pub use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference as typeinference;

mod golden;

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

    // TODO: Namespace individual files
    let namespace = Path(vec![]);

    macro_rules! try_or_report {
        ($to_try:expr) => {
            match $to_try {
                Ok(result) => result,
                Err(e) => {
                    e.report(&opts.infile, &file_content, opts.no_color);
                    return Err(anyhow!("aborting due to previous error"));
                }
            }
        };
    }

    let module_ast = try_or_report!(parser.module_body());

    let mut symtab = symbol_table::SymbolTable::new();
    let mut item_list = ItemList::new();
    spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut item_list);

    try_or_report!(global_symbols::gather_symbols(
        &module_ast,
        &Path(vec![]),
        &mut symtab,
        &mut item_list
    ));

    // First pass over the module to collect all global symbols
    for item in &module_ast.members {
        try_or_report!(global_symbols::visit_item(
            &item,
            &namespace,
            &mut symtab,
            &mut item_list
        ));
    }

    let mut idtracker = id_tracker::IdTracker::new();
    let item_list = try_or_report!(visit_module_body(
        item_list,
        &module_ast,
        &namespace,
        &mut symtab,
        &mut idtracker
    ));

    let mut module_code = vec![];
    let mut frozen_symtab = symtab.freeze();
    for item in item_list.executables.values() {
        match item {
            ExecutableItem::Entity(e) => {
                let mut type_state = typeinference::TypeState::new();
                try_or_report!(type_state.visit_entity(&e, &frozen_symtab.symtab()));

                let mir = try_or_report!(spade_hir_lowering::generate_entity(
                    &e.inner,
                    frozen_symtab.symtab(),
                    &type_state,
                    &item_list
                ));

                let code = spade_mir::codegen::entity_code(&mir);

                module_code.push(code.to_string());
            }
            ExecutableItem::Pipeline(p) => {
                let mut type_state = typeinference::TypeState::new();
                try_or_report!(type_state.visit_pipeline(&p, &frozen_symtab.symtab()));

                let mir = try_or_report!(spade_hir_lowering::generate_pipeline(
                    &p,
                    &type_state,
                    &mut frozen_symtab,
                    &item_list
                ));

                let code = spade_mir::codegen::entity_code(&mir);

                module_code.push(code.to_string());
            }
            ExecutableItem::EnumInstance { .. } => {}
        }
    }

    std::fs::write(opts.outfile, module_code.join("\n\n"))?;

    Ok(())
}
