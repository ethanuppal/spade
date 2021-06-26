use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use anyhow::{anyhow, Result};
use logos::Logos;
use structopt::StructOpt;

use spade_ast as ast;
use spade_ast_lowering::{global_symbols, visit_entity};
use spade_common::{error_reporting::CompilationError, id_tracker, name::Path};
use spade_hir::symbol_table;
pub use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference as typeinference;
use spade_typeinference::{ProcessedEntity, ProcessedItem, ProcessedPipeline};

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
    spade_ast_lowering::builtins::populate_symtab(&mut symtab);

    // First pass over the module to collect all global symbols
    for item in &module_ast.members {
        try_or_report!(global_symbols::visit_item(&item, &namespace, &mut symtab));
    }

    // Second pass to actually generate the mir
    let mut idtracker = id_tracker::IdTracker::new();
    let mut hir_items = vec![];
    for item in module_ast.members {
        match item {
            ast::Item::Entity(entity_ast) => {
                let hir = try_or_report!(visit_entity(
                    &entity_ast,
                    &namespace,
                    &mut symtab,
                    &mut idtracker
                ));

                let mut type_state = typeinference::TypeState::new();
                try_or_report!(type_state.visit_entity(&hir, &symtab));

                hir_items.push(ProcessedItem::Entity(ProcessedEntity {
                    entity: hir.inner,
                    type_state,
                }));
            }
            ast::Item::TraitDef(_) => {
                todo!("Trait definitions are not supported by the compiler")
            }
            ast::Item::Type(_) => {
                // Types are invisible at this level
            }
            ast::Item::Pipeline(pipeline_ast) => {
                let hir = try_or_report!(spade_ast_lowering::pipelines::visit_pipeline(
                    &pipeline_ast,
                    &namespace,
                    &mut symtab,
                    &mut idtracker
                ));

                let mut type_state = typeinference::TypeState::new();
                try_or_report!(type_state.visit_pipeline(&hir, &symtab));

                hir_items.push(ProcessedItem::Pipeline(ProcessedPipeline {
                    pipeline: hir.inner,
                    type_state,
                }));
            }
        }
    }

    let mut module_code = vec![];
    let mut frozen_symtab = symtab.freeze();
    for item in hir_items {
        match item {
            ProcessedItem::Entity(e) => {
                let mir = try_or_report!(spade_hir_lowering::generate_entity(
                    &e.entity,
                    frozen_symtab.symtab(),
                    &e.type_state
                ));

                let code = spade_mir::codegen::entity_code(&mir);

                module_code.push(code.to_string());
            }
            ProcessedItem::Pipeline(p) => {
                let mir = try_or_report!(spade_hir_lowering::generate_pipeline(
                    &p.pipeline,
                    &p.type_state,
                    &mut frozen_symtab
                ));

                let code = spade_mir::codegen::entity_code(&mir);

                module_code.push(code.to_string());
            }
        }
    }

    std::fs::write(opts.outfile, module_code.join("\n\n"))?;

    Ok(())
}
