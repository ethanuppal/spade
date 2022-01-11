use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use anyhow::{anyhow, Context, Result};
use logos::Logos;
use spade_common::error_reporting::CodeBundle;
use structopt::StructOpt;

use spade_ast_lowering::{global_symbols, visit_module_body};
use spade_common::{error_reporting::CompilationError, id_tracker, name::Path};
use spade_hir::{symbol_table, ExecutableItem, ItemList};
pub use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference as typeinference;
use typeinference::trace_stack::format_trace_stack;

#[derive(StructOpt)]
#[structopt(name = "spade", about = "Compiler for the spade language")]
struct Opt {
    #[structopt(name = "INPUT_FILE")]
    pub infile: PathBuf,
    #[structopt(name = "EXTRA_FILES")]
    pub extra_files: Vec<PathBuf>,
    #[structopt(short = "o")]
    pub outfile: PathBuf,
    /// Do not include color in the error report
    #[structopt(long = "no-color")]
    pub no_color: bool,

    /// Print a traceback of the type inference process if type inference or hir lowering fails
    #[structopt(long = "print-type-traceback")]
    pub print_type_traceback: bool,
}

fn main() -> Result<()> {
    let mut opts = Opt::from_args();

    let no_color = opts.no_color;

    let mut infiles = vec![opts.infile];
    infiles.append(&mut opts.extra_files);

    let mut symtab = symbol_table::SymbolTable::new();
    let mut item_list = ItemList::new();
    spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut item_list);

    let mut code = CodeBundle::new("".to_string());

    macro_rules! try_or_report {
        ($to_try:expr$(, $extra_code:tt)?) => {
            match $to_try {
                Ok(result) => result,
                Err(e) => {
                    $($extra_code();)?
                    e.report(&code, no_color);
                    return Err(anyhow!("aborting due to previous error"));
                }
            }
        };
    }

    let mut module_asts = vec![];
    // TODO: Namespace individual files
    let namespace = Path(vec![]);
    // Read and parse input files
    for infile in infiles {
        let mut file = File::open(&infile)
            .with_context(|| format!("Failed to open {}", &infile.to_string_lossy()))?;
        let mut file_content = String::new();
        file.read_to_string(&mut file_content)?;

        let file_id = code.add_file(infile, file_content.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&file_content), file_id);

        module_asts.push(try_or_report!(parser.module_body()));
    }

    for module_ast in &module_asts {
        try_or_report!(global_symbols::gather_types(
            &module_ast,
            &Path(vec![]),
            &mut symtab,
        ));
    }

    for module_ast in &module_asts {
        try_or_report!(global_symbols::gather_symbols(
            &module_ast,
            &Path(vec![]),
            &mut symtab,
            &mut item_list
        ));
    }

    let mut idtracker = id_tracker::ExprIdTracker::new();

    for module_ast in &module_asts {
        for item in &module_ast.members {
            try_or_report!(global_symbols::visit_item(
                &item,
                &namespace,
                &mut symtab,
                &mut item_list
            ));
        }

        item_list = try_or_report!(visit_module_body(
            item_list,
            &module_ast,
            &namespace,
            &mut symtab,
            &mut idtracker
        ));
    }

    let mut frozen_symtab = symtab.freeze();
    let mut module_code = vec![];

    for item in item_list.executables.values() {
        match item {
            ExecutableItem::Entity(e) => {
                let mut type_state = typeinference::TypeState::new();
                try_or_report!(type_state.visit_entity(&e, &frozen_symtab.symtab()), {
                    if opts.print_type_traceback {
                        type_state.print_equations();
                        println!("{}", format_trace_stack(&type_state.trace_stack))
                    }
                });

                let mir = try_or_report!(
                    spade_hir_lowering::generate_entity(
                        &e.inner,
                        &mut frozen_symtab,
                        &mut idtracker,
                        &type_state,
                        &item_list
                    ),
                    {
                        if opts.print_type_traceback {
                            type_state.print_equations();
                            println!("{}", format_trace_stack(&type_state.trace_stack))
                        }
                    }
                );

                let code = spade_mir::codegen::entity_code(&mir);

                module_code.push(code.to_string());
            }
            ExecutableItem::Pipeline(p) => {
                let mut type_state = typeinference::TypeState::new();
                try_or_report!(type_state.visit_pipeline(&p, &frozen_symtab.symtab()), {
                    if opts.print_type_traceback {
                        type_state.print_equations();
                        println!("{}", format_trace_stack(&type_state.trace_stack))
                    }
                });

                let mir = try_or_report!(
                    spade_hir_lowering::generate_pipeline(
                        &p,
                        &type_state,
                        &mut frozen_symtab,
                        &mut idtracker,
                        &item_list
                    ),
                    {
                        if opts.print_type_traceback {
                            type_state.print_equations();
                            println!("{}", format_trace_stack(&type_state.trace_stack))
                        }
                    }
                );

                let code = spade_mir::codegen::entity_code(&mir);

                module_code.push(code.to_string());
            }
            ExecutableItem::EnumInstance { .. } => {}
        }
    }

    std::fs::write(opts.outfile, module_code.join("\n\n"))?;

    Ok(())
}
