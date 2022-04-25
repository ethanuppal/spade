use codespan_reporting::term::termcolor::Buffer;
use logos::Logos;
use spade_typeinference::dump::dump_types;
use std::collections::HashMap;
use std::path::PathBuf;
use thiserror::Error;

use spade_ast_lowering::{global_symbols, visit_module_body, Context as AstLoweringCtx};
use spade_common::error_reporting::CodeBundle;
use spade_common::error_reporting::CompilationError;
use spade_common::id_tracker;
use spade_hir::{symbol_table, ExecutableItem, ItemList};
pub use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference as typeinference;
use typeinference::trace_stack::format_trace_stack;

pub struct Opt<'b> {
    pub error_buffer: &'b mut Buffer,
    pub outfile: Option<PathBuf>,
    pub mir_output: Option<PathBuf>,
    pub type_dump_file: Option<PathBuf>,
    pub print_type_traceback: bool,
    pub print_parse_traceback: bool,
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("parse error")]
    ParseError(#[from] spade_parser::error::Error),

    #[error("ast lowering error")]
    AstLoweringError(#[from] spade_ast_lowering::Error),

    #[error("hir lowering error")]
    HirLoweringError(#[from] spade_hir_lowering::Error),

    #[error("type inference error")]
    TypeInferenceError(#[from] spade_typeinference::result::Error),

    #[error("io error")]
    IoError(#[from] std::io::Error),
}

pub fn compile(sources: Vec<(String, String)>, opts: Opt) -> Result<(), ()> {
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
                    e.report(opts.error_buffer, &code);
                    return Err(());
                }
            }
        };
    }

    let mut module_asts = vec![];
    // Read and parse input files
    for (name, content) in sources {
        let file_id = code.add_file(name, content.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&content), file_id);

        module_asts.push(try_or_report!(parser.top_level_module_body(), {
            if opts.print_parse_traceback {
                println!("{}", spade_parser::format_parse_stack(&parser.parse_stack));
            }
        }));
    }

    for module_ast in &module_asts {
        try_or_report!(global_symbols::gather_types(&module_ast, &mut symtab,));
    }

    for module_ast in &module_asts {
        try_or_report!(global_symbols::gather_symbols(
            &module_ast,
            &mut symtab,
            &mut item_list
        ));
    }

    let idtracker = id_tracker::ExprIdTracker::new();
    let mut ctx = AstLoweringCtx {
        symtab,
        idtracker,
        pipeline_ctx: None,
    };

    for module_ast in &module_asts {
        item_list = try_or_report!(visit_module_body(item_list, &module_ast, &mut ctx,));
    }

    let AstLoweringCtx {
        symtab,
        mut idtracker,
        pipeline_ctx: _,
    } = ctx;

    let mut frozen_symtab = symtab.freeze();
    let mut module_code = vec![];
    let mut mir_code = vec![];

    let mut all_types = HashMap::new();

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
                mir_code.push(format!("{mir}"));

                let code = spade_mir::codegen::entity_code(mir);

                module_code.push(code.to_string());

                all_types.extend(dump_types(
                    &type_state,
                    &item_list.types,
                    frozen_symtab.symtab(),
                ))
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
                        p,
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

                mir_code.push(format!("{mir}"));

                let code = spade_mir::codegen::entity_code(mir);

                module_code.push(code.to_string());

                all_types.extend(dump_types(
                    &type_state,
                    &item_list.types,
                    frozen_symtab.symtab(),
                ))
            }
            ExecutableItem::EnumInstance { .. } => {}
            ExecutableItem::StructInstance { .. } => {}
        }
    }

    if let Some(outfile) = opts.outfile {
        try_or_report!(std::fs::write(outfile, module_code.join("\n\n")));
    }
    if let Some(mir_output) = opts.mir_output {
        try_or_report!(std::fs::write(mir_output, mir_code.join("\n\n")));
    }
    if let Some(type_dump_file) = opts.type_dump_file {
        match ron::to_string(&all_types) {
            Ok(encoded_type_info) => {
                try_or_report!(std::fs::write(type_dump_file, encoded_type_info))
            }
            Err(e) => {
                println!("Failed to encode type info as RON {:?}", e)
            }
        }
    }
    Ok(())
}
