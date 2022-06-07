use codespan_reporting::term::termcolor::Buffer;
use logos::Logos;
use spade_hir_lowering::monomorphisation::MirOutput;
use spade_typeinference::dump::dump_types;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::RwLock;
use thiserror::Error;
use typeinference::equation::TypedExpression;

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
    AstLoweringError(#[from] spade_ast_lowering::error::Error),

    #[error("hir lowering error")]
    HirLoweringError(#[from] spade_hir_lowering::error::Error),

    #[error("type inference error")]
    TypeInferenceError(#[from] spade_typeinference::result::Error),

    #[error("io error")]
    IoError(#[from] std::io::Error),
}

trait Reportable<T> {
    /// Report the error, then discard the error, returning Some if it was Ok
    fn or_report(self, errors: &mut ErrorHandler) -> Option<T>;

    // Reprot the error and continue without modifying the result
    fn report(self, errors: &mut ErrorHandler) -> Self;
}

impl<T, E> Reportable<T> for Result<T, E>
where
    E: CompilationError,
{
    fn report(self, errors: &mut ErrorHandler) -> Self {
        self.map_err(|e| {
            errors.report(&e);
            e
        })
    }

    fn or_report(self, errors: &mut ErrorHandler) -> Option<T> {
        self.report(errors).ok()
    }
}

struct ErrorHandler<'a> {
    pub failed: bool,
    pub error_buffer: &'a mut Buffer,
    /// Using a RW lock here is just a lazy way of managing the ownership of code to
    /// be able to report errors even while modifying CodeBundle
    pub code: Rc<RwLock<CodeBundle>>,
}

impl<'a> ErrorHandler<'a> {
    fn report(&mut self, err: &impl CompilationError) {
        self.failed = true;
        err.report(self.error_buffer, &self.code.read().unwrap());
    }
}

pub struct Artefacts {
    // MIR entities before aliases have been flattened
    pub bumpy_mir_entities: Vec<spade_mir::Entity>,
    // MIR entities after flattening
    pub flat_mir_entities: Vec<spade_mir::Entity>,
}

pub fn compile(sources: Vec<(String, String)>, opts: Opt) -> Result<Artefacts, ()> {
    let mut symtab = symbol_table::SymbolTable::new();
    let mut item_list = ItemList::new();

    // Declared early in order to be able to return early in case this is only
    // partial compilation

    let mut bumpy_mir_entities = vec![];
    let mut flat_mir_entities = vec![];

    spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut item_list);

    let code = Rc::new(RwLock::new(CodeBundle::new("".to_string())));

    let mut errors = ErrorHandler {
        failed: false,
        error_buffer: opts.error_buffer,
        code: code.clone(),
    };

    let mut module_asts = vec![];
    // Read and parse input files
    for (name, content) in sources {
        let file_id = code.write().unwrap().add_file(name, content.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&content), file_id);

        let result = parser
            .top_level_module_body()
            .map_err(|e| {
                if opts.print_parse_traceback {
                    println!("{}", spade_parser::format_parse_stack(&parser.parse_stack));
                };
                e
            })
            .or_report(&mut errors);

        if let Some(ast) = result {
            module_asts.push(ast)
        }
    }

    for module_ast in &module_asts {
        global_symbols::gather_types(&module_ast, &mut symtab).or_report(&mut errors);
    }

    for module_ast in &module_asts {
        global_symbols::gather_symbols(&module_ast, &mut symtab, &mut item_list)
            .or_report(&mut errors);
    }

    let idtracker = id_tracker::ExprIdTracker::new();
    let mut ctx = AstLoweringCtx {
        symtab,
        idtracker,
        pipeline_ctx: None,
    };

    for module_ast in &module_asts {
        visit_module_body(&mut item_list, &module_ast, &mut ctx).or_report(&mut errors);
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

    let executables_and_types = item_list
        .executables
        .iter()
        .filter_map(|(name, item)| match item {
            ExecutableItem::Entity(e) => {
                let mut type_state = typeinference::TypeState::new();

                if let Ok(()) = type_state
                    .visit_entity(&e, &frozen_symtab.symtab())
                    .report(&mut errors)
                {
                    all_types.extend(dump_types(
                        &type_state,
                        &item_list.types,
                        frozen_symtab.symtab(),
                    ));

                    Some((name, (item, type_state)))
                } else {
                    if opts.print_type_traceback {
                        type_state.print_equations();
                        println!("{}", format_trace_stack(&type_state.trace_stack))
                    }
                    None
                }
            }
            ExecutableItem::Pipeline(p) => {
                let mut type_state = typeinference::TypeState::new();

                type_state
                    .visit_pipeline(&p, &frozen_symtab.symtab())
                    .or_report(&mut errors)
                    .unwrap_or_else(|| {
                        if opts.print_type_traceback {
                            type_state.print_equations();
                            println!("{}", format_trace_stack(&type_state.trace_stack))
                        }
                    });

                Some((name, (item, type_state)))
            }
            ExecutableItem::EnumInstance { .. } => None,
            ExecutableItem::StructInstance { .. } => None,
            ExecutableItem::BuiltinEntity(_, _) => None,
            ExecutableItem::BuiltinPipeline(_, _) => None,
        })
        .collect::<HashMap<_, _>>();

    let mir_entities = spade_hir_lowering::monomorphisation::compile_items(
        &executables_and_types,
        &mut frozen_symtab,
        &mut idtracker,
        &item_list,
    );

    for mir in mir_entities {
        if let Some(MirOutput {
            mut mir,
            type_state,
            reg_name_map,
        }) = mir.or_report(&mut errors)
        {
            bumpy_mir_entities.push(mir.clone());

            let code = spade_mir::codegen::entity_code(&mut mir, &code.read().unwrap());

            mir_code.push(format!("{}", mir));

            flat_mir_entities.push(mir);

            module_code.push(code.to_string());

            all_types.extend(dump_types(
                &type_state,
                &item_list.types,
                frozen_symtab.symtab(),
            ));

            // Map the types of names generated by pipeline lowering
            for (new, original) in reg_name_map {
                let original_type = all_types
                    .get(&TypedExpression::Name(original))
                    .cloned()
                    .flatten();

                all_types.insert(TypedExpression::Name(new), original_type);
            }
        }
    }

    if let Some(outfile) = opts.outfile {
        std::fs::write(outfile, module_code.join("\n\n")).or_report(&mut errors);
    }
    if let Some(mir_output) = opts.mir_output {
        std::fs::write(mir_output, mir_code.join("\n\n")).or_report(&mut errors);
    }
    if let Some(type_dump_file) = opts.type_dump_file {
        match ron::to_string(&all_types) {
            Ok(encoded_type_info) => {
                std::fs::write(type_dump_file, encoded_type_info).or_report(&mut errors);
            }
            Err(e) => {
                println!("Failed to encode type info as RON {:?}", e)
            }
        }
    }

    if errors.failed {
        Err(())
    } else {
        Ok(Artefacts {
            bumpy_mir_entities,
            flat_mir_entities,
        })
    }
}
