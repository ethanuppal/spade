pub mod compiler_state;
mod name_dump;
pub mod namespaced_file;

use codespan_reporting::term::termcolor::Buffer;
use compiler_state::CompilerState;
use logos::Logos;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::RwLock;
use thiserror::Error;
use tracing::Level;

use spade_ast::ModuleBody;
use spade_ast_lowering::{
    ensure_unique_anonymous_traits, global_symbols, visit_module_body, Context as AstLoweringCtx,
};
use spade_common::id_tracker;
use spade_common::name::Path as SpadePath;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};
use spade_hir::symbol_table::{FrozenSymtab, SymbolTable};
use spade_hir::{ExecutableItem, ItemList};
use spade_hir_lowering::error::Error as HirLoweringError;
use spade_hir_lowering::monomorphisation::MirOutput;
use spade_hir_lowering::NameSourceMap;
pub use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference as typeinference;
use spade_typeinference::dump::dump_types;
use spade_typeinference::equation::TypedExpression;
use spade_typeinference::trace_stack::format_trace_stack;
use spade_types::ConcreteType;

pub struct Opt<'b> {
    pub error_buffer: &'b mut Buffer,
    pub outfile: Option<PathBuf>,
    pub mir_output: Option<PathBuf>,
    pub type_dump_file: Option<PathBuf>,
    pub state_dump_file: Option<PathBuf>,
    pub item_list_file: Option<PathBuf>,
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
    TypeInferenceError(#[from] spade_typeinference::error::Error),

    #[error("io error")]
    IoError(#[from] std::io::Error),
}

trait Reportable<T> {
    /// Report the error, then discard the error, returning Some if it was Ok
    fn or_report(self, errors: &mut ErrorHandler) -> Option<T>;

    // Report the error and continue without modifying the result
    fn report(self, errors: &mut ErrorHandler) -> Self;
}

impl<T, E> Reportable<T> for Result<T, E>
where
    E: CompilationError,
{
    fn report(self, errors: &mut ErrorHandler) -> Self {
        if let Err(e) = &self {
            errors.report(e);
        }
        self
    }

    fn or_report(self, errors: &mut ErrorHandler) -> Option<T> {
        self.report(errors).ok()
    }
}

pub struct ErrorHandler<'a> {
    pub failed: bool,
    pub error_buffer: &'a mut Buffer,
    pub diag_handler: DiagHandler,
    /// Using a RW lock here is just a lazy way of managing the ownership of code to
    /// be able to report errors even while modifying CodeBundle
    pub code: Rc<RwLock<CodeBundle>>,
}

impl<'a> ErrorHandler<'a> {
    fn report(&mut self, err: &impl CompilationError) {
        self.failed = true;
        err.report(
            self.error_buffer,
            &self.code.read().unwrap(),
            &mut self.diag_handler,
        );
    }
}

pub struct ModuleNamespace {
    pub namespace: SpadePath,
    pub base_namespace: SpadePath,
}

pub struct Artefacts {
    // MIR entities before aliases have been flattened
    pub bumpy_mir_entities: Vec<spade_mir::Entity>,
    // MIR entities after flattening
    pub flat_mir_entities: Vec<spade_mir::Entity>,
}

struct CodegenArtefacts {
    bumpy_mir_entities: Vec<spade_mir::Entity>,
    flat_mir_entities: Vec<spade_mir::Entity>,
    module_code: Vec<String>,
    mir_code: Vec<String>,
}

#[tracing::instrument(skip_all)]
pub fn compile(
    sources: Vec<(ModuleNamespace, String, String)>,
    opts: Opt,
    diag_handler: DiagHandler,
) -> Result<Artefacts, ()> {
    let mut symtab = SymbolTable::new();
    let mut item_list = ItemList::new();

    spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut item_list);

    let code = Rc::new(RwLock::new(CodeBundle::new("".to_string())));
    let mut errors = ErrorHandler {
        failed: false,
        error_buffer: opts.error_buffer,
        diag_handler,
        code: Rc::clone(&code),
    };

    let module_asts = parse(
        sources,
        Rc::clone(&code),
        opts.print_parse_traceback,
        &mut errors,
    );

    if errors.failed {
        return Err(());
    }

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut symtab, &mut |symtab| {
            global_symbols::gather_types(module_ast, symtab).or_report(&mut errors);
        })
    }

    if errors.failed {
        return Err(());
    }

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut symtab, &mut |symtab| {
            global_symbols::gather_symbols(module_ast, symtab, &mut item_list)
                .or_report(&mut errors);
        })
    }

    if errors.failed {
        return Err(());
    }

    let idtracker = id_tracker::ExprIdTracker::new();
    let impl_idtracker = id_tracker::ImplIdTracker::new();
    let mut ctx = AstLoweringCtx {
        symtab,
        idtracker,
        impl_idtracker,
        pipeline_ctx: None,
    };

    lower_ast(&module_asts, &mut item_list, &mut ctx, &mut errors);

    let AstLoweringCtx {
        symtab,
        mut idtracker,
        impl_idtracker,
        pipeline_ctx: _,
    } = ctx;

    for e in ensure_unique_anonymous_traits(&item_list) {
        errors.report(&e)
    }

    // If we have errors during AST lowering, we need to early return becausue the
    // items have already been added to the symtab when they are detected. Further compilation
    // relies on all names in the symtab being in the item list, which will not be the
    // case if we failed to compile some
    if errors.failed {
        return Err(());
    }

    let mut frozen_symtab = symtab.freeze();
    let mut all_types = HashMap::new();

    let type_inference_ctx = typeinference::Context {
        symtab: &frozen_symtab.symtab(),
        items: &item_list,
    };

    let executables_and_types = item_list
        .executables
        .iter()
        .filter_map(|(name, item)| match item {
            ExecutableItem::Entity(e) => {
                let mut type_state = typeinference::TypeState::new();

                if let Ok(()) = type_state
                    .visit_entity(e, &type_inference_ctx)
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
                    .visit_pipeline(p, &type_inference_ctx)
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

    if errors.failed {
        return Err(());
    }

    let mut name_source_map = NameSourceMap::new();
    let mir_entities = spade_hir_lowering::monomorphisation::compile_items(
        &executables_and_types,
        &mut frozen_symtab,
        &mut idtracker,
        &mut name_source_map,
        &item_list,
        &mut errors.diag_handler,
    );

    let CodegenArtefacts {
        bumpy_mir_entities,
        flat_mir_entities,
        module_code,
        mir_code,
    } = codegen(
        mir_entities,
        Rc::clone(&code),
        &item_list,
        &frozen_symtab,
        &mut all_types,
        &mut errors,
    );

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
    if let Some(item_list_file) = opts.item_list_file {
        let list = name_dump::list_names(&item_list);

        match ron::to_string(&list) {
            Ok(encoded) => {
                std::fs::write(item_list_file, &encoded).or_report(&mut errors);
            }
            Err(e) => {
                println!("Failed to encode item list as RON {e:?}")
            }
        }
    }
    if let Some(state_dump_file) = opts.state_dump_file {
        let state = CompilerState {
            code: code.read().unwrap().dump_files(),
            symtab: frozen_symtab,
            idtracker,
            impl_idtracker,
            item_list,
            name_source_map,
        };
        match ron::to_string(&state) {
            Ok(encoded) => {
                std::fs::write(state_dump_file, encoded).or_report(&mut errors);
            }
            Err(e) => {
                println!("Failed to encode compiler state info as RON {:?}", e)
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

fn do_in_namespace(
    namespace: &ModuleNamespace,
    symtab: &mut SymbolTable,
    to_do: &mut dyn FnMut(&mut SymbolTable),
) {
    for ident in &namespace.namespace.0 {
        // NOTE: These identifiers do not have the correct file_id. However,
        // as far as I know, they will never be part of an error, so we *should*
        // be safe.
        symtab.push_namespace(ident.clone());
    }
    symtab.set_base_namespace(namespace.base_namespace.clone());
    to_do(symtab);
    symtab.set_base_namespace(SpadePath(vec![]));
    for _ in &namespace.namespace.0 {
        symtab.pop_namespace();
    }
}

#[tracing::instrument(skip_all)]
fn parse(
    sources: Vec<(ModuleNamespace, String, String)>,
    code: Rc<RwLock<CodeBundle>>,
    print_parse_traceback: bool,
    errors: &mut ErrorHandler,
) -> Vec<(ModuleNamespace, ModuleBody)> {
    let mut module_asts = vec![];
    // Read and parse input files
    for (namespace, name, content) in sources {
        let _span = tracing::span!(Level::TRACE, "source", ?name).entered();
        let file_id = code.write().unwrap().add_file(name, content.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&content), file_id);

        let result = parser
            .top_level_module_body()
            .map_err(|e| {
                if print_parse_traceback {
                    println!("{}", spade_parser::format_parse_stack(&parser.parse_stack));
                };
                e
            })
            .or_report(errors);

        if let Some(ast) = result {
            module_asts.push((namespace, ast))
        }
    }

    module_asts
}

#[tracing::instrument(skip_all)]
fn lower_ast(
    module_asts: &[(ModuleNamespace, ModuleBody)],
    item_list: &mut ItemList,
    ctx: &mut AstLoweringCtx,
    errors: &mut ErrorHandler,
) {
    for (namespace, module_ast) in module_asts {
        // Can not be done by do_in_namespace because the symtab has been moved
        // into `ctx`
        for ident in &namespace.namespace.0 {
            // NOTE: These identifiers do not have the correct file_id. However,
            // as far as I know, they will never be part of an error, so we *should*
            // be safe.
            ctx.symtab.push_namespace(ident.clone());
        }
        ctx.symtab
            .set_base_namespace(namespace.base_namespace.clone());
        visit_module_body(item_list, module_ast, ctx).or_report(errors);
        ctx.symtab.set_base_namespace(SpadePath(vec![]));
        for _ in &namespace.namespace.0 {
            ctx.symtab.pop_namespace();
        }
    }
}

#[tracing::instrument(skip_all)]
fn codegen(
    mir_entities: Vec<Result<MirOutput, HirLoweringError>>,
    code: Rc<RwLock<CodeBundle>>,
    item_list: &ItemList,
    frozen_symtab: &FrozenSymtab,
    all_types: &mut HashMap<TypedExpression, Option<ConcreteType>>,
    errors: &mut ErrorHandler,
) -> CodegenArtefacts {
    let mut bumpy_mir_entities = vec![];
    let mut flat_mir_entities = vec![];
    let mut module_code = vec![];
    let mut mir_code = vec![];

    for mir in mir_entities {
        if let Some(MirOutput {
            mut mir,
            type_state,
            reg_name_map,
        }) = mir.or_report(errors)
        {
            bumpy_mir_entities.push(mir.clone());

            let code =
                spade_mir::codegen::entity_code(&mut mir, &Some(code.read().unwrap().clone()));

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

    CodegenArtefacts {
        bumpy_mir_entities,
        flat_mir_entities,
        module_code,
        mir_code,
    }
}
