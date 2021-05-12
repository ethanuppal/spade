use std::path::PathBuf;

use logos::Logos;

use spade_ast as ast;
use spade_ast_lowering::{global_symbols, pipelines::visit_pipeline, visit_entity};
use spade_common::{error_reporting::CompilationError, id_tracker::IdTracker, name::Path};
use spade_hir::symbol_table::{FrozenSymtab, SymbolTable};
use spade_hir_lowering::{ProcessedEntity, ProcessedItem, ProcessedPipeline};
use spade_parser::{self as parser, lexer};
use spade_typeinference::{self as typeinference};

pub fn parse_typecheck_entity<'a>(input: &str) -> (ProcessedEntity, FrozenSymtab) {
    let ParseTypececkResult { mut items, symtab } = parse_typecheck_module_body(input);

    if items.is_empty() {
        panic!("No entities items");
    } else if items.len() > 1 {
        panic!("Found multiple items");
    } else {
        match items.pop().unwrap() {
            ProcessedItem::Entity(e) => (e, symtab),
            ProcessedItem::Pipeline(_) => panic!("Found a pipeline, expected entity"),
        }
    }
}

pub fn parse_typecheck_pipeline<'a>(input: &str) -> (ProcessedPipeline, FrozenSymtab) {
    let mut result = parse_typecheck_module_body(input);

    if result.items.is_empty() {
        panic!("No items found");
    } else if result.items.len() > 1 {
        panic!("Found multiple items");
    } else {
        match result.items.pop().unwrap() {
            ProcessedItem::Pipeline(p) => (p, result.symtab),
            ProcessedItem::Entity(_) => panic!("Found entity, expected pipeline"),
        }
    }
}

pub struct ParseTypececkResult {
    pub items: Vec<ProcessedItem>,
    pub symtab: FrozenSymtab,
}

pub fn parse_typecheck_module_body(input: &str) -> ParseTypececkResult {
    let mut parser = parser::Parser::new(lexer::TokenKind::lexer(&input));

    macro_rules! try_or_report {
        ($to_try:expr) => {
            match $to_try {
                Ok(result) => result,
                Err(e) => {
                    e.report(&PathBuf::new(), &"", true);
                    panic!("Aborting due to previous error")
                }
            }
        };
    }

    let module_ast = try_or_report!(parser.module_body());

    let mut symtab = SymbolTable::new();
    spade_ast_lowering::builtins::populate_symtab(&mut symtab);
    for item in &module_ast.members {
        try_or_report!(global_symbols::visit_item(item, &Path(vec![]), &mut symtab));
    }

    let mut idtracker = IdTracker::new();

    let mut items = vec![];
    for item in &module_ast.members {
        match item {
            ast::Item::Entity(entity_ast) => {
                let hir = try_or_report!(visit_entity(
                    &entity_ast,
                    &Path(vec![]),
                    &mut symtab,
                    &mut idtracker,
                ));

                let mut type_state = typeinference::TypeState::new();

                try_or_report!(type_state.visit_entity(&hir, &symtab));

                items.push(ProcessedItem::Entity(ProcessedEntity {
                    entity: hir.inner,
                    type_state,
                }))
            }
            ast::Item::TraitDef(_) => {
                todo!("Parse and typecheck trait definitions")
            }
            ast::Item::Type(_) => {
                // Types are invisible at this level
            }
            ast::Item::Pipeline(pipeline_ast) => {
                println!("visiting pipeline");
                let hir = try_or_report!(visit_pipeline(
                    &pipeline_ast,
                    &Path(vec![]),
                    &mut symtab,
                    &mut idtracker,
                ));

                let mut type_state = typeinference::TypeState::new();

                try_or_report!(type_state.visit_pipeline(&hir, &symtab));

                items.push(ProcessedItem::Pipeline(ProcessedPipeline {
                    pipeline: hir.inner,
                    type_state,
                }));
            }
        }
    }

    ParseTypececkResult {
        items,
        symtab: symtab.freeze(),
    }
}

#[macro_export]
macro_rules! assert_matches {
    ($lhs:expr, $pattern:pat) => {
        if let $pattern = $lhs {
        } else {
            panic!("{:?} does not match the specified pattern", $lhs)
        }
    };
}
