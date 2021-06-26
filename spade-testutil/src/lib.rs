use std::path::PathBuf;

use logos::Logos;

use spade_ast as ast;
use spade_ast_lowering::{
    global_symbols, pipelines::visit_pipeline, visit_entity, visit_module_body,
};
use spade_common::{error_reporting::CompilationError, id_tracker::IdTracker, name::Path};
use spade_hir::{
    symbol_table::{FrozenSymtab, SymbolTable},
    ExecutableItem,
};
use spade_parser::{self as parser, lexer};
use spade_typeinference::{self as typeinference};
use spade_typeinference::{ProcessedEntity, ProcessedItem, ProcessedPipeline};
use typeinference::ItemListWithTypes;

pub fn parse_typecheck_entity<'a>(input: &str) -> (ProcessedEntity, FrozenSymtab) {
    let ParseTypececkResult { mut items, symtab } = parse_typecheck_module_body(input);

    if items.executables.is_empty() {
        panic!("No entities items");
    } else if items.executables.len() > 1 {
        panic!("Found multiple items");
    } else {
        match items.executables.pop().unwrap() {
            ProcessedItem::Entity(e) => (e, symtab),
            ProcessedItem::Pipeline(_) => panic!("Found a pipeline, expected entity"),
        }
    }
}

pub fn parse_typecheck_pipeline<'a>(input: &str) -> (ProcessedPipeline, FrozenSymtab) {
    let mut result = parse_typecheck_module_body(input);

    if result.items.executables.is_empty() {
        panic!("No items found");
    } else if result.items.executables.len() > 1 {
        panic!("Found multiple items");
    } else {
        match result.items.executables.pop().unwrap() {
            ProcessedItem::Pipeline(p) => (p, result.symtab),
            ProcessedItem::Entity(_) => panic!("Found entity, expected pipeline"),
        }
    }
}

pub struct ParseTypececkResult {
    pub items: ItemListWithTypes,
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
    try_or_report!(global_symbols::gather_symbols(
        &module_ast,
        &Path(vec![]),
        &mut symtab
    ));

    let mut idtracker = IdTracker::new();

    let item_list = try_or_report!(visit_module_body(
        &module_ast,
        &Path(vec![]),
        &mut symtab,
        &mut idtracker
    ));

    let items = try_or_report!(typeinference::ItemListWithTypes::typecheck(
        item_list, &symtab
    ));

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
