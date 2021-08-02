use std::path::PathBuf;

use logos::Logos;

use spade_ast_lowering::{global_symbols, visit_module_body};
use spade_common::{error_reporting::CompilationError, id_tracker::IdTracker, name::Path};
use spade_hir::{
    symbol_table::{FrozenSymtab, SymbolTable},
    ItemList,
};
use spade_parser::{self as parser, lexer};
use spade_typeinference::{self as typeinference};
use spade_typeinference::{ProcessedEntity, ProcessedItem, ProcessedPipeline};
use typeinference::ProcessedItemList;

pub fn parse_typecheck_entity<'a>(input: &str) -> (ProcessedEntity, FrozenSymtab, ItemList) {
    let ParseTypececkResult {
        mut items_with_types,
        item_list,
        symtab,
    } = parse_typecheck_module_body(input);

    if items_with_types.executables.is_empty() {
        panic!("No entities items");
    } else if items_with_types.executables.len() > 1 {
        panic!("Found multiple items");
    } else {
        match items_with_types.executables.pop().unwrap() {
            ProcessedItem::Entity(e) => (e, symtab, item_list),
            ProcessedItem::Pipeline(_) => panic!("Found a pipeline, expected entity"),
            ProcessedItem::EnumInstance => panic!("Found enum instance, expected entity"),
        }
    }
}

pub fn parse_typecheck_pipeline<'a>(input: &str) -> (ProcessedPipeline, FrozenSymtab, ItemList) {
    let mut result = parse_typecheck_module_body(input);

    if result.items_with_types.executables.is_empty() {
        panic!("No items found");
    } else if result.items_with_types.executables.len() > 1 {
        panic!("Found multiple items");
    } else {
        match result.items_with_types.executables.pop().unwrap() {
            ProcessedItem::Pipeline(p) => (p, result.symtab, result.item_list),
            ProcessedItem::Entity(_) => panic!("Found entity, expected pipeline"),
            ProcessedItem::EnumInstance => panic!("Found enum instance, expected pipeline"),
        }
    }
}

pub struct ParseTypececkResult {
    pub items_with_types: ProcessedItemList,
    pub item_list: ItemList,
    pub symtab: FrozenSymtab,
}

pub fn parse_typecheck_module_body(input: &str) -> ParseTypececkResult {
    let mut parser = parser::Parser::new(lexer::TokenKind::lexer(&input));

    macro_rules! try_or_report {
        ($to_try:expr) => {
            match $to_try {
                Ok(result) => result,
                Err(e) => {
                    e.report(&PathBuf::new(), &input, true);
                    panic!("Aborting due to previous error")
                }
            }
        };
    }

    let module_ast = try_or_report!(parser.module_body());

    let mut symtab = SymbolTable::new();
    let mut item_list = ItemList::new();
    spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut item_list);
    try_or_report!(global_symbols::gather_symbols(
        &module_ast,
        &Path(vec![]),
        &mut symtab,
        &mut item_list
    ));

    let mut idtracker = IdTracker::new();

    let item_list = try_or_report!(visit_module_body(
        item_list,
        &module_ast,
        &Path(vec![]),
        &mut symtab,
        &mut idtracker
    ));

    let items = try_or_report!(typeinference::ProcessedItemList::typecheck(
        &item_list, &symtab
    ));

    ParseTypececkResult {
        items_with_types: items,
        item_list,
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
