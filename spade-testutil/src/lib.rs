use std::path::PathBuf;

use logos::Logos;

use spade_ast_lowering::{global_symbols, id_tracker::IdTracker, symbol_table, visit_entity};
use spade_common::{
    error_reporting::CompilationError,
    location_info::{Loc, WithLocation},
};
use spade_hir::{self as hir, NameID};
use spade_parser::{self as parser, ast, lexer};
use spade_typeinference::{self as typeinference, TypeState};

pub struct ProcessedEntity {
    pub entity: hir::Entity,
    pub type_state: TypeState,
}

pub fn parse_typecheck_entity<'a>(input: &str) -> ProcessedEntity {
    let mut entities = parse_typecheck_module_body(input);

    if entities.is_empty() {
        panic!("No entities found");
    } else if entities.len() > 1 {
        panic!("Found multiple entities");
    } else {
        entities.pop().unwrap()
    }
}

pub fn parse_typecheck_module_body(input: &str) -> Vec<ProcessedEntity> {
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

    let mut symtab = symbol_table::SymbolTable::new();
    spade_builtins::populate_symtab(&mut symtab);
    for item in &module_ast.members {
        try_or_report!(global_symbols::visit_item(item, &ast::Path(vec![]), &mut symtab));
    }

    let mut idtracker = IdTracker::new();

    let mut entities = vec![];
    for item in &module_ast.members {
        match item {
            ast::Item::Entity(entity_ast) => {
                let hir = try_or_report!(visit_entity(
                    &entity_ast,
                    &ast::Path(vec![]),
                    &mut symtab,
                    &mut idtracker,
                ));

                let mut type_state = typeinference::TypeState::new();

                try_or_report!(type_state.visit_entity(&hir, &symtab));

                entities.push(ProcessedEntity {
                    entity: hir.inner,
                    type_state,
                })
            }
            ast::Item::TraitDef(_) => {
                todo!("Parse and typecheck trait definitions")
            }
        }
    }

    entities
}

pub fn name_id(id: u64, name: &str) -> Loc<NameID> {
    NameID(id, ast::Path::from_strs(&[name])).nowhere()
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
