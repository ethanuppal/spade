use std::path::PathBuf;

use logos::Logos;

use spade_ast_lowering::{
    error_reporting::report_semantic_error, global_symbols, id_tracker::IdTracker, symbol_table,
    visit_entity,
};
use spade_common::location_info::{Loc, WithLocation};
use spade_hir::{self as hir, NameID};
use spade_parser::{self as parser, ast, error_reporting::report_parse_error, lexer};
use spade_typeinference::{
    self as typeinference, error_reporting::report_typeinference_error, TypeState,
};

pub struct ProcessedEntity {
    pub entity: hir::Entity,
    pub type_state: TypeState,
}

pub fn parse_typecheck_entity<'a>(input: &str) -> ProcessedEntity {
    let mut parser = parser::Parser::new(lexer::TokenKind::lexer(&input));

    let entity_ast = match parser.entity() {
        Ok(Some(v)) => v,
        Ok(None) => panic!("No parse error but code contained no entity"),
        Err(e) => {
            report_parse_error(&PathBuf::from(""), &input, e, false);
            panic!("Parse error")
        }
    };

    let mut symtab = symbol_table::SymbolTable::new();
    spade_builtins::populate_symtab(&mut symtab);
    match global_symbols::visit_entity(&entity_ast, &ast::Path(vec![]), &mut symtab) {
        Ok(_) => (),
        Err(e) => {
            report_semantic_error(&PathBuf::from(""), &input, e, false);
            panic!("Semantic error")
        }
    }
    let mut idtracker = IdTracker::new();
    let hir = match visit_entity(&entity_ast, &ast::Path(vec![]), &mut symtab, &mut idtracker) {
        Ok(v) => v,
        Err(e) => {
            report_semantic_error(&PathBuf::from(""), &input, e, false);
            panic!("Semantic error")
        }
    };

    let mut type_state = typeinference::TypeState::new();

    match type_state.visit_entity(&hir, &symtab) {
        Ok(()) => {}
        Err(e) => {
            println!(
                "Type check trace:\n{}",
                typeinference::format_trace_stack(&type_state.trace_stack)
            );
            report_typeinference_error(&PathBuf::from(""), &input, e, false);
            panic!("Type error")
        }
    }

    ProcessedEntity {
        entity: hir.inner,
        type_state,
    }
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
