use std::path::PathBuf;

use logos::Logos;

use crate::hir;
use crate::location_info::{Loc, WithLocation};
use crate::{
    ast, semantic_analysis, semantic_analysis::visit_entity, typeinference,
    typeinference::TypeState,
};

use crate::error_reporting;
use crate::lexer;
use crate::parser;
use crate::symbol_table;

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
            error_reporting::report_parse_error(&PathBuf::from(""), &input, e);
            panic!("Parse error")
        }
    };

    let mut symtab = symbol_table::SymbolTable::new();
    let mut idtracker = semantic_analysis::IdTracker::new();
    let hir = match visit_entity(&entity_ast.inner, &mut symtab, &mut idtracker) {
        Ok(v) => v,
        Err(e) => {
            error_reporting::report_semantic_error(&PathBuf::from(""), &input, e);
            panic!("Semantic error")
        }
    };

    let mut type_state = typeinference::TypeState::new();

    match type_state.visit_entity(&hir) {
        Ok(()) => {}
        Err(e) => {
            error_reporting::report_typeinference_error(&PathBuf::from(""), &input, e);
            panic!("Type error")
        }
    }

    ProcessedEntity {
        entity: hir,
        type_state,
    }
}

pub fn ast_ident(name: &str) -> Loc<ast::Identifier> {
    ast::Identifier(name.to_string()).nowhere()
}

pub fn hir_ident(name: &str) -> Loc<hir::Identifier> {
    hir::Identifier::Named(name.to_string()).nowhere()
}

pub fn ast_path(name: &str) -> Loc<ast::Path> {
    ast::Path(vec![ast_ident(name)]).nowhere()
}
pub fn hir_path(name: &str) -> Loc<hir::Path> {
    hir::Path(vec![hir_ident(name).inner]).nowhere()
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

#[macro_export]
macro_rules! assert_same_code {
    ($got:expr, $expected:expr) => {
        if $got != $expected {
            println!("got:\n{}", $got);
            println!("==============================================");
            println!("expected:\n{}", $expected);
            println!("==============================================");
            println!("{}", prettydiff::diff_chars($got, $expected));
            panic!("Code missmatch")
        }
    };
}
