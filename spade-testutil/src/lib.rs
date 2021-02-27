use std::path::PathBuf;

use logos::Logos;

use spade_ast_lowering::{id_tracker::IdTracker, symbol_table, visit_entity};
use spade_common::location_info::{Loc, WithLocation};
use spade_error_reporting as error_reporting;
use spade_hir::{self as hir, NameID};
use spade_parser::{self as parser, ast, lexer};
use spade_typeinference::{self as typeinference, TypeState};

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
            error_reporting::report_parse_error(&PathBuf::from(""), &input, e, false);
            panic!("Parse error")
        }
    };

    let mut symtab = symbol_table::SymbolTable::new();
    spade_builtins::populate_symtab(&mut symtab);
    let mut idtracker = IdTracker::new();
    let hir = match visit_entity(&entity_ast, &mut symtab, &mut idtracker) {
        Ok(v) => v,
        Err(e) => {
            error_reporting::report_semantic_error(&PathBuf::from(""), &input, e, false);
            panic!("Semantic error")
        }
    };

    let mut type_state = typeinference::TypeState::new();

    match type_state.visit_entity(&hir) {
        Ok(()) => {}
        Err(e) => {
            println!(
                "Type check trace:\n{}",
                typeinference::format_trace_stack(&type_state.trace_stack)
            );
            error_reporting::report_typeinference_error(&PathBuf::from(""), &input, e, false);
            panic!("Type error")
        }
    }

    ProcessedEntity {
        entity: hir.inner,
        type_state,
    }
}

pub fn ast_ident(name: &str) -> Loc<ast::Identifier> {
    ast::Identifier(name.to_string()).nowhere()
}

pub fn ast_path(name: &str) -> Loc<ast::Path> {
    ast::Path(vec![ast_ident(name)]).nowhere()
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

#[macro_export]
macro_rules! assert_same_code {
    ($got:expr, $expected:expr) => {
        if $got != $expected {
            println!("{}:\n{}", "got".red(), $got);
            println!("{}", "==============================================".red());
            println!("{}:\n{}", "expected".green(), $expected);
            println!(
                "{}",
                "==============================================".green()
            );
            println!("{}", prettydiff::diff_chars($got, $expected));
            println!(
                "{}",
                "==============================================".yellow()
            );
            panic!("Code missmatch")
        }
    };
}