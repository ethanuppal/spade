use spade_common::location_info::Loc;
use spade_hir::NameID;
use spade_parser::ast;
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Clone)]
pub enum Error {
    #[error("Lookup error")]
    LookupError(#[from] crate::symbol_table::Error),
    #[error("Duplicate type variable")]
    DuplicateTypeVariable {
        found: Loc<ast::Identifier>,
        previously: Loc<ast::Identifier>,
    },
    #[error("Argument list lenght missmatch, expected {expected} got {got}")]
    ArgumentListLenghtMissmatch {
        expected: usize,
        got: usize,
        at: Loc<()>,
        for_entity: Loc<()>,
    },
}

pub type Result<T> = std::result::Result<T, Error>;
