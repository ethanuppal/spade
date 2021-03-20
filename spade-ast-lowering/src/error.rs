use spade_common::location_info::Loc;
use spade_hir as hir;
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
    #[error("Argument list lenght mismatch, expected {expected} got {got}")]
    ArgumentListLenghtMismatch {
        expected: usize,
        got: usize,
        at: Loc<()>,
        for_entity: Loc<()>,
    },
    #[error("{new} was bound more than once")]
    DuplicateNamedBindings {
        new: Loc<ast::Identifier>,
        prev_loc: Loc<()>,
    },
    #[error("Entity has no argument named {name}")]
    NoSuchArgument {
        name: Loc<ast::Identifier>,
        for_entity: Loc<hir::EntityHead>,
    },
    #[error("Missing arguments")]
    MissingArguments {
        missing: Vec<ast::Identifier>,
        for_entity: Loc<hir::EntityHead>,
        at: Loc<()>,
    },
}

pub type Result<T> = std::result::Result<T, Error>;
