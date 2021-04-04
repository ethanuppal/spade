use spade_ast as ast;
use spade_common::{location_info::Loc, name::Identifier};
use spade_hir as hir;
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Clone)]
pub enum Error {
    #[error("Lookup error")]
    LookupError(#[from] crate::symbol_table::Error),
    #[error("Duplicate type variable")]
    DuplicateTypeVariable {
        found: Loc<Identifier>,
        previously: Loc<Identifier>,
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
        new: Loc<Identifier>,
        prev_loc: Loc<()>,
    },
    #[error("Entity has no argument named {name}")]
    NoSuchArgument {
        name: Loc<Identifier>,
        for_entity: Loc<hir::EntityHead>,
    },
    #[error("Missing arguments")]
    MissingArguments {
        missing: Vec<Identifier>,
        for_entity: Loc<hir::EntityHead>,
        at: Loc<()>,
    },
    #[error("Missing pipeline return")]
    MissingPipelineReturn { in_stage: Loc<hir::PipelineStage> },
    #[error("Pipelines must have at least one stage")]
    NoPipelineStages { pipeline: Loc<ast::Pipeline> },
    #[error("Incorrect stage count")]
    IncorrectStageCount {
        got: usize,
        expected: Loc<u128>,
        pipeline: Loc<ast::Pipeline>,
    },
    #[error("Early pipeline return")]
    EarlyPipelineReturn { expression: Loc<hir::Expression> },
}

pub type Result<T> = std::result::Result<T, Error>;
