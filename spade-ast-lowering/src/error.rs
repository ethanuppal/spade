use spade_ast as ast;
use spade_common::{
    location_info::Loc,
    name::{Identifier, Path},
};
use spade_hir as hir;
use thiserror::Error;

pub enum ItemKind {
    Pipeline,
    Entity,
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum Error {
    #[error("Lookup error")]
    LookupError(#[from] spade_hir::symbol_table::Error),
    #[error("Duplicate type variable")]
    DuplicateTypeVariable {
        found: Loc<Identifier>,
        previously: Loc<Identifier>,
    },
    #[error("Argument list length mismatch, expected {expected} got {got}")]
    ArgumentListLenghtMismatch {
        expected: usize,
        got: usize,
        at: Loc<()>,
    },
    #[error("{new} was bound more than once")]
    DuplicateNamedBindings {
        new: Loc<Identifier>,
        prev_loc: Loc<()>,
    },
    #[error("No argument named {name}")]
    NoSuchArgument { name: Loc<Identifier> },
    #[error("Missing arguments")]
    MissingArguments {
        missing: Vec<Identifier>,
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
    #[error("Pipeline depth mismatch")]
    PipelineDepthMissmatch { expected: usize, got: Loc<u128> },
    #[error("Pipeline missing clock")]
    MissingPipelineClock { at_loc: Loc<()> },

    // Type related errors
    #[error("Generic parameters for generic name")]
    GenericsGivenForGeneric {
        at_loc: Loc<()>,
        for_type: Loc<Path>,
    },
}

pub type Result<T> = std::result::Result<T, Error>;
