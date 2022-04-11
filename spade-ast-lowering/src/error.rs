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
    LookupError(#[from] spade_hir::symbol_table::LookupError),
    #[error("Declaration error")]
    DeclarationError(#[from] spade_hir::symbol_table::DeclarationError),
    #[error("Duplicate type variable")]
    DuplicateTypeVariable {
        found: Loc<Identifier>,
        previously: Loc<Identifier>,
    },
    #[error("Duplicate argument")]
    DuplicateArgument {
        new: Loc<Identifier>,
        prev: Loc<Identifier>,
    },
    #[error("Duplicate enum option")]
    DuplicateEnumOption {
        new: Loc<Identifier>,
        prev: Loc<Identifier>,
    },
    #[error("Argument list length mismatch, expected {expected} got {got}")]
    ArgumentListLenghtMismatch {
        expected: usize,
        got: usize,
        at: Loc<()>,
    },
    #[error("Pattern list length mismatch, expected {expected} arguments, got {got}")]
    PatternListLengthMismatch {
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
    #[error("Incorrect stage count")]
    IncorrectStageCount {
        got: usize,
        expected: Loc<u128>,
        pipeline: Loc<ast::Pipeline>,
    },
    #[error("Early pipeline return")]
    EarlyPipelineReturn { expression: Loc<hir::Expression> },
    #[error("Pipeline depth mismatch")]
    PipelineDepthMismatch { expected: usize, got: Loc<u128> },
    #[error("Pipeline missing clock")]
    MissingPipelineClock { at_loc: Loc<()> },
    #[error("Referencing negative pipeline stage")]
    NegativePipelineReference {
        at_loc: Loc<()>,
        absolute_stage: i64,
    },
    #[error("Referencing out of bounds pipeline stage")]
    PipelineStageOOB {
        at_loc: Loc<()>,
        absolute_stage: usize,
        num_stages: usize,
    },
    #[error("Undefined pipeline stage")]
    UndefinedPipelineStage { stage: Loc<Identifier> },
    #[error("Undefined pipeline stage")]
    DuplicatePipelineStage {
        stage: Loc<Identifier>,
        previous: Loc<Identifier>,
    },
    #[error("Multiple labels for same stage")]
    MultipleStageLabels {
        new: Loc<Identifier>,
        previous: Loc<Identifier>,
    },

    #[error("Declarations can only be defined by registers")]
    DeclarationOfNonReg {
        at: Loc<Identifier>,
        declaration_location: Loc<()>,
    },

    #[error("Variable declared but not defined")]
    UndefinedDeclaration(Loc<Identifier>),

    #[error("Redefinition of declaration")]
    RedefinitionOfDeclaration {
        at: Loc<Identifier>,
        previous: Loc<()>,
    },

    // Type related errors
    #[error("Generic parameters for generic name")]
    GenericsGivenForGeneric {
        at_loc: Loc<()>,
        for_type: Loc<Path>,
    },
}

pub type Result<T> = std::result::Result<T, Error>;
