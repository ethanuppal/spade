use spade_ast as ast;
use spade_common::{location_info::Loc, name::Identifier};
use spade_diagnostics::Diagnostic;
use spade_hir as hir;
use thiserror::Error;

pub enum ItemKind {
    Pipeline,
    Entity,
}

pub(crate) struct WireOfPort {
    pub(crate) full_type: Loc<()>,
    pub(crate) inner_type: Loc<()>,
}

impl From<WireOfPort> for Diagnostic {
    fn from(err: WireOfPort) -> Self {
        Diagnostic::error(err.full_type, "Can't create a wire of ports")
            .primary_label("This can't be a wire")
            .secondary_label(err.inner_type, "Because this is a port")
    }
}

pub(crate) struct PatternListLengthMismatch {
    pub(crate) expected: usize,
    pub(crate) got: usize,
    pub(crate) at: Loc<()>,
}

impl From<PatternListLengthMismatch> for Diagnostic {
    fn from(err: PatternListLengthMismatch) -> Self {
        Diagnostic::error(
            err.at,
            format!("Expected {} arguments, got {}", err.expected, err.got),
        )
        .primary_label(format!("Expected {} arguments here", err.expected))
    }
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum Error {
    #[error("Lookup error")]
    LookupError(#[from] spade_hir::symbol_table::LookupError),
    #[error("Declaration error")]
    DeclarationError(#[from] spade_hir::symbol_table::DeclarationError),
    #[error("Uniqueness error")]
    UniquenessError(#[from] spade_hir::symbol_table::UniqueNameError),
    #[error("Argument error")]
    ArgumentError(#[from] spade_hir::param_util::ArgumentError),
    #[error("Duplicate type variable")]
    DuplicateTypeVariable {
        found: Loc<Identifier>,
        previously: Loc<Identifier>,
    },
    #[error("Incorrect stage count")]
    IncorrectStageCount {
        got: usize,
        expected: Loc<u128>,
        pipeline: Loc<ast::Pipeline>,
    },
    #[error("Early pipeline return")]
    EarlyPipelineReturn { expression: Loc<hir::Expression> },
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
    #[error("Duplicate pipeline stage")]
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

    #[error("Match block has no arms")]
    NoMatchArms { body: Loc<()> },

    #[error("Spade diagnostic")]
    SpadeDiagnostic(#[from] spade_diagnostics::Diagnostic),
}

pub type Result<T> = std::result::Result<T, Error>;
