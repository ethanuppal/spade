use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
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
    #[error("Uniqueness error")]
    UniquenessError(#[from] spade_hir::symbol_table::UniqueNameError),
    #[error("Argument error")]
    ArgumentError(#[from] spade_hir::param_util::ArgumentError),

    #[error("Spade diagnostic")]
    SpadeDiagnostic(#[from] spade_diagnostics::Diagnostic),
}

pub type Result<T> = std::result::Result<T, Error>;
