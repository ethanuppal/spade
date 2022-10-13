use spade_common::{location_info::Loc, name::NameID};
use spade_diagnostics::Diagnostic;
use spade_types::ConcreteType;
use thiserror::Error;

use crate::usefulness::Witness;

#[derive(Error, Debug)]
pub enum Error {
    #[error("(Internal) Argument error")]
    ArgumentError(#[from] spade_hir::param_util::ArgumentError),
    #[error("concat size mismatch")]
    ConcatSizeMismatch {
        lhs: Loc<u64>,
        rhs: Loc<u64>,
        result: Loc<u64>,
        expected: u64,
    },
    #[error("Use of undefined identifier")]
    UndefinedVariable { name: Loc<NameID> },
    #[error("Use of value before it is ready")]
    UseBeforeReady {
        name: Loc<NameID>,
        // The number of stages left until the value is available
        unavailable_for: usize,
        // The absolute stage at which the variable is requested
        referenced_at_stage: usize,
    },
    #[error("Availability mismatch")]
    AvailabilityMismatch { prev: Loc<usize>, new: Loc<usize> },
    #[error("Generic builtin")]
    InstantiatingGenericBuiltin { loc: Loc<()>, head: Loc<()> },
    #[error("Missing patterns")]
    MissingPatterns {
        match_expr: Loc<()>,
        useful_branches: Vec<Witness>,
    },
    #[error("Refutable pattern")]
    RefutablePattern {
        pattern: Loc<()>,
        witnesses: Vec<Witness>,
        // The statement in which this binding occurs. (let, reg etc.)
        binding_kind: &'static str,
    },
    #[error("Port in register")]
    PortInRegister { loc: Loc<()>, ty: ConcreteType },
    #[error("Port in generic type")]
    PortInGenericType {
        loc: Loc<()>,
        param: NameID,
        actual: ConcreteType,
    },
    #[error("Unification error")]
    UnificationError(#[source] spade_typeinference::error::Error),

    #[error("Spade diagnostic")]
    SpadeDiagnostic(#[from] Diagnostic),
}
pub type Result<T> = std::result::Result<T, Error>;
