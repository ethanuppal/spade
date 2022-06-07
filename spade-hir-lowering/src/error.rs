use spade_common::{location_info::Loc, name::NameID};
use spade_hir::Expression;
use spade_typeinference::equation::TypeVar;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("using generic type")]
    UsingGenericType { expr: Loc<Expression>, t: TypeVar },
    #[error("cast to larger")]
    CastToLarger { from: Loc<u64>, to: Loc<u64> },
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
    InstanciatingGenericBuiltin { loc: Loc<()>, head: Loc<()> },
    #[error("Unification error")]
    UnificationError(#[source] spade_typeinference::result::Error),
}
pub type Result<T> = std::result::Result<T, Error>;
