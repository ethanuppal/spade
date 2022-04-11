use spade_common::{location_info::Loc, name::NameID};
use spade_hir::Expression;
use spade_typeinference::equation::TypeVar;
use thiserror::Error;

// TODO better error descriptions that uses fields
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
        // Amount of cycles left until the value is available
        available_in: usize,
    },
}
pub type Result<T> = std::result::Result<T, Error>;
