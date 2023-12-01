use itertools::Itertools;
use num::BigInt;
use spade_diagnostics::Diagnostic;
use spade_hir::{param_util::ArgumentError, UnitHead};
use thiserror::Error;

use crate::constraints::ConstraintSource;

use super::equation::{TypeVar, TypedExpression};
use spade_common::{
    location_info::{FullSpan, Loc, WithLocation},
    name::{Identifier, NameID},
};

/// A trace of a unification error. The `failing` field indicates which exact type failed to unify,
/// while the `inside` is the "top level" type which failed to unify if it's not the same as
/// failing.
///
/// For example, if unifying `int<7>` with `int<8>`, this would be `failing: 8, inside: int<8>`
/// while if unifying `int<7>` with `bool`, inside would be `None`
#[derive(Debug, PartialEq, Clone)]
pub struct UnificationTrace {
    pub failing: TypeVar,
    pub inside: Option<TypeVar>,
}
impl WithLocation for UnificationTrace {}
impl std::fmt::Display for UnificationTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.outer())
    }
}
impl UnificationTrace {
    pub fn new(failing: TypeVar) -> Self {
        Self {
            failing,
            inside: None,
        }
    }

    pub fn outer(&self) -> &TypeVar {
        self.inside.as_ref().unwrap_or(&self.failing)
    }
}
pub trait UnificationErrorExt<T>: Sized {
    fn add_context(
        self,
        got: TypeVar,
        expected: TypeVar,
    ) -> std::result::Result<T, UnificationError>;

    /// Creates a diagnostic with a generic type mismatch error
    fn into_default_diagnostic(
        self,
        unification_point: impl Into<FullSpan>,
    ) -> std::result::Result<T, Diagnostic> {
        self.into_diagnostic(unification_point, |d, _| d)
    }

    /// Creates a diagnostic from the unification error that will be emitted at the unification
    /// point, unless the unification error was caused by constraints, at which point
    /// the source of those constraints will be the location of the error.
    /// If trait constraints were not met, a default message will be provided at the unification
    /// point
    fn into_diagnostic<F>(
        self,
        unification_point: impl Into<FullSpan>,
        message: F,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic;
}
impl<T> UnificationErrorExt<T> for std::result::Result<T, UnificationError> {
    fn add_context(
        self,
        got: TypeVar,
        expected: TypeVar,
    ) -> std::result::Result<T, UnificationError> {
        match self {
            Ok(val) => Ok(val),
            Err(UnificationError::Normal(TypeMismatch {
                e: mut old_e,
                g: mut old_g,
            })) => {
                old_e.inside.replace(expected);
                old_g.inside.replace(got);
                Err(UnificationError::Normal(TypeMismatch {
                    e: old_e,
                    g: old_g,
                }))
            }
            e @ Err(UnificationError::UnsatisfiedTraits(_, _)) => e,
            Err(
                UnificationError::FromConstraints { .. } | UnificationError::NegativeInteger { .. },
            ) => {
                panic!("Called add_context on a constraint based unfication error")
            }
        }
    }

    fn into_diagnostic<F>(
        self,
        unification_point: impl Into<FullSpan>,
        message: F,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic,
    {
        self.map_err(|e| match e {
            UnificationError::Normal(TypeMismatch { e, g }) => {
                let msg = format!("Expected type {e}, got {g}");
                let diag = Diagnostic::error(unification_point, msg)
                    .primary_label(format!("Expected {e}"));
                message(
                    diag,
                    TypeMismatch {
                        e: e.clone(),
                        g: g.clone(),
                    },
                )
                .type_error(
                    format!("{}", e.failing),
                    e.inside.map(|o| format!("{o}")),
                    format!("{}", g.failing),
                    g.inside.map(|o| format!("{o}")),
                )
            }
            UnificationError::UnsatisfiedTraits(var, impls) => {
                let impls_str = if impls.len() >= 2 {
                    format!(
                        "{} and {}",
                        impls[0..impls.len() - 1]
                            .iter()
                            .map(|i| format!("{i}"))
                            .join(", "),
                        impls[impls.len() - 1]
                    )
                } else {
                    format!("{}", impls[0])
                };
                let short_msg = format!("{var} does not impl {impls_str}");
                // TODO: Secondary labels for source
                Diagnostic::error(
                    unification_point,
                    format!("Unsatisfied trait requirements. {short_msg}"),
                )
                .primary_label(short_msg)
            }
            UnificationError::FromConstraints {
                expected,
                got,
                source,
                loc,
            } => {
                Diagnostic::error(loc, format!("Expected type {}, got {}", expected, got))
                    .primary_label(format!("Expected {}, got {}", expected, got))
                    .note(match source {
                        ConstraintSource::AdditionOutput => format!(
                            "Addition creates one more output bit than the input to avoid overflow"
                        ),
                        ConstraintSource::MultOutput => {
                            format!("The size of a multiplication is the sum of the operand sizes")
                        }
                        ConstraintSource::ArrayIndexing => {
                            // NOTE: This error message could probably be improved
                            format!("because the value is used as an index to an array")
                        }
                        ConstraintSource::MemoryIndexing => {
                            // NOTE: This error message could probably be improved
                            format!("because the value is used as an index to a memory")
                        }
                        ConstraintSource::Concatenation => {
                            format!("The size of a concatenation is the sum of the operand sizes")
                        }
                    })
            }
            UnificationError::NegativeInteger { got, inside, loc } => {
                Diagnostic::bug(loc, "Inferred integer <= 0")
                    .primary_label(format!("{got} is not > 0 in {inside}"))
            }
        })
    }
}

#[derive(Debug, Error, PartialEq, Clone)]
pub struct TypeMismatch {
    /// Expected type
    pub e: UnificationTrace,
    /// Got type
    pub g: UnificationTrace,
}
impl std::fmt::Display for TypeMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "expected {}, got {}", self.e, self.g)
    }
}

#[derive(Debug, Error, PartialEq, Clone)]
pub enum UnificationError {
    #[error("Unification error")]
    Normal(TypeMismatch),
    #[error("Unsatisfied traits")]
    UnsatisfiedTraits(TypeVar, Vec<NameID>),
    #[error("Unification error from constraints")]
    FromConstraints {
        expected: UnificationTrace,
        got: UnificationTrace,
        source: ConstraintSource,
        loc: Loc<()>,
    },
    #[error("Negative integer from constraints")]
    NegativeInteger {
        got: BigInt,
        inside: TypeVar,
        loc: Loc<()>,
    },
}

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("The specified expression has no type information {}", 0.0)]
    UnknownType(TypedExpression),
    #[error("Type mismatch between {0:?} and {1:?}")]
    TypeMismatch(UnificationTrace, UnificationTrace),

    #[error("Entity output type mismatch")]
    EntityOutputTypeMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        // The location of the type specification
        type_spec: Loc<()>,
        // The location of the output expression with the offending type
        output_expr: Loc<()>,
    },
    // An entity output mismatch where the output type was unspecified and defaulted
    // to unit
    #[error("Entity output type mismatch without spec")]
    UnspecedEntityOutputTypeMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        // The location of the output expression with the offending type
        output_expr: Loc<()>,
    },
    #[error("Type error: expected {expected}, got: {got}")]
    UnspecifiedTypeError {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },
    #[error("Type mismatch due to constraints")]
    ConstraintMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        source: ConstraintSource,
        loc: Loc<()>,
    },

    #[error("If condition must be boolean")]
    NonBooleanCondition { got: UnificationTrace, loc: Loc<()> },
    #[error("If condition mismatch")]
    IfConditionMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        first_branch: Loc<()>,
        incorrect_branch: Loc<()>,
    },
    #[error("Match branch mismatch")]
    MatchBranchMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        first_branch: Loc<()>,
        incorrect_branch: Loc<()>,
    },
    #[error("Non clock used as register clock")]
    NonClockClock {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },
    #[error("Reset condition must be a bool")]
    NonBoolReset {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },
    #[error("Reset value must match register type")]
    RegisterResetMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },
    #[error("Initial value must match register type")]
    RegisterInitialMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },

    #[error("Named argument mismatch")]
    NamedArgumentMismatch {
        name: Loc<Identifier>,
        expr: Loc<()>,
        expected: UnificationTrace,
        got: UnificationTrace,
    },
    #[error("Named argument mismatch")]
    ShortNamedArgumentMismatch {
        name: Loc<Identifier>,
        expected: UnificationTrace,
        got: UnificationTrace,
    },
    #[error("Positional argument mismatch")]
    PositionalArgumentMismatch {
        index: usize,
        expr: Loc<()>,
        expected: UnificationTrace,
        got: UnificationTrace,
    },

    #[error("Tuple index of generic argument")]
    TupleIndexOfGeneric { loc: Loc<()> },
    #[error("Tuple index out of bounds")]
    TupleIndexOutOfBounds { index: Loc<u128>, actual_size: u128 },

    #[error("Field access on incomplete")]
    FieldAccessOnIncomplete { loc: Loc<()> },
    #[error("Field access on generic")]
    FieldAccessOnGeneric { loc: Loc<()>, name: NameID },
    #[error("Field access on non-struct")]
    FieldAccessOnNonStruct { loc: Loc<()>, got: TypeVar },
    #[error("Field access on integer")]
    FieldAccessOnInteger { loc: Loc<()> },
    #[error("Field access on enum")]
    FieldAccessOnEnum { loc: Loc<()>, actual_type: NameID },
    #[error("Field access on primitive type")]
    FieldAccessOnPrimitive { loc: Loc<()>, actual_type: NameID },
    #[error("No such field")]
    NoSuchField {
        field: Loc<Identifier>,
        _struct: NameID,
    },

    #[error("Array element mismatch")]
    ArrayElementMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
        first_element: Loc<()>,
    },

    #[error("Index must be an integer")]
    IndexMustBeInteger { got: UnificationTrace, loc: Loc<()> },
    #[error("Indexee must be an array")]
    IndexeeMustBeArray { got: UnificationTrace, loc: Loc<()> },

    #[error("Pattern type mismatch")]
    PatternTypeMismatch {
        pattern: Loc<()>,
        reason: Loc<()>,
        expected: UnificationTrace,
        got: UnificationTrace,
    },

    #[error("The first argument of a pipeline must be a clock")]
    FirstPipelineArgNotClock {
        expected: UnificationTrace,
        spec: Loc<UnificationTrace>,
    },

    #[error("Attempting to instantiate generic type")]
    GenericTypeInstantiation,

    #[error("Argument error")]
    ArgumentError {
        source: ArgumentError,
        unit: Loc<UnitHead>,
    },

    #[error("(internal)No entry in generic list")]
    InternalNoEntryInGenericList(Loc<NameID>),

    #[error("Spade diagnostic")]
    SpadeDiagnostic(#[from] Diagnostic),
}
pub type Result<T> = std::result::Result<T, Diagnostic>;

pub fn error_pattern_type_mismatch(
    reason: Loc<()>,
) -> impl Fn(Diagnostic, TypeMismatch) -> Diagnostic {
    move |diag,
          TypeMismatch {
              e: expected,
              g: got,
          }| {
        diag.message(format!(
            "Pattern type mismatch. Expected {expected} got {got}"
        ))
        .primary_label(format!("expected {expected}, got {got}"))
        .secondary_label(reason, format!("because this has type {expected}"))
    }
}
