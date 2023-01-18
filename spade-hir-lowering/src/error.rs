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

/// Error to emit when instantiating non-function without inst
pub fn expect_function(
    callee: &Loc<NameID>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Error {
    let callee_name = &callee.map_ref(|n| n.1.tail());
    let diag = spade_diagnostics::Diagnostic::error(
        callee_name,
        format!("Expected {callee_name} to be a function"),
    )
    .primary_label("Expected function");

    match found_instead {
        spade_hir::UnitKind::Function(_) => {
            spade_diagnostics::Diagnostic::bug(callee_name, "expected fn and got it")
        }
        spade_hir::UnitKind::Entity => diag
            .span_suggest_insert_before("consider adding inst", callee_name, "inst ")
            .secondary_label(unit_def, format!("{callee_name} is an entity")),
        spade_hir::UnitKind::Pipeline(depth) => diag
            .span_suggest_insert_before(
                "consider adding inst",
                callee_name,
                format!("inst({depth}) "),
            )
            .secondary_label(unit_def, format!("{callee_name} is a pipeline")),
    }
    .into()
}

/// Error to emit when using `inst` to instantiate pipeline or entity
pub fn expect_entity(
    inst: &Loc<()>,
    callee: &Loc<NameID>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Error {
    let unit_name = &callee.map_ref(|n| n.1.tail());
    let diag = spade_diagnostics::Diagnostic::error(
        unit_name,
        format!("Expected {unit_name} to be an entity"),
    )
    .primary_label("Expected entity")
    .secondary_label(
        unit_def,
        format!("{unit_name} is a {}", found_instead.name()),
    )
    .secondary_label(inst, "because of this inst");

    match found_instead {
        spade_hir::UnitKind::Function(_) => {
            diag.span_suggest_remove("Consider removing inst", inst)
        }
        spade_hir::UnitKind::Entity => {
            spade_diagnostics::Diagnostic::bug(unit_name, "expected entity and got it")
        }
        spade_hir::UnitKind::Pipeline(depth) => {
            diag.span_suggest_insert_after("Consider adding depth", inst, format!("({depth})"))
        }
    }
    .into()
}

/// Error to emit when using `inst` to instantiate pipeline or entity
pub fn expect_pipeline(
    inst: &Loc<()>,
    callee: &Loc<NameID>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Error {
    let unit_name = &callee.map_ref(|n| n.1.tail());
    let diag = spade_diagnostics::Diagnostic::error(
        unit_name,
        format!("Expected {unit_name} to be a pipeline"),
    )
    .primary_label("Expected pipeline")
    .secondary_label(inst, "because of this inst");

    match found_instead {
        spade_hir::UnitKind::Function(_) => diag
            .span_suggest_remove("Consider removing inst", inst)
            .secondary_label(unit_def, format!("{unit_name} is a function")),
        spade_hir::UnitKind::Entity => diag
            .span_suggest_replace("Consider removing the depth", inst, "inst")
            .secondary_label(unit_def, format!("{unit_name} is an entity")),
        spade_hir::UnitKind::Pipeline(_) => {
            spade_diagnostics::Diagnostic::bug(unit_name, "expected pipeline and got it")
        }
    }
    .into()
}
