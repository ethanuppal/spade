use spade_common::{location_info::Loc, name::Path};
use spade_macros::IntoDiagnostic;
use thiserror::Error;

pub enum ItemKind {
    Pipeline,
    Entity,
}

#[derive(IntoDiagnostic)]
#[diagnostic(error, "Can't create a wire of ports")]
pub(crate) struct WireOfPort {
    #[diagnostic(primary, "This can't be a wire")]
    pub(crate) full_type: Loc<()>,
    #[diagnostic(secondary, "Because this is a port")]
    pub(crate) inner_type: Loc<()>,
}

#[derive(IntoDiagnostic)]
#[diagnostic(error, "Expected {} arguments, got {}", diag.expected, diag.got)]
pub(crate) struct PatternListLengthMismatch {
    pub(crate) expected: usize,
    pub(crate) got: usize,
    #[diagnostic(primary, "Expected {} arguments here", diag.expected)]
    pub(crate) at: Loc<()>,
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum Error {
    #[error("Lookup error")]
    LookupError(#[from] spade_hir::symbol_table::LookupError),
    #[error("Argument error")]
    ArgumentError(#[from] spade_hir::param_util::ArgumentError),

    // Type related errors
    #[error("Spade diagnostic")]
    SpadeDiagnostic(#[from] spade_diagnostics::Diagnostic),
}

pub type Result<T> = std::result::Result<T, Error>;

/// Error to emit when instantiating non-function without inst
pub fn expect_function(
    unit_name: &Loc<Path>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Error {
    let diag = spade_diagnostics::Diagnostic::error(
        unit_name,
        format!("Expected {unit_name} to be a function"),
    )
    .primary_label("Expected function");

    match found_instead {
        spade_hir::UnitKind::Function(_) => {
            spade_diagnostics::Diagnostic::bug(unit_name, "expected fn and got it")
        }
        spade_hir::UnitKind::Entity => diag
            .span_suggest_insert_before("consider adding inst", unit_name, "inst ")
            .secondary_label(unit_def, format!("{unit_name} is an entity")),
        spade_hir::UnitKind::Pipeline(depth) => diag
            .span_suggest_insert_before(
                "consider adding inst",
                unit_name,
                format!("inst({depth}) "),
            )
            .secondary_label(unit_def, format!("{unit_name} is a pipeline")),
    }
    .into()
}

/// Error to emit when using `inst` to instantiate pipeline or entity
pub fn expect_entity(
    inst: &Loc<()>,
    unit_name: &Loc<Path>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Error {
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
    unit_name: &Loc<Path>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Error {
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
