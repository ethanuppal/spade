use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_macros::IntoDiagnostic;

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
    #[diagnostic(
        primary,
        "Expected {} argument{}{}",
        diag.expected,
        if diag.expected == 1 { "" } else { "s" },
        if let Some(for_what) = &diag.for_what { format!(" for this {for_what}") } else { format!("") },
    )]
    pub(crate) at: Loc<()>,
    pub(crate) for_what: Option<String>,
}

pub type Result<T> = std::result::Result<T, Diagnostic>;
