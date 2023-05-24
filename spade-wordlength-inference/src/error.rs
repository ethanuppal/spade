use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_macros::IntoDiagnostic;

#[derive(IntoDiagnostic)]
#[diagnostic(
    error,
    "Got a type-error while doing wordlength inference - please report this!"
)]
pub struct UnificationError {
    #[diagnostic(primary, "This place is somehow related")]
    pub at: Loc<()>,
}

#[derive(IntoDiagnostic)]
#[diagnostic(error, "The wordlength isn't what we infered it to - inference got {} bits and you claimed {} bits", diag.infered, diag.typechecked)]
pub struct WordlengthMismatch {
    pub infered: u32,
    #[diagnostic(primary, "Here {} bits were infered", diag.infered)]
    pub infered_at: Loc<()>,
    pub typechecked: u32,
    #[diagnostic(primary, "Here you said {} bits", diag.typechecked)]
    pub typechecked_at: Loc<()>,
}

pub type Result<T> = std::result::Result<T, Diagnostic>;
