struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoDiagnostic)]
#[diagnostic(error, "error")]
struct Diagnostic1 {
    #[diagnostic(primary, <=>)]
    at: Loc<()>,
}

#[derive(spade_macros::IntoDiagnostic)]
#[diagnostic(error, "error")]
struct Diagnostic2 {
    #[diagnostic(primary)]
    at: Loc<()>,
    #[diagnostic(secondary, ::<>)]
    extra: Loc<()>,
}

fn main() {}
