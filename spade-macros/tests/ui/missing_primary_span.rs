struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoDiagnostic)]
#[diagnostic(error, "wrong")]
struct Diagnostic {
    #[diagnostic(secondary, "over here")]
    at: Loc<()>,
}

fn main() {}
