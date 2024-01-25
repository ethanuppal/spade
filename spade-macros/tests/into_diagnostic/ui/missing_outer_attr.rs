struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoDiagnostic)]
struct Diagnostic {
    #[diagnostic(primary)]
    at: Loc<()>,
}

fn main() {}
