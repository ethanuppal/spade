struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoDiagnostic)]
#[diagnostic(arrow goes brrrrr ----------->>>>>>>)]
struct Diagnostic {
    #[diagnostic(primary)]
    at: Loc<()>,
}

fn main() {}
