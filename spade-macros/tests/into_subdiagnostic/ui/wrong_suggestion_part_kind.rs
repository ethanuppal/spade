struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoSubdiagnostic)]
#[diagnostic(suggestion, "do this and that")]
struct Diagnostic1 {
    #[diagnostic(waho, "waho")]
    this: Loc<()>,
}

#[derive(spade_macros::IntoSubdiagnostic)]
#[diagnostic(suggestion, "do this and that")]
struct Diagnostic2 {
    #[diagnostic(waho)]
    this: Loc<()>,
}

fn main() {}
