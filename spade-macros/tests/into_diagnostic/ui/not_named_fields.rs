struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoDiagnostic)]
#[diagnostic(error, "hhheheheh")]
struct Diagnostic(#[diagnostic(primary)] Loc<usize>);

fn main() {}
