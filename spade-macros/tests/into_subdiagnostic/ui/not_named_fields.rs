struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoSubdiagnostic)]
#[diagnostic(error, "hhheheheh")]
struct Diagnostic(Loc<usize>);

fn main() {}
