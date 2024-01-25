struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoSubdiagnostic)]
struct Diagnostic {
    at: Loc<()>,
}

fn main() {}
