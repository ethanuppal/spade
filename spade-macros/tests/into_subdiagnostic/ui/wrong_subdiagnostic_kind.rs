struct Loc<T>(std::marker::PhantomData<T>);

#[derive(spade_macros::IntoSubdiagnostic)]
#[diagnostic(blub_blub, "do this and that")]
struct Diagnostic1 {
    #[diagnostic(waho, "waho")]
    this: Loc<()>,
}

fn main() {}
