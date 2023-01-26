use spade_common::{
    location_info::{Loc, WithLocation},
    name::Path,
};

#[derive(PartialEq, Clone, Debug)]
pub enum ComptimeCondOp {
    Eq,
    Lt,
    Gt,
    Le,
    Ge,
}

#[derive(PartialEq, Clone, Debug)]
pub struct ComptimeCondition<T> {
    pub condition: (Loc<Path>, ComptimeCondOp, Loc<u128>),
    pub on_true: Box<T>,
    pub on_false: Option<Box<T>>,
}
impl<T> WithLocation for ComptimeCondition<T> {}

#[derive(PartialEq, Clone, Debug)]
pub enum MaybeComptime<T> {
    Raw(T),
    Comptime(Loc<ComptimeCondition<T>>),
}
impl<T> WithLocation for MaybeComptime<T> {}

impl<T> MaybeComptime<T> {
    pub fn transpose(self, wrapper: impl Fn(Loc<ComptimeCondition<T>>) -> T) -> T {
        match self {
            MaybeComptime::Raw(inner) => inner,
            MaybeComptime::Comptime(cond) => wrapper(cond),
        }
    }
}
