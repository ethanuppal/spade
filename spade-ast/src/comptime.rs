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
