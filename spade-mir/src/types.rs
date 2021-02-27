#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Int(u128),
    Bool,
    Tuple(Vec<Box<Type>>),
}
