#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Int(u64),
    Bool,
    Tuple(Vec<Type>),
}

impl Type {
    pub fn size(&self) -> u64 {
        match self {
            Type::Int(len) => *len,
            Type::Bool => 1,
            Type::Tuple(inner) => inner.iter().map(|i| Type::size(i)).sum::<u64>(),
        }
    }
}
