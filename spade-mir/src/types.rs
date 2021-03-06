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

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int(val) => write!(f, "int<{}>", val),
            Type::Bool => write!(f, "bool"),
            Type::Tuple(inner) => {
                let inner = inner
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", inner)
            }
        }
    }
}
