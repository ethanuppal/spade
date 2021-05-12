use spade_common::name::{Identifier, NameID};

#[derive(Debug, Clone, PartialEq)]
pub enum PrimitiveType {
    Int,
    Uint,
    Clock,
    Bool,
}

impl std::fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimitiveType::Int => write!(f, "int"),
            PrimitiveType::Uint => write!(f, "uint"),
            PrimitiveType::Clock => write!(f, "clk"),
            PrimitiveType::Bool => write!(f, "bool"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConcreteType {
    Tuple(Vec<ConcreteType>),
    Enum {
        name: Identifier,
        options: Vec<(Identifier, ConcreteType)>,
    },
    Single {
        base: PrimitiveType,
        params: Vec<ConcreteType>,
    },
    Integer(u128),
}

impl std::fmt::Display for ConcreteType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcreteType::Tuple(inner) => {
                write!(
                    f,
                    "({})",
                    inner
                        .iter()
                        .map(|p| format!("{}", p))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ConcreteType::Enum { name, options: _ } => {
                write!(f, "{}", name)
            }
            ConcreteType::Single { base, params } => {
                let params_str = if params.is_empty() {
                    format!("")
                } else {
                    format!(
                        "{}",
                        params
                            .iter()
                            .map(|p| format!("{}", p))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };

                write!(f, "{}{}", base, params_str)
            }
            ConcreteType::Integer(size) => {
                write!(f, "#{}", size)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum KnownType {
    Type(NameID),
    Integer(u128),
}

impl std::fmt::Display for KnownType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KnownType::Type(t) => {
                write!(f, "{}", t)
            }
            KnownType::Integer(v) => {
                write!(f, "{}", v)
            }
        }
    }
}
