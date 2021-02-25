/// Base type without generic parameters
#[derive(Clone, Debug, PartialEq)]
pub enum BaseType {
    Int,
    Bool,
    Clock,
    Unit,
}

impl spade_common::location_info::WithLocation for BaseType {}

impl std::fmt::Display for BaseType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BaseType::Int => {
                write!(f, "int")
            }
            BaseType::Bool => {
                write!(f, "bool")
            }
            BaseType::Clock => {
                write!(f, "Clock")
            }
            BaseType::Unit => {
                write!(f, "()")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConcreteType {
    Tuple(Vec<ConcreteType>),
    Single {
        base: KnownType,
        params: Vec<ConcreteType>,
    },
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
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum KnownType {
    Type(BaseType),
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
