/// Base type without generic parameters
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Int,
    Bool,
    Clock,
    Unit,
}

impl crate::location_info::WithLocation for Type {}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => {
                write!(f, "int")
            }
            Type::Bool => {
                write!(f, "bool")
            }
            Type::Clock => {
                write!(f, "Clock")
            }
            Type::Unit => {
                write!(f, "()")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConcreteType {
    pub base: KnownType,
    pub params: Vec<ConcreteType>,
}

impl std::fmt::Display for ConcreteType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params_str = if self.params.is_empty() {
            format!("")
        } else {
            format!(
                "{}",
                self.params
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };

        write!(f, "{}{}", self.base, params_str)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum KnownType {
    Type(Type),
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
