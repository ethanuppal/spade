#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Int(u64),
    Bool,
    Tuple(Vec<Type>),
    Enum(Vec<Vec<Type>>),
}

impl Type {
    pub fn size(&self) -> u64 {
        match self {
            Type::Int(len) => *len,
            Type::Bool => 1,
            Type::Tuple(inner) => inner.iter().map(|i| Type::size(i)).sum::<u64>(),
            Type::Enum(inner) => {
                let discriminant_size = (inner.len() as f32).log2().ceil() as u64;

                let members_size = inner
                    .iter()
                    .map(|m| m.iter().map(|t| t.size()).sum())
                    .max()
                    .unwrap_or(0);

                discriminant_size + members_size
            }
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
            Type::Enum(inner) => {
                let inner = inner
                    .iter()
                    .map(|variant| {
                        let members = variant
                            .iter()
                            .map(|t| format!("{}", t))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("option [{}]", members)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");

                write!(f, "enum {}", inner)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pure_enum_size_is_correct() {
        // 2 variant enum
        assert_eq!(Type::Enum(vec![vec![], vec![]]).size(), 1);
    }

    #[test]
    fn enum_with_payload_size_is_correct() {
        // 2 variant enum
        assert_eq!(
            Type::Enum(vec![vec![Type::Int(5)], vec![Type::Bool]]).size(),
            6
        );
    }

    #[test]
    fn single_variant_enum_is_0_bits() {
        assert_eq!(Type::Enum(vec![vec![]]).size(), 0);
    }
}
