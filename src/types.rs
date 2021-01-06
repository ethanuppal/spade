use thiserror::Error;

use crate::ast::Expression as AstExpr;
use crate::ast::Type as AstType;
use crate::location_info::Loc;
use crate::location_info::WithLocation;

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum Type {
    Unit,
    Bit,
    Bool,
    // Primitive types
    /// Fixed length bit vector
    BitVector(u128),
    /// Fixed length unsigned int
    UInt(u128),
    /// Fixed length int
    Int(u128),

    KnownInt,

    Clock,

    // Compound types
    Array(u128, Box<Type>),
    Struct(Vec<(String, Box<Type>)>),
    SumType(Vec<(String, Box<Type>)>),

    Alias(String, Box<Type>),

    Function(Vec<Type>, Box<Type>),
    Entity(Vec<Type>, Box<Type>),
}

impl Type {
    pub fn convert_from_ast(value: &AstType) -> Result<Self, Error> {
        match value {
            AstType::Named(name) => match name.as_strs().as_slice() {
                ["bit"] => Ok(Type::Bit),
                ["clk"] => Ok(Type::Clock),
                ["bool"] => Ok(Type::Bool),
                ["uint"] | ["int"] | ["bits"] => {
                    Err(Error::BitWidthRequired(name.as_strings()[0].to_string()))
                }
                _ => Err(Error::NamedTypesUnsupported),
            },
            AstType::UnitType => Ok(Type::Unit),
            AstType::WithSize(inner, size) => {
                let size = match size.inner {
                    AstExpr::IntLiteral(size) => size,
                    _ => Err(Error::NonLiteralTypeSize(size.loc()))?,
                };
                match &inner.inner {
                    AstType::Named(name) => match name.as_strs().as_slice() {
                        ["uint"] => Ok(Type::UInt(size)),
                        ["int"] => Ok(Type::Int(size)),
                        ["bits"] => Ok(Type::BitVector(size)),
                        _ => Err(Error::CompoundArrayUnsupported),
                    },
                    _ => Err(Error::CompoundArrayUnsupported),
                }
            }
        }
    }

    // returns the amount of bits of this type
    pub fn size(&self) -> u128 {
        match self {
            Type::Unit => todo!("Size of the unit type is kind of hard to define in a useful way"),
            Type::Bit => 1,
            Type::Bool => 1,
            Type::BitVector(len) => *len,
            Type::UInt(len) => *len,
            Type::Int(len) => *len,
            Type::KnownInt => {
                panic!("attempting to get the size of knownint which can not be synthesised")
            }
            Type::Clock => 1,
            Type::Array(len, inner) => len * inner.size(),
            Type::Struct(inner) => inner.iter().map(|(_, t)| t.size()).sum(),
            Type::SumType(_inner) => {
                todo!("Size of sum types is not computed right now")
                // inner.iter().map(|(_, t)| t.size()).max()
            }
            Type::Alias(_, target) => target.size(),
            Type::Function(_, _) => {
                panic!(
                    "Trying to get the size of a function type which should never be synthesised"
                );
            }
            Type::Entity(_, _) => {
                panic!(
                    "Trying to get the size of an entity type which should never be synthesised"
                );
            }
        }
    }
}

impl WithLocation for Type {}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => write!(f, "()"),
            Type::Bit => write!(f, "bit"),
            Type::Bool => write!(f, "bool"),
            Type::BitVector(size) => write!(f, "bits[{}]", size),
            Type::UInt(size) => write!(f, "uint[{}]", size),
            Type::Int(size) => write!(f, "int[{}]", size),
            Type::KnownInt => write!(f, "KnownInt"),
            Type::Clock => write!(f, "clock"),
            Type::Array(length, inner) => write!(f, "{}[{}]", length, inner),
            Type::Struct(members) => {
                write!(f, "{{")?;
                for (name, t) in members {
                    write!(f, "{}: {}, ", name, t)?;
                }
                write!(f, "}}")
            }
            Type::SumType(options) => {
                write!(f, "{{")?;
                for (name, t) in options {
                    write!(f, "{}({}), ", name, t)?;
                }
                write!(f, "}}")
            }
            Type::Alias(name, _) => write!(f, "{}", name),
            Type::Function(_, _) => {
                unimplemented! {}
            }
            Type::Entity(_, _) => {
                unimplemented! {}
            }
        }
    }
}

// NOTE: These enums do not carry location info if it affects the whole type,
// that task is defered to type consumers as they would otherwise duplicate the info.
#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("Unknown type name {}", 0.0)]
    UnknownTypeName(Loc<String>),
    #[error("{0} requires a bit width")]
    BitWidthRequired(String),

    #[error("Named types are not yet supported")]
    NamedTypesUnsupported,

    #[error("Non literal type sizes are unsupported")]
    NonLiteralTypeSize(Loc<()>),

    #[error("Compound array types are not supported")]
    CompoundArrayUnsupported,
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::testutil::ast_path;

    #[test]
    fn primitive_type_arrays_work() {
        {
            let input = AstType::WithSize(
                Box::new(AstType::Named(ast_path("uint").strip()).nowhere()),
                AstExpr::IntLiteral(10).nowhere(),
            );

            assert_eq!(Type::convert_from_ast(&input), Ok(Type::UInt(10)));
        }

        {
            let input = AstType::WithSize(
                Box::new(AstType::Named(ast_path("int").strip()).nowhere()),
                AstExpr::IntLiteral(10).nowhere(),
            );

            assert_eq!(Type::convert_from_ast(&input), Ok(Type::Int(10)));
        }

        {
            let input = AstType::WithSize(
                Box::new(AstType::Named(ast_path("bits").strip()).nowhere()),
                AstExpr::IntLiteral(10).nowhere(),
            );

            assert_eq!(Type::convert_from_ast(&input), Ok(Type::BitVector(10)));
        }
    }
}
