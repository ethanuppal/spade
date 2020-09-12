use thiserror::Error;

use crate::ast::Expression as AstExpr;
use crate::ast::Type as AstType;
use crate::location_info::Loc;
use crate::location_info::WithLocation;

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Unit,
    // Primitive types
    /// Fixed length bit vector
    BitVector(u128),
    /// Fixed length unsigned int
    UInt(u128),
    /// Fixed length int
    Int(u128),

    // Compound types
    Array(u128, Box<Type>),
    Struct(Vec<(String, Box<Type>)>),
    SumType(Vec<(String, Box<Type>)>),

    Alias(String, Box<Type>),
}

impl WithLocation for Type {}

#[derive(Debug, Error, PartialEq)]
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

impl Type {
    pub fn convert_from_ast(value: AstType) -> Result<Self, Error> {
        match value {
            AstType::Named(name) => match name.0.as_str() {
                "uint" | "int" | "bits" => Err(Error::BitWidthRequired(name.0.to_string())),
                _ => Err(Error::NamedTypesUnsupported),
            },
            AstType::UnitType => Ok(Type::Unit),
            AstType::WithSize(inner, size) => {
                let size = match size.inner {
                    AstExpr::IntLiteral(size) => size,
                    _ => Err(Error::NonLiteralTypeSize(size.loc()))?,
                };
                match inner.inner {
                    AstType::Named(name) => match name.0.as_str() {
                        "uint" => Ok(Type::UInt(size)),
                        "int" => Ok(Type::Int(size)),
                        "bits" => Ok(Type::BitVector(size)),
                        _ => Err(Error::CompoundArrayUnsupported),
                    },
                    _ => Err(Error::CompoundArrayUnsupported),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ast::Identifier;

    #[test]
    fn primitive_type_arrays_work() {
        {
            let input = AstType::WithSize(
                Box::new(AstType::Named(Identifier("uint".into())).nowhere()),
                AstExpr::IntLiteral(10).nowhere(),
            );

            assert_eq!(Type::convert_from_ast(input), Ok(Type::UInt(10)));
        }

        {
            let input = AstType::WithSize(
                Box::new(AstType::Named(Identifier("int".into())).nowhere()),
                AstExpr::IntLiteral(10).nowhere(),
            );

            assert_eq!(Type::convert_from_ast(input), Ok(Type::Int(10)));
        }

        {
            let input = AstType::WithSize(
                Box::new(AstType::Named(Identifier("bits".into())).nowhere()),
                AstExpr::IntLiteral(10).nowhere(),
            );

            assert_eq!(Type::convert_from_ast(input), Ok(Type::BitVector(10)));
        }
    }
}
