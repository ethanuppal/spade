use crate::types::{KnownType, Type};

pub fn t_int() -> KnownType {
    KnownType::Type(Type::Int)
}
pub fn t_bool() -> KnownType {
    KnownType::Type(Type::Bool)
}
pub fn t_clock() -> KnownType {
    KnownType::Type(Type::Clock)
}
