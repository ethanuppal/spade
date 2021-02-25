use spade_types::{BaseType, KnownType};

pub fn t_int() -> KnownType {
    KnownType::Type(BaseType::Int)
}
pub fn t_bool() -> KnownType {
    KnownType::Type(BaseType::Bool)
}
pub fn t_clock() -> KnownType {
    KnownType::Type(BaseType::Clock)
}
