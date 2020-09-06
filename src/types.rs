pub enum Type {
    // Primitive types
    /// Fixed length bit vector
    BitVector(u64),
    /// Fixed length unsigned int
    UInt(u64),
    /// Fixed length int
    Int(u64),

    // Compound types
    Array(u64, Box<Type>),
    Struct(Vec<(String, Box<Type>)>),
    SumType(Vec<(String, Box<Type>)>),

    Alias(String, Box<Type>),
}
