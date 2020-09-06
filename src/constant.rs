pub enum Constant {
    BitVector(Vec<bool>),
    UInt(u64),
    Int(i64),

    // Compound values
    Array(Vec<Box<Constant>>),
    Struct(Vec<Box<Constant>>),
    SumType(Vec<Box<Constant>>),
}
