pub mod codegen;
pub mod diff;
pub mod diff_printing;
pub mod macros;
pub mod types;
mod verilog;

use types::Type;

#[derive(Clone, PartialEq, Debug)]
pub enum ConstantValue {
    Int(u64),
    Bool(bool),
}

impl std::fmt::Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValue::Int(val) => write!(f, "{}", val),
            ConstantValue::Bool(val) => write!(f, "{}", val),
        }
    }
}

/// A name of a value. Can either come from the NameID of the underlying
/// variable, or the id of the underlying expression
#[derive(Clone, PartialEq, Debug)]
pub enum ValueName {
    /// A named value in the code with with an index to make that name globally unique
    /// In the resulting verilog, this is translated as _n_$id_$name
    Named(u64, String),
    /// An un-named expression. In the resulting verilog, this is called _e_$id
    Expr(u64),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Operator {
    /// Binary arithmetic operators
    Add,
    Sub,
    Mul,
    Eq,
    Gt,
    Lt,
    LeftShift,
    RightShift,
    LogicalAnd,
    LogicalOr,
    /// Select [1] if [0] else [2]
    Select,
    /// Construct a tuple from all the operand expressions
    ConstructTuple,
    /// Construct the nth enum variant with the operand expressions as the payload
    ConstructEnum {
        variant: usize,
        variant_count: usize,
    },
    /// Get the `.0`th element of a tuple. The types of the elements are specified
    /// in the second argument
    IndexTuple(u64, Vec<Type>),
    /// Instantiation of another module with the specified name. The operands are passed
    /// positionally to the entity. The target module can only have a single output which
    /// must be the last argument
    Instance(String),
    /// Alias another named value
    Alias,
}

impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operator::Add => write!(f, "Add"),
            Operator::Sub => write!(f, "Sub"),
            Operator::Mul => write!(f, "Mul"),
            Operator::Eq => write!(f, "Eq"),
            Operator::Gt => write!(f, "Gt"),
            Operator::Lt => write!(f, "Lt"),
            Operator::RightShift => write!(f, "RightShift"),
            Operator::LogicalAnd => write!(f, "LogicalAnd"),
            Operator::LogicalOr => write!(f, "LogicalOr"),
            Operator::Select => write!(f, "Select"),
            Operator::LeftShift => write!(f, "LeftShift"),
            Operator::ConstructEnum {
                variant,
                variant_count,
            } => write!(f, "ConstructEnum({}, {})", variant, variant_count),
            Operator::ConstructTuple => write!(f, "ConstructTuple"),
            Operator::IndexTuple(idx, _) => write!(f, "IndexTuple({})", idx),
            Operator::Instance(name) => write!(f, "Instance({})", name),
            Operator::Alias => write!(f, "Alias"),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Binding {
    pub name: ValueName,
    pub operator: Operator,
    pub operands: Vec<ValueName>,
    pub ty: Type,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Register {
    pub name: ValueName,
    pub ty: Type,
    pub clock: ValueName,
    pub reset: Option<(ValueName, ValueName)>,
    pub value: ValueName,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Statement {
    Binding(Binding),
    Register(Register),
    /// A constant expression with the specified ID and value
    Constant(u64, Type, ConstantValue),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Entity {
    /// The name of the module
    pub name: String,
    /// A module input which is called `.1` externally and `.2` internally in the module
    pub inputs: Vec<(String, ValueName, Type)>,
    pub output: ValueName,
    pub output_type: Type,
    pub statements: Vec<Statement>,
}
