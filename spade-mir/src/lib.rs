pub mod codegen;
pub mod macros;
pub mod types;
mod util;
mod verilog;

use types::Type;

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
    Add,
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
