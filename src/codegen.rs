use crate::constant::Constant;
use crate::expression::Expression;
use crate::identifier::Identifier;

impl Constant {
    pub fn get_verilog(&self) -> String {
        match self {
            Constant::Int(value) => format!("{}", value),
            Constant::UInt(value) => format!("{}", value),
            _ => unimplemented! {},
        }
    }
}

impl Expression {
    /// Gets the verilog corresponding to an expression. Assumes types have already
    /// been checked
    pub fn get_verilog(&self) -> String {
        match self {
            Expression::Add(lhs, rhs) => infix_binop("+", lhs, rhs),
        }
    }
}

impl Identifier {
    pub fn get_verilog_name(&self) -> String {
        match self {
            Identifier::Id(num) => format!("\\%{}", num),
            Identifier::Str(name) => name.clone(),
        }
    }
}

fn infix_binop(op: &str, lhs: &Identifier, rhs: &Identifier) -> String {
    format!(
        "({} {} {})",
        op,
        lhs.get_verilog_name(),
        rhs.get_verilog_name()
    )
}
