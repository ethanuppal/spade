use crate::ValueName;

impl ValueName {
    pub fn var_name(&self) -> String {
        match self {
            ValueName::Named(id, name) => {
                format!("{}_n{}", name, id)
            }
            ValueName::Expr(id) => {
                format!("_e_{}", id)
            }
        }
    }

    pub fn backward_var_name(&self) -> String {
        match self {
            ValueName::Named(id, name) => {
                format!("{}_n{}_o", name, id)
            }
            ValueName::Expr(id) => {
                format!("_e_{}_o", id)
            }
        }
    }
}

pub fn escape_path(path: String) -> String {
    path.replace("::", "_")
}

pub fn mangle_entity(module: &str) -> String {
    format!("e_{}", module)
}

pub fn mangle_input(input: &str) -> String {
    format!("{}_i", input)
}

pub fn mangle_output(input: &str) -> String {
    format!("{}_o", input)
}

pub enum TupleIndex {
    /// The index is a single bit, i.e. codegens as [val]
    Single(u64),
    /// The index is a range of bits, codegens as [left:right]
    Range { left: u64, right: u64 },
}

impl TupleIndex {
    pub fn verilog_code(&self) -> String {
        match self {
            TupleIndex::Single(i) => format!("[{i}]"),
            TupleIndex::Range { left, right } => format!("[{left}:{right}]"),
        }
    }
}
