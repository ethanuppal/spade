use crate::hir::Path;
use crate::typeinference::equation::KnownType;

pub fn t_int() -> KnownType {
    KnownType::Path(Path::from_strs(&["builtin", "int"]))
}
pub fn t_bool() -> KnownType {
    KnownType::Path(Path::from_strs(&["builtin", "bool"]))
}
pub fn t_clock() -> KnownType {
    KnownType::Path(Path::from_strs(&["builtin", "clk"]))
}
