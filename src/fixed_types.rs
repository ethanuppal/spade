use crate::hir::Path;
use crate::typeinference::equation::KnownType;

pub const INT_PATH: &[&str] = &["int"];
pub const BOOL_PATH: &[&str] = &["bool"];
pub const CLK_PATH: &[&str] = &["clk"];

pub fn t_int() -> KnownType {
    KnownType::Path(Path::from_strs(INT_PATH))
}
pub fn t_bool() -> KnownType {
    KnownType::Path(Path::from_strs(BOOL_PATH))
}
pub fn t_clock() -> KnownType {
    KnownType::Path(Path::from_strs(CLK_PATH))
}
