use local_impl::local_impl;
use spade_ast::comptime::{ComptimeCondOp, ComptimeCondition};
use spade_hir::symbol_table::SymbolTable;

use crate::error::Result;

#[local_impl]
impl<T: Clone> ComptimeCondExt for ComptimeCondition<T> {
    /// Evaluates the comptime condition returning the resulting ast node. If the else
    /// branch is not provided, None is returned
    fn maybe_unpack(&self, symtab: &SymbolTable) -> Result<Option<T>> {
        let (var, op, val) = &self.condition;

        let var_val = symtab.lookup_comptime_config(var)?.1.inner;

        let result_bool = match op {
            ComptimeCondOp::Eq => var_val == val.inner,
            ComptimeCondOp::Lt => var_val < val.inner,
            ComptimeCondOp::Gt => var_val > val.inner,
            ComptimeCondOp::Le => var_val <= val.inner,
            ComptimeCondOp::Ge => var_val >= val.inner,
        };

        if result_bool {
            Ok(Some(self.on_true.as_ref().clone()))
        } else {
            Ok(self.on_false.clone().map(|b| b.as_ref().clone()))
        }
    }
}
