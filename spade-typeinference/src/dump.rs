use std::collections::HashMap;

use spade_hir::{symbol_table::SymbolTable, TypeList};
use spade_types::ConcreteType;

use crate::{equation::TypedExpression, TypeState};

// TODO: Remove this
pub fn dump_types(
    type_state: &TypeState,
    type_list: &TypeList,
    symtab: &SymbolTable,
) -> HashMap<TypedExpression, Option<ConcreteType>> {
    type_state
        .get_equations()
        .iter()
        .map(|(expr, t)| {
            (
                expr.clone(),
                TypeState::ungenerify_type(t, symtab, type_list),
            )
        })
        .collect()
}
