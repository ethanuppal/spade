use std::collections::HashMap;

use spade_common::location_info::Loc;
use spade_common::name::{Identifier, NameID};

use spade_diagnostics::Diagnostic;
use spade_hir::ItemList;

use crate::Result;

/// Attempts to look up which functiono to call when calling `method` on a var
/// of type `self_type`.
pub fn select_method(
    expr: Loc<()>,
    type_name: &NameID,
    method: &Loc<Identifier>,
    items: &ItemList,
) -> Result<NameID> {
    // Go to the item list to check if this name has any methods
    let impld_traits = items
        .impls
        .get(type_name)
        .cloned()
        .unwrap_or_else(|| HashMap::new());

    // Gather all the candidate methods which we may want to call.
    let candidates = impld_traits
        .iter()
        .flat_map(|(_, r#impl)| {
            r#impl.fns.iter().map(move |(fn_name, actual_fn)| {
                if fn_name == &method.inner {
                    Some(actual_fn)
                } else {
                    None
                }
            })
        })
        .filter_map(|r| r)
        .collect::<Vec<_>>();

    let final_method = match candidates.as_slice() {
        [(name, _)] => name,
        [] => {
            return Err(Diagnostic::error(expr, "{type_name} as no method {method}")
                .primary_label("No such method")
                .into())
        }
        _ => {
            let diag = Diagnostic::error(expr, "{type_name} has multiple methods named {method}")
                .primary_label("Ambiguous method call");

            // TODO: List the options

            return Err(diag.into());
        }
    };

    Ok(final_method.clone())
}
