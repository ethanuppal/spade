use std::collections::HashMap;

use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID};

use spade_diagnostics::Diagnostic;
use spade_hir::ItemList;

/// Attempts to look up which functiono to call when calling `method` on a var
/// of type `self_type`.
pub fn select_method(
    expr: Loc<()>,
    type_name: &NameID,
    method: &Loc<Identifier>,
    items: &ItemList,
) -> Result<Loc<NameID>, Diagnostic> {
    // Go to the item list to check if this name has any methods
    let impld_traits = items
        .impls
        .get(type_name)
        .cloned()
        .unwrap_or_else(HashMap::new);

    // Gather all the candidate methods which we may want to call.
    let candidates = impld_traits
        .iter()
        .flat_map(|(_, r#impl)| {
            r#impl.fns.iter().map(move |(fn_name, actual_fn)| {
                if fn_name == &method.inner {
                    Some(actual_fn.0.clone().at_loc(&actual_fn.1))
                } else {
                    None
                }
            })
        })
        .flatten()
        .collect::<Vec<_>>();

    let final_method = match candidates.as_slice() {
        [name] => name,
        [] => {
            return Err(
                Diagnostic::error(expr, format!("{type_name} has no method {method}"))
                    .primary_label("No such method"),
            )
        }
        all_candidates => {
            let mut diag = Diagnostic::error(
                expr,
                format!("{type_name} has multiple methods named {method}"),
            )
            .primary_label("Ambiguous method call");

            for candidate in all_candidates {
                diag = diag.secondary_label(candidate, format!("{type_name} is defined here"))
            }

            return Err(diag);
        }
    };

    Ok(final_method.clone())
}
