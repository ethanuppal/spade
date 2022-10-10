use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use spade_ast_lowering::id_tracker::ExprIdTracker;
use spade_hir::{symbol_table::FrozenSymtab, ItemList};
use spade_hir_lowering::{
    name_map::{NameSource, NamedValue},
    NameSourceMap,
};

/// All the state required in order to add more things to the compilation process
#[derive(Serialize, Deserialize)]
pub struct CompilerState {
    // (filename, file content) of all the compiled files
    pub code: Vec<(String, String)>,
    pub symtab: FrozenSymtab,
    pub idtracker: ExprIdTracker,
    pub item_list: ItemList,
    pub name_source_map: NameSourceMap,
}

impl CompilerState {
    // Attempts to demangle the specified string to the corresponding snippet of source code
    pub fn demangle_string(&self, mangled: &str) -> Option<String> {
        // We'll need to first mangle the ValueNames into actual strings to search.
        // NOTE: A smart non-lazy person would do this once, not every time we ask
        // for demangling
        let string_map = self
            .name_source_map
            .inner
            .iter()
            .flat_map(|(k, v)| {
                vec![
                    (k.var_name(), v.clone()),
                    (k.backward_var_name(), v.clone()),
                ]
            })
            .collect::<HashMap<_, _>>();

        string_map.get(mangled).map(|name| match name {
            NamedValue::Primary(source) => self.demangle_name_source(source),
            NamedValue::Secondary(source, description) => {
                format!("{} ({description})", self.demangle_name_source(source))
            }
        })
    }

    pub fn demangle_name_source(&self, source: &NameSource) -> String {
        match source {
            NameSource::Name(n) => format!("{n}"),
            NameSource::Expr(e) => {
                format!(
                    "(id) {}",
                    &self.code[e.file_id].1[e.span.start().to_usize()..e.span.end().to_usize()]
                )
            }
        }
    }
}
