use std::collections::{BTreeMap, HashMap};

use serde::{Deserialize, Serialize};
use spade_ast_lowering::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_common::name::NameID;
use spade_hir::{symbol_table::FrozenSymtab, ItemList};
use spade_hir_lowering::{
    name_map::{NameSource, NamedValue},
    NameSourceMap,
};
use spade_mir::{renaming::VerilogNameMap, unit_name::InstanceMap};
use spade_typeinference::TypeMap;

#[derive(Serialize, Deserialize)]
pub struct MirContext {
    /// Mapping to concrete types for this instantiation of the entity
    pub type_map: TypeMap,
    pub reg_name_map: BTreeMap<NameID, NameID>,
    pub verilog_name_map: VerilogNameMap,
}

/// All the state required in order to add more things to the compilation process
#[derive(Serialize, Deserialize)]
pub struct CompilerState {
    // (filename, file content) of all the compiled files
    pub code: Vec<(String, String)>,
    pub symtab: FrozenSymtab,
    pub idtracker: ExprIdTracker,
    pub impl_idtracker: ImplIdTracker,
    pub item_list: ItemList,
    pub name_source_map: NameSourceMap,
    pub instance_map: InstanceMap,
    pub mir_context: HashMap<NameID, MirContext>,
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
