use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use spade_hir::{ExecutableItem, ItemList, UnitName};
use spade_hir_lowering::Manglable;

#[derive(Serialize, Deserialize)]
pub enum ItemKind {
    /// The item is a unit which is not generic and can thus easily be
    /// refered to
    Normal(String),
    /// The item exist, is a unit but is generic and there is therefore
    /// not an easy mapping between the path and name
    Generic,
    /// The item is a type
    Type,
}

pub fn list_names(item_list: &ItemList) -> HashMap<Vec<String>, ItemKind> {
    let mut result = HashMap::new();
    for (name, item) in &item_list.executables {
        let unit_name = match item {
            ExecutableItem::EnumInstance { .. } => None,
            ExecutableItem::StructInstance => None,
            ExecutableItem::Entity(e) => Some(&e.name),
            ExecutableItem::Pipeline(p) => Some(&p.name),
            ExecutableItem::BuiltinEntity(n, _) => Some(n),
            ExecutableItem::BuiltinPipeline(n, _) => Some(n),
        };

        let item = match unit_name {
            Some(n @ UnitName::FullPath(_) | n @ UnitName::Unmangled(_, _)) => {
                ItemKind::Normal(n.mangled())
            }
            Some(UnitName::WithID(_)) => ItemKind::Generic,
            None => ItemKind::Type,
        };

        let path = name.1 .0.iter().map(|ident| format!("{ident}")).collect();

        result.insert(path, item);
    }

    result
}
