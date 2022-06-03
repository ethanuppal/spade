use std::collections::{HashMap, VecDeque};

use crate::{error::Result, generate_entity, generate_pipeline};
use spade_common::{id_tracker::ExprIdTracker, name::NameID};
use spade_hir::{symbol_table::FrozenSymtab, ExecutableItem, ItemList};
use spade_mir as mir;
use spade_typeinference::{equation::TypeVar, GenericListToken, TypeState};

/// An item to be monomorphised
struct MonoItem {
    /// The name of the original item which this is a monomorphised version of
    pub source_name: NameID,
    /// The new name of the new item
    pub new_name: NameID,
    /// The types to replace the generic types in the item. Positional replacement
    pub params: Vec<TypeVar>,
}

pub struct MonoState {
    /// List of mono items left to compile
    to_compile: VecDeque<MonoItem>,
    /// Mapping between items with types specified and names
    translation: HashMap<(NameID, Vec<TypeVar>), NameID>,
}

impl MonoState {
    fn new() -> MonoState {
        MonoState {
            to_compile: VecDeque::new(),
            translation: HashMap::new(),
        }
    }

    /// Request compilation of a unit with the specified type parameters, returning the name of the
    /// unit which will be compiled with these parameters. It is up to the caller of this
    /// function to ensure that the type params are valid for this item.
    pub fn request_compilation(
        &mut self,
        source_name: NameID,
        params: Vec<TypeVar>,
        symtab: &mut FrozenSymtab,
    ) -> NameID {
        match self.translation.get(&(source_name.clone(), params.clone())) {
            Some(prev) => prev.clone(),
            None => {
                let new_name = symtab.new_name(source_name.1.clone());
                self.to_compile.push_back(MonoItem {
                    source_name,
                    new_name: new_name.clone(),
                    params,
                });
                new_name
            }
        }
    }

    fn next_target(&mut self) -> Option<MonoItem> {
        self.to_compile.pop_front()
    }
}

pub struct MirOutput {
    pub mir: mir::Entity,
    pub type_state: TypeState,
    /// Mapping between new names for registers and their previous value. Used
    /// to add type information for registers generated by pipelines
    pub reg_name_map: HashMap<NameID, NameID>,
}

pub fn compile_items(
    items: &HashMap<&NameID, (&ExecutableItem, TypeState)>,
    symtab: &mut FrozenSymtab,
    idtracker: &mut ExprIdTracker,
    item_list: &ItemList,
) -> Vec<Result<MirOutput>> {
    // Build a map of items to use for compilation later. Also push all non
    // generic items to the compilation queue

    let mut state = MonoState::new();

    for (_, (item, _)) in items {
        match item {
            ExecutableItem::Entity(e) => {
                if e.head.type_params.is_empty() {
                    state.request_compilation(e.name.inner.clone(), vec![], symtab);
                }
            }
            ExecutableItem::Pipeline(p) => {
                if p.head.type_params.is_empty() {
                    state.request_compilation(p.name.inner.clone(), vec![], symtab);
                }
            }
            ExecutableItem::StructInstance => {}
            ExecutableItem::EnumInstance { .. } => {}
        }
    }

    let mut result = vec![];
    while let Some(item) = state.next_target() {
        let original_item = items.get(&item.source_name);

        let mut reg_name_map = HashMap::new();
        match original_item {
            Some((ExecutableItem::Entity(e), old_type_state)) => {
                let mut type_state = old_type_state.clone();
                if !e.head.type_params.is_empty() {
                    let generic_list = type_state
                        .get_generic_list(&GenericListToken::Definition(e.name.inner.clone()))
                        .clone();

                    for (source_param, new) in e.head.type_params.iter().zip(item.params.iter()) {
                        let source_var = &generic_list[&source_param.name_id()];

                        match type_state.unify(source_var, new, symtab.symtab()) {
                            Ok(_) => {}
                            Err(e) => {
                                // TODO: Handle this gracefully
                                panic!("unification error during lowering {e}")
                            }
                        }
                    }
                }
                let out = generate_entity(e, symtab, idtracker, &type_state, item_list, &mut state)
                    .map(|mir| MirOutput {
                        mir,
                        type_state: type_state.clone(),
                        reg_name_map,
                    });
                result.push(out);
            }
            Some((ExecutableItem::Pipeline(p), type_state)) => {
                if !p.head.type_params.is_empty() {
                    // TODO: Implement
                    todo!()
                }
                let out = generate_pipeline(
                    p,
                    type_state,
                    symtab,
                    idtracker,
                    item_list,
                    &mut reg_name_map,
                    &mut state,
                )
                .map(|mir| MirOutput {
                    mir,
                    type_state: type_state.clone(),
                    reg_name_map,
                });
                result.push(out);
            }
            Some((ExecutableItem::StructInstance, _)) => {
                panic!("Requesting compilation of struct instance as module")
            }
            Some((ExecutableItem::EnumInstance { .. }, _)) => {
                panic!("Requesting compilation of enum instance as module")
            }
            None => {
                panic!(
                    "Requesting compilation of {} but no such item is present",
                    item.source_name
                )
            }
        }
    }
    result
}
