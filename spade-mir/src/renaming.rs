use std::collections::HashMap;

use crate::{Binding, Entity, Register, ValueName};

struct NameState {
    /// Mapping between names and the amount of copies of that name we've seen so far
    names: HashMap<String, u64>,
    /// Mapping between ValueName and predictable name
    name_map: HashMap<ValueName, ValueName>,
}

impl NameState {
    pub fn new() -> NameState {
        Self {
            names: HashMap::new(),
            name_map: HashMap::new(),
        }
    }

    pub fn push(&mut self, name: &ValueName) {
        let new_name = match name {
            ValueName::Named(_, name_str) => {
                let id = self
                    .names
                    .entry(name_str.clone())
                    .and_modify(|v| *v = *v + 1)
                    .or_insert(0);

                ValueName::Named(*id, name_str.clone())
            }
            v @ ValueName::Expr(_) => v.clone(),
        };

        self.name_map.insert(name.clone(), new_name);
    }

    pub fn get(&mut self, name: &ValueName) -> ValueName {
        self.name_map
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.clone())
    }
}

pub fn make_names_predictable(e: &mut Entity) {
    let mut state = NameState::new();

    {
        // Walk through all statements adding defined names to the state
        let Entity {
            name: _, // we should not translate the outer name
            inputs,
            output: _,
            output_type: _,
            statements,
        } = e;

        for input in inputs {
            state.push(&input.1);
        }

        for stmt in statements {
            match stmt {
                crate::Statement::Binding(Binding {
                    name,
                    operator: _,
                    operands: _,
                    ty: _,
                    loc: _,
                }) => state.push(name),
                crate::Statement::Register(Register {
                    name,
                    ty: _,
                    clock: _,
                    reset: _,
                    value: _,
                    loc: _,
                }) => state.push(name),
                crate::Statement::Constant(_, _, _) => {}
                crate::Statement::Assert(_) => {}
                crate::Statement::Set {
                    target: _,
                    value: _,
                } => {}
            }
        }
    }

    {
        // Walk through the whole structure again, replacing names by their predictable versions
        let Entity {
            name: _, // we should not translate the outer name
            inputs,
            output,
            output_type: _,
            statements,
        } = e;

        for (_, val, _) in inputs.iter_mut() {
            *val = state.get(val)
        }

        *output = state.get(output);

        for stmt in statements.iter_mut() {
            match stmt {
                crate::Statement::Binding(Binding {
                    name,
                    operator: _,
                    operands,
                    ty: _,
                    loc: _,
                }) => {
                    *name = state.get(name);

                    for op in operands {
                        *op = state.get(op)
                    }
                }
                crate::Statement::Register(Register {
                    name,
                    ty: _,
                    clock,
                    reset,
                    value,
                    loc: _,
                }) => {
                    *name = state.get(name);
                    *clock = state.get(clock);
                    reset.as_mut().map(|(trig, val)| {
                        *trig = state.get(trig);
                        *val = state.get(val);
                    });
                    *value = state.get(value)
                }
                crate::Statement::Constant(_, _, _) => {}
                crate::Statement::Assert(val) => val.inner = state.get(val),
                crate::Statement::Set { target, value } => {
                    target.inner = state.get(target);
                    value.inner = state.get(value);
                }
            }
        }
    }
}