use parse_tree_macros::local_impl;
use spade_common::{
    id_tracker::ExprIdTracker,
    location_info::WithLocation,
    name::{Identifier, NameID},
};
use spade_hir::{symbol_table::FrozenSymtab, ItemList, Pipeline, PipelineBinding, PipelineStage};
use spade_mir as mir;
use spade_typeinference::TypeState;

use crate::{substitution::Substitutions, Result};
use crate::{ConcreteTypeLocal, ExprLocal, NameIDLocal, PatternLocal, TypeStateLocal};

#[local_impl]
impl BindingLocal for PipelineBinding {
    fn lower(
        &self,
        symtab: &mut FrozenSymtab,
        idtracker: &mut ExprIdTracker,
        types: &TypeState,
        live_vars: &mut Vec<NameID>,
        subs: &Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        // Code for the expression itself
        let mut result = self
            .value
            .lower(symtab, idtracker, types, subs, item_list)?;

        // Add a let binding for this var
        result.push(mir::Statement::Binding(mir::Binding {
            name: self.pat.value_name(),
            operator: mir::Operator::Alias,
            operands: vec![self.value.variable(subs)],
            ty: types
                .type_of_id(self.pat.id, symtab.symtab(), &item_list.types)
                .to_mir_type(),
        }));

        // Add this variable to the live vars list
        for name in self.pat.get_names() {
            live_vars.push(name.clone());
        }

        Ok(result)
    }
}

#[local_impl]
impl StageLocal for PipelineStage {
    fn lower(
        &self,
        stage_num: usize,
        symtab: &mut FrozenSymtab,
        idtracker: &mut ExprIdTracker,
        types: &TypeState,
        live_vars: &mut Vec<NameID>,
        clock: &NameID,
        subs: &mut Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = vec![];

        // Generate the local expressions
        for binding in &self.bindings {
            result
                .append(&mut binding.lower(symtab, idtracker, types, live_vars, subs, item_list)?);
        }

        // Generate pipeline regs for previous live vars
        for name in live_vars {
            let new_name = symtab.new_name(
                name.1
                    .push_ident(Identifier(format!("s{}", stage_num)).nowhere()),
            );

            result.push(mir::Statement::Register(mir::Register {
                name: new_name.value_name(),
                ty: types
                    .type_of_name(name, symtab.symtab(), &item_list.types)
                    .to_mir_type(),
                clock: clock.value_name(),
                reset: None,
                value: subs.lookup(name).value_name(),
            }));

            subs.replace(name.clone(), new_name.clone());
        }

        Ok(result)
    }
}

pub fn generate_pipeline<'a>(
    pipeline: &Pipeline,
    types: &TypeState,
    symtab: &mut FrozenSymtab,
    idtracker: &mut ExprIdTracker,
    item_list: &ItemList,
) -> Result<mir::Entity> {
    let Pipeline {
        name,
        inputs,
        body,
        result,
        depth: _,
        output_type: _,
    } = pipeline;

    // Skip because the clock does not need to be pipelined
    let mut live_vars = inputs.iter().skip(1).map(|var| var.0.clone()).collect();

    let lowered_inputs = inputs
        .iter()
        .map(|(name_id, _)| {
            let name = name_id.1.to_string();
            let val_name = name_id.value_name();
            let ty = types
                .type_of_name(name_id, symtab.symtab(), &item_list.types)
                .to_mir_type();

            (name, val_name, ty)
        })
        .collect::<Vec<_>>();

    let mut subs = Substitutions::new();
    let mut statements = vec![];
    for (stage_num, stage) in body.iter().enumerate() {
        statements.append(&mut stage.lower(
            stage_num,
            symtab,
            idtracker,
            types,
            &mut live_vars,
            &inputs[0].0,
            &mut subs,
            item_list,
        )?);
    }

    statements.append(&mut result.lower(symtab, idtracker, types, &subs, item_list)?);

    let output = result.variable(&subs);

    let output_type = types
        .expr_type(&result, symtab.symtab(), &item_list.types)?
        .to_mir_type();

    Ok(mir::Entity {
        name: name.1.to_string(),
        inputs: lowered_inputs,
        output,
        output_type,
        statements,
    })
}
