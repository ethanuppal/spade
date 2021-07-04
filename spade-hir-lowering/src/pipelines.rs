use spade_common::{
    location_info::WithLocation,
    name::{Identifier, NameID},
};
use spade_hir::{
    symbol_table::{FrozenSymtab, SymbolTable},
    Pipeline, PipelineBinding, PipelineStage, TypeList,
};
use spade_mir as mir;
use spade_typeinference::TypeState;

use crate::{substitution::Substitutions, Result};
use crate::{ConcreteTypeLocal, ExprLocal, NameIDLocal, TypeStateLocal};

trait BindingLocal {
    fn lower(
        &self,
        symtab: &SymbolTable,
        types: &TypeState,
        live_vars: &mut Vec<NameID>,
        subs: &Substitutions,
        type_list: &TypeList,
    ) -> Result<Vec<mir::Statement>>;
}

impl BindingLocal for PipelineBinding {
    fn lower(
        &self,
        symtab: &SymbolTable,
        types: &TypeState,
        live_vars: &mut Vec<NameID>,
        subs: &Substitutions,
        type_list: &TypeList,
    ) -> Result<Vec<mir::Statement>> {
        // Code for the expression itself
        let mut result = self.value.lower(symtab, types, subs, type_list)?;

        // Add a let binding for this var
        result.push(mir::Statement::Binding(mir::Binding {
            name: self.name.value_name(),
            operator: mir::Operator::Alias,
            operands: vec![self.value.variable(subs)],
            ty: types
                .type_of_name(&self.name, symtab, type_list)
                .to_mir_type(),
        }));

        // Add this variable to the live vars list
        live_vars.push(self.name.inner.clone());

        Ok(result)
    }
}

trait StageLocal {
    fn lower(
        &self,
        stage_num: usize,
        symtab: &mut FrozenSymtab,
        types: &TypeState,
        live_vars: &mut Vec<NameID>,
        clock: &NameID,
        subs: &mut Substitutions,
        type_list: &TypeList,
    ) -> Result<Vec<mir::Statement>>;
}
impl StageLocal for PipelineStage {
    fn lower(
        &self,
        stage_num: usize,
        symtab: &mut FrozenSymtab,
        types: &TypeState,
        live_vars: &mut Vec<NameID>,
        clock: &NameID,
        subs: &mut Substitutions,
        type_list: &TypeList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = vec![];

        // Generate the local expressions
        for binding in &self.bindings {
            result.append(&mut binding.lower(
                symtab.symtab(),
                types,
                live_vars,
                subs,
                type_list,
            )?);
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
                    .type_of_name(name, symtab.symtab(), type_list)
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
    type_list: &TypeList,
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
            let name = format!("_i_{}", name_id.1.to_string());
            let val_name = name_id.value_name();
            let ty = types
                .type_of_name(name_id, symtab.symtab(), type_list)
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
            types,
            &mut live_vars,
            &inputs[0].0,
            &mut subs,
            type_list,
        )?);
    }

    statements.append(&mut result.lower(symtab.symtab(), types, &subs, type_list)?);

    let output = result.variable(&subs);

    let output_type = types
        .expr_type(&result, symtab.symtab(), type_list)?
        .to_mir_type();

    Ok(mir::Entity {
        name: name.1.to_string(),
        inputs: lowered_inputs,
        output,
        output_type,
        statements,
    })
}
