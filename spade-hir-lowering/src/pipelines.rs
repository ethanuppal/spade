use spade_common::{
    location_info::WithLocation,
    name::{Identifier, NameID},
    symbol_table::SymbolTracker,
};
use spade_hir::{Pipeline, PipelineBinding, PipelineStage};
use spade_mir as mir;
use spade_typeinference::TypeState;

use crate::{substitution::Substitutions, Result};
use crate::{ConcreteTypeLocal, ExprLocal, NameIDLocal, TypeStateLocal};

trait BindingLocal {
    fn lower(
        &self,
        types: &TypeState,
        live_vars: &mut Vec<NameID>,
        subs: &Substitutions,
    ) -> Result<Vec<mir::Statement>>;
}

impl BindingLocal for PipelineBinding {
    fn lower(
        &self,
        types: &TypeState,
        live_vars: &mut Vec<NameID>,
        subs: &Substitutions,
    ) -> Result<Vec<mir::Statement>> {
        // Code for the expression itself
        let mut result = self.value.lower(types, subs)?;

        // Add a let binding for this var
        result.push(mir::Statement::Binding(mir::Binding {
            name: self.name.value_name(),
            operator: mir::Operator::Alias,
            operands: vec![self.value.variable(subs)],
            ty: types.type_of_name(&self.name).to_mir_type(),
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
        types: &TypeState,
        id_tracker: &mut SymbolTracker,
        live_vars: &mut Vec<NameID>,
        clock: &NameID,
        subs: &mut Substitutions,
    ) -> Result<Vec<mir::Statement>>;
}
impl StageLocal for PipelineStage {
    fn lower(
        &self,
        stage_num: usize,
        types: &TypeState,
        id_tracker: &mut SymbolTracker,
        live_vars: &mut Vec<NameID>,
        clock: &NameID,
        subs: &mut Substitutions,
    ) -> Result<Vec<mir::Statement>> {
        // ExprKind::Block(block) => {
        //     for statement in &block.statements {
        //         result.append(&mut statement.lower(types)?);
        //     }
        //     result.append(&mut block.result.lower(types)?);

        //     // Empty. The block result will always be the last expression
        // }
        let mut result = vec![];

        // Generate the local expressions
        for binding in &self.bindings {
            result.append(&mut binding.lower(types, live_vars, subs)?);
        }

        // Generate pipeline regs for previous live vars
        for name in live_vars {
            let new_name = id_tracker.new_name(
                name.1
                    .push_ident(Identifier(format!("s{}", stage_num)).nowhere()),
            );

            result.push(mir::Statement::Register(mir::Register {
                name: new_name.value_name(),
                ty: types.type_of_name(name).to_mir_type(),
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
    id_tracker: &mut SymbolTracker,
) -> Result<mir::Entity> {
    let Pipeline {
        name,
        clock,
        inputs,
        body,
        result,
        depth: _,
        output_type: _,
    } = pipeline;

    let mut live_vars = inputs.iter().map(|var| var.0.clone()).collect();

    let mut inputs = inputs
        .iter()
        .map(|(name_id, _)| {
            let name = format!("_i_{}", name_id.1.to_string());
            let val_name = name_id.value_name();
            let ty = types.type_of_name(name_id).to_mir_type();

            (name, val_name, ty)
        })
        .collect::<Vec<_>>();

    let clk_input_name = format!("_i_{}", clock.1.to_string());
    let clk_val_name = clock.value_name();
    let clk_ty = types.type_of_name(clock).to_mir_type();
    inputs.insert(0, (clk_input_name, clk_val_name, clk_ty));

    let mut subs = Substitutions::new();
    let mut statements = vec![];
    for (stage_num, stage) in body.iter().enumerate() {
        statements.append(&mut stage.lower(
            stage_num,
            types,
            id_tracker,
            &mut live_vars,
            clock,
            &mut subs,
        )?);
    }
    let output = result.variable(&subs);

    let output_type = types.expr_type(&result)?.to_mir_type();

    Ok(mir::Entity {
        name: name.1.to_string(),
        inputs,
        output,
        output_type,
        statements,
    })
}
