use parse_tree_macros::trace_typechecker;
use spade_common::location_info::WithLocation;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::{Pipeline, PipelineBinding, PipelineStage};

use crate::{equation::TypedExpression, fixed_types::t_clock, result::Error};

use super::{Result, TraceStackEntry, TypeState};

impl TypeState {
    #[trace_typechecker]
    pub fn visit_pipeline_binding(
        &mut self,
        binding: &PipelineBinding,
        symtab: &SymbolTable,
    ) -> Result<()> {
        self.visit_expression(&binding.value, symtab)?;

        if binding.type_spec.is_some() {
            todo!("Let bindings with fixed types are unsupported")
        }

        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Name(binding.name.clone().inner), new_type)
            .commit(self);

        self.unify_expression_generic_error(
            &binding.value,
            &TypedExpression::Name(binding.name.clone().inner),
            symtab,
        )?
        .commit(self);

        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_pipeline_stage(
        &mut self,
        stage: &PipelineStage,
        symtab: &SymbolTable,
    ) -> Result<()> {
        for binding in &stage.bindings {
            // Add a type eq for the name
            self.visit_pipeline_binding(binding, symtab)?;
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_pipeline(&mut self, pipeline: &Pipeline, symtab: &SymbolTable) -> Result<()> {
        let Pipeline {
            name: _,
            inputs,
            body,
            result,
            depth: _,
            output_type,
        } = pipeline;

        let generic_list = self.create_generic_list(&[]);

        // Add an equation for the clock
        let input_tvar = self.type_var_from_hir(&inputs[0].1.inner, &generic_list);
        self.add_equation(TypedExpression::Name(inputs[0].0.clone()), input_tvar)
            .commit(self);
        self.unify(
            &TypedExpression::Name(inputs[0].0.clone()),
            &t_clock(symtab),
            symtab,
        )
        .map_err(|(got, expected)| Error::FirstPipelineArgNotClock {
            expected,
            spec: got.at_loc(&inputs[0].1.loc()),
        })?
        .commit(self);

        // Add equations for the inputs
        for (name, t) in inputs.iter().skip(1) {
            let tvar = self.type_var_from_hir(t, &generic_list);
            self.add_equation(TypedExpression::Name(name.clone()), tvar)
                .commit(self);
        }

        // Go through the stages
        for stage in body {
            self.visit_pipeline_stage(stage, symtab)?
        }

        self.visit_expression(result, symtab)?;

        let tvar = self.type_var_from_hir(output_type, &generic_list);
        self.unify(&TypedExpression::Id(result.inner.id), tvar.as_ref(), symtab)
            .map_err(|(got, expected)| Error::EntityOutputTypeMismatch {
                expected,
                got,
                type_spec: output_type.loc(),
                output_expr: result.loc(),
            })?
            .commit(self);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::InnerTypeVar as TVar;
    use crate::InnerTypeVar;
    use crate::TypedExpression as TExpr;

    use crate::equation::TypeVarRef;
    use crate::{ensure_same_type, HasType};
    use crate::{fixed_types::t_int, format_trace_stack, hir, kvar};
    use hir::ItemList;
    use hir::{dtype, testutil::t_num, ExprKind, Expression, PipelineStage};
    use spade_ast::testutil::ast_path;
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;
    use spade_hir::symbol_table::SymbolTable;
    use spade_types::KnownType;

    #[test]
    fn pipeline_bindings_fixes_type_of_name() {
        let input = PipelineBinding {
            name: name_id(0, "a"),
            type_spec: None,
            value: Expression::ident(1, 1, "b").nowhere(),
        };

        let mut state = TypeState::new();
        let symtab = SymbolTable::new();

        let expr_a = TExpr::Name(name_id(1, "b").inner);
        state
            .add_equation(
                expr_a.clone(),
                TypeVarRef::from_owned(TVar::Unknown(100), &state),
            )
            .commit(&mut state);

        state.visit_pipeline_binding(&input, &symtab).unwrap();

        ensure_same_type!(
            state,
            TExpr::Name(name_id(1, "a").inner),
            TExpr::Name(name_id(1, "b").inner)
        );
    }

    #[test]
    fn pipelines_typecheck_correctly() {
        let mut symtab = SymbolTable::new();

        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = Pipeline {
            name: name_id(0, "pipe"),
            inputs: vec![
                (name_id(10, "clk").inner, dtype!(symtab => "clk")),
                (name_id(1, "a").inner, dtype!(symtab => "int"; (t_num(5)))),
            ],
            body: vec![
                PipelineStage {
                    bindings: vec![PipelineBinding {
                        name: name_id(3, "b"),
                        type_spec: None,
                        value: Expression::ident(2, 1, "a").nowhere(),
                    }
                    .nowhere()],
                }
                .nowhere(),
                PipelineStage { bindings: vec![] }.nowhere(),
            ],
            result: ExprKind::IntLiteral(0).with_id(10).nowhere(),
            depth: 3.nowhere(),
            output_type: dtype!(symtab => "int"; (t_num(8))),
        };

        let mut state = TypeState::new();

        state.visit_pipeline(&input, &mut symtab).unwrap();

        let a_type = kvar!( t_int(&symtab); ( kvar!( KnownType::Integer(5) ) ) );
        let ret_type = kvar!( t_int(&symtab); ( kvar!( KnownType::Integer(8) ) ) );
        let clk_type = kvar!(t_clock(&symtab));

        ensure_same_type!(state, TExpr::Name(name_id(1, "b").inner), a_type);
        ensure_same_type!(state, TExpr::Id(10), ret_type);
        ensure_same_type!(state, TExpr::Name(name_id(10, "clk").inner), clk_type);

        // ensure_same_type!(state, t_a, t_b);
    }

    #[test]
    fn pipeline_first_argument_is_clock() {
        // Add the head to the symtab
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        // Add the entity to the symtab
        let pipeline = Pipeline {
            name: name_id(0, "pipe"),
            inputs: vec![(name_id(1, "clk").inner, dtype!(symtab => "int"; (t_num(5))))],
            body: vec![
                PipelineStage {
                    bindings: vec![PipelineBinding {
                        name: name_id(3, "b"),
                        type_spec: None,
                        value: Expression::ident(2, 1, "a").nowhere(),
                    }
                    .nowhere()],
                }
                .nowhere(),
                PipelineStage { bindings: vec![] }.nowhere(),
            ],
            result: ExprKind::IntLiteral(0).with_id(10).nowhere(),
            depth: 3.nowhere(),
            output_type: dtype!(symtab => "int"; (t_num(8))),
        };

        let mut state = TypeState::new();

        match state.visit_pipeline(&pipeline, &symtab) {
            Err(Error::FirstPipelineArgNotClock { .. }) => {}
            other => {
                println!("{}", format_trace_stack(&state.trace_stack));
                panic!("Expected FirstPipelineArgNotClock, got {:?}", other)
            }
        }
    }
}
