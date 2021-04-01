use parse_tree_macros::trace_typechecker;
use spade_ast_lowering::symbol_table::SymbolTable;
use spade_hir::{Pipeline, PipelineBinding, PipelineStage};

use crate::{equation::TypedExpression, fixed_types::t_clock, result::Error};

use super::{Result, TraceStack, TypeState};

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
        self.add_equation(TypedExpression::Name(binding.name.clone().inner), new_type);

        self.unify_expression_generic_error(
            &binding.value,
            &TypedExpression::Name(binding.name.clone().inner),
        )?;

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
            clock,
            inputs,
            body,
            result,
            depth: _,
            output_type,
        } = pipeline;

        // Add an equation for the clock
        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Name(clock.clone().inner), new_type);
        self.unify_types(&TypedExpression::Name(clock.clone().inner), &t_clock())
            .map_err(|(got, expected)| Error::NonClockClock {
                expected,
                got,
                loc: clock.loc(),
            })?;

        // Add equations for the inputs
        for (name, t) in inputs {
            self.add_equation(
                TypedExpression::Name(name.clone()),
                Self::type_var_from_hir(t),
            );
        }

        // Go through the stages
        for stage in body {
            self.visit_pipeline_stage(stage, symtab)?
        }

        self.visit_expression(result, symtab)?;

        self.unify_types(
            &TypedExpression::Id(result.inner.id),
            &Self::type_var_from_hir(output_type),
        )
        .map_err(|(got, expected)| Error::EntityOutputTypeMismatch {
            expected,
            got,
            type_spec: output_type.loc(),
            output_expr: result.loc(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::TypeVar as TVar;
    use crate::TypedExpression as TExpr;

    use crate::{ensure_same_type, get_type, HasType};
    use crate::{format_trace_stack, hir};
    use hir::{ExprKind, Expression, PipelineStage, TypeExpression, TypeSpec};
    use spade_ast_lowering::symbol_table::SymbolTable;
    use spade_common::location_info::WithLocation;
    use spade_testutil::name_id;
    use spade_types::{BaseType, KnownType};

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
        state.add_equation(expr_a.clone(), TVar::Generic(100));

        state.visit_pipeline_binding(&input, &symtab).unwrap();

        let t_a = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let t_b = get_type!(state, &TExpr::Name(name_id(1, "b").inner));

        ensure_same_type!(state, t_a, t_b);
    }

    #[test]
    fn pipelines_typecheck_correctly() {
        let input = Pipeline {
            name: name_id(0, "pipe"),
            clock: name_id(4, "clk"),
            inputs: vec![(
                name_id(1, "a").inner,
                TypeSpec::Concrete(
                    BaseType::Int.nowhere(),
                    vec![TypeExpression::Integer(5).nowhere()],
                )
                .nowhere(),
            )],
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
            output_type: TypeSpec::Concrete(
                BaseType::Int.nowhere(),
                vec![TypeExpression::Integer(8).nowhere()],
            )
            .nowhere(),
        };

        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();

        state.visit_pipeline(&input, &mut symtab).unwrap();

        let a_type = TVar::Known(
            KnownType::Type(BaseType::Int),
            vec![TVar::Known(KnownType::Integer(5), vec![], None)],
            None,
        );
        let ret_type = TVar::Known(
            KnownType::Type(BaseType::Int),
            vec![TVar::Known(KnownType::Integer(8), vec![], None)],
            None,
        );
        let clk_type = TVar::Known(KnownType::Type(BaseType::Clock), vec![], None);

        let t_b = get_type!(state, &TExpr::Name(name_id(1, "b").inner));
        let t_ret = get_type!(state, &TExpr::Id(10));
        let t_clk = get_type!(state, &TExpr::Name(name_id(4, "clk").inner));

        ensure_same_type!(state, t_b, a_type);
        ensure_same_type!(state, t_ret, ret_type);
        ensure_same_type!(state, t_clk, clk_type);

        // ensure_same_type!(state, t_a, t_b);
    }
}
