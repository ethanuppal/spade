use num::{BigInt, One};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::Identifier;
use spade_common::num_ext::InfallibleToBigUint;
use spade_diagnostics::diagnostic::DiagnosticLevel;
use spade_diagnostics::{diag_anyhow, Diagnostic};
use spade_hir::expression::{BinaryOperator, NamedArgument, UnaryOperator};
use spade_hir::{ExprKind, Expression};
use spade_macros::trace_typechecker;
use spade_types::KnownType;

use crate::constraints::{bits_to_store, ce_int, ce_var, ConstraintSource};
use crate::equation::{TypeVar, TypedExpression};
use crate::error::{TypeMismatch as Tm, UnificationErrorExt};
use crate::fixed_types::{t_bit, t_bool, t_void};
use crate::requirements::Requirement;
use crate::{kvar, Context, GenericListToken, HasType, Result, TraceStackEntry, TypeState};

macro_rules! assuming_kind {
    ($pattern:pat = $expr:expr => $block:block) => {
        if let $pattern = &$expr.inner.kind {
            $block
        } else {
            panic!("Incorrect assumption about expression kind")
        };
    };
}

impl TypeState {
    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_identifier(&mut self, expression: &Loc<Expression>, ctx: &Context) -> Result<()> {
        assuming_kind!(ExprKind::Identifier(ident) = &expression => {
            // Add an equation for the anonymous id
            self.unify_expression_generic_error(
                &expression,
                &TypedExpression::Name(ident.clone()),
                ctx
            )?;
        });
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_pipeline_ref(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
    ) -> Result<()> {
        assuming_kind!(ExprKind::PipelineRef{stage: _, name, declares_name} = &expression => {
            // If this reference declares the referenced name, add a new equation
            if *declares_name {
                let new_var = self.new_generic();
                self.add_equation(TypedExpression::Name(name.clone().inner), new_var)
            }

            // Add an equation for the anonymous id
            self.unify_expression_generic_error(
                &expression,
                &TypedExpression::Name(name.clone().inner),
                ctx
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_int_literal(&mut self, expression: &Loc<Expression>, ctx: &Context) -> Result<()> {
        assuming_kind!(ExprKind::IntLiteral(value) = &expression => {
            let t = self.new_generic_int(&ctx.symtab);
            self.unify(&t, &expression.inner, ctx)
                .into_diagnostic(expression.loc(), |diag, Tm{e: _, g: _got}| {
                    diag
                        .level(DiagnosticLevel::Bug)
                        .message("Failed to unify integer literal with integer")
                })?;
            self.add_requirement(Requirement::FitsIntLiteral {
                value: value.clone(),
                target_type: t.at_loc(&expression)
            });
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_bool_literal(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
    ) -> Result<()> {
        assuming_kind!(ExprKind::BoolLiteral(_) = &expression => {
            self.unify_expression_generic_error(&expression, &t_bool(&ctx.symtab), ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_bit_literal(&mut self, expression: &Loc<Expression>, ctx: &Context) -> Result<()> {
        assuming_kind!(ExprKind::BitLiteral(_) = &expression => {
            self.unify_expression_generic_error(&expression, &t_bit(&ctx.symtab), ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_tuple_literal(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TupleLiteral(inner) = &expression => {
            for expr in inner {
                self.visit_expression(expr, ctx, generic_list)?;
                // NOTE: safe unwrap, we know this expr has a type because we just visited
            }

            let mut inner_types = vec![];
            for expr in inner {
                let t = self.type_of(&TypedExpression::Id(expr.id)).unwrap();

                inner_types.push(t);
            }

            self.unify_expression_generic_error(
                &expression,
                &TypeVar::Known(KnownType::Tuple, inner_types),
                ctx
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_tuple_index(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TupleIndex(tup, index) = &expression => {
            self.visit_expression(tup, ctx, generic_list)?;
            let t = self.type_of(&TypedExpression::Id(tup.id))?;

            let inner_types = match t {
                TypeVar::Known(KnownType::Tuple, inner) => inner,
                t @ TypeVar::Known(_, _) => {
                    return Err(Diagnostic::error(tup.loc(), "Attempt to use tuple indexing on non-tuple")
                        .primary_label(format!("expected tuple, got {t}"))
                        .secondary_label(index, "Because this is a tuple index")
                        .into()
                    );
                }
                TypeVar::Unknown(_, _) => {
                    return Err(
                        Diagnostic::error(tup.as_ref(), "Type of tuple indexee must be known at this point")
                            .primary_label("The type of this must be known")
                    )
                }
            };

            if (index.inner as usize) < inner_types.len() {
                let true_inner_type = inner_types[index.inner as usize].clone();
                self.unify_expression_generic_error(
                    &expression,
                    &true_inner_type,
                    ctx
                )?
            } else {
                return Err(Diagnostic::error(index, "Tuple index out of bounds")
                    .primary_label(format!("Tuple only has {} elements", inner_types.len()))
                    .note(format!("     Index: {}", index))
                    .note(format!("Tuple size: {}", inner_types.len()))
                );
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_field_access(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::FieldAccess(target, field) = &expression => {
            self.visit_expression(&target, ctx, generic_list)?;

            let target_type = self.type_of(&TypedExpression::Id(target.id))?;
            let self_type = self.type_of(&TypedExpression::Id(expression.id))?;

            let requirement = Requirement::HasField {
                target_type: target_type.at_loc(target),
                field: field.clone(),
                expr: self_type.at_loc(expression)
            };

            requirement.check_or_add(self, ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_method_call(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::MethodCall{call_kind: _, target, name, args} = &expression => {
            // NOTE: We don't visit_expression here as it is being added to the argument_list
            // which we *do* visit
            // self.visit_expression(target, ctx, generic_list)?;

            let args_with_self = args.clone().map(|mut args| {
                match &mut args {
                    spade_hir::ArgumentList::Named(inner) => {
                        inner.push(NamedArgument::Full(
                            Identifier("self".to_string()).at_loc(target),
                            target.as_ref().clone()
                        ))
                    },
                    spade_hir::ArgumentList::Positional(list) => list.insert(0, target.as_ref().clone()),
                };
                args
            });

            self.visit_argument_list(&args_with_self, ctx, generic_list)?;

            let target_type = self.type_of(&TypedExpression::Id(target.id))?;
            let self_type = self.type_of(&TypedExpression::Id(expression.id))?;

            let requirement = Requirement::HasMethod {
                expr_id: expression.map_ref(|e| e.id),
                target_type: target_type.at_loc(target),
                method: name.clone(),
                expr: self_type.at_loc(expression),
                args: args_with_self
            };

            requirement.check_or_add(self, ctx)?
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_array_literal(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::ArrayLiteral(members) = &expression => {
            for expr in members {
                self.visit_expression(expr, ctx, generic_list)?;
            }

            for (l, r) in members.iter().zip(members.iter().skip(1)) {
                self.unify(r, l, ctx)
                    .into_diagnostic(r, |diag, Tm{e: expected, g: _got}| {
                        diag.message(format!(
                            "Array element type mismatch. Expected {}",
                            expected
                        ))
                        .primary_label(format!("Expected {}", expected))
                        .secondary_label(members.first().unwrap().loc(), format!("To match this"))
                    })?;
            }

            let inner_type = if members.is_empty() {
                self.new_generic()
            }
            else {
                members[0].get_type(self)?
            };

            let size_type = kvar!(KnownType::Integer(members.len().to_biguint()));
            let result_type = TypeVar::array(
                inner_type,
                size_type,
            );

            self.unify_expression_generic_error(expression, &result_type, ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_create_ports(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        _generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::CreatePorts = &expression => {
            let inner_type = self.new_generic();
            let inverted = TypeVar::Known(KnownType::Inverted, vec![inner_type.clone()]);
            let compound = TypeVar::tuple(vec![inner_type, inverted]);
            self.unify_expression_generic_error(expression, &compound, ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_index(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Index(target, index) = &expression => {
            // Visit child nodes
            self.visit_expression(&target, ctx, generic_list)?;
            self.visit_expression(&index, ctx, generic_list)?;

            // Add constraints
            let inner_type = self.new_generic();

            // Unify inner type with this expression
            self.unify_expression_generic_error(
                &expression,
                &inner_type,
                ctx
            )?;

            let array_size = self.new_generic();
            let (int_type, int_size) = self.new_split_generic_int(&&ctx.symtab);

            // NOTE[et]: Only used for size constraints of this exact type - this can be a
            // requirement instead, that way we remove a lot of complexity! :D
            self.add_constraint(
                int_size,
                bits_to_store(ce_var(&array_size) - ce_int(BigInt::one())),
                index.loc(),
                &int_type,
                ConstraintSource::ArrayIndexing
            );

            self.unify(&index.inner, &int_type, ctx)
                .into_diagnostic(index.as_ref(), |diag, Tm{e: _expected, g: got}| {

                    diag.message(format!("Index must be an integer, got {}", got))
                        .primary_label(format!("Expected integer"))
                })?;

            let array_type = TypeVar::array(
                expression.get_type(self)?,
                array_size
            );
            self.unify(&target.inner, &array_type, ctx)
                .into_diagnostic(target.as_ref(), |diag, Tm{e: _expected, g: got}| {
                    diag
                        .message(format!("Index target must be an array, got {}", got))
                        .primary_label(format!("Expected array"))
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_block_expr(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Block(block) = expression => {
            self.visit_block(block, ctx, generic_list)?;

            if let Some(result) = &block.result {
                // Unify the return type of the block with the type of this expression
                self.unify(&expression.inner, &result.inner, ctx)
                    // NOTE: We could be more specific about this error specifying
                    // that the type of the block must match the return type, though
                    // that might just be spammy.
                    .into_default_diagnostic(result)?;
            } else {
                // Block without return value. Unify with void type.
                self.unify(&expression.inner, &t_void(ctx.symtab), ctx)
                    .into_diagnostic(Loc::nowhere(()), |err, Tm{g: _, e: _}| {
                        diag_anyhow!(
                            Loc::nowhere(()),
                            "This error shouldn't be possible: {err:?}"
                        ).into()})?;
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_if(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::If(cond, on_true, on_false) = &expression => {
            self.visit_expression(&cond, ctx, generic_list)?;
            self.visit_expression(&on_true, ctx, generic_list)?;
            self.visit_expression(&on_false, ctx, generic_list)?;

            self.unify(&cond.inner, &t_bool(&ctx.symtab), ctx)
                .into_diagnostic(cond.as_ref(), |diag, Tm{e: _expected, g: got}| {
                    diag.
                        message(format!("If condition must be a bool, got {}", got))
                        .primary_label("Expected boolean")
                })?;
            self.unify(&on_true.inner, &on_false.inner, ctx)
                .into_diagnostic(on_false.as_ref(), |diag, Tm{e: expected, g: got}| {
                    diag.message("If branches have incompatible type")
                        .primary_label(format!("But this has type {expected}"))
                        .secondary_label(on_true.as_ref(), format!("This branch has type {got}"))
                })?;
            self.unify(expression, &on_false.inner, ctx)
                .into_default_diagnostic(expression)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_match(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Match(cond, branches) = &expression => {
            self.visit_expression(&cond, ctx, generic_list)?;

            for (i, (pattern, result)) in branches.iter().enumerate() {
                self.visit_pattern(pattern, ctx, generic_list)?;
                self.visit_expression(result, ctx, generic_list)?;

                self.unify(&cond.inner, pattern, ctx)
                    .into_default_diagnostic(pattern)?;

                if i != 0 {
                    self.unify(&branches[0].1, result, ctx).into_diagnostic(
                        result,
                        |diag, Tm{e: _expected, g: got}| {
                            diag.message("Match branches have incompatible type")
                                .primary_label("This branch has type {}")
                                .secondary_label(&branches[0].1, format!("But this one has type {got}"))
                        }
                    )?;
                }
            }

            assert!(
                !branches.is_empty(),
                "Empty match statements should be checked by ast lowering"
            );

            self.unify_expression_generic_error(&branches[0].1, expression, ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_binary_operator(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::BinaryOperator(lhs, op, rhs) = &expression => {
            self.visit_expression(&lhs, ctx, generic_list)?;
            self.visit_expression(&rhs, ctx, generic_list)?;
            match *op {
                BinaryOperator::Add
                | BinaryOperator::Sub | BinaryOperator::Mul if self.use_wordlenght_inference => {
                    let lhs_t = self.new_generic_int(&ctx.symtab);
                    self.unify_expression_generic_error(&lhs, &lhs_t, ctx)?;
                    let rhs_t = self.new_generic_int(&ctx.symtab);
                    self.unify_expression_generic_error(&rhs, &rhs_t, ctx)?;
                    let result_t = self.new_generic_int(&ctx.symtab);
                    self.unify_expression_generic_error(expression, &result_t, ctx)?;
                }
                BinaryOperator::Add
                | BinaryOperator::Sub => {
                    let (lhs_t, lhs_size) = self.new_split_generic_int(&ctx.symtab);
                    let (result_t, result_size) = self.new_split_generic_int(&ctx.symtab);

                    self.add_constraint(
                        result_size.clone(),
                        ce_var(&lhs_size) + ce_int(BigInt::one()),
                        expression.loc(),
                        &result_t,
                        ConstraintSource::AdditionOutput
                    );
                    self.add_constraint(
                        lhs_size.clone(),
                        ce_var(&result_size) + -ce_int(BigInt::one()),
                        lhs.loc(),
                        &lhs_t,
                        ConstraintSource::AdditionOutput
                    );

                    // FIXME: Make generic over types that can be added
                    self.unify_expression_generic_error(&lhs, &lhs_t, ctx)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, ctx)?;
                    self.unify_expression_generic_error(expression, &result_t, ctx)?;
                }
                BinaryOperator::Mul => {
                    let (lhs_t, lhs_size) = self.new_split_generic_int(&ctx.symtab);
                    let (rhs_t, rhs_size) = self.new_split_generic_int(&ctx.symtab);
                    let (result_t, result_size) = self.new_split_generic_int(&ctx.symtab);

                    // Result size is sum of input sizes
                    self.add_constraint(
                        result_size.clone(),
                        ce_var(&lhs_size) + ce_var(&rhs_size),
                        expression.loc(),
                        &result_t,
                        ConstraintSource::MultOutput
                    );
                    self.add_constraint(
                        lhs_size.clone(),
                        ce_var(&result_size) + -ce_var(&rhs_size),
                        lhs.loc(),
                        &lhs_t,
                        ConstraintSource::MultOutput
                    );
                    self.add_constraint(rhs_size.clone(),
                        ce_var(&result_size) + -ce_var(&lhs_size),
                        rhs.loc(),
                        &rhs_t
                        , ConstraintSource::MultOutput
                    );

                    self.unify_expression_generic_error(&lhs, &lhs_t, ctx)?;
                    self.unify_expression_generic_error(&rhs, &rhs_t, ctx)?;
                    self.unify_expression_generic_error(expression, &result_t, ctx)?;
                }
                // Shift operators have the same width in as they do out
                BinaryOperator::LeftShift
                | BinaryOperator::BitwiseAnd
                | BinaryOperator::BitwiseXor
                | BinaryOperator::BitwiseOr
                | BinaryOperator::ArithmeticRightShift
                | BinaryOperator::RightShift => {
                    let int_type = self.new_generic_int(&ctx.symtab);

                    // FIXME: Make generic over types that can be bitmanipulated
                    self.unify_expression_generic_error(&lhs, &int_type, ctx)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, ctx)?;
                    self.unify_expression_generic_error(expression, &rhs.inner, ctx)?;
                }
                BinaryOperator::Eq
                | BinaryOperator::NotEq
                | BinaryOperator::Gt
                | BinaryOperator::Lt
                | BinaryOperator::Ge
                | BinaryOperator::Le => {
                    let int_type = self.new_generic_int(&ctx.symtab);
                    // FIXME: Make generic over types that can be compared
                    self.unify_expression_generic_error(&lhs, &int_type, ctx)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, ctx)?;
                    self.unify_expression_generic_error(expression, &t_bool(&ctx.symtab), ctx)?;
                }
                BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::LogicalXor => {
                    self.unify_expression_generic_error(&lhs, &t_bool(&ctx.symtab), ctx)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, ctx)?;

                    self.unify_expression_generic_error(expression, &t_bool(&ctx.symtab), ctx)?;
                }
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_unary_operator(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::UnaryOperator(op, operand) = &expression => {
            self.visit_expression(&operand, ctx, generic_list)?;
            match op {
                UnaryOperator::Sub | UnaryOperator::BitwiseNot => {
                    let int_type = self.new_generic_int(&ctx.symtab);
                    self.unify_expression_generic_error(operand, &int_type, ctx)?;
                    self.unify_expression_generic_error(expression, &int_type, ctx)?
                }
                UnaryOperator::Not => {
                    self.unify_expression_generic_error(operand, &t_bool(&ctx.symtab), ctx)?;
                    self.unify_expression_generic_error(expression, &t_bool(&ctx.symtab), ctx)?
                }
                UnaryOperator::Dereference => {
                    let result_type = self.new_generic();
                    let reference_type = TypeVar::wire(result_type.clone());
                    self.unify_expression_generic_error(operand, &reference_type, ctx)?;
                    self.unify_expression_generic_error(expression, &result_type, ctx)?
                }
                UnaryOperator::Reference => {
                    let result_type = self.new_generic();
                    let reference_type = TypeVar::wire(result_type.clone());
                    self.unify_expression_generic_error(operand, &result_type, ctx)?;
                    self.unify_expression_generic_error(expression, &reference_type, ctx)?
                }
                UnaryOperator::FlipPort => {
                    let inner_type = self.new_generic();
                    let inverted_type = TypeVar::inverted(inner_type.clone());
                    self.unify_expression_generic_error(operand, &inner_type, ctx)?;
                    self.unify_expression_generic_error(expression, &inverted_type, ctx)?
                }
            }
        });
        Ok(())
    }
}
