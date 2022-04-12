use parse_tree_macros::trace_typechecker;
use spade_common::location_info::Loc;
use spade_hir::expression::{BinaryOperator, UnaryOperator};
use spade_hir::symbol_table::{SymbolTable, TypeDeclKind, TypeSymbol};
use spade_hir::{ExprKind, Expression};
use spade_types::KnownType;

use crate::constraints::{bits_to_store, ce_int, ce_var, ConstraintSource};
use crate::equation::{TypeVar, TypedExpression};
use crate::fixed_types::t_bool;
use crate::result::{Error, UnificationErrorExt};
use crate::{kvar, Result};
use crate::{GenericListToken, TypeState};
use crate::{HasType, TraceStackEntry};

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
    pub fn visit_identifier(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Identifier(ident) = &expression => {
            // Add an equation for the anonymous id
            self.unify_expression_generic_error(
                &expression,
                &TypedExpression::Name(ident.clone()),
                symtab,
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_int_literal(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::IntLiteral(_) = &expression => {
            let t = self.new_generic_int(symtab);
            self.unify(&t, &expression.inner, symtab)
                .map_normal_err(|(_, got)| Error::IntLiteralIncompatible {
                    got,
                    loc: expression.loc(),
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_bool_literal(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::BoolLiteral(_) = &expression => {
            self.unify_expression_generic_error(&expression, &t_bool(symtab), symtab)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_tuple_literal(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TupleLiteral(inner) = &expression => {
            for expr in inner {
                self.visit_expression(expr, symtab, generic_list)?;
                // NOTE: safe unwrap, we know this expr has a type because we just visited
            }

            let mut inner_types = vec![];
            for expr in inner {
                let t = self.type_of(&TypedExpression::Id(expr.id)).unwrap();

                inner_types.push(t);
            }

            self.unify_expression_generic_error(
                &expression,
                &TypeVar::Tuple(inner_types),
                symtab,
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_tuple_index(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TupleIndex(tup, index) = &expression => {
            self.visit_expression(tup, symtab, generic_list)?;
            let t = self.type_of(&TypedExpression::Id(tup.id));

            match t {
                Ok(TypeVar::Tuple(inner)) => {
                    if (index.inner as usize) < inner.len() {
                        self.unify_expression_generic_error(
                            &expression,
                            &inner[index.inner as usize],
                            symtab,
                        )?
                    } else {
                        return Err(Error::TupleIndexOutOfBounds {
                            index: index.clone(),
                            actual_size: inner.len() as u128,
                        });
                    }
                }
                Ok(t @ TypeVar::Known(_, _) | t @ TypeVar::Array { .. }) => {
                    return Err(Error::TupleIndexOfNonTuple {
                        got: t.clone(),
                        loc: tup.loc(),
                    })
                }
                Ok(TypeVar::Unknown(_)) => {
                    return Err(Error::TupleIndexOfGeneric { loc: tup.loc() })
                }
                Err(e) => return Err(e.clone()),
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_field_access(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::FieldAccess(target, field) = &expression => {
            self.visit_expression(&target, symtab, generic_list)?;

            let t = self.type_of(&TypedExpression::Id(target.id));

            match t {
                Ok(TypeVar::Known(inner, _)) => {
                    // Look up the type of the known var
                    match inner {
                        KnownType::Type(inner) => {
                            // Check if we're dealing with a struct
                            match symtab.type_symbol_by_id(&inner).inner {
                                TypeSymbol::Declared(_, TypeDeclKind::Struct) => {}
                                TypeSymbol::Declared(_, TypeDeclKind::Enum) => {
                                    return Err(Error::FieldAccessOnEnum{
                                        loc: target.loc(),
                                        actual_type: inner.clone()
                                    })
                                }
                                TypeSymbol::Declared(_, TypeDeclKind::Primitive) => {
                                    return Err(Error::FieldAccessOnPrimitive {
                                        loc: target.loc(),
                                        actual_type: inner.clone()
                                    })
                                }
                                TypeSymbol::GenericArg | TypeSymbol::GenericInt => {
                                    return Err(Error::FieldAccessOnGeneric{
                                        loc: target.loc(),
                                        name: inner.clone()
                                    })
                                }
                            }

                            // Get the struct, find the type of the field and unify
                            let s = symtab.struct_by_id(&inner);

                            let field_spec = if let Some(spec) = s.params.try_get_arg_type(field) {
                                spec
                            }
                            else {
                                return Err(Error::NoSuchField{field: field.clone(), _struct: inner.clone()})
                            };

                            let field_type = self.type_var_from_hir(&field_spec, generic_list);

                            self.unify_expression_generic_error(expression, &field_type, symtab)?
                                ;
                        },
                        KnownType::Integer(_) => {
                            return Err(Error::FieldAccessOnInteger{loc: expression.loc()})
                        },
                    }
                }
                Ok(TypeVar::Unknown(_)) => {
                    return Err(Error::FieldAccessOnIncomplete{loc: expression.loc()})
                }
                Ok(other) => {
                    return Err(Error::FieldAccessOnNonStruct{ loc: expression.loc(), got: other.clone() })
                }
                Err(e) => return Err(e.clone())
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_array_literal(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::ArrayLiteral(members) = &expression => {
            for expr in members {
                self.visit_expression(expr, symtab, generic_list)?;
            }

            for (l, r) in members.iter().zip(members.iter().skip(1)) {
                self.unify(l, r, symtab)
                    .map_normal_err(|(expected, got)| Error::ArrayElementMismatch {
                        got,
                        expected,
                        loc: r.loc(),
                        first_element: members.first().unwrap().loc(),
                    })?;
            }

            let inner_type = if members.is_empty() {
                self.new_generic()
            }
            else {
                members[0].get_type(self)?
            };

            let size_type = kvar!(KnownType::Integer(members.len() as u128));
            let result_type = TypeVar::Array {
                inner: Box::new(inner_type),
                size: Box::new(size_type),
            };

            self.unify_expression_generic_error(expression, &result_type, symtab)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_index(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Index(target, index) = &expression => {
            // Visit child nodes
            self.visit_expression(&target, symtab, generic_list)?;
            self.visit_expression(&index, symtab, generic_list)?;

            // Add constraints
            let inner_type = self.new_generic();

            // Unify inner type with this expression
            self.unify_expression_generic_error(
                &expression,
                &inner_type,
                symtab
            )?;

            let array_size = self.new_generic();
            let (int_type, int_size) = self.new_split_generic_int(&symtab);

            self.add_constraint(
                int_size,
                bits_to_store(ce_var(&array_size) - ce_int(1)),
                index.loc(),
                &int_type,
                ConstraintSource::ArrayIndexing
            );

            // self.add_equation(TypedExpression::Id(index.id), int_type.clone());
            self.unify(&index.inner, &int_type, symtab)
                .map_normal_err(|(got, _)| {
                    Error::IndexMustBeInteger{got, loc: index.loc()}
                })?;

            let array_type = TypeVar::Array{
                inner: Box::new(expression.get_type(self)?),
                size: Box::new(array_size)
            };
            self.unify(&target.inner, &array_type, symtab)
                .map_normal_err(|(got, _)| {
                    Error::IndexeeMustBeArray{got, loc: target.loc()}
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_block_expr(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Block(block) = &expression => {
            self.visit_block(block, symtab, generic_list)?;

            // Unify the return type of the block with the type of this expression
            self.unify(&expression.inner, &block.result.inner, symtab)
                // NOTE: We could be more specific about this error specifying
                // that the type of the block must match the return type, though
                // that might just be spammy.
                .map_normal_err(|(expected, got)| Error::UnspecifiedTypeError {
                    expected,
                    got,
                    loc: block.result.loc(),
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_if(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::If(cond, on_true, on_false) = &expression => {
            self.visit_expression(&cond, symtab, generic_list)?;
            self.visit_expression(&on_true, symtab, generic_list)?;
            self.visit_expression(&on_false, symtab, generic_list)?;

            self.unify(&cond.inner, &t_bool(symtab), symtab)
                .map_normal_err(|(got, _)| Error::NonBooleanCondition {
                    got,
                    loc: cond.loc(),
                })?;
            self.unify(&on_true.inner, &on_false.inner, symtab)
                .map_normal_err(|(expected, got)| Error::IfConditionMismatch {
                    expected,
                    got,
                    first_branch: on_true.loc(),
                    incorrect_branch: on_false.loc(),
                })?;
            self.unify(expression, &on_false.inner, symtab)
                .map_normal_err(|(got, expected)| Error::UnspecifiedTypeError {
                    expected,
                    got,
                    loc: expression.loc(),
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_match(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Match(cond, branches) = &expression => {
            self.visit_expression(&cond, symtab, generic_list)?;

            for (i, (pattern, result)) in branches.iter().enumerate() {
                self.visit_pattern(pattern, symtab)?;
                self.visit_expression(result, symtab, generic_list)?;

                self.unify(&cond.inner, pattern, symtab)
                    .map_normal_err(|(expected, got)| {
                        // FIXME: Consider introducing a more specific error
                        Error::UnspecifiedTypeError {
                            expected,
                            got,
                            loc: pattern.loc(),
                        }
                    })?;

                if i != 0 {
                    self.unify(&branches[0].1, result, symtab).map_normal_err(
                        |(expected, got)| Error::MatchBranchMismatch {
                            expected,
                            got,
                            first_branch: branches[0].1.loc(),
                            incorrect_branch: result.loc(),
                        },
                    )?;
                }
            }

            assert!(
                !branches.is_empty(),
                "Empty match statements should be checked by ast lowering"
            );

            self.unify_expression_generic_error(&branches[0].1, expression, symtab)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_binary_operator(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::BinaryOperator(lhs, op, rhs) = &expression => {
            self.visit_expression(&lhs, symtab, generic_list)?;
            self.visit_expression(&rhs, symtab, generic_list)?;
            match *op {
                BinaryOperator::Add
                | BinaryOperator::Sub => {
                    let (lhs_t, lhs_size) = self.new_split_generic_int(symtab);
                    let (result_t, result_size) = self.new_split_generic_int(symtab);

                    self.add_constraint(
                        result_size.clone(),
                        ce_var(&lhs_size) + ce_int(1),
                        expression.loc(),
                        &result_t,
                        ConstraintSource::AdditionOutput
                    );
                    self.add_constraint(
                        lhs_size.clone(),
                        ce_var(&result_size) + -ce_int(1),
                        lhs.loc(),
                        &lhs_t,
                        ConstraintSource::AdditionOutput
                    );

                    // FIXME: Make generic over types that can be added
                    self.unify_expression_generic_error(&lhs, &lhs_t, symtab)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;
                    self.unify_expression_generic_error(expression, &result_t, symtab)?;
                }
                BinaryOperator::Mul => {
                    let (lhs_t, lhs_size) = self.new_split_generic_int(symtab);
                    let (rhs_t, rhs_size) = self.new_split_generic_int(symtab);
                    let (result_t, result_size) = self.new_split_generic_int(symtab);

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

                    self.unify_expression_generic_error(&lhs, &lhs_t, symtab)?;
                    self.unify_expression_generic_error(&rhs, &rhs_t, symtab)?;
                    self.unify_expression_generic_error(expression, &result_t, symtab)?;
                }
                // Shift operators have the same widht in as they do out
                BinaryOperator::LeftShift
                | BinaryOperator::BitwiseAnd
                | BinaryOperator::BitwiseOr
                | BinaryOperator::RightShift => {
                    let int_type = self.new_generic_int(symtab);

                    // FIXME: Make generic over types that can be added
                    self.unify_expression_generic_error(&lhs, &int_type, symtab)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;
                    self.unify_expression_generic_error(expression, &rhs.inner, symtab)?;
                }
                BinaryOperator::Eq
                | BinaryOperator::Gt
                | BinaryOperator::Lt
                | BinaryOperator::Ge
                | BinaryOperator::Le => {
                    let int_type = self.new_generic_int(symtab);
                    // FIXME: Make generic over types that can be added
                    self.unify_expression_generic_error(&lhs, &int_type, symtab)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;
                    self.unify_expression_generic_error(expression, &t_bool(symtab), symtab)?;
                }
                BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::Xor => {
                    // FIXME: Make generic over types that can be ored
                    self.unify_expression_generic_error(&lhs, &t_bool(symtab), symtab)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;

                    self.unify_expression_generic_error(expression, &t_bool(symtab), symtab)?;
                }
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_unary_operator(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::UnaryOperator(op, operand) = &expression => {
            self.visit_expression(&operand, symtab, generic_list)?;
            match op {
                UnaryOperator::Sub | UnaryOperator::BitwiseNot => {
                    let int_type = self.new_generic_int(symtab);
                    self.unify_expression_generic_error(operand, &int_type, symtab)?
                }
                UnaryOperator::Not => {
                    self.unify_expression_generic_error(operand, &t_bool(symtab), symtab)?
                }
            }
        });
        Ok(())
    }
}
