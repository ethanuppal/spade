use num::traits::Pow;
use num::{BigInt, ToPrimitive, Zero};
use spade_common::location_info::WithLocation;
use spade_common::name::Path;
use spade_common::num_ext::InfallibleToBigInt;
use spade_common::{location_info::Loc, name::Identifier};
use spade_diagnostics::{diag_anyhow, diag_assert, diag_bail, Diagnostic};
use spade_hir::symbol_table::{TypeDeclKind, TypeSymbol};
use spade_hir::ArgumentList;
use spade_types::KnownType;

use crate::equation::TypeVar;
use crate::error::{Result, TypeMismatch, UnificationErrorExt};
use crate::method_resolution::select_method;
use crate::trace_stack::TraceStackEntry;
use crate::{Context, GenericListSource, TypeState};

#[derive(Clone, Debug)]
pub enum Requirement {
    HasField {
        /// The type which should have the associated field
        target_type: Loc<TypeVar>,
        /// The field which is required to exist on the struct
        field: Loc<Identifier>,
        /// The expression from which this requirement arises
        expr: Loc<TypeVar>,
    },
    HasMethod {
        /// The ID of the expression which causes this requirement
        expr_id: Loc<u64>,
        /// The type which should have the associated method
        target_type: Loc<TypeVar>,
        /// The method which should exist on the type
        method: Loc<Identifier>,
        /// The expression from which this requirement arises
        expr: Loc<TypeVar>,
        /// The argument list passed to the method. This should include the `self` expression as
        /// the appropriate argument (first positional or a non-shorthand self otherwise)
        args: Loc<ArgumentList>,
    },
    /// The type should be an integer large enough to fit the specified value
    FitsIntLiteral {
        value: BigInt,
        target_type: Loc<TypeVar>,
    },
    /// The provided TypeVar should all share a base type
    SharedBase(Vec<Loc<TypeVar>>),
}

impl Requirement {
    pub fn replace_type_var(&mut self, from: &TypeVar, to: &TypeVar) {
        match self {
            Requirement::HasField {
                target_type,
                expr,
                field: _,
            } => {
                TypeState::replace_type_var(target_type, from, to);
                TypeState::replace_type_var(expr, from, to);
            }
            Requirement::HasMethod {
                expr_id: _,
                target_type,
                expr,
                method: _,
                args: _,
            } => {
                TypeState::replace_type_var(target_type, from, to);
                TypeState::replace_type_var(expr, from, to);
            }
            Requirement::FitsIntLiteral {
                value: _,
                target_type,
            } => {
                TypeState::replace_type_var(target_type, from, to);
            }
            Requirement::SharedBase(bases) => {
                for t in bases {
                    TypeState::replace_type_var(t, from, to)
                }
            }
        }
    }

    /// Check if there are updates that allow us to resolve the requirement.
    /// - If target_type is still `Unknown`, we don't know how to resolve the requirement
    /// - Otherwise it will either be unsatsifieable. i.e. the new type does not fulfil the
    /// requirement, in which case an error is returned
    /// - Or the requirement is now satisfied, in which case new unification tasks which are
    /// applied due to the result are returned. After this, the constraint is no longer needed
    /// and can be dropped
    pub fn check(&self, type_state: &mut TypeState, ctx: &Context) -> Result<RequirementResult> {
        match self {
            Requirement::HasField {
                target_type,
                field,
                expr,
            } => {
                target_type.expect_named_or_inverted(
                    false,
                    |inverted, type_name, params| {
                        // Check if we're dealing with a struct
                        match ctx.symtab.type_symbol_by_id(type_name).inner {
                            TypeSymbol::Declared(_, TypeDeclKind::Struct { is_port: _ }) => {}
                            TypeSymbol::Declared(_, TypeDeclKind::Enum) => {
                                return Err(Diagnostic::error(
                                    target_type,
                                    "Field access on an enum type",
                                )
                                .primary_label(format!("expected a struct, got {}", type_name))
                                .help("Field access is only allowed on structs"));
                            }
                            TypeSymbol::Declared(_, TypeDeclKind::Primitive { is_port: _ }) => {
                                return Err(Diagnostic::error(
                                    target_type,
                                    "Field access on a primitive type",
                                )
                                .primary_label(format!("expected a struct, got {}", type_name))
                                .note("Field access is only allowed on structs"));
                            }
                            TypeSymbol::GenericArg { traits: _ } | TypeSymbol::GenericInt => {
                                return Err(Diagnostic::error(
                                    target_type,
                                    "Field access on a generic type",
                                )
                                .primary_label(format!("Expected struct found {target_type}"))
                                .note("Field access is only allowed on structs"))
                            }
                        }

                        // Get the struct, find the type of the field and unify
                        let s = ctx.symtab.struct_by_id(type_name);

                        let field_spec = if let Some(spec) = s.params.try_get_arg_type(field) {
                            spec
                        } else {
                            return Err(Diagnostic::error(
                                field,
                                format!("{} has no field named {}", type_name, field),
                            )
                            .primary_label(format!("Not a field of {type_name}")));
                        };

                        // The generic list here refers to the generics being passed to the
                        // types of the struct here. We need to construct it from the
                        // inferred generics.
                        let mapping = s
                            .type_params
                            .iter()
                            .map(|p| p.clone().name_id())
                            .zip(params.iter().cloned())
                            .collect();

                        let generic_list = type_state
                            .add_mapped_generic_list(GenericListSource::Anonymous, mapping);

                        let raw_field_type =
                            type_state.type_var_from_hir(field_spec, &generic_list);
                        let field_type = if inverted {
                            match raw_field_type {
                                TypeVar::Known(KnownType::Backward, inner) => {
                                    TypeVar::wire(inner[0].clone())
                                }
                                TypeVar::Known(KnownType::Wire, inner) => {
                                    TypeVar::backward(inner[0].clone())
                                }
                                TypeVar::Known(KnownType::Inverted, _) => raw_field_type,
                                // If we were in an inverted context and we find
                                // a type which is not a wire, we need to invert
                                // it.
                                // This means that `a.b` if b is `T` is `~T`
                                other => TypeVar::inverted(other),
                            }
                        } else {
                            raw_field_type
                        };

                        Ok(RequirementResult::Satisfied(vec![Replacement {
                            from: expr.clone(),
                            to: field_type,
                            context: None,
                        }]))
                    },
                    || Ok(RequirementResult::NoChange),
                    |_| {
                        Err(Diagnostic::error(
                            target_type,
                            format!("Field access on {} which is not a struct", target_type),
                        )
                        .primary_label(format!("Expected a struct, found {}", target_type))
                        .help("Field access is only allowed on structs"))
                    },
                )
            }
            Requirement::HasMethod {
                expr_id,
                target_type,
                method,
                expr,
                args,
            } => target_type.expect_named(
                |type_name, _params| {
                    let implementor = select_method(expr.loc(), type_name, method, ctx.items)?;

                    let fn_head = ctx.symtab.unit_by_id(&implementor);

                    type_state.handle_function_like(
                        *expr_id,
                        &expr.inner,
                        &implementor,
                        &fn_head,
                        args,
                        ctx,
                        false,
                        true,
                    )?;
                    Ok(RequirementResult::Satisfied(vec![]))
                },
                || Ok(RequirementResult::NoChange),
                |other| {
                    Err(Diagnostic::error(
                        expr,
                        format!("{other} does not have any methods"),
                    ))
                },
            ),
            Requirement::FitsIntLiteral { value, target_type } => {
                let int_type = ctx
                    .symtab
                    .lookup_type_symbol(&Path::from_strs(&["int"]).nowhere())
                    .map_err(|_| diag_anyhow!(target_type, "The type int was not in the symtab"))?
                    .0;
                let uint_type = ctx
                    .symtab
                    .lookup_type_symbol(&Path::from_strs(&["uint"]).nowhere())
                    .map_err(|_| diag_anyhow!(target_type, "The type int was not in the symtab"))?
                    .0;

                target_type.expect_named(
                    |name, params| {
                        let unsigned = if name == &int_type {
                            false
                        }
                        else if name == &uint_type {
                            true
                        }
                        else {
                            return Err(Diagnostic::error(
                                target_type,
                                format!("Expected {target_type}, got integer literal")
                            )
                                .primary_label(format!("expected {target_type}")));
                        };

                        diag_assert!(target_type, params.len() == 1);
                        params[0].expect_integer(
                            |size| {
                                let two = 2.to_bigint();

                                let size_u32 = size.to_u32().ok_or_else(|| {
                                    Diagnostic::bug(
                                        target_type,
                                        "Integer size does not fit in 32-bit unsigned number",
                                    )
                                    .note("How did you manage to trigger this 🤔")
                                })?;

                                // If the value is 0, we can fit it into any integer and
                                // can get rid of the requirement
                                if value == &BigInt::zero() {
                                    return Ok(RequirementResult::Satisfied(vec![]));
                                }

                                let contained_range = if unsigned {
                                    (
                                        BigInt::zero(),
                                        two.pow(size_u32) - 1.to_bigint(),
                                    )
                                } else {
                                    (
                                        -two.clone().pow(size_u32.saturating_sub(1)),
                                        two.pow(size_u32.saturating_sub(1)).checked_sub(&1.to_bigint()).unwrap_or(0.to_bigint())
                                    )
                                };

                                if value < &contained_range.0 || value > &contained_range.1 {
                                    let diagnostic = Diagnostic::error(
                                        target_type,
                                        format!("Integer value does not fit in int<{size}>"),
                                    )
                                    .primary_label(format!(
                                        "{value} does not fit in an {name}<{size}>"
                                    ));

                                    let diagnostic = if unsigned {
                                        diagnostic.note(format!(
                                            "{name}<{size}> fits unsigned integers in the range (0, {})",
                                            contained_range.1,
                                        ))
                                    } else {
                                        diagnostic.note(format!(
                                            "{name}<{size}> fits integers in the range ({}, {})",
                                            contained_range.0, contained_range.1
                                        ))
                                    };

                                    Err(diagnostic)
                                } else {
                                    Ok(RequirementResult::Satisfied(vec![]))
                                }
                            },
                            || Ok(RequirementResult::NoChange),
                            |_| diag_bail!(target_type, "Inferred {target_type} for integer literal"),
                        )
                    },
                    || Ok(RequirementResult::NoChange),
                    |other| diag_bail!(target_type, "Inferred {other} for integer literal"),
                )
            }
            Requirement::SharedBase(types) => {
                let first_known = types.iter().find_map(|t| match &t.inner {
                    TypeVar::Known(base, params) => Some((base.clone().at_loc(t), params)),
                    TypeVar::Unknown(_, _) => None,
                });

                if let Some((base, first_params)) = first_known {
                    Ok(RequirementResult::Satisfied(
                        types
                            .iter()
                            .map(|ty| {
                                let base = base.clone();
                                // Since we unify requirement results, we can just use placeholder
                                // parameters here. We know that the number of parameters should
                                // be the same as the params of the first base we found
                                Replacement {
                                    from: ty.clone(),
                                    to: TypeVar::Known(
                                        base.inner.clone(),
                                        first_params
                                            .iter()
                                            .map(|_| type_state.new_generic())
                                            .collect(),
                                    ),
                                    context: Some(Box::new(move |d, TypeMismatch { e, g }| {
                                        let base = base.clone();
                                        d.message(format!("Expected type {e}, got {g}"))
                                            .primary_label(format!("expected {e}"))
                                            .secondary_label(
                                                base,
                                                format!("type {g} inferred here"),
                                            )
                                    })),
                                }
                            })
                            .collect(),
                    ))
                } else {
                    Ok(RequirementResult::NoChange)
                }
            }
        }
    }

    /// Check if this requirement is satisfied. If so, apply the resulting replacements to the
    /// type state, otherwise add the requirement to the type state requirement list
    #[tracing::instrument(level = "trace", skip(type_state, ctx))]
    pub fn check_or_add(self, type_state: &mut TypeState, ctx: &Context) -> Result<()> {
        match self.check(type_state, ctx)? {
            RequirementResult::NoChange => {
                type_state.add_requirement(self);
                Ok(())
            }
            RequirementResult::Satisfied(replacements) => {
                type_state
                    .trace_stack
                    .push(TraceStackEntry::ResolvedRequirement(self.clone()));
                for Replacement { from, to, context } in replacements {
                    type_state
                        .unify(&from.inner, &to, ctx)
                        .into_diagnostic_or_default(&from, context)?;
                }
                Ok(())
            }
        }
    }
}

pub struct Replacement {
    pub from: Loc<TypeVar>,
    pub to: TypeVar,
    pub context: Option<Box<dyn Fn(Diagnostic, TypeMismatch) -> Diagnostic>>,
}

#[must_use]
pub enum RequirementResult {
    /// The requirement remains but not enough information is available about
    /// whether or not it is satisfied
    NoChange,
    /// The requirement is now satisfied and can be removed. Refinements of other
    /// type variables which can now be applied are returned
    Satisfied(Vec<Replacement>),
}
