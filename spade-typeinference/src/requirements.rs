use spade_common::location_info::WithLocation;
use spade_common::name::Path;
use spade_common::{location_info::Loc, name::Identifier};
use spade_diagnostics::Diagnostic;
use spade_hir::symbol_table::{SymbolTable, TypeDeclKind, TypeSymbol};
use spade_types::KnownType;

use crate::equation::TypeVar;
use crate::error::{Error, Result, UnificationErrorExt};
use crate::{GenericListSource, TypeState};

#[derive(Clone, Debug)]
pub enum Requirement {
    HasField {
        /// The type which should have the associated field
        target_type: Loc<TypeVar>,
        /// The field which is required to exist on the struct
        field: Loc<Identifier>,
        /// The expression from which this requirement arrises
        expr: Loc<TypeVar>,
    },
    /// The type should be an integer large enough to fit the specified value
    FitsIntLiteral {
        value: u128,
        target_type: Loc<TypeVar>,
    },
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
            Requirement::FitsIntLiteral {
                value: _,
                target_type,
            } => {
                TypeState::replace_type_var(target_type, from, to);
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
    pub fn check(
        &self,
        type_state: &mut TypeState,
        symtab: &SymbolTable,
    ) -> Result<RequirementResult> {
        match self {
            Requirement::HasField {
                target_type,
                field,
                expr,
            } => {
                let (known_type, params) = match &target_type.inner {
                    // To know if we can access the field, we need to see if this type is actually
                    // known in the first place
                    TypeVar::Known(t, params) => (t, params),
                    other @ TypeVar::Backward(_) => {
                        return Err(Error::FieldAccessOnNonStruct {
                            loc: expr.loc(),
                            got: other.clone(),
                        });
                    }
                    TypeVar::Unknown(_) => return Ok(RequirementResult::NoChange),
                    other => {
                        return Err(Error::FieldAccessOnNonStruct {
                            loc: expr.loc(),
                            got: other.clone(),
                        })
                    }
                };

                match known_type {
                    KnownType::Type(type_name) => {
                        // Check if we're dealing with a struct
                        match symtab.type_symbol_by_id(&type_name).inner {
                            TypeSymbol::Declared(_, TypeDeclKind::Struct { is_port: _ }) => {}
                            TypeSymbol::Declared(_, TypeDeclKind::Enum) => {
                                return Err(Error::FieldAccessOnEnum {
                                    loc: target_type.loc(),
                                    actual_type: type_name.clone(),
                                })
                            }
                            TypeSymbol::Declared(_, TypeDeclKind::Primitive { is_port: _ }) => {
                                return Err(Error::FieldAccessOnPrimitive {
                                    loc: target_type.loc(),
                                    actual_type: type_name.clone(),
                                })
                            }
                            TypeSymbol::GenericArg | TypeSymbol::GenericInt => {
                                return Err(Error::FieldAccessOnGeneric {
                                    loc: target_type.loc(),
                                    name: type_name.clone(),
                                })
                            }
                        }

                        // Get the struct, find the type of the field and unify
                        let s = symtab.struct_by_id(&type_name);

                        let field_spec = if let Some(spec) = s.params.try_get_arg_type(field) {
                            spec
                        } else {
                            return Err(Error::NoSuchField {
                                field: field.clone(),
                                _struct: type_name.clone(),
                            });
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

                        let field_type = type_state.type_var_from_hir(&field_spec, &generic_list);

                        Ok(RequirementResult::Satisfied(vec![Replacement {
                            from: expr.clone(),
                            to: field_type,
                        }]))
                    }
                    KnownType::Integer(_) => Err(Error::FieldAccessOnInteger { loc: expr.loc() }),
                }
            }
            Requirement::FitsIntLiteral { value, target_type } => {
                let int_type = symtab
                    .lookup_type_symbol(&Path::from_strs(&["int"]).nowhere())
                    .map_err(|_| {
                        Diagnostic::bug(target_type, "The type `int` was not in the symtab")
                            .primary_label(format!("When evaluating requirement for this type"))
                    })?
                    .0;

                match &target_type.inner {
                    TypeVar::Known(KnownType::Type(name), params) if name == &int_type => {
                        match params.as_slice() {
                            [param] => {
                                match param {
                                    TypeVar::Known(KnownType::Integer(size), _) => {
                                        // If the value is 0, we can fit it into any integer and
                                        // can get rid of the requirement
                                        if *value == 0 {
                                            return Ok(RequirementResult::Satisfied(vec![]))
                                        }

                                        // +1 for signed
                                        let minimum_size = ((*value) as f64).log2() + 1.;
                                        if *value > 0 && *size <= minimum_size as u128 {
                                            Err(Diagnostic::error(target_type, format!("Integer value does not fit in int<{size}>"))
                                                .primary_label(format!("{value} does not fit in an int<{size}>")).into())
                                        }
                                        else {
                                            Ok(RequirementResult::NoChange)
                                        }
                                    },
                                    TypeVar::Unknown(_) => Ok(RequirementResult::NoChange),
                                    _ => Err(Diagnostic::bug(target_type, "Inferred non-integer type for integer literal").into())
                                }
                            },
                            _ => Err(Diagnostic::bug(target_type, "Integer without exactly one type params when evaluating requirement").into())
                        }
                    }
                    TypeVar::Unknown(_) => Ok(RequirementResult::NoChange),
                    other => Err(Diagnostic::bug(
                        target_type,
                        format!(
                            "Found non-integer for type '{other}' with integer size constraint"
                        ),
                    )
                    .into()),
                }
            }
        }
    }

    /// Check if this requirement is satisfied. If so, apply the resulting replacements to the
    /// type state, otherwise add the requirement to the type state requirement list
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn check_or_add(self, type_state: &mut TypeState, symtab: &SymbolTable) -> Result<()> {
        match self.check(type_state, symtab)? {
            RequirementResult::NoChange => Ok(type_state.add_requirement(self)),
            RequirementResult::Satisfied(replacements) => {
                for Replacement { from, to } in replacements {
                    type_state.unify(&from.inner, &to, symtab).map_normal_err(
                        |(got, expected)| Error::UnspecifiedTypeError {
                            expected,
                            got,
                            loc: from.loc(),
                        },
                    )?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug)]
pub struct Replacement {
    pub from: Loc<TypeVar>,
    pub to: TypeVar,
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
