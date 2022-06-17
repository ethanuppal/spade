use spade_common::{location_info::Loc, name::Identifier};
use spade_hir::symbol_table::{SymbolTable, TypeDeclKind, TypeSymbol};
use spade_types::KnownType;

use crate::{
    equation::TypeVar,
    result::{Error, Result, UnificationErrorExt},
    GenericListToken, TypeState,
};

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
        }
    }

    /// Check if there are updates that allow us to resolve the requirement.
    /// - If target_type is still `Unknown`, we don't know how to resolve the requirement
    /// - Otherwise it will either be unsatsifieable. i.e. the new type does not fullfill the
    /// requirement, in which case an error is returned
    /// - Or the requirement is now satisfied, in which case new unification tasks which are
    /// applied due to the result are returned. After this, the constraint is no longer needed
    /// and can be dropped
    pub fn check(
        &self,
        type_state: &TypeState,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<RequirementResult> {
        match self {
            Requirement::HasField {
                target_type,
                field,
                expr,
            } => {
                match &target_type.inner {
                    TypeVar::Known(inner, _) => {
                        // Look up the type of the known var
                        match inner {
                            KnownType::Type(inner) => {
                                // Check if we're dealing with a struct
                                match symtab.type_symbol_by_id(&inner).inner {
                                    TypeSymbol::Declared(_, TypeDeclKind::Struct) => {}
                                    TypeSymbol::Declared(_, TypeDeclKind::Enum) => {
                                        return Err(Error::FieldAccessOnEnum {
                                            loc: target_type.loc(),
                                            actual_type: inner.clone(),
                                        })
                                    }
                                    TypeSymbol::Declared(_, TypeDeclKind::Primitive) => {
                                        return Err(Error::FieldAccessOnPrimitive {
                                            loc: target_type.loc(),
                                            actual_type: inner.clone(),
                                        })
                                    }
                                    TypeSymbol::GenericArg | TypeSymbol::GenericInt => {
                                        return Err(Error::FieldAccessOnGeneric {
                                            loc: target_type.loc(),
                                            name: inner.clone(),
                                        })
                                    }
                                }

                                // Get the struct, find the type of the field and unify
                                let s = symtab.struct_by_id(&inner);

                                let field_spec =
                                    if let Some(spec) = s.params.try_get_arg_type(field) {
                                        spec
                                    } else {
                                        return Err(Error::NoSuchField {
                                            field: field.clone(),
                                            _struct: inner.clone(),
                                        });
                                    };

                                let field_type =
                                    type_state.type_var_from_hir(&field_spec, generic_list);

                                Ok(RequirementResult::Satisfied(vec![Replacement {
                                    from: expr.clone(),
                                    to: field_type,
                                }]))
                            }
                            KnownType::Integer(_) => {
                                Err(Error::FieldAccessOnInteger { loc: expr.loc() })
                            }
                        }
                    }
                    TypeVar::Unknown(_) => Ok(RequirementResult::NoChange),
                    other => Err(Error::FieldAccessOnNonStruct {
                        loc: expr.loc(),
                        got: other.clone(),
                    }),
                }
            }
        }
    }

    /// Check if this requirement is satisfied. If so, apply the resulting replacments to the
    /// type state, otherwise add the requirement to the type state requirement list
    pub fn check_or_add(
        self,
        type_state: &mut TypeState,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        match self.check(type_state, symtab, generic_list)? {
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
