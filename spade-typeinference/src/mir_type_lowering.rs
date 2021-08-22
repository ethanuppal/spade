use std::collections::HashMap;

use hir::symbol_table::SymbolTable;
use hir::TypeSpec;
use spade_common::name::NameID;
use spade_hir as hir;
use spade_hir::{TypeDeclaration, TypeList};
use spade_types::{ConcreteType, KnownType};

use crate::equation::{TypeVar, TypedExpression};
use crate::TypeState;

impl TypeState {
    pub fn type_decl_to_concrete(
        decl: &TypeDeclaration,
        type_list: &TypeList,
        params: Vec<ConcreteType>,
    ) -> ConcreteType {
        // Mapping between generic name and type param

        assert!(
            params.len() == decl.generic_args.len(),
            "Too few type decl params"
        );

        let generic_subs = decl
            .generic_args
            .iter()
            .zip(params.iter())
            .map(|(lhs, rhs)| (lhs.name_id(), rhs))
            .collect::<HashMap<_, _>>();

        match &decl.kind {
            hir::TypeDeclKind::Enum(e) => {
                let options = e
                    .options
                    .iter()
                    .map(|(name, args)| {
                        let args = args
                            .0
                            .iter()
                            .map(|arg| {
                                Self::type_spec_to_concrete(&arg.1.inner, type_list, &generic_subs)
                            })
                            .collect();
                        (name.inner.clone(), args)
                    })
                    .collect();
                ConcreteType::Enum { options }
            }
            hir::TypeDeclKind::Primitive(primitive) => ConcreteType::Single {
                base: primitive.clone(),
                params,
            },
        }
    }

    pub fn type_spec_to_concrete(
        spec: &TypeSpec,
        type_list: &TypeList,
        generic_substitutions: &HashMap<NameID, &ConcreteType>,
    ) -> ConcreteType {
        match spec {
            TypeSpec::Declared(name, params) => {
                let params = params
                    .iter()
                    .map(|p| match &p.inner {
                        hir::TypeExpression::Integer(val) => ConcreteType::Integer(*val),
                        hir::TypeExpression::TypeSpec(inner) => {
                            Self::type_spec_to_concrete(&inner, type_list, generic_substitutions)
                        }
                    })
                    .collect();

                let actual = type_list
                    .get(&name)
                    .expect(&format!("Expected {:?} to be in type list", name));

                Self::type_decl_to_concrete(actual, type_list, params)
            }
            TypeSpec::Generic(name) => {
                // Substitute the generic for the current substitution
                (*generic_substitutions
                    .get(&name)
                    .expect(&format!("Expected a substitution for {}", name)))
                .clone()
            }
            TypeSpec::Tuple(t) => {
                let inner = t
                    .iter()
                    .map(|v| {
                        Self::type_spec_to_concrete(&v.inner, type_list, &generic_substitutions)
                    })
                    .collect::<Vec<_>>();
                ConcreteType::Tuple(inner)
            }
            TypeSpec::Unit(_) => todo!("Handle unit type"),
        }
    }

    /// Converts the specified type to a concrete type, returning None
    /// if it fails
    pub fn ungenerify_type(
        var: &TypeVar,
        symtab: &SymbolTable,
        type_list: &TypeList,
    ) -> Option<ConcreteType> {
        match var {
            TypeVar::Known(KnownType::Type(t), params, _) => {
                let params = params
                    .iter()
                    .map(|v| Self::ungenerify_type(v, symtab, type_list))
                    .collect::<Option<Vec<_>>>()?;

                match type_list.get(t) {
                    Some(t) => Some(Self::type_decl_to_concrete(&t.inner, type_list, params)),
                    None => {
                        panic!("Missing type declaration for {:?}", t)
                    }
                }
            }
            TypeVar::Known(KnownType::Integer(size), params, _) => {
                assert!(params.len() == 0, "integers can not have type parameters");

                Some(ConcreteType::Integer(*size))
            }
            TypeVar::Tuple(inner) => {
                let inner = inner
                    .iter()
                    .map(|v| Self::ungenerify_type(v, symtab, type_list))
                    .collect::<Option<Vec<_>>>()?;
                Some(ConcreteType::Tuple(inner))
            }
            TypeVar::Unknown(_) => None,
        }
    }

    /// Returns the type of the specified name as a concrete type. If the type is not known,
    /// or tye type is Generic, panics
    pub fn type_of_name(
        &self,
        name: &NameID,
        symtab: &SymbolTable,
        type_list: &TypeList,
    ) -> ConcreteType {
        Self::ungenerify_type(
            &self
                .type_of(&TypedExpression::Name(name.clone()))
                .expect("Expression had no specified type"),
            symtab,
            type_list,
        )
        .expect("Expr had generic type")
    }
}
