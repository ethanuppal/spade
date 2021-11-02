pub mod builtins;
pub mod error;
pub mod error_reporting;
pub mod global_symbols;
pub mod pipelines;
pub mod types;

use ast::ParameterList;
use hir::symbol_table::DeclarationState;
use hir::util::path_from_ident;
use hir::ExecutableItem;
pub use spade_common::id_tracker;

use std::collections::HashMap;

use thiserror::Error;

use spade_ast as ast;
use spade_common::id_tracker::ExprIdTracker;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::Path,
};
use spade_hir as hir;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::symbol_table::{LookupError, Thing, TypeSymbol};
use spade_hir::{expression::BinaryOperator, EntityHead};

pub use error::{Error, Result};

trait LocExt<T> {
    fn try_visit<V, U>(
        &self,
        visitor: V,
        symtab: &mut SymbolTable,
        idtracker: &mut ExprIdTracker,
    ) -> Result<Loc<U>>
    where
        V: Fn(&T, &mut SymbolTable, &mut ExprIdTracker) -> Result<U>;
}

impl<T> LocExt<T> for Loc<T> {
    fn try_visit<V, U>(
        &self,
        visitor: V,
        symtab: &mut SymbolTable,
        idtracker: &mut ExprIdTracker,
    ) -> Result<Loc<U>>
    where
        V: Fn(&T, &mut SymbolTable, &mut ExprIdTracker) -> Result<U>,
    {
        self.map_ref(|t| visitor(&t, symtab, idtracker))
            .map_err(|e, _| e)
    }
}

/// Visit an AST type parameter, converting it to a HIR type parameter. The name is not
/// added to the symbol table as this function is re-used for both global symbol collection
/// and normal HIR lowering.
pub fn visit_type_param(
    param: &ast::TypeParam,
    symtab: &mut SymbolTable,
) -> Result<hir::TypeParam> {
    match &param {
        ast::TypeParam::TypeName(ident) => {
            let name_id = symtab.add_thing(
                Path(vec![ident.clone()]),
                Thing::Type(TypeSymbol::GenericArg.at_loc(&ident)),
            );

            Ok(hir::TypeParam::TypeName(ident.inner.clone(), name_id))
        }
        ast::TypeParam::Integer(ident) => {
            let name_id = symtab.add_thing(
                Path(vec![ident.clone()]),
                Thing::Type(TypeSymbol::GenericArg.at_loc(&ident)),
            );

            Ok(hir::TypeParam::Integer(ident.inner.clone(), name_id))
        }
    }
}

pub fn visit_type_expression(
    expr: &ast::TypeExpression,
    symtab: &mut SymbolTable,
) -> Result<hir::TypeExpression> {
    // todo!("Implement visiting type expressions")
    match expr {
        ast::TypeExpression::TypeSpec(spec) => {
            let inner = visit_type_spec(spec, symtab)?;
            // Look up the type. For now, we'll panic if we don't find a concrete type
            Ok(hir::TypeExpression::TypeSpec(inner))
        }
        ast::TypeExpression::Integer(val) => Ok(hir::TypeExpression::Integer(*val)),
    }
}

pub fn visit_type_spec(t: &ast::TypeSpec, symtab: &mut SymbolTable) -> Result<hir::TypeSpec> {
    match t {
        ast::TypeSpec::Named(path, params) => {
            // Lookup the referenced type
            // NOTE: this weird scope is required because the borrow of t lasts
            // until the end of the outer scope even if we clone here.
            let (base_id, t) = { symtab.lookup_type_symbol(path)?.clone() };

            // Check if the type is a declared type or a generic argument.
            match &t.inner {
                TypeSymbol::Declared(_) => {
                    // We'll defer checking the validity of generic args to the type checker,
                    // but we still have to visit them now
                    let params = params
                        .iter()
                        .map(|p| p.try_map_ref(|p| visit_type_expression(p, symtab)))
                        .collect::<Result<Vec<_>>>()?;

                    Ok(hir::TypeSpec::Declared(base_id.at_loc(path), params))
                }
                TypeSymbol::GenericArg => {
                    // If this typename refers to a generic argument we need to make
                    // sure that no generic arguments are passed, as generic names
                    // can't have generic parameters

                    if !params.is_empty() {
                        let at_loc =
                            ().between_locs(params.first().unwrap(), params.last().unwrap());
                        Err(Error::GenericsGivenForGeneric {
                            at_loc,
                            for_type: base_id.1.clone().at_loc(&t.loc()),
                        })
                    } else {
                        Ok(hir::TypeSpec::Generic(base_id.at_loc(&path)))
                    }
                }
                TypeSymbol::GenericInt => {
                    todo!("Support generic ints");
                }
            }
        }
        ast::TypeSpec::Tuple(inner) => {
            let inner = inner
                .iter()
                .map(|p| p.try_map_ref(|p| visit_type_spec(p, symtab)))
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::TypeSpec::Tuple(inner))
        }
        ast::TypeSpec::Unit(w) => Ok(hir::TypeSpec::Unit(w.clone())),
    }
}

fn visit_parameter_list(l: &ParameterList, symtab: &mut SymbolTable) -> Result<hir::ParameterList> {
    let mut result = vec![];
    for (name, input_type) in &l.0 {
        let t = input_type.try_map_ref(|t| visit_type_spec(t, symtab))?;

        result.push((name.clone(), t));
    }
    Ok(hir::ParameterList(result))
}

/// Visit the head of an entity to generate an entity head
pub fn entity_head(item: &ast::Entity, symtab: &mut SymbolTable) -> Result<EntityHead> {
    let type_params = vec![];
    if !item.type_params.is_empty() {
        todo!("Handle generic type parameters in entities");
    }

    let output_type = if let Some(output_type) = &item.output_type {
        Some(output_type.try_map_ref(|t| visit_type_spec(t, symtab))?)
    } else {
        None
    };

    Ok(EntityHead {
        inputs: visit_parameter_list(&item.inputs, symtab)?,
        output_type,
        type_params,
    })
}

pub fn visit_entity(
    item: &Loc<ast::Entity>,
    namespace: &Path,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<Loc<hir::Entity>> {
    symtab.new_scope();

    let path = namespace.push_ident(item.name.clone());
    let (id, head) = symtab
        .lookup_entity(&path.at_loc(&item.name))
        .expect("Attempting to lower an entity that has not been added to the symtab previously");
    let head = head.clone(); // An offering to the borrow checker. May ferris have mercy on us all

    // Add the inputs to the symtab
    let inputs = head
        .inputs
        .0
        .iter()
        .map(|(ident, ty)| (symtab.add_local_variable(ident.clone()), ty.clone()))
        .collect();

    let body = item.body.try_visit(visit_expression, symtab, idtracker)?;

    symtab.close_scope();

    Ok(hir::Entity {
        name: id.at_loc(&item.name),
        head: head.clone().inner,
        inputs,
        body,
    }
    .at_loc(item))
}

// pub fn visit_trait_def(
//     item: ast::TraitDef,
//     symtab: &mut SymbolTable,
//     idtracker: &mut IdTracker,
// ) -> Result<hir::TraitDef> {
//     unimplemented!{}
// }

pub fn visit_item(
    item: &ast::Item,
    namespace: &Path,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<Option<hir::Item>> {
    match item {
        ast::Item::Entity(e) => Ok(Some(hir::Item::Entity(visit_entity(
            e, namespace, symtab, idtracker,
        )?))),
        ast::Item::Pipeline(p) => Ok(Some(hir::Item::Pipeline(pipelines::visit_pipeline(
            p, namespace, symtab, idtracker,
        )?))),
        ast::Item::TraitDef(_) => {
            todo!("Visit trait definitions")
        }
        ast::Item::Type(_) => {
            // Global symbol lowering already visits type declarations
            Ok(None)
        }
    }
}

pub fn visit_module_body(
    mut item_list: hir::ItemList,
    module: &ast::ModuleBody,
    namespace: &Path,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<hir::ItemList> {
    let all_items = module
        .members
        .iter()
        .map(|i| visit_item(i, namespace, symtab, idtracker))
        .collect::<Result<Vec<_>>>()?
        .into_iter();

    for item in all_items {
        // Insertion in hash maps return a value if duplicates are present (or not if try_insert is
        // used) We need to get rid of that for the type of the match block here to work, and a macro
        // hides those details
        macro_rules! add_item {
            ($map:expr, $name:expr, $item:expr) => {{
                if let Some(_) = $map.insert($name.inner.clone(), $item) {
                    panic!("Internal error: Multiple thigns named {}", $name.inner)
                }
            }};
        }
        use hir::Item::*;
        match item {
            Some(Entity(e)) => add_item!(
                item_list.executables,
                e.name,
                ExecutableItem::Entity(e.clone())
            ),
            Some(Pipeline(p)) => add_item!(
                item_list.executables,
                p.name,
                ExecutableItem::Pipeline(p.clone())
            ),
            None => {}
        }
    }

    Ok(item_list)
}

pub fn visit_pattern(
    p: &ast::Pattern,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
    allow_declarations: bool,
) -> Result<hir::Pattern> {
    let kind = match &p {
        ast::Pattern::Integer(_) => todo!(),
        ast::Pattern::Bool(_) => todo!(),
        ast::Pattern::Path(path) => {
            // TODO: Support paths with a single identifier refering to constants
            // and types
            match path.inner.0.as_slice() {
                [ident] => {
                    // Check if this is declaring a variable
                    let (name_id, pre_declared) = if let Some(state) = symtab.get_declaration(ident)
                    {
                        if allow_declarations {
                            match state.inner {
                                DeclarationState::Undefined(id) => {
                                    symtab.mark_declaration_defined(ident.clone(), ident.loc());
                                    (id, true)
                                }
                                DeclarationState::Defined(previous) => {
                                    return Err(Error::RedefinitionOfDeclaration {
                                        at: ident.clone(),
                                        previous: previous.loc(),
                                    })
                                }
                            }
                        } else {
                            return Err(Error::DeclarationOfNonReg {
                                at: ident.clone(),
                                declaration_location: state.loc(),
                            });
                        }
                    } else {
                        (
                            symtab.add_thing(
                                path_from_ident(ident.clone()).inner,
                                Thing::Variable(ident.clone()),
                            ),
                            false,
                        )
                    };

                    hir::PatternKind::Name {
                        name: name_id.at_loc(&ident),
                        pre_declared,
                    }
                }
                [] => unreachable!(),
                _ => match symtab.lookup_enum_variant(path) {
                    Ok((name_id, variant)) => {
                        if variant.inner.params.argument_num() != 0 {
                            return Err(Error::PatternListLengthMismatch {
                                expected: variant.inner.params.argument_num(),
                                got: 0,
                                at: path.loc(),
                            });
                        } else {
                            hir::PatternKind::Type(name_id.at_loc(path), vec![])
                        }
                    }
                    Err(e) => return Err(e.into()),
                },
            }
        }
        ast::Pattern::Tuple(pattern) => {
            let inner = pattern
                .iter()
                .map(|p| p.try_map_ref(|p| visit_pattern(p, symtab, idtracker, allow_declarations)))
                .collect::<Result<_>>()?;
            hir::PatternKind::Tuple(inner)
        }
        ast::Pattern::Type(path, args) => {
            // Look up the name to see if it's an enum variant.
            match symtab.lookup_enum_variant(path) {
                Ok((name_id, variant)) => {
                    match &args.inner {
                        ast::ArgumentPattern::Named(_) => {
                            todo!("support positional enum destructuring")
                        }
                        ast::ArgumentPattern::Positional(patterns) => {
                            // Ensure we have the correct amount of arguments
                            if variant.inner.params.argument_num() != patterns.len() {
                                return Err(Error::PatternListLengthMismatch {
                                    expected: variant.inner.params.argument_num(),
                                    got: patterns.len(),
                                    at: args.loc(),
                                });
                            }

                            let patterns = patterns
                                .iter()
                                .zip(variant.inner.params.0.iter())
                                .map(|(p, arg)| {
                                    let pat = p.try_map_ref(|p| {
                                        visit_pattern(p, symtab, idtracker, allow_declarations)
                                    })?;
                                    Ok(hir::PatternArgument {
                                        target: arg.0.clone(),
                                        value: pat,
                                        kind: hir::ArgumentKind::Positional,
                                    })
                                })
                                .collect::<Result<Vec<_>>>()?;

                            hir::PatternKind::Type(name_id.at_loc(path), patterns)
                        }
                    }
                }
                Err(spade_hir::symbol_table::LookupError::NoSuchSymbol(_)) => {
                    todo!("Handle new symbols")
                }
                Err(e) => return Err(e.into()),
            }
        }
    };
    Ok(kind.with_id(idtracker.next()))
}

/// Visit a pattern where definition of previously declared variables
/// is an error
pub fn visit_pattern_normal(
    p: &ast::Pattern,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<hir::Pattern> {
    visit_pattern(p, symtab, idtracker, false)
}

/// Visit a pattern which can define previously declared variables
pub fn visit_pattern_allow_declarations(
    p: &ast::Pattern,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<hir::Pattern> {
    visit_pattern(p, symtab, idtracker, true)
}

pub fn visit_statement(
    s: &Loc<ast::Statement>,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<Loc<hir::Statement>> {
    match &s.inner {
        ast::Statement::Declaration(names) => {
            let names = names
                .iter()
                .map(|name| {
                    symtab
                        .add_declaration(name.clone())
                        .map_err(Error::DeclarationError)
                        .map(|id| id.at_loc(name))
                })
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::Statement::Declaration(names).at_loc(&s))
        }
        ast::Statement::Binding(pattern, t, expr) => {
            let hir_type = if let Some(t) = t {
                Some(t.try_map_ref(|t| visit_type_spec(t, symtab))?)
            } else {
                None
            };

            let pat = pattern.try_visit(visit_pattern_normal, symtab, idtracker)?;

            let expr = expr.try_visit(visit_expression, symtab, idtracker)?;

            Ok(hir::Statement::Binding(pat, hir_type, expr).at_loc(s))
        }
        ast::Statement::Register(inner) => {
            let (result, span) = visit_register(&inner, symtab, idtracker)?.separate_loc();
            Ok(hir::Statement::Register(result).at_loc(&span))
        }
    }
}

fn visit_argument_list(
    arguments: &Loc<ast::ArgumentList>,
    inputs: &hir::ParameterList,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<Vec<hir::Argument>> {
    match &arguments.inner {
        ast::ArgumentList::Positional(args) => {
            if args.len() != inputs.0.len() {
                return Err(Error::ArgumentListLenghtMismatch {
                    got: args.len(),
                    expected: inputs.0.len(),
                    at: arguments.loc(),
                });
            }

            let args = args
                .iter()
                .map(|a| a.try_visit(visit_expression, symtab, idtracker))
                .zip(inputs.0.iter())
                .map(|(arg, target)| {
                    Ok(hir::Argument {
                        target: target.0.clone(),
                        value: arg?,
                        kind: hir::ArgumentKind::Positional,
                    })
                })
                .collect::<Result<Vec<_>>>()?;

            Ok(args)
        }
        ast::ArgumentList::Named(args) => {
            let mut unbound_args = inputs
                .0
                .iter()
                .enumerate()
                .map(|(index, (name, _))| (name.clone(), index))
                .collect::<HashMap<_, _>>();
            let mut bound_args = vec![];

            let mut result_args = vec![];
            for arg in args {
                match arg {
                    ast::NamedArgument::Full(name, value) => {
                        let value = value.try_visit(visit_expression, symtab, idtracker)?;

                        if let Some(arg_idx) = unbound_args.remove(name) {
                            // Mark it as bound
                            bound_args.push(name);

                            result_args.push((
                                arg_idx,
                                hir::Argument {
                                    target: name.clone(),
                                    value: value,
                                    kind: hir::ArgumentKind::Positional,
                                },
                            ));
                        } else {
                            // Check if we bound it already
                            let prev_idx = bound_args.iter().position(|n| n == &name);
                            if let Some(idx) = prev_idx {
                                return Err(Error::DuplicateNamedBindings {
                                    new: name.clone(),
                                    prev_loc: bound_args[idx].loc(),
                                });
                            } else {
                                return Err(Error::NoSuchArgument { name: name.clone() });
                            }
                        }
                    }
                    ast::NamedArgument::Short(name) => {
                        let expr =
                            ast::Expression::Identifier(Path(vec![name.clone()]).at_loc(name));
                        let value = visit_expression(&expr, symtab, idtracker)?;

                        if let Some(arg_idx) = unbound_args.remove(name) {
                            // Mark it as bound
                            bound_args.push(name);

                            result_args.push((
                                arg_idx,
                                hir::Argument {
                                    target: name.clone(),
                                    value: value.nowhere(),
                                    kind: hir::ArgumentKind::ShortNamed,
                                },
                            ));
                        } else {
                            // Check if we bound it already
                            let prev_idx = bound_args.iter().position(|n| n == &name);
                            if let Some(idx) = prev_idx {
                                return Err(Error::DuplicateNamedBindings {
                                    new: name.clone(),
                                    prev_loc: bound_args[idx].loc(),
                                });
                            } else {
                                return Err(Error::NoSuchArgument { name: name.clone() });
                            }
                        }
                    }
                }
            }

            if !unbound_args.is_empty() {
                return Err(Error::MissingArguments {
                    missing: unbound_args
                        .into_iter()
                        .map(|(name, _)| name.inner)
                        .collect(),
                    at: arguments.loc(),
                });
            }

            // Sort the arguments based on the position of the bound arg
            result_args.sort_by_key(|(idx, _)| *idx);

            Ok(result_args.into_iter().map(|(_, name)| name).collect())
        }
    }
}

pub fn visit_expression(
    e: &ast::Expression,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<hir::Expression> {
    match e {
        ast::Expression::IntLiteral(val) => Ok(hir::ExprKind::IntLiteral(val.clone())),
        ast::Expression::BoolLiteral(val) => Ok(hir::ExprKind::BoolLiteral(*val)),
        ast::Expression::BinaryOperator(lhs, tok, rhs) => {
            let lhs = lhs.try_visit(visit_expression, symtab, idtracker)?;
            let rhs = rhs.try_visit(visit_expression, symtab, idtracker)?;

            let operator = |op| hir::ExprKind::BinaryOperator(Box::new(lhs), op, Box::new(rhs));

            match tok {
                ast::BinaryOperator::Add => Ok(operator(BinaryOperator::Add)),
                ast::BinaryOperator::Sub => Ok(operator(BinaryOperator::Sub)),
                ast::BinaryOperator::Mul => Ok(operator(BinaryOperator::Mul)),
                ast::BinaryOperator::Equals => Ok(operator(BinaryOperator::Eq)),
                ast::BinaryOperator::Gt => Ok(operator(BinaryOperator::Gt)),
                ast::BinaryOperator::Lt => Ok(operator(BinaryOperator::Lt)),
                ast::BinaryOperator::LeftShift => Ok(operator(BinaryOperator::LeftShift)),
                ast::BinaryOperator::RightShift => Ok(operator(BinaryOperator::RightShift)),
                ast::BinaryOperator::LogicalAnd => Ok(operator(BinaryOperator::LogicalAnd)),
                ast::BinaryOperator::LogicalOr => Ok(operator(BinaryOperator::LogicalOr)),
                ast::BinaryOperator::BitwiseOr => Ok(operator(BinaryOperator::BitwiseOr)),
                ast::BinaryOperator::BitwiseAnd => Ok(operator(BinaryOperator::BitwiseAnd)),
            }
        }
        ast::Expression::EntityInstance(name, arg_list) => {
            let (name_id, head) = symtab.lookup_entity(name)?;
            let head = head.clone();

            let args = visit_argument_list(arg_list, &head.inputs, symtab, idtracker)?;
            Ok(hir::ExprKind::EntityInstance(name_id.at_loc(name), args))
        }
        ast::Expression::PipelineInstance(depth, name, arg_list) => {
            let (name_id, head) = symtab.lookup_pipeline(name)?;
            let head = head.clone();

            if head.depth.inner != depth.inner as usize {
                return Err(Error::PipelineDepthMissmatch {
                    expected: head.depth.inner,
                    got: depth.clone(),
                });
            }

            let args = visit_argument_list(arg_list, &head.inputs, symtab, idtracker)?;
            Ok(hir::ExprKind::PipelineInstance {
                depth: depth.clone(),
                name: name_id.at_loc(name),
                args,
            })
        }
        ast::Expression::TupleLiteral(exprs) => {
            let exprs = exprs
                .into_iter()
                .map(|e| e.try_map_ref(|e| visit_expression(e, symtab, idtracker)))
                .collect::<Result<Vec<_>>>()?;
            Ok(hir::ExprKind::TupleLiteral(exprs))
        }
        ast::Expression::TupleIndex(tuple, index) => Ok(hir::ExprKind::TupleIndex(
            Box::new(tuple.try_visit(visit_expression, symtab, idtracker)?),
            index.clone(),
        )),
        ast::Expression::If(cond, ontrue, onfalse) => {
            let cond = cond.try_visit(visit_expression, symtab, idtracker)?;
            let ontrue = ontrue.try_visit(visit_expression, symtab, idtracker)?;
            let onfalse = onfalse.try_visit(visit_expression, symtab, idtracker)?;

            Ok(hir::ExprKind::If(
                Box::new(cond),
                Box::new(ontrue),
                Box::new(onfalse),
            ))
        }
        ast::Expression::Match(expression, branches) => {
            let e = expression.try_visit(visit_expression, symtab, idtracker)?;

            let b = branches
                .iter()
                .map(|(pattern, result)| {
                    let p = pattern.try_visit(visit_pattern_normal, symtab, idtracker)?;
                    let r = result.try_visit(visit_expression, symtab, idtracker)?;
                    Ok((p, r))
                })
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::ExprKind::Match(Box::new(e), b))
        }
        ast::Expression::Block(block) => Ok(hir::ExprKind::Block(Box::new(visit_block(
            block, symtab, idtracker,
        )?))),
        ast::Expression::FnCall(callee, args) => {
            let (name_id, head) = symtab.lookup_function(callee)?;
            let head = head.clone();

            let args = visit_argument_list(args, &head.inputs, symtab, idtracker)?;

            Ok(hir::ExprKind::FnCall(name_id.at_loc(callee), args))
        }
        ast::Expression::Identifier(path) => {
            // If the identifier isn't a valid variable, report as "expected value".
            let id = symtab.lookup_variable(path).map_err(|err| match err {
                LookupError::NotAVariable(path, was) => LookupError::NotAValue(path, was),
                err => err,
            })?;

            Ok(hir::ExprKind::Identifier(id))
        }
    }
    .map(|kind| kind.with_id(idtracker.next()))
}

pub fn visit_block(
    b: &ast::Block,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<hir::Block> {
    symtab.new_scope();
    let statements = b
        .statements
        .iter()
        .map(|statement| visit_statement(statement, symtab, idtracker))
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .collect::<Vec<_>>();

    let result = b.result.try_visit(visit_expression, symtab, idtracker)?;

    symtab.close_scope();

    Ok(hir::Block { statements, result })
}

pub fn visit_register(
    reg: &Loc<ast::Register>,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<Loc<hir::Register>> {
    let (reg, loc) = reg.split_loc_ref();

    let pattern = reg
        .pattern
        .try_visit(visit_pattern_allow_declarations, symtab, idtracker)?;

    let clock = reg.clock.try_visit(visit_expression, symtab, idtracker)?;

    let reset = if let Some((trig, value)) = &reg.reset {
        Some((
            trig.try_visit(visit_expression, symtab, idtracker)?,
            value.try_visit(visit_expression, symtab, idtracker)?,
        ))
    } else {
        None
    };

    let value = reg.value.try_visit(visit_expression, symtab, idtracker)?;

    let value_type = if let Some(value_type) = &reg.value_type {
        Some(value_type.try_map_ref(|t| visit_type_spec(t, symtab))?)
    } else {
        None
    };

    Ok(hir::Register {
        pattern,
        clock,
        reset,
        value,
        value_type,
    }
    .at_loc(&loc))
}

#[cfg(test)]
mod entity_visiting {
    use super::*;

    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::name::testutil::name_id;
    use spade_common::{location_info::WithLocation, name::Identifier};

    use pretty_assertions::assert_eq;

    #[test]
    fn entity_visits_work() {
        let input = ast::Entity {
            name: Identifier("test".to_string()).nowhere(),
            inputs: ParameterList(vec![(
                ast_ident("a"),
                ast::TypeSpec::Unit(().nowhere()).nowhere(),
            )]),
            output_type: None,
            body: ast::Expression::Block(Box::new(ast::Block {
                statements: vec![ast::Statement::Binding(
                    ast::Pattern::name("var"),
                    Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
                    ast::Expression::IntLiteral(0).nowhere(),
                )
                .nowhere()],
                result: ast::Expression::IntLiteral(0).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        let expected = hir::Entity {
            name: name_id(0, "test"),
            head: hir::EntityHead {
                inputs: hir::ParameterList(vec![(ast_ident("a"), hir::TypeSpec::unit().nowhere())]),
                output_type: None,
                type_params: vec![],
            },
            inputs: vec![((name_id(1, "a").inner, hir::TypeSpec::unit().nowhere()))],
            body: hir::ExprKind::Block(Box::new(hir::Block {
                statements: vec![hir::Statement::Binding(
                    hir::PatternKind::name(name_id(2, "var")).idless().nowhere(),
                    Some(hir::TypeSpec::unit().nowhere()),
                    hir::ExprKind::IntLiteral(0).idless().nowhere(),
                )
                .nowhere()],
                result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
            }))
            .idless()
            .nowhere(),
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        global_symbols::visit_entity(&input, &Path(vec![]), &mut symtab)
            .expect("Failed to collect global symbols");

        let result = visit_entity(&input, &Path(vec![]), &mut symtab, &mut idtracker);

        assert_eq!(result, Ok(expected));

        // But the local variables should not
        assert!(!symtab.has_symbol(ast_path("a").inner));
        assert!(!symtab.has_symbol(ast_path("var").inner));
    }

    #[ignore]
    #[test]
    fn entity_with_generics_works() {
        unimplemented![]
        // let input = ast::Entity {
        //     name: Identifier("test".to_string()).nowhere(),
        //     inputs: vec![(ast_ident("a"), ast::Type::UnitType.nowhere())],
        //     output_type: ast::Type::UnitType.nowhere(),
        //     body: ast::Expression::Block(Box::new(ast::Block {
        //         statements: vec![ast::Statement::Binding(
        //             ast_ident("var"),
        //             Some(ast::Type::UnitType.nowhere()),
        //             ast::Expression::IntLiteral(0).nowhere(),
        //         )
        //         .nowhere()],
        //         result: ast::Expression::IntLiteral(0).nowhere(),
        //     }))
        //     .nowhere(),
        //     type_params: vec![
        //         ast::TypeParam::TypeName(ast_ident("a").inner).nowhere(),
        //         ast::TypeParam::Integer(ast_ident("b")).nowhere(),
        //     ],
        // };

        // let expected = hir::Entity {
        //     head: hir::EntityHead {
        //         inputs: vec![
        //             ((
        //                 NameID(0, Path::from_strs(&["a"])),
        //                 hir::Type::Unit.nowhere(),
        //             )),
        //         ],
        //         output_type: hir::Type::Unit.nowhere(),
        //         type_params: vec![
        //             hir::TypeParam::TypeName(hir_ident("a").inner).nowhere(),
        //             hir::TypeParam::Integer(hir_ident("b")).nowhere(),
        //         ],
        //     },
        //     body: hir::ExprKind::Block(Box::new(hir::Block {
        //         statements: vec![hir::Statement::Binding(
        //             hir_ident("var"),
        //             Some(hir::Type::Unit.nowhere()),
        //             hir::ExprKind::IntLiteral(0).idless().nowhere(),
        //         )
        //         .nowhere()],
        //         result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
        //     }))
        //     .idless()
        //     .nowhere(),
        // };

        // let mut symtab = SymbolTable::new();
        // let mut idtracker = ExprIdTracker::new();

        // let result = visit_entity(&input, &mut symtab, &mut idtracker);

        // assert_eq!(result, Ok(expected));

        // // But the local variables should not
        // assert!(!symtab.has_symbol(&hir_ident("a").inner));
        // assert!(!symtab.has_symbol(&hir_ident("var").inner));
    }
}

#[cfg(test)]
mod statement_visiting {
    use super::*;

    use hir::symbol_table::DeclarationError;
    use matches::assert_matches;
    use pretty_assertions::assert_eq;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    #[test]
    fn bindings_convert_correctly() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        let input = ast::Statement::Binding(
            ast::Pattern::name("a"),
            Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            ast::Expression::IntLiteral(0).nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Binding(
            hir::PatternKind::name(name_id(0, "a")).idless().nowhere(),
            Some(hir::TypeSpec::unit().nowhere()),
            hir::ExprKind::IntLiteral(0).idless().nowhere(),
        )
        .nowhere();

        assert_eq!(
            visit_statement(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
        assert_eq!(symtab.has_symbol(ast_path("a").inner), true);
    }

    #[test]
    fn registers_are_statements() {
        let input = ast::Statement::Register(
            ast::Register {
                pattern: ast::Pattern::name("regname"),
                clock: ast::Expression::Identifier(ast_path("clk")).nowhere(),
                reset: None,
                value: ast::Expression::IntLiteral(0).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Register(
            hir::Register {
                pattern: hir::PatternKind::name(name_id(1, "regname"))
                    .idless()
                    .nowhere(),
                clock: hir::ExprKind::Identifier(name_id(0, "clk").inner)
                    .with_id(0)
                    .nowhere(),
                reset: None,
                value: hir::ExprKind::IntLiteral(0).idless().nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        let clk_id = symtab.add_local_variable(ast_ident("clk"));
        assert_eq!(clk_id.0, 0);
        assert_eq!(
            visit_statement(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
        assert_eq!(symtab.has_symbol(ast_path("regname").inner), true);
    }

    #[test]
    fn declarations_declare_variables() {
        let input = ast::Statement::Declaration(vec![ast_ident("x"), ast_ident("y")]).nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_statement(&input, &mut symtab, &mut idtracker),
            Ok(hir::Statement::Declaration(vec![name_id(0, "x"), name_id(1, "y")]).nowhere())
        );
        assert_eq!(symtab.has_symbol(ast_path("x").inner), true);
        assert_eq!(symtab.has_symbol(ast_path("y").inner), true);
    }

    #[test]
    fn duplicate_declarations_cauases_error() {
        let input = ast::Statement::Declaration(vec![ast_ident("x"), ast_ident("x")]).nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_statement(&input, &mut symtab, &mut idtracker),
            Err(Error::DeclarationError(
                DeclarationError::DuplicateDeclaration {
                    new: ast_ident("x"),
                    old: ast_ident("x")
                }
            ))
        );
    }

    #[test]
    fn register_with_declaration_defines_declaration() {
        let input = ast::Statement::Register(
            ast::Register {
                pattern: ast::Pattern::name("regname"),
                clock: ast::Expression::Identifier(ast_path("clk")).nowhere(),
                reset: None,
                value: ast::Expression::IntLiteral(0).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        symtab.add_local_variable(ast_ident("clk"));
        let id = symtab.add_declaration(ast_ident("regname")).unwrap();

        let result = visit_statement(&input, &mut symtab, &mut idtracker).unwrap();
        match result.inner {
            hir::Statement::Register(reg) => match reg.pattern.kind {
                hir::PatternKind::Name {
                    name: ref reg_id,
                    pre_declared: _,
                } => assert_eq!(id, reg_id.inner),
                _ => panic!("Expected single name in register"),
            },
            other => panic!("Expected register, found {:?}", other),
        }
    }

    #[test]
    fn let_binding_declared_variables_is_not_allowed() {
        let input = ast::Statement::Binding(
            ast::Pattern::name("regname"),
            None,
            ast::Expression::IntLiteral(0).nowhere(),
        )
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        symtab.add_local_variable(ast_ident("clk"));
        symtab.add_declaration(ast_ident("regname")).unwrap();

        let result = visit_statement(&input, &mut symtab, &mut idtracker);

        assert_matches!(result, Err(Error::DeclarationOfNonReg { .. }));
    }

    #[test]
    fn multiple_definitions_of_declared_variables_are_not_allowed() {
        let input = ast::Statement::Register(
            ast::Register {
                pattern: ast::Pattern::name("regname"),
                clock: ast::Expression::Identifier(ast_path("clk")).nowhere(),
                reset: None,
                value: ast::Expression::IntLiteral(0).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        symtab.add_local_variable(ast_ident("clk"));
        symtab.add_declaration(ast_ident("regname")).unwrap();

        visit_statement(&input, &mut symtab, &mut idtracker).unwrap();
        let result = visit_statement(&input, &mut symtab, &mut idtracker);
        assert_matches!(result, Err(Error::RedefinitionOfDeclaration { .. }));
    }
}

#[cfg(test)]
mod expression_visiting {
    use super::*;

    use hir::symbol_table::EnumVariant;
    use hir::{FunctionHead, PipelineHead};
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    #[test]
    fn int_literals_work() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        let input = ast::Expression::IntLiteral(123);
        let expected = hir::ExprKind::IntLiteral(123).idless();

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }

    macro_rules! binop_test {
        ($test_name:ident, $token:ident, $op:ident) => {
            #[test]
            fn $test_name() {
                let mut symtab = SymbolTable::new();
                let mut idtracker = ExprIdTracker::new();
                let input = ast::Expression::BinaryOperator(
                    Box::new(ast::Expression::IntLiteral(123).nowhere()),
                    spade_ast::BinaryOperator::$token,
                    Box::new(ast::Expression::IntLiteral(456).nowhere()),
                );
                let expected = hir::ExprKind::BinaryOperator(
                    Box::new(hir::ExprKind::IntLiteral(123).idless().nowhere()),
                    BinaryOperator::$op,
                    Box::new(hir::ExprKind::IntLiteral(456).idless().nowhere()),
                )
                .idless();

                assert_eq!(
                    visit_expression(&input, &mut symtab, &mut idtracker),
                    Ok(expected)
                );
            }
        };
    }

    binop_test!(additions, Add, Add);
    binop_test!(subtractions, Sub, Sub);
    binop_test!(equals, Equals, Eq);
    binop_test!(bitwise_or, BitwiseOr, BitwiseOr);
    binop_test!(bitwise_and, BitwiseAnd, BitwiseAnd);

    #[test]
    fn identifiers_cause_error_if_undefined() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        let input = ast::Expression::Identifier(ast_path("test"));

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Err(Error::LookupError(
                spade_hir::symbol_table::LookupError::NoSuchSymbol(ast_path("test"))
            ))
        );
    }

    #[test]
    fn blocks_work() {
        let input = ast::Expression::Block(Box::new(ast::Block {
            statements: vec![ast::Statement::Binding(
                ast::Pattern::name("a"),
                None,
                ast::Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            result: ast::Expression::IntLiteral(0).nowhere(),
        }));
        let expected = hir::ExprKind::Block(Box::new(hir::Block {
            statements: vec![hir::Statement::Binding(
                hir::PatternKind::name(name_id(0, "a")).idless().nowhere(),
                None,
                hir::ExprKind::IntLiteral(0).idless().nowhere(),
            )
            .nowhere()],
            result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
        }))
        .idless();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
        assert!(!symtab.has_symbol(ast_path("a").inner));
    }

    #[test]
    fn if_expressions_work() {
        let input = ast::Expression::If(
            Box::new(ast::Expression::IntLiteral(0).nowhere()),
            Box::new(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![],
                    result: ast::Expression::IntLiteral(1).nowhere(),
                }))
                .nowhere(),
            ),
            Box::new(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![],
                    result: ast::Expression::IntLiteral(2).nowhere(),
                }))
                .nowhere(),
            ),
        );
        let expected = hir::ExprKind::If(
            Box::new(hir::ExprKind::IntLiteral(0).idless().nowhere()),
            Box::new(
                hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: hir::ExprKind::IntLiteral(1).idless().nowhere(),
                }))
                .idless()
                .nowhere(),
            ),
            Box::new(
                hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: hir::ExprKind::IntLiteral(2).idless().nowhere(),
                }))
                .idless()
                .nowhere(),
            ),
        )
        .idless();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }

    #[test]
    fn match_expressions_work() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::IntLiteral(1).nowhere()),
            vec![(
                ast::Pattern::name("x"),
                ast::Expression::IntLiteral(2).nowhere(),
            )],
        );

        let expected = hir::ExprKind::Match(
            Box::new(hir::ExprKind::IntLiteral(1).idless().nowhere()),
            vec![(
                hir::PatternKind::name(name_id(0, "x")).idless().nowhere(),
                hir::ExprKind::IntLiteral(2).idless().nowhere(),
            )],
        )
        .idless();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        )
    }

    #[test]
    fn match_expressions_with_enum_members_works() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::IntLiteral(1).nowhere()),
            vec![(
                ast::Pattern::Type(
                    ast_path("x"),
                    ast::ArgumentPattern::Positional(vec![
                        ast::Pattern::Path(ast_path("y")).nowhere()
                    ])
                    .nowhere(),
                )
                .nowhere(),
                ast::Expression::Identifier(ast_path("y")).nowhere(),
            )],
        );

        let expected = hir::ExprKind::Match(
            Box::new(hir::ExprKind::IntLiteral(1).idless().nowhere()),
            vec![(
                hir::PatternKind::Type(
                    name_id(100, "x"),
                    vec![hir::PatternArgument {
                        target: ast_ident("x"),
                        value: hir::PatternKind::name(name_id(0, "y")).idless().nowhere(),
                        kind: hir::ArgumentKind::Positional,
                    }],
                )
                .idless()
                .nowhere(),
                hir::ExprKind::Identifier(name_id(0, "y").inner)
                    .idless()
                    .nowhere(),
            )],
        )
        .idless();

        let mut symtab = SymbolTable::new();

        let enum_variant = EnumVariant {
            output_type: hir::TypeSpec::Unit(().nowhere()).nowhere(),
            option: 0,
            params: hir::ParameterList(vec![(
                ast_ident("x"),
                hir::TypeSpec::Unit(().nowhere()).nowhere(),
            )]),
            type_params: vec![],
        }
        .nowhere();

        symtab.add_thing_with_id(100, ast_path("x").inner, Thing::EnumVariant(enum_variant));
        let mut idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        )
    }

    #[test]
    fn match_expressions_with_0_argument_enum_works() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::IntLiteral(1).nowhere()),
            vec![(
                ast::Pattern::Type(
                    ast_path("x"),
                    ast::ArgumentPattern::Positional(vec![
                        ast::Pattern::Path(ast_path("y")).nowhere()
                    ])
                    .nowhere(),
                )
                .nowhere(),
                ast::Expression::Identifier(ast_path("y")).nowhere(),
            )],
        );

        let expected = hir::ExprKind::Match(
            Box::new(hir::ExprKind::IntLiteral(1).idless().nowhere()),
            vec![(
                hir::PatternKind::Type(
                    name_id(100, "x"),
                    vec![hir::PatternArgument {
                        target: ast_ident("x"),
                        value: hir::PatternKind::name(name_id(0, "y")).idless().nowhere(),
                        kind: hir::ArgumentKind::Positional,
                    }],
                )
                .idless()
                .nowhere(),
                hir::ExprKind::Identifier(name_id(0, "y").inner)
                    .idless()
                    .nowhere(),
            )],
        )
        .idless();

        let mut symtab = SymbolTable::new();

        let enum_variant = EnumVariant {
            output_type: hir::TypeSpec::Unit(().nowhere()).nowhere(),
            option: 0,
            params: hir::ParameterList(vec![(
                ast_ident("x"),
                hir::TypeSpec::Unit(().nowhere()).nowhere(),
            )]),
            type_params: vec![],
        }
        .nowhere();

        symtab.add_thing_with_id(100, ast_path("x").inner, Thing::EnumVariant(enum_variant));
        let mut idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        )
    }

    #[test]
    fn entity_instanciation_works() {
        let input = ast::Expression::EntityInstance(
            ast_path("test"),
            ast::ArgumentList::Positional(vec![
                ast::Expression::IntLiteral(1).nowhere(),
                ast::Expression::IntLiteral(2).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        let expected = hir::ExprKind::EntityInstance(
            name_id(0, "test"),
            vec![
                hir::Argument {
                    target: ast_ident("a"),
                    value: hir::ExprKind::IntLiteral(1).idless().nowhere(),
                    kind: hir::ArgumentKind::Positional,
                },
                hir::Argument {
                    target: ast_ident("b"),
                    value: hir::ExprKind::IntLiteral(2).idless().nowhere(),
                    kind: hir::ArgumentKind::Positional,
                },
            ],
        )
        .idless();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Entity(
                EntityHead {
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![],
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }

    #[test]
    fn entity_instanciation_with_named_args_works() {
        let input = ast::Expression::EntityInstance(
            ast_path("test"),
            ast::ArgumentList::Named(vec![
                ast::NamedArgument::Full(ast_ident("b"), ast::Expression::IntLiteral(2).nowhere()),
                ast::NamedArgument::Full(ast_ident("a"), ast::Expression::IntLiteral(1).nowhere()),
            ])
            .nowhere(),
        )
        .nowhere();

        let expected = hir::ExprKind::EntityInstance(
            name_id(0, "test"),
            vec![
                hir::Argument {
                    target: ast_ident("a"),
                    value: hir::ExprKind::IntLiteral(1).idless().nowhere(),
                    kind: hir::ArgumentKind::Positional,
                },
                hir::Argument {
                    target: ast_ident("b"),
                    value: hir::ExprKind::IntLiteral(2).idless().nowhere(),
                    kind: hir::ArgumentKind::Positional,
                },
            ],
        )
        .idless();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Entity(
                EntityHead {
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![],
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }

    #[test]
    fn function_instantiation_works() {
        let input = ast::Expression::FnCall(
            ast_path("test"),
            ast::ArgumentList::Positional(vec![
                ast::Expression::IntLiteral(1).nowhere(),
                ast::Expression::IntLiteral(2).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        let expected = hir::ExprKind::FnCall(
            name_id(0, "test"),
            vec![
                hir::Argument {
                    target: ast_ident("a"),
                    value: hir::ExprKind::IntLiteral(1).idless().nowhere(),
                    kind: hir::ArgumentKind::Positional,
                },
                hir::Argument {
                    target: ast_ident("b"),
                    value: hir::ExprKind::IntLiteral(2).idless().nowhere(),
                    kind: hir::ArgumentKind::Positional,
                },
            ],
        )
        .idless();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Function(
                FunctionHead {
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![],
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }

    macro_rules! test_named_argument_error {
        ($name:ident($($input_arg:expr),*; $($expected_arg:expr),*; $err:pat)) => {
            #[test]
            fn $name() {
                let input = ast::Expression::EntityInstance(
                        ast_path("test"),
                        ast::ArgumentList::Named(
                            vec![
                                $(
                                    ast::NamedArgument::Full(
                                        ast_ident($input_arg), ast::Expression::IntLiteral(1).nowhere(),
                                    )
                                ),*
                            ]
                        ).nowhere()
                    ).nowhere();

                let mut symtab = SymbolTable::new();
                let mut idtracker = ExprIdTracker::new();

                symtab.add_thing(ast_path("test").inner, Thing::Entity(EntityHead {
                    inputs: hir::ParameterList(vec! [
                        $(
                            (ast_ident($expected_arg), hir::TypeSpec::unit().nowhere())
                        ),*
                    ]),
                    output_type: None,
                    type_params: vec![],
                }.nowhere()));

                matches::assert_matches!(
                    visit_expression(&input, &mut symtab, &mut idtracker),
                    Err($err)
                )
            }
        }
    }

    test_named_argument_error!(missing_arg(
        "a"; "a", "b"; Error::MissingArguments{..}
    ));

    test_named_argument_error!(too_many_args(
        "a", "b", "c"; "a", "b"; Error::NoSuchArgument{..}
    ));

    test_named_argument_error!(duplicate_name_causes_error(
        "a", "b", "b"; "a", "b"; Error::DuplicateNamedBindings{..}
    ));

    macro_rules! test_shorthand_named_arg {
        (
            $name:ident($($input_arg:expr),*; $($expected_arg:expr),*; $err:pat)
                $symtab:tt
        ) => {
            #[test]
            fn $name() {
                let input = ast::Expression::EntityInstance(
                        ast_path("test"),
                        ast::ArgumentList::Named(
                            vec![
                                $(
                                    ast::NamedArgument::Short(ast_ident($input_arg))
                                ),*
                            ]
                        ).nowhere()
                    ).nowhere();

                let mut symtab = $symtab;
                let mut idtracker = ExprIdTracker::new();

                symtab.add_thing(ast_path("test").inner, Thing::Entity(EntityHead {
                    inputs: hir::ParameterList(vec! [
                        $(
                            (ast_ident($expected_arg), hir::TypeSpec::unit().nowhere())
                        ),*
                    ]),
                    output_type: None,
                    type_params: vec![],
                }.nowhere()));

                matches::assert_matches!(
                    visit_expression(&input, &mut symtab, &mut idtracker),
                    Err($err)
                )
            }
        }
    }

    test_shorthand_named_arg!(shorthand_missing_arg(
        "a"; "a", "b"; Error::MissingArguments{..}) {
            let mut symtab = SymbolTable::new();
            symtab.add_local_variable(ast_ident("a"));
            symtab
        }
    );

    test_shorthand_named_arg!(shorthand_too_many_args(
        "a", "b", "c"; "a", "b"; Error::NoSuchArgument{..}) {
            let mut symtab = SymbolTable::new();
            symtab.add_local_variable(ast_ident("a"));
            symtab.add_local_variable(ast_ident("b"));
            symtab.add_local_variable(ast_ident("c"));
            symtab
        }
    );

    test_shorthand_named_arg!(shorthand_duplicate_name_causes_error(
        "a", "b", "b"; "a", "b"; Error::DuplicateNamedBindings{..}) {
            let mut symtab = SymbolTable::new();
            symtab.add_local_variable(ast_ident("a"));
            symtab.add_local_variable(ast_ident("b"));
            symtab
        }
    );

    #[test]
    fn pipeline_instanciation_works() {
        let input = ast::Expression::PipelineInstance(
            2.nowhere(),
            ast_path("test"),
            ast::ArgumentList::Positional(vec![
                ast::Expression::IntLiteral(1).nowhere(),
                ast::Expression::IntLiteral(2).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        let expected = hir::ExprKind::PipelineInstance {
            depth: 2.nowhere(),
            name: name_id(0, "test"),
            args: vec![
                hir::Argument {
                    target: ast_ident("a"),
                    value: hir::ExprKind::IntLiteral(1).idless().nowhere(),
                    kind: hir::ArgumentKind::Positional,
                },
                hir::Argument {
                    target: ast_ident("b"),
                    value: hir::ExprKind::IntLiteral(2).idless().nowhere(),
                    kind: hir::ArgumentKind::Positional,
                },
            ],
        }
        .idless();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Pipeline(
                PipelineHead {
                    depth: 2.nowhere(),
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![]
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }

    #[test]
    fn pipeline_instantiation_with_missmatched_depth_causes_error() {
        let input = ast::Expression::PipelineInstance(
            2.nowhere(),
            ast_path("test"),
            ast::ArgumentList::Positional(vec![
                ast::Expression::IntLiteral(1).nowhere(),
                ast::Expression::IntLiteral(2).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Pipeline(
                PipelineHead {
                    depth: 3.nowhere(),
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![]
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Err(Error::PipelineDepthMissmatch {
                expected: 3,
                got: 2.nowhere()
            })
        );
    }

    // NOTE: This test should be removed once/if we introduce higher order functions
    #[test]
    fn functions_are_not_returnable_values() {
        let input = ast::Expression::Identifier(ast_path("test")).nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        let head = Thing::Function(
            FunctionHead {
                inputs: hir::ParameterList(vec![]),
                output_type: None,
                type_params: vec![],
            }
            .nowhere(),
        );
        symtab.add_thing(ast_path("test").inner, head.clone());

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Err(Error::LookupError(
                hir::symbol_table::LookupError::NotAValue(ast_path("test"), head)
            ))
        );
    }

    #[test]
    fn types_are_not_returnable_values() {
        let input = ast::Expression::Identifier(ast_path("test")).nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();

        let head = Thing::Type(TypeSymbol::Declared(vec![]).nowhere());
        symtab.add_thing(ast_path("test").inner, head.clone());

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Err(Error::LookupError(
                hir::symbol_table::LookupError::NotAValue(ast_path("test"), head)
            ))
        );
    }
}

#[cfg(test)]
mod register_visiting {
    use super::*;

    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    #[test]
    fn register_visiting_works() {
        let input = ast::Register {
            pattern: ast::Pattern::name("test"),
            clock: ast::Expression::Identifier(ast_path("clk")).nowhere(),
            reset: Some((
                ast::Expression::Identifier(ast_path("rst")).nowhere(),
                ast::Expression::IntLiteral(0).nowhere(),
            )),
            value: ast::Expression::IntLiteral(1).nowhere(),
            value_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
        }
        .nowhere();

        let expected = hir::Register {
            pattern: hir::PatternKind::name(name_id(2, "test"))
                .idless()
                .nowhere(),
            clock: hir::ExprKind::Identifier(name_id(0, "clk").inner)
                .with_id(0)
                .nowhere(),
            reset: Some((
                hir::ExprKind::Identifier(name_id(1, "rst").inner)
                    .idless()
                    .nowhere(),
                hir::ExprKind::IntLiteral(0).idless().nowhere(),
            )),
            value: hir::ExprKind::IntLiteral(1).idless().nowhere(),
            value_type: Some(hir::TypeSpec::unit().nowhere()),
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        let clk_id = symtab.add_local_variable(ast_ident("clk"));
        assert_eq!(clk_id.0, 0);
        let rst_id = symtab.add_local_variable(ast_ident("rst"));
        assert_eq!(rst_id.0, 1);
        assert_eq!(
            visit_register(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }
}

#[cfg(test)]
mod item_visiting {
    use super::*;

    use hir::ItemList;
    use spade_ast::testutil::ast_ident;
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    use pretty_assertions::assert_eq;

    #[test]
    pub fn item_entity_visiting_works() {
        let input = ast::Item::Entity(
            ast::Entity {
                name: ast_ident("test"),
                output_type: None,
                inputs: ParameterList(vec![]),
                body: ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![],
                    result: ast::Expression::IntLiteral(0).nowhere(),
                }))
                .nowhere(),
                type_params: vec![],
            }
            .nowhere(),
        );

        let expected = hir::Item::Entity(
            hir::Entity {
                name: name_id(0, "test"),
                head: EntityHead {
                    output_type: None,
                    inputs: hir::ParameterList(vec![]),
                    type_params: vec![],
                },
                inputs: vec![],
                body: hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
                }))
                .idless()
                .nowhere(),
            }
            .nowhere(),
        );

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        let namespace = Path(vec![]);
        crate::global_symbols::visit_item(&input, &namespace, &mut symtab, &mut ItemList::new())
            .unwrap();
        assert_eq!(
            visit_item(&input, &namespace, &mut symtab, &mut idtracker),
            Ok(Some(expected))
        );
    }
}

#[cfg(test)]
mod module_visiting {
    use super::*;

    use hir::ItemList;
    use spade_ast::testutil::ast_ident;
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    use pretty_assertions::assert_eq;

    #[test]
    fn visiting_module_with_one_entity_works() {
        let input = ast::ModuleBody {
            members: vec![ast::Item::Entity(
                ast::Entity {
                    name: ast_ident("test"),
                    output_type: None,
                    inputs: ParameterList(vec![]),
                    body: ast::Expression::Block(Box::new(ast::Block {
                        statements: vec![],
                        result: ast::Expression::IntLiteral(0).nowhere(),
                    }))
                    .nowhere(),
                    type_params: vec![],
                }
                .nowhere(),
            )],
        };

        let expected = hir::ItemList {
            executables: vec![(
                name_id(0, "test").inner,
                hir::ExecutableItem::Entity(
                    hir::Entity {
                        name: name_id(0, "test"),
                        head: EntityHead {
                            output_type: None,
                            inputs: hir::ParameterList(vec![]),
                            type_params: vec![],
                        },
                        inputs: vec![],
                        body: hir::ExprKind::Block(Box::new(hir::Block {
                            statements: vec![],
                            result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
                        }))
                        .idless()
                        .nowhere(),
                    }
                    .nowhere(),
                ),
            )]
            .into_iter()
            .collect(),
            types: vec![].into_iter().collect(),
        };

        let mut symtab = SymbolTable::new();
        let mut idtracker = ExprIdTracker::new();
        global_symbols::gather_symbols(&input, &Path(vec![]), &mut symtab, &mut ItemList::new())
            .expect("failed to collect global symbols");
        assert_eq!(
            visit_module_body(
                ItemList::new(),
                &input,
                &Path(vec![]),
                &mut symtab,
                &mut idtracker
            ),
            Ok(expected)
        );
    }
}
