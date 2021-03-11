pub mod error_reporting;
pub mod id_tracker;
pub mod symbol_table;

use thiserror::Error;

use crate::symbol_table::SymbolTable;
use crate::{
    id_tracker::IdTracker,
    symbol_table::{Thing, TypeSymbol},
};
use spade_common::location_info::{Loc, WithLocation};
use spade_hir as hir;
use spade_hir::{expression::BinaryOperator, EntityHead, NameID};
use spade_parser::ast;
use spade_parser::lexer::TokenKind;

trait LocExt<T> {
    fn try_visit<V, U>(
        &self,
        visitor: V,
        symtab: &mut SymbolTable,
        idtracker: &mut IdTracker,
    ) -> Result<Loc<U>>
    where
        V: Fn(&T, &mut SymbolTable, &mut IdTracker) -> Result<U>;
}

impl<T> LocExt<T> for Loc<T> {
    fn try_visit<V, U>(
        &self,
        visitor: V,
        symtab: &mut SymbolTable,
        idtracker: &mut IdTracker,
    ) -> Result<Loc<U>>
    where
        V: Fn(&T, &mut SymbolTable, &mut IdTracker) -> Result<U>,
    {
        self.map_ref(|t| visitor(&t, symtab, idtracker))
            .map_err(|e, _| e)
    }
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum Error {
    #[error("Lookup error")]
    LookupError(#[from] crate::symbol_table::Error),
    #[error("Duplicate type variable")]
    DuplicateTypeVariable {
        found: Loc<ast::Identifier>,
        previously: Loc<ast::Identifier>,
    },
}

pub type Result<T> = std::result::Result<T, Error>;

pub fn path_from_ident(ident: Loc<ast::Identifier>) -> Loc<ast::Path> {
    ast::Path(vec![ident.clone()]).at_loc(&ident)
}

pub fn visit_type_param(_param: &Loc<ast::TypeParam>, _symtab: &mut SymbolTable) -> NameID {
    // let (name, kind) = match param {
    //     ast::TypeParam::TypeName(name) => (param.map(|_| name), hir::TypeParam::TypeName),
    //     ast::TypeParam::Integer(name) => (name, hir::TypeParam::Integer),
    // };
    // symtab.add_item(name, param.map(|_| kind))
    todo!("Implement visiting type parameters")
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
        ast::TypeSpec::Named(name, params) => {
            // NOTE: this weird scope is required because the borrow of t lasts
            // until the end of the outer scope even if we clone here.
            let t = {
                let (_, t) = symtab.lookyp_type_symbol(name)?;
                t.clone()
            };

            let base = match t {
                TypeSymbol::Alias(t) => t.clone(),
                _ => todo!("Implement support for generic type parameters"),
            };

            let params = params
                .iter()
                .map(|p| p.try_map_ref(|p| visit_type_expression(p, symtab)))
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::TypeSpec::Concrete(base, params))
        }
        ast::TypeSpec::Tuple(inner) => {
            let inner = inner
                .iter()
                .map(|p| p.try_map_ref(|p| visit_type_spec(p, symtab)))
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::TypeSpec::Tuple(inner))
        }
        ast::TypeSpec::Unit(w) => Ok(hir::TypeSpec::Concrete(
            w.map(|_| spade_types::BaseType::Unit),
            vec![],
        )),
    }
}

/// Visit an entity to generate an entity head. The symtab gets populated with the name of the
/// entity and its definition, but not with the inputs and type parameteres
///
/// The `add_local_symbols` parameter determines wether or not symbols should be added to the
/// current scope or not. If false, a new throw-away scope will be created.
///
/// This is kind of an ugly hack to enable code re-use. We should get rid of it eventually
pub fn entity_head(
    item: &ast::Entity,
    symtab: &mut SymbolTable,
    add_local_symbols: bool,
) -> Result<EntityHead> {
    if !add_local_symbols {
        symtab.new_scope();
    }
    let type_params = vec![];
    if !item.type_params.is_empty() {
        todo!("Handle generic type parameters in entities");
    }

    let mut inputs = vec![];
    for (name, input_type) in &item.inputs {
        let t = input_type.try_map_ref(|t| visit_type_spec(t, symtab))?;

        let id = symtab.add_thing(
            path_from_ident(name.clone()).inner,
            Thing::Variable(name.clone()),
        );
        inputs.push((id, t));
    }

    let output_type = if let Some(output_type) = &item.output_type {
        Some(output_type.try_map_ref(|t| visit_type_spec(t, symtab))?)
    } else {
        None
    };

    if !add_local_symbols {
        symtab.close_scope()
    }

    Ok(EntityHead {
        inputs,
        output_type,
        type_params,
    })
}

pub fn visit_entity(
    item: &Loc<ast::Entity>,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<Loc<hir::Entity>> {
    symtab.new_scope();

    let head = entity_head(item, symtab, true)?;

    let body = item.body.try_visit(visit_expression, symtab, idtracker)?;

    symtab.close_scope();

    let name = symtab.add_thing(
        path_from_ident(item.name.clone()).inner,
        Thing::Entity(head.clone().at_loc(item)),
    );

    Ok(hir::Entity {
        name: name.at_loc(&item.name),
        head,
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
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<Option<hir::Item>> {
    match item {
        ast::Item::Entity(e) => Ok(Some(hir::Item::Entity(visit_entity(e, symtab, idtracker)?))),
        ast::Item::TraitDef(_) => {
            // NOTE: Traits are invisible at the HIR stage, so we just ignore them
            Ok(None)
        }
    }
}

pub fn visit_module_body(
    module: &ast::ModuleBody,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<hir::ModuleBody> {
    Ok(hir::ModuleBody {
        members: module
            .members
            .iter()
            .map(|i| visit_item(i, symtab, idtracker))
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .filter_map(|x| x)
            .collect::<Vec<_>>(),
    })
}

pub fn visit_statement(
    s: &Loc<ast::Statement>,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<Loc<hir::Statement>> {
    let (s, span) = s.split_ref();
    match s {
        ast::Statement::Binding(ident, t, expr) => {
            let hir_type = if let Some(t) = t {
                Some(t.try_map_ref(|t| visit_type_spec(t, symtab))?)
            } else {
                None
            };
            let name_id = symtab.add_thing(
                path_from_ident(ident.clone()).inner,
                Thing::Variable(ident.clone()),
            );

            let expr = expr.try_visit(visit_expression, symtab, idtracker)?;

            Ok(Loc::new(
                hir::Statement::Binding(name_id.at_loc(ident), hir_type, expr),
                span,
            ))
        }
        ast::Statement::Register(inner) => {
            let (result, span) = visit_register(&inner, symtab, idtracker)?.separate();
            Ok(Loc::new(hir::Statement::Register(result), span))
        }
    }
}

pub fn visit_expression(
    e: &ast::Expression,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<hir::Expression> {
    match e {
        ast::Expression::IntLiteral(val) => Ok(hir::ExprKind::IntLiteral(val.clone())),
        ast::Expression::BoolLiteral(val) => Ok(hir::ExprKind::BoolLiteral(*val)),
        ast::Expression::BinaryOperator(lhs, tok, rhs) => {
            let lhs = lhs.try_visit(visit_expression, symtab, idtracker)?;
            let rhs = rhs.try_visit(visit_expression, symtab, idtracker)?;

            let operator = |op| hir::ExprKind::BinaryOperator(Box::new(lhs), op, Box::new(rhs));

            match tok {
                TokenKind::Plus => Ok(operator(BinaryOperator::Add)),
                TokenKind::Minus => Ok(operator(BinaryOperator::Sub)),
                TokenKind::Asterisk => Ok(operator(BinaryOperator::Mul)),
                TokenKind::Slash => panic!("division is unsupported"),
                TokenKind::Equals => Ok(operator(BinaryOperator::Eq)),
                TokenKind::Gt => Ok(operator(BinaryOperator::Gt)),
                TokenKind::Lt => Ok(operator(BinaryOperator::Lt)),
                TokenKind::LeftShift => Ok(operator(BinaryOperator::LeftShift)),
                TokenKind::RightShift => Ok(operator(BinaryOperator::RightShift)),
                TokenKind::LogicalAnd => Ok(operator(BinaryOperator::LogicalAnd)),
                TokenKind::LogicalOr => Ok(operator(BinaryOperator::LogicalOr)),
                _ => unreachable! {},
            }
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
        ast::Expression::Block(block) => Ok(hir::ExprKind::Block(Box::new(visit_block(
            block, symtab, idtracker,
        )?))),
        ast::Expression::Identifier(path) => {
            let id = symtab.lookup_id(path)?;

            Ok(hir::ExprKind::Identifier(id))
        }
    }
    .map(|kind| kind.with_id(idtracker.next()))
}

pub fn visit_block(
    b: &ast::Block,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<hir::Block> {
    symtab.new_scope();
    let mut statements = vec![];
    for statement in &b.statements {
        statements.push(visit_statement(&statement, symtab, idtracker)?)
    }

    let result = b.result.try_visit(visit_expression, symtab, idtracker)?;

    symtab.close_scope();

    Ok(hir::Block { statements, result })
}

pub fn visit_register(
    reg: &Loc<ast::Register>,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<Loc<hir::Register>> {
    let (reg, loc) = reg.split_ref();

    let name_id = symtab
        .add_thing(
            path_from_ident(reg.clone().name).inner,
            Thing::Variable(reg.name.clone()),
        )
        .at_loc(&reg.name);

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

    Ok(Loc::new(
        hir::Register {
            name: name_id,
            clock,
            reset,
            value,
            value_type,
        },
        loc,
    ))
}

#[cfg(test)]
mod entity_visiting {
    use super::*;

    use spade_common::location_info::WithLocation;
    use spade_parser::testutil::{ast_ident, ast_path};
    use spade_testutil::name_id;

    use pretty_assertions::assert_eq;

    #[test]
    fn entity_visits_work() {
        let input = ast::Entity {
            name: ast::Identifier("test".to_string()).nowhere(),
            inputs: vec![(ast_ident("a"), ast::TypeSpec::Unit(().nowhere()).nowhere())],
            output_type: None,
            body: ast::Expression::Block(Box::new(ast::Block {
                statements: vec![ast::Statement::Binding(
                    ast_ident("var"),
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
            name: name_id(2, "test"),
            head: hir::EntityHead {
                inputs: vec![((name_id(0, "a").inner, hir::TypeSpec::unit().nowhere()))],
                output_type: None,
                type_params: vec![],
            },
            body: hir::ExprKind::Block(Box::new(hir::Block {
                statements: vec![hir::Statement::Binding(
                    name_id(1, "var"),
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
        let mut idtracker = IdTracker::new();

        let result = visit_entity(&input, &mut symtab, &mut idtracker);

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
        //     name: ast::Identifier("test".to_string()).nowhere(),
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
        //                 NameID(0, ast::Path::from_strs(&["a"])),
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
        // let mut idtracker = IdTracker::new();

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

    use spade_common::location_info::WithLocation;
    use spade_parser::testutil::{ast_ident, ast_path};
    use spade_testutil::name_id;

    #[test]
    fn bindings_convert_correctly() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();

        let input = ast::Statement::Binding(
            ast_ident("a"),
            Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            ast::Expression::IntLiteral(0).nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Binding(
            name_id(0, "a"),
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
                name: ast_ident("regname"),
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
                name: name_id(1, "regname"),
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
        let mut idtracker = IdTracker::new();
        let clk_id = symtab.add_local_variable(ast_ident("clk"));
        assert_eq!(clk_id.0, 0);
        assert_eq!(
            visit_statement(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
        assert_eq!(symtab.has_symbol(ast_path("regname").inner), true);
    }
}

#[cfg(test)]
mod expression_visiting {
    use super::*;

    use spade_common::location_info::WithLocation;
    use spade_parser::testutil::ast_path;
    use spade_testutil::name_id;

    #[test]
    fn int_literals_work() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();
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
                let mut idtracker = IdTracker::new();
                let input = ast::Expression::BinaryOperator(
                    Box::new(ast::Expression::IntLiteral(123).nowhere()),
                    spade_parser::lexer::TokenKind::$token,
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

    binop_test!(additions, Plus, Add);
    binop_test!(subtractions, Minus, Sub);
    binop_test!(multiplication, Asterisk, Mul);
    binop_test!(equals, Equals, Eq);

    #[test]
    fn identifiers_cause_error_if_undefined() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();
        let input = ast::Expression::Identifier(ast_path("test"));

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Err(Error::LookupError(
                crate::symbol_table::Error::NoSuchSymbol(ast_path("test"))
            ))
        );
    }

    #[test]
    fn blocks_work() {
        let input = ast::Expression::Block(Box::new(ast::Block {
            statements: vec![ast::Statement::Binding(
                ast::Identifier("a".to_string()).nowhere(),
                None,
                ast::Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            result: ast::Expression::IntLiteral(0).nowhere(),
        }));
        let expected = hir::ExprKind::Block(Box::new(hir::Block {
            statements: vec![hir::Statement::Binding(
                name_id(0, "a"),
                None,
                hir::ExprKind::IntLiteral(0).idless().nowhere(),
            )
            .nowhere()],
            result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
        }))
        .idless();

        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();
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
        let mut idtracker = IdTracker::new();
        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }
}

#[cfg(test)]
mod register_visiting {
    use super::*;

    use spade_common::location_info::WithLocation;
    use spade_parser::testutil::{ast_ident, ast_path};
    use spade_testutil::name_id;

    #[test]
    fn register_visiting_works() {
        let input = ast::Register {
            name: ast::Identifier("test".to_string()).nowhere(),
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
            name: name_id(2, "test"),
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
        let mut idtracker = IdTracker::new();
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

    use spade_common::location_info::WithLocation;
    use spade_parser::testutil::ast_ident;
    use spade_testutil::name_id;

    use pretty_assertions::assert_eq;

    #[test]
    pub fn item_entity_visiting_works() {
        let input = ast::Item::Entity(
            ast::Entity {
                name: ast_ident("test"),
                output_type: None,
                inputs: vec![],
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
                    inputs: vec![],
                    type_params: vec![],
                },
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
        let mut idtracker = IdTracker::new();
        assert_eq!(
            visit_item(&input, &mut symtab, &mut idtracker),
            Ok(Some(expected))
        );
    }
}

#[cfg(test)]
mod module_visiting {
    use super::*;

    use spade_common::location_info::WithLocation;
    use spade_parser::testutil::ast_ident;
    use spade_testutil::name_id;

    use pretty_assertions::assert_eq;

    #[test]
    fn visiting_module_with_one_entity_works() {
        let input = ast::ModuleBody {
            members: vec![ast::Item::Entity(
                ast::Entity {
                    name: ast_ident("test"),
                    output_type: None,
                    inputs: vec![],
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

        let expected = hir::ModuleBody {
            members: vec![hir::Item::Entity(
                hir::Entity {
                    name: name_id(0, "test"),
                    head: EntityHead {
                        output_type: None,
                        inputs: vec![],
                        type_params: vec![],
                    },
                    body: hir::ExprKind::Block(Box::new(hir::Block {
                        statements: vec![],
                        result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
                    }))
                    .idless()
                    .nowhere(),
                }
                .nowhere(),
            )],
        };

        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();
        assert_eq!(
            visit_module_body(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }
}
