use thiserror::Error;

use crate::hir;
use crate::lexer::TokenKind;
use crate::location_info::{Loc, WithLocation};
use crate::symbol_table::SymbolTable;
use crate::types::Error as TypeError;
use crate::types::Type;
use crate::{ast, hir::EntityHead};

impl<T> Loc<T> {
    pub fn try_visit<V, U>(
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
    #[error("Undefined path {}", 0.0)]
    UndefinedPath(Loc<ast::Path>),
    #[error("Duplicate type variable")]
    DuplicateTypeVariable {
        found: Loc<hir::Identifier>,
        previously: Loc<hir::Identifier>,
    },
    #[error("Type error")]
    InvalidType(#[source] TypeError, Loc<()>),
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct IdTracker {
    id: u64,
}
impl IdTracker {
    pub fn new() -> Self {
        Self { id: 0 }
    }

    fn next(&mut self) -> u64 {
        let result = self.id;
        self.id += 1;
        result
    }
}

pub fn visit_type_param(param: &ast::TypeParam) -> hir::TypeParam {
    match param {
        ast::TypeParam::TypeName(name) => hir::TypeParam::TypeName(visit_identifier(name)),
        ast::TypeParam::Integer(name) => hir::TypeParam::Integer(name.map_ref(visit_identifier)),
    }
}

pub fn entity_head(item: &ast::Entity) -> Result<EntityHead> {
    let mut inputs = vec![];
    for (name, input_type) in &item.inputs {
        let t = input_type
            .map_ref(Type::convert_from_ast)
            .map_err(Error::InvalidType)?;

        inputs.push((name.map_ref(visit_identifier), t));
    }

    let output_type = item
        .output_type
        .map_ref(Type::convert_from_ast)
        .map_err(Error::InvalidType)?;

    let mut type_params: Vec<Loc<hir::TypeParam>> = vec![];
    for param in &item.type_params {
        let param = param.map_ref(visit_type_param);
        if let Some(prev) = type_params
            .iter()
            .filter(|prev| prev.name() == param.name())
            .next()
        {
            return Err(Error::DuplicateTypeVariable {
                found: param.name().clone().at(param.span),
                previously: prev.map_ref(|p| p.name().clone()),
            });
        }
        type_params.push(param.clone());
    }

    Ok(EntityHead {
        inputs,
        output_type,
        type_params,
    })
}

pub fn visit_entity(
    item: &ast::Entity,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<hir::Entity> {
    symtab.new_scope();

    let name = item.name.map_ref(visit_identifier);

    let head = entity_head(item)?;
    for (name, _) in &head.inputs {
        symtab.add_ident(name);
    }

    let body = item.body.try_visit(visit_expression, symtab, idtracker)?;

    symtab.close_scope();

    Ok(hir::Entity { name, head, body })
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
        ast::Item::Entity(e) => Ok(Some(hir::Item::Entity(e.try_visit(
            &visit_entity,
            symtab,
            idtracker,
        )?))),
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
                Some(
                    t.map_ref(Type::convert_from_ast)
                        .map_err(Error::InvalidType)?,
                )
            } else {
                None
            };
            let name = ident.map_ref(visit_identifier);
            symtab.add_ident(&name);

            let expr = expr.try_visit(visit_expression, symtab, idtracker)?;

            Ok(Loc::new(
                hir::Statement::Binding(name, hir_type, expr),
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
        ast::Expression::BinaryOperator(lhs, tok, rhs) => {
            let lhs = lhs.try_visit(visit_expression, symtab, idtracker)?;
            let rhs = rhs.try_visit(visit_expression, symtab, idtracker)?;

            let intrinsic = |name| {
                hir::ExprKind::FnCall(
                    hir::Path::from_strs(&["intrinsics", name]).nowhere(),
                    vec![lhs, rhs],
                )
            };

            match tok {
                TokenKind::Plus => Ok(intrinsic("add")),
                TokenKind::Minus => Ok(intrinsic("sub")),
                TokenKind::Asterisk => Ok(intrinsic("mul")),
                TokenKind::Slash => Ok(intrinsic("div")),
                TokenKind::Equals => Ok(intrinsic("eq")),
                _ => unreachable! {},
            }
        }
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
            let hir_path = path.clone().map_ref(visit_path);
            if let Some(id) = hir_path.maybe_identifier() {
                if symtab.has_symbol(id) {
                    Ok(hir::ExprKind::Identifier(hir_path))
                } else {
                    Err(Error::UndefinedPath(path.clone()))
                }
            } else {
                println!("NOTE: global symbols are currently unsupported");
                Err(Error::UndefinedPath(path.clone()))
            }
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

pub fn visit_identifier(id: &ast::Identifier) -> hir::Identifier {
    hir::Identifier::Named(id.0.clone())
}
pub fn visit_path(path: &ast::Path) -> hir::Path {
    let result = path.0.iter().map(|p| visit_identifier(&p)).collect();
    hir::Path(result)
}

pub fn visit_register(
    reg: &Loc<ast::Register>,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<Loc<hir::Register>> {
    let (reg, loc) = reg.split_ref();

    let name = reg.name.map_ref(visit_identifier);
    symtab.add_ident(&name);

    let clock = reg.clock.clone().map_ref(visit_path);
    if let Some(id) = clock.maybe_identifier() {
        if !symtab.has_symbol(id) {
            return Err(Error::UndefinedPath(reg.clock.clone()));
        }
    } else {
        unimplemented!("Global clocks are unsupported")
    }

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
        Some(
            value_type
                .map_ref(Type::convert_from_ast)
                .map_err(Error::InvalidType)?,
        )
    } else {
        None
    };

    Ok(Loc::new(
        hir::Register {
            name,
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

    use crate::location_info::WithLocation;
    use crate::testutil::{ast_ident, hir_ident};

    use pretty_assertions::assert_eq;

    #[test]
    fn entity_visits_work() {
        let input = ast::Entity {
            name: ast::Identifier("test".to_string()).nowhere(),
            inputs: vec![(ast_ident("a"), ast::Type::UnitType.nowhere())],
            output_type: ast::Type::UnitType.nowhere(),
            body: ast::Expression::Block(Box::new(ast::Block {
                statements: vec![ast::Statement::Binding(
                    ast_ident("var"),
                    Some(ast::Type::UnitType.nowhere()),
                    ast::Expression::IntLiteral(0).nowhere(),
                )
                .nowhere()],
                result: ast::Expression::IntLiteral(0).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        };

        let expected = hir::Entity {
            name: hir_ident("test"),
            head: hir::EntityHead {
                inputs: vec![
                    ((
                        hir::Identifier::Named("a".to_string()).nowhere(),
                        Type::Unit.nowhere(),
                    )),
                ],
                output_type: Type::Unit.nowhere(),
                type_params: vec![],
            },
            body: hir::ExprKind::Block(Box::new(hir::Block {
                statements: vec![hir::Statement::Binding(
                    hir_ident("var"),
                    Some(Type::Unit.nowhere()),
                    hir::ExprKind::IntLiteral(0).idless().nowhere(),
                )
                .nowhere()],
                result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
            }))
            .idless()
            .nowhere(),
        };

        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();

        let result = visit_entity(&input, &mut symtab, &mut idtracker);

        assert_eq!(result, Ok(expected));

        // But the local variables should not
        assert!(!symtab.has_symbol(&hir_ident("a").inner));
        assert!(!symtab.has_symbol(&hir_ident("var").inner));
    }

    #[test]
    fn entity_with_generics_works() {
        let input = ast::Entity {
            name: ast::Identifier("test".to_string()).nowhere(),
            inputs: vec![(ast_ident("a"), ast::Type::UnitType.nowhere())],
            output_type: ast::Type::UnitType.nowhere(),
            body: ast::Expression::Block(Box::new(ast::Block {
                statements: vec![ast::Statement::Binding(
                    ast_ident("var"),
                    Some(ast::Type::UnitType.nowhere()),
                    ast::Expression::IntLiteral(0).nowhere(),
                )
                .nowhere()],
                result: ast::Expression::IntLiteral(0).nowhere(),
            }))
            .nowhere(),
            type_params: vec![
                ast::TypeParam::TypeName(ast_ident("a").inner).nowhere(),
                ast::TypeParam::Integer(ast_ident("b")).nowhere(),
            ],
        };

        let expected = hir::Entity {
            name: hir_ident("test"),
            head: hir::EntityHead {
                inputs: vec![
                    ((
                        hir::Identifier::Named("a".to_string()).nowhere(),
                        Type::Unit.nowhere(),
                    )),
                ],
                output_type: Type::Unit.nowhere(),
                type_params: vec![
                    hir::TypeParam::TypeName(hir_ident("a").inner).nowhere(),
                    hir::TypeParam::Integer(hir_ident("b")).nowhere(),
                ],
            },
            body: hir::ExprKind::Block(Box::new(hir::Block {
                statements: vec![hir::Statement::Binding(
                    hir_ident("var"),
                    Some(Type::Unit.nowhere()),
                    hir::ExprKind::IntLiteral(0).idless().nowhere(),
                )
                .nowhere()],
                result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
            }))
            .idless()
            .nowhere(),
        };

        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();

        let result = visit_entity(&input, &mut symtab, &mut idtracker);

        assert_eq!(result, Ok(expected));

        // But the local variables should not
        assert!(!symtab.has_symbol(&hir_ident("a").inner));
        assert!(!symtab.has_symbol(&hir_ident("var").inner));
    }
}

#[cfg(test)]
mod statement_visiting {
    use super::*;

    use crate::location_info::WithLocation;

    use crate::testutil::{ast_ident, ast_path, hir_ident, hir_path};

    #[test]
    fn bindings_convert_correctly() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();

        let input = ast::Statement::Binding(
            ast_ident("a"),
            Some(ast::Type::UnitType.nowhere()),
            ast::Expression::IntLiteral(0).nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Binding(
            hir_ident("a"),
            Some(Type::Unit.nowhere()),
            hir::ExprKind::IntLiteral(0).idless().nowhere(),
        )
        .nowhere();

        assert_eq!(
            visit_statement(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
        assert_eq!(symtab.has_symbol(&hir_ident("a").inner), true);
    }

    #[test]
    fn registers_are_statements() {
        let input = ast::Statement::Register(
            ast::Register {
                name: ast_ident("regname"),
                clock: ast_path("clk"),
                reset: None,
                value: ast::Expression::IntLiteral(0).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Register(
            hir::Register {
                name: hir_ident("regname"),
                clock: hir_path("clk"),
                reset: None,
                value: hir::ExprKind::IntLiteral(0).idless().nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();
        symtab.add_ident(&hir_ident("clk"));
        assert_eq!(
            visit_statement(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
        assert_eq!(symtab.has_symbol(&hir_ident("regname").inner), true);
    }
}

#[cfg(test)]
mod expression_visiting {
    use super::*;

    use crate::testutil::{ast_path, hir_path};
    use crate::{location_info::WithLocation, testutil::hir_ident};

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
        ($test_name:ident, $token:ident, $kind:expr) => {
            #[test]
            fn $test_name() {
                let mut symtab = SymbolTable::new();
                let mut idtracker = IdTracker::new();
                let input = ast::Expression::BinaryOperator(
                    Box::new(ast::Expression::IntLiteral(123).nowhere()),
                    crate::lexer::TokenKind::$token,
                    Box::new(ast::Expression::IntLiteral(456).nowhere()),
                );
                let expected = hir::ExprKind::FnCall(
                    hir::Path::from_strs(&["intrinsics", $kind]).nowhere(),
                    vec![
                        hir::ExprKind::IntLiteral(123).idless().nowhere(),
                        hir::ExprKind::IntLiteral(456).idless().nowhere(),
                    ],
                )
                .idless();

                assert_eq!(
                    visit_expression(&input, &mut symtab, &mut idtracker),
                    Ok(expected)
                );
            }
        };
    }

    binop_test!(additions, Plus, "add");
    binop_test!(subtractions, Minus, "sub");
    binop_test!(multiplication, Asterisk, "mul");
    binop_test!(division, Slash, "div");
    binop_test!(equals, Equals, "eq");

    #[test]
    fn identifiers_work() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();
        symtab.add_ident(&hir_ident("test"));
        let input = ast::Expression::Identifier(ast_path("test"));
        let expected = hir::ExprKind::Identifier(hir_path("test")).idless();

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }

    #[test]
    fn identifiers_cause_error_if_undefined() {
        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();
        let input = ast::Expression::Identifier(ast_path("test"));

        assert_eq!(
            visit_expression(&input, &mut symtab, &mut idtracker),
            Err(Error::UndefinedPath(ast_path("test")))
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
                hir::Identifier::Named("a".to_string()).nowhere(),
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
        assert!(!symtab.has_symbol(&hir_ident("a").inner));
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

    use crate::location_info::WithLocation;
    use crate::testutil::{ast_path, hir_ident, hir_path};

    #[test]
    fn register_visiting_works() {
        let input = ast::Register {
            name: ast::Identifier("test".to_string()).nowhere(),
            clock: ast_path("clk"),
            reset: Some((
                ast::Expression::Identifier(ast_path("rst")).nowhere(),
                ast::Expression::IntLiteral(0).nowhere(),
            )),
            value: ast::Expression::IntLiteral(1).nowhere(),
            value_type: Some(ast::Type::UnitType.nowhere()),
        }
        .nowhere();

        let expected = hir::Register {
            name: hir_ident("test"),
            clock: hir_path("clk"),
            reset: Some((
                hir::ExprKind::Identifier(hir_path("rst"))
                    .idless()
                    .nowhere(),
                hir::ExprKind::IntLiteral(0).idless().nowhere(),
            )),
            value: hir::ExprKind::IntLiteral(1).idless().nowhere(),
            value_type: Some(Type::Unit.nowhere()),
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut idtracker = IdTracker::new();
        symtab.add_ident(&hir_ident("clk"));
        symtab.add_ident(&hir_ident("rst"));
        assert_eq!(
            visit_register(&input, &mut symtab, &mut idtracker),
            Ok(expected)
        );
    }
}

#[cfg(test)]
mod item_visiting {
    use super::*;

    use crate::location_info::WithLocation;
    use crate::testutil::{ast_ident, hir_ident};

    use pretty_assertions::assert_eq;

    #[test]
    pub fn item_entity_visiting_works() {
        let input = ast::Item::Entity(
            ast::Entity {
                name: ast_ident("test"),
                output_type: ast::Type::UnitType.nowhere(),
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
                name: hir_ident("test"),
                head: EntityHead {
                    output_type: Type::Unit.nowhere(),
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

    use crate::location_info::WithLocation;
    use crate::testutil::{ast_ident, hir_ident};

    use pretty_assertions::assert_eq;

    #[test]
    fn visiting_module_with_one_entity_works() {
        let input = ast::ModuleBody {
            members: vec![ast::Item::Entity(
                ast::Entity {
                    name: ast_ident("test"),
                    output_type: ast::Type::UnitType.nowhere(),
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
                    name: hir_ident("test"),
                    head: EntityHead {
                        output_type: Type::Unit.nowhere(),
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
