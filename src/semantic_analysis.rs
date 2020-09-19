use thiserror::Error;

use crate::ast;
use crate::hir;
use crate::lexer::TokenKind;
use crate::location_info::Loc;
use crate::symbol_table::SymbolTable;
use crate::types::Error as TypeError;
use crate::types::Type;

#[derive(Error, Debug, PartialEq)]
pub enum Error {
    #[error("Undefined path {}", 0.0)]
    UndefinedPath(Loc<ast::Path>),
    #[error("Type error")]
    InvalidType(#[source] TypeError, Loc<()>),
}

pub type Result<T> = std::result::Result<T, Error>;

pub fn visit_entity(item: ast::Entity, symtab: &mut SymbolTable) -> Result<hir::Entity> {
    symtab.add_ident(&item.name);
    symtab.new_scope();

    let name = item.name.map(visit_identifier);

    let mut inputs = vec![];
    for (name, input_type) in item.inputs {
        symtab.add_ident(&name);

        let t = input_type
            .map(Type::convert_from_ast)
            .map_err(Error::InvalidType)?;

        inputs.push((name.map(visit_identifier), t));
    }

    let output_type = item
        .output_type
        .map(Type::convert_from_ast)
        .map_err(Error::InvalidType)?;

    let block = item
        .block
        .map(|block| visit_block(block, symtab))
        .map_err(|e, _| e)?;

    symtab.close_scope();

    Ok(hir::Entity {
        name,
        inputs,
        output_type,
        block,
    })
}

pub fn visit_statement(
    s: Loc<ast::Statement>,
    symtab: &mut SymbolTable,
) -> Result<Loc<hir::Statement>> {
    let (s, span) = s.split();
    match s {
        ast::Statement::Binding(ident, t, expr) => {
            symtab.add_ident(&ident);
            let hir_type = if let Some(t) = t {
                Some(t.map(Type::convert_from_ast).map_err(Error::InvalidType)?)
            } else {
                None
            };
            let name = ident.map(visit_identifier);

            let expr = expr
                .map(|e| visit_expression(e, symtab))
                .map_err(|e, _| e)?;

            Ok(Loc::new(
                hir::Statement::Binding(name, hir_type, expr),
                span,
            ))
        }
        ast::Statement::Register(inner) => {
            let (result, span) = visit_register(inner, symtab)?.separate();
            Ok(Loc::new(hir::Statement::Register(result), span))
        }
    }
}

pub fn visit_expression(e: ast::Expression, symtab: &mut SymbolTable) -> Result<hir::Expression> {
    match e {
        ast::Expression::IntLiteral(val) => Ok(hir::Expression::IntLiteral(val)),
        ast::Expression::BinaryOperator(lhs, tok, rhs) => {
            let lhs = lhs.map(|x| visit_expression(x, symtab)).map_err(|e, _| e)?;
            let rhs = rhs.map(|x| visit_expression(x, symtab)).map_err(|e, _| e)?;
            match tok {
                TokenKind::Plus => Ok(hir::Expression::Add(Box::new(lhs), Box::new(rhs))),
                TokenKind::Minus => Ok(hir::Expression::Sub(Box::new(lhs), Box::new(rhs))),
                TokenKind::Asterisk => Ok(hir::Expression::Mul(Box::new(lhs), Box::new(rhs))),
                TokenKind::Slash => Ok(hir::Expression::Div(Box::new(lhs), Box::new(rhs))),
                TokenKind::Equals => Ok(hir::Expression::Equals(Box::new(lhs), Box::new(rhs))),
                _ => unreachable! {},
            }
        }
        ast::Expression::If(cond, ontrue, onfalse) => {
            let cond = cond
                .map(|x| visit_expression(x, symtab))
                .map_err(|e, _| e)?;
            let ontrue = ontrue.map(|x| visit_block(x, symtab)).map_err(|e, _| e)?;
            let onfalse = onfalse.map(|x| visit_block(x, symtab)).map_err(|e, _| e)?;

            Ok(hir::Expression::If(
                Box::new(cond),
                Box::new(ontrue),
                Box::new(onfalse),
            ))
        }
        ast::Expression::Block(block) => Ok(hir::Expression::Block(Box::new(visit_block(
            *block, symtab,
        )?))),
        ast::Expression::Identifier(path) => {
            if symtab.has_path(&path.inner) {
                Ok(hir::Expression::Identifier(path.map(visit_path)))
            } else {
                Err(Error::UndefinedPath(path))
            }
        }
    }
}

pub fn visit_block(b: ast::Block, symtab: &mut SymbolTable) -> Result<hir::Block> {
    symtab.new_scope();
    let mut statements = vec![];
    for statement in b.statements {
        statements.push(visit_statement(statement, symtab)?)
    }

    let result = b
        .result
        .map(|e| visit_expression(e, symtab))
        .map_err(|e, _| e)?;

    symtab.close_scope();

    Ok(hir::Block { statements, result })
}

pub fn visit_identifier(id: ast::Identifier) -> hir::Identifier {
    hir::Identifier::Named(id.0)
}
pub fn visit_path(path: ast::Path) -> hir::Path {
    let result = path
        .0
        .iter()
        .cloned()
        .map(|p| p.map(visit_identifier))
        .collect();
    hir::Path(result)
}

pub fn visit_register(
    reg: Loc<ast::Register>,
    symtab: &mut SymbolTable,
) -> Result<Loc<hir::Register>> {
    let (reg, loc) = reg.split();

    symtab.add_ident(&reg.name);
    let name = reg.name.map(visit_identifier);

    if !symtab.has_path(&reg.clock.inner) {
        return Err(Error::UndefinedPath(reg.clock));
    }
    let clock = reg.clock.map(visit_path);

    let reset = if let Some((trig, value)) = reg.reset {
        Some((
            trig.map(|e| visit_expression(e, symtab))
                .map_err(|e, _| e)?,
            value
                .map(|e| visit_expression(e, symtab))
                .map_err(|e, _| e)?,
        ))
    } else {
        None
    };

    let value = reg
        .value
        .map(|e| visit_expression(e, symtab))
        .map_err(|e, _| e)?;

    let value_type = if let Some(value_type) = reg.value_type {
        Some(
            value_type
                .map(Type::convert_from_ast)
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
    use crate::testutil::{ast_ident, ast_path, hir_ident};

    use pretty_assertions::assert_eq;

    #[test]
    fn entity_visits_work() {
        let input = ast::Entity {
            name: ast::Identifier("test".to_string()).nowhere(),
            inputs: vec![(ast_ident("a"), ast::Type::UnitType.nowhere())],
            output_type: ast::Type::UnitType.nowhere(),
            block: ast::Block {
                statements: vec![ast::Statement::Binding(
                    ast_ident("var"),
                    Some(ast::Type::UnitType.nowhere()),
                    ast::Expression::IntLiteral(0).nowhere(),
                )
                .nowhere()],
                result: ast::Expression::IntLiteral(0).nowhere(),
            }
            .nowhere(),
        };

        let expected = hir::Entity {
            name: hir_ident("test"),
            inputs: vec![
                ((
                    hir::Identifier::Named("a".to_string()).nowhere(),
                    Type::Unit.nowhere(),
                )),
            ],
            output_type: Type::Unit.nowhere(),
            block: hir::Block {
                statements: vec![hir::Statement::Binding(
                    hir_ident("var"),
                    Some(Type::Unit.nowhere()),
                    hir::Expression::IntLiteral(0).nowhere(),
                )
                .nowhere()],
                result: hir::Expression::IntLiteral(0).nowhere(),
            }
            .nowhere(),
        };

        let mut symtab = SymbolTable::new();

        let result = visit_entity(input, &mut symtab);

        assert_eq!(result, Ok(expected));

        // The entity symbol should be defined
        assert!(symtab.has_path(&ast_path("test").inner));
        // But the local variables should not
        assert!(!symtab.has_path(&ast_path("a").inner));
        assert!(!symtab.has_path(&ast_path("var").inner));
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

        let input = ast::Statement::Binding(
            ast_ident("a"),
            Some(ast::Type::UnitType.nowhere()),
            ast::Expression::IntLiteral(0).nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Binding(
            hir_ident("a"),
            Some(Type::Unit.nowhere()),
            hir::Expression::IntLiteral(0).nowhere(),
        )
        .nowhere();

        assert_eq!(visit_statement(input, &mut symtab), Ok(expected));
        assert_eq!(symtab.has_path(&ast_path("a").inner), true);
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
                value: hir::Expression::IntLiteral(0).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let mut symtab = SymbolTable::new();
        symtab.add_ident(&ast_ident("clk"));
        assert_eq!(visit_statement(input, &mut symtab), Ok(expected));
        assert_eq!(symtab.has_path(&ast_path("regname").inner), true);
    }
}

#[cfg(test)]
mod expression_visiting {
    use super::*;

    use crate::location_info::WithLocation;
    use crate::testutil::{ast_ident, ast_path, hir_ident, hir_path};

    #[test]
    fn int_literals_work() {
        let mut symtab = SymbolTable::new();
        let input = ast::Expression::IntLiteral(123);
        let expected = hir::Expression::IntLiteral(123);

        assert_eq!(visit_expression(input, &mut symtab), Ok(expected));
    }

    macro_rules! binop_test {
        ($test_name:ident, $token:ident, $kind:ident) => {
            #[test]
            fn $test_name() {
                let mut symtab = SymbolTable::new();
                let input = ast::Expression::BinaryOperator(
                    Box::new(ast::Expression::IntLiteral(123).nowhere()),
                    crate::lexer::TokenKind::$token,
                    Box::new(ast::Expression::IntLiteral(456).nowhere()),
                );
                let expected = hir::Expression::$kind(
                    Box::new(hir::Expression::IntLiteral(123).nowhere()),
                    Box::new(hir::Expression::IntLiteral(456).nowhere()),
                );

                assert_eq!(visit_expression(input, &mut symtab), Ok(expected));
            }
        };
    }

    binop_test!(additions, Plus, Add);
    binop_test!(subtractions, Minus, Sub);
    binop_test!(multiplication, Asterisk, Mul);
    binop_test!(division, Slash, Div);
    binop_test!(equals, Equals, Equals);

    #[test]
    fn identifiers_work() {
        let mut symtab = SymbolTable::new();
        symtab.add_ident(&ast_ident("test"));
        let input = ast::Expression::Identifier(ast_path("test"));
        let expected = hir::Expression::Identifier(hir_path("test"));

        assert_eq!(visit_expression(input, &mut symtab), Ok(expected));
    }

    #[test]
    fn identifiers_cause_error_if_undefined() {
        let mut symtab = SymbolTable::new();
        let input = ast::Expression::Identifier(ast_path("test"));

        assert_eq!(
            visit_expression(input, &mut symtab),
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
        let expected = hir::Expression::Block(Box::new(hir::Block {
            statements: vec![hir::Statement::Binding(
                hir::Identifier::Named("a".to_string()).nowhere(),
                None,
                hir::Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            result: hir::Expression::IntLiteral(0).nowhere(),
        }));

        let mut symtab = SymbolTable::new();
        assert_eq!(visit_expression(input, &mut symtab), Ok(expected));
        assert!(!symtab.has_path(&ast_path("a").inner));
    }

    #[test]
    fn if_expressions_work() {
        let input = ast::Expression::If(
            Box::new(ast::Expression::IntLiteral(0).nowhere()),
            Box::new(
                ast::Block {
                    statements: vec![],
                    result: ast::Expression::IntLiteral(1).nowhere(),
                }
                .nowhere(),
            ),
            Box::new(
                ast::Block {
                    statements: vec![],
                    result: ast::Expression::IntLiteral(2).nowhere(),
                }
                .nowhere(),
            ),
        );
        let expected = hir::Expression::If(
            Box::new(hir::Expression::IntLiteral(0).nowhere()),
            Box::new(
                hir::Block {
                    statements: vec![],
                    result: hir::Expression::IntLiteral(1).nowhere(),
                }
                .nowhere(),
            ),
            Box::new(
                hir::Block {
                    statements: vec![],
                    result: hir::Expression::IntLiteral(2).nowhere(),
                }
                .nowhere(),
            ),
        );

        let mut symtab = SymbolTable::new();
        assert_eq!(visit_expression(input, &mut symtab), Ok(expected));
    }
}

#[cfg(test)]
mod register_visiting {
    use super::*;

    use crate::location_info::WithLocation;
    use crate::testutil::{ast_ident, ast_path, hir_ident, hir_path};

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
                hir::Expression::Identifier(hir_path("rst")).nowhere(),
                hir::Expression::IntLiteral(0).nowhere(),
            )),
            value: hir::Expression::IntLiteral(1).nowhere(),
            value_type: Some(Type::Unit.nowhere()),
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        symtab.add_ident(&ast_ident("clk"));
        symtab.add_ident(&ast_ident("rst"));
        assert_eq!(visit_register(input, &mut symtab), Ok(expected));
    }
}
