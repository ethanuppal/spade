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
    #[error("Undefined identifier {}", 0.0)]
    UndefinedIdentifier(Loc<ast::Identifier>),
    #[error("Type error")]
    TypeError(#[source] TypeError, Loc<()>),

    #[error("Type inference not yet supported")]
    UntypedBinding(Loc<()>),
}

pub type Result<T> = std::result::Result<T, Error>;

pub fn visit_entity(item: ast::Entity, symtab: &mut SymbolTable) -> Result<hir::Entity> {
    symtab.add_symbol(item.name.map_ref(|x| x.0.clone()));
    symtab.new_scope();

    let name = item.name.map(visit_identifier);

    let mut inputs = vec![];
    for (name, input_type) in item.inputs {
        symtab.add_symbol(name.map_ref(|x| x.0.clone()));

        let t = input_type
            .map(Type::convert_from_ast)
            .map_err(Error::TypeError)?;

        inputs.push((name.map(visit_identifier), t));
    }

    let output_type = item
        .output_type
        .map(Type::convert_from_ast)
        .map_err(Error::TypeError)?;

    let mut statements = vec![];
    for statement in item.statements {
        statements.push(visit_statement(statement, symtab)?)
    }

    let output_value = item
        .output_value
        .map(|e| visit_expression(e, symtab))
        .map_err(|e, _| e)?;

    symtab.close_scope();

    Ok(hir::Entity {
        name,
        inputs,
        statements,
        output_type,
        output_value,
    })
}

pub fn visit_statement(
    s: Loc<ast::Statement>,
    symtab: &mut SymbolTable,
) -> Result<Loc<hir::Statement>> {
    let (s, span) = s.split();
    match s {
        ast::Statement::Binding(ident, t, expr) => {
            symtab.add_symbol(ident.map_ref(|x| x.0.clone()));
            if let Some(t) = t {
                let name = ident.map(visit_identifier);
                let hir_type = t.map(Type::convert_from_ast).map_err(Error::TypeError)?;

                let expr = expr
                    .map(|e| visit_expression(e, symtab))
                    .map_err(|e, _| e)?;

                Ok(Loc::new(
                    hir::Statement::Binding(name, hir_type, expr),
                    span,
                ))
            } else {
                Err(Error::UntypedBinding(Loc::new((), span)))
            }
        }
        _ => unimplemented!(),
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
                _ => unreachable! {},
            }
        }
        ast::Expression::Identifier(id) => {
            if symtab.has_symbol(&id.inner.0) {
                Ok(hir::Expression::Identifier(id.map(visit_identifier)))
            } else {
                Err(Error::UndefinedIdentifier(id))
            }
        }
    }
}

pub fn visit_identifier(id: ast::Identifier) -> hir::Identifier {
    hir::Identifier::Named(id.0)
}

#[cfg(test)]
mod entity_visiting {
    use super::*;

    use crate::location_info::WithLocation;

    use pretty_assertions::assert_eq;

    #[test]
    fn entity_visits_work() {
        let input = ast::Entity {
            name: ast::Identifier("test".to_string()).nowhere(),
            inputs: vec![(
                ast::Identifier("a".to_string()).nowhere(),
                ast::Type::UnitType.nowhere(),
            )],
            statements: vec![ast::Statement::Binding(
                ast::Identifier("var".to_string()).nowhere(),
                Some(ast::Type::UnitType.nowhere()),
                ast::Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            output_type: ast::Type::UnitType.nowhere(),
            output_value: ast::Expression::IntLiteral(0).nowhere(),
        };

        let expected = hir::Entity {
            name: hir::Identifier::Named("test".to_string()).nowhere(),
            inputs: vec![
                ((
                    hir::Identifier::Named("a".to_string()).nowhere(),
                    Type::Unit.nowhere(),
                )),
            ],
            statements: vec![hir::Statement::Binding(
                hir::Identifier::Named("var".to_string()).nowhere(),
                Type::Unit.nowhere(),
                hir::Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            output_type: Type::Unit.nowhere(),
            output_value: hir::Expression::IntLiteral(0).nowhere(),
        };

        let mut symtab = SymbolTable::new();

        let result = visit_entity(input, &mut symtab);

        assert_eq!(result, Ok(expected));

        // The entity symbol should be defined
        assert!(symtab.has_symbol(&"test".to_string()));
        // But the local variables should not
        assert!(!symtab.has_symbol(&"a".to_string()));
        assert!(!symtab.has_symbol(&"var".to_string()));
    }
}

#[cfg(test)]
mod statement_visiting {
    use super::*;

    use crate::location_info::WithLocation;

    #[test]
    fn bindings_convert_correctly() {
        let mut symtab = SymbolTable::new();

        let input = ast::Statement::Binding(
            ast::Identifier("a".to_string()).nowhere(),
            Some(ast::Type::UnitType.nowhere()),
            ast::Expression::IntLiteral(0).nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Binding(
            hir::Identifier::Named("a".to_string()).nowhere(),
            Type::Unit.nowhere(),
            hir::Expression::IntLiteral(0).nowhere(),
        )
        .nowhere();

        assert_eq!(visit_statement(input, &mut symtab), Ok(expected));
        assert_eq!(symtab.has_symbol(&"a".to_string()), true);
    }
}

#[cfg(test)]
mod expression_visiting {
    use super::*;

    use crate::location_info::WithLocation;

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

    #[test]
    fn identifiers_work() {
        let mut symtab = SymbolTable::new();
        symtab.add_symbol(Loc::nowhere("test".to_string()));
        let input = ast::Expression::Identifier(ast::Identifier("test".to_string()).nowhere());
        let expected =
            hir::Expression::Identifier(hir::Identifier::Named("test".to_string()).nowhere());

        assert_eq!(visit_expression(input, &mut symtab), Ok(expected));
    }

    #[test]
    fn identifiers_cause_error_if_undefined() {
        let mut symtab = SymbolTable::new();
        let input = ast::Expression::Identifier(ast::Identifier("test".to_string()).nowhere());

        assert_eq!(
            visit_expression(input, &mut symtab),
            Err(Error::UndefinedIdentifier(
                ast::Identifier("test".to_string()).nowhere()
            ))
        );
    }
}
