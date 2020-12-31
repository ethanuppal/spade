use indoc::formatdoc;

use crate::{
    hir::{Entity, ExprKind, Expression},
    typeinference::TypeState,
};

mod util;

use util::{verilog_assign, Indentable};

use self::util::verilog_wire;

fn expr_variable(expr: &Expression) -> String {
    if let ExprKind::Identifier(name) = &expr.kind {
        name.inner.mangle()
    } else {
        format!("__expr__{}", expr.id)
    }
}

pub fn generate_expression<'a>(expr: &Expression, types: &TypeState) -> String {
    let result_var = format!("__expr__{}", expr.id);
    // Generate a wire for the variable if it is needed
    let mut result = if let ExprKind::Identifier(_) = &expr.kind {
        vec![]
    } else {
        vec![verilog_wire(&result_var, types.expr_type(expr).size())]
    };

    match &expr.kind {
        ExprKind::Identifier(_) => {
            // Empty. The identifier will be defined elsewhere
        }
        ExprKind::IntLiteral(_) => todo!("codegen for int literals"),
        ExprKind::BoolLiteral(_) => todo!("codegen for bool literals"),
        ExprKind::FnCall(_, _) => todo!("codegen for function calls is unimplemented"),
        ExprKind::Block(block) => {
            if !block.statements.is_empty() {
                todo!("Blocks with statements are unimplemented");
            }
            let sub = generate_expression(&block.result.inner, types);
            if !sub.is_empty() {
                result.push(sub);
            }
            let input_var = expr_variable(&block.result.inner);
            result.push(verilog_assign(&result_var, &input_var))
        }
        ExprKind::If(_, _, _) => todo!("codegen for ifs is unimplemented"),
    }
    result.join("\n")
}

pub fn generate_entity<'a>(entity: &Entity, types: &TypeState) -> String {
    let inputs = entity
        .inputs
        .iter()
        .map(|(name, t)| format!("input[{}:0] {},", t.inner.size() - 1, name.inner))
        .collect::<Vec<_>>()
        .join("\n");

    let output = format!("output[{}:0] __output", entity.output_type.inner.size() - 1);

    let args = format!("{}\n{}", inputs, output);

    let output_assignment = verilog_assign("__output", &expr_variable(&entity.body.inner));
    let inner = formatdoc!(
        "{}\n{}",
        generate_expression(&entity.body.inner, types),
        output_assignment
    );

    formatdoc!(
        r#"
        module {} (
        {}
            )
        begin
        {}
        end
    "#,
        entity.name.inner,
        args.indent(2),
        inner.indent(1)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_same_code, testutil::parse_typecheck_entity};
    use indoc::indoc;

    #[test]
    fn entity_defintions_are_correct() {
        let code = r#"
        entity name(a: int[16], b: int[16]) -> int[16] {
            a
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input[15:0] a,
                input[15:0] b,
                output[15:0] __output
            )
        begin
            wire[15:0] __expr__1;
            assign __expr__1 = _m_a;
            assign __output = __expr__1;
        end
        "#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state);
        assert_same_code!(&result, expected);
    }

    #[ignore]
    #[test]
    fn if_expressions_have_correct_codegen() {
        let code = r#"
        entity name(c: bool, a: int[16], b: int[16]) -> int[16] {
            if c {
                a
            }
            else {
                b
            }
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input c,
                input[15:0] a,
                input[15:0] b,
                output[15:0] __output
            )
        begin
            wire[15:0] __expr__2;
            wire[15:0] __expr__1;
            assign __expr__1 = __expr__0;
            assign __output = __expr__1;
        end
        "#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state);
        assert_same_code!(&result, expected);
    }
}
