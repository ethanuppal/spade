use indoc::formatdoc;

use crate::{
    hir::{Entity, Expression},
    typeinference::TypeState,
};

mod util;

use util::{verilog_assign, Indentable};

use self::util::verilog_wire;

fn expr_variable(id: u64) -> String {
    format!("__expr__{}", id)
}

pub fn generate_expression<'a>(expr: &Expression, types: &TypeState) -> String {
    let result_var = format!("__expr__{}", expr.id);
    let mut result = vec![verilog_wire(&result_var, types.expr_type(expr).size())];

    match &expr.kind {
        crate::hir::ExprKind::Identifier(ident) => {
            result.push(verilog_assign(&result_var, &ident.inner.mangle()));
        }
        crate::hir::ExprKind::IntLiteral(_) => todo!("codegen for int literals"),
        crate::hir::ExprKind::BoolLiteral(_) => todo!("codegen for bool literals"),
        crate::hir::ExprKind::FnCall(_, _) => todo!("codegen for function calls is unimplemented"),
        crate::hir::ExprKind::Block(block) => {
            if !block.statements.is_empty() {
                todo!("Blocks with statements are unimplemented");
            }
            result.push(generate_expression(&block.result.inner, types));
            let input_var = expr_variable(block.result.inner.id);
            result.push(verilog_assign(&result_var, &input_var))
        }
        crate::hir::ExprKind::If(_, _, _) => todo!("codegen for ifs is unimplemented"),
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

    let output_assignment = verilog_assign("__output", &expr_variable(entity.body.inner.id));
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
            wire[15:0] __expr__0;
            assign __expr__0 = _m_a;
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
