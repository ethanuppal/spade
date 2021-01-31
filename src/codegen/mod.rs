use indoc::formatdoc;

use crate::{fixed_types::{t_bool, t_int}, hir::{self, Entity, ExprKind, Expression, Path}, typeinference::{
        equation::{ConcreteType, KnownType, TypedExpression},
        TypeState,
    }};

mod util;
mod verilog;

use self::{
    util::Code,
    verilog::{assign, size_spec, wire},
};

use crate::code;

fn size_of_type(t: ConcreteType) -> u128 {
    match t.base {
        _t if _t == t_int() => match t.params.as_slice() {
            [ConcreteType {
                base: KnownType::Integer(size),
                ..
            }] => *size,
            other => panic!("Expected integer to have size, got {:?}", other),
        },
        _t if _t == t_bool() => {
            assert!(t.params.is_empty(), "Bool type got generics");

            1
        }
        KnownType::Integer(_) => {
            panic!("A type level integer has no size")
        }
        KnownType::Unit => 0,
        other => panic!("{:?} has no size right now", other),
    }
}

impl Expression {
    /// If the verilog code for this expression is just an alias for another variable
    /// that is returned here. This allows us to skip generating wires that we don't
    /// really need
    pub fn alias(&self) -> Option<String> {
        match &self.kind {
            ExprKind::Identifier(ident) => Some(ident.inner.mangle()),
            ExprKind::IntLiteral(_) => todo!(),
            ExprKind::BoolLiteral(_) => todo!(),
            ExprKind::FnCall(_, _) => None,
            ExprKind::Block(block) => Some(block.result.inner.variable()),
            ExprKind::If(_, _, _) => None,
        }
    }
    pub fn variable(&self) -> String {
        // If this expressions should not use the standard __expr__{} variable,
        // that is specified here

        self.alias()
            .unwrap_or_else(|| format!("__expr__{}", self.id))
    }

    pub fn code(&self, types: &TypeState) -> Code {
        let mut code = Code::new();

        // Define the wire if it is needed
        if self.alias().is_none() {
            code.join(&wire(&self.variable(), size_of_type(types.expr_type(self))))
        }

        match &self.kind {
            ExprKind::Identifier(_) => {
                // Empty. The identifier will be defined elsewhere
            }
            ExprKind::IntLiteral(_) => todo!("codegen for int literals"),
            ExprKind::BoolLiteral(_) => todo!("codegen for bool literals"),
            ExprKind::FnCall(name, params) => {
                if name.inner == hir::Path::from_strs(&["intrinsics", "add"]) {
                    if let [lhs, rhs] = params.as_slice() {
                        code.join(&lhs.inner.code(types));
                        code.join(&rhs.inner.code(types));

                        let this_code = formatdoc! {r#"
                            assign {} = {} + {};"#,
                            self.variable(),
                            lhs.inner.variable(),
                            rhs.inner.variable(),
                        };
                        code.join(&this_code)
                    }
                    else {
                        panic!("intrinsics::add called with more than 2 arguments")
                    }
                }
                else {
                    panic!("Unrecognised function {}", name.inner)
                }
            }
            ExprKind::Block(block) => {
                if !block.statements.is_empty() {
                    todo!("Blocks with statements are unimplemented");
                }
                code.join(&block.result.inner.code(types))
                // Empty. The block result will always be the last expression
            }
            ExprKind::If(cond, on_true, on_false) => {
                // TODO: Add a code struct that handles all this bullshit
                code.join(&cond.inner.code(types));
                code.join(&on_true.inner.code(types));
                code.join(&on_false.inner.code(types));

                let self_var = self.variable();
                let this_code = formatdoc! {r#"
                    always @* begin
                        if ({}) begin
                            {} <= {};
                        end
                        else begin
                            {} <= {};
                        end
                    end"#,
                    cond.inner.variable(),
                    self_var,
                    on_true.inner.variable(),
                    self_var,
                    on_false.inner.variable()
                };
                code.join(&this_code)
            }
        }
        code
    }
}

pub fn generate_entity<'a>(entity: &Entity, types: &TypeState) -> Code {
    let inputs = entity.head.inputs.iter().map(|(name, _)| {
        let t = types.type_of_name(&Path(vec![name.inner.clone()]));
        format!("input{} {},", size_spec(size_of_type(t)), name.inner)
    });

    let output_t = types.expr_type(&entity.body);
    let output_definition = format!("output{} __output", size_spec(size_of_type(output_t)));

    let output_assignment = assign("__output", &entity.body.inner.variable());

    code! {
        [0] &format!("module {} (", entity.name.inner);
                [2] &inputs.collect::<Vec<_>>();
                [2] &output_definition;
            [1] &")";
        [0] &"begin";
            [1] &entity.body.inner.code(types);
            [1] &output_assignment;
        [0] &"end"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_same_code, testutil::parse_typecheck_entity};
    use indoc::indoc;

    #[test]
    fn entity_defintions_are_correct() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
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
            assign __output = _m_a;
        end"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn if_expressions_have_correct_codegen() {
        let code = r#"
        entity name(c: bool, a: int<16>, b: int<16>) -> int<16> {
            if c
                a
            else
                b
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
            wire[15:0] __expr__3;
            always @* begin
                if (_m_c) begin
                    __expr__3 <= _m_a;
                end
                else begin
                    __expr__3 <= _m_b;
                end
            end
            assign __output = __expr__3;
        end"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn an_adder_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a + b
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
            wire[15:0] __expr__2;
            assign __expr__2 = _m_a + _m_b;
            assign __output = __expr__2;
        end"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }
}
