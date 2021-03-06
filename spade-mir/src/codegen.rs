use crate::{
    code,
    util::Code,
    verilog::{self, assign, size_spec, wire},
    ConstantValue, Entity, Operator, Statement, ValueName,
};

impl ValueName {
    fn var_name(&self) -> String {
        match self {
            ValueName::Named(id, name) => {
                format!("_n{}_{}", id, name)
            }
            ValueName::Expr(id) => {
                format!("_e_{}", id)
            }
        }
    }
}

fn statement_code(statement: &Statement) -> Code {
    match statement {
        Statement::Binding(binding) => {
            let name = binding.name.var_name();
            let declaration = wire(&name, binding.ty.size());

            let ops = &binding
                .operands
                .iter()
                .map(ValueName::var_name)
                .collect::<Vec<_>>();
            let expression = match binding.operator {
                Operator::Add => {
                    assert!(
                        binding.operands.len() == 2,
                        "expected 2 operands to Add operator"
                    );
                    format!("{} + {}", ops[0], ops[1])
                }
                Operator::Select => {
                    assert!(
                        binding.operands.len() == 3,
                        "expected 3 operands to Select operator"
                    );
                    format!("{} ? {} : {}", ops[0], ops[1], ops[2])
                }
                Operator::ConstructTuple => {
                    format!("{{{}}}", ops.join(", "))
                }
            };

            let assignment = format!("assign {} = {};", name, expression);

            code! {
                [0] &declaration;
                [0] &assignment
            }
        }
        Statement::Register(reg) => {
            if let Some((rst_trig, rst_val)) = &reg.reset {
                let name = reg.name.var_name();
                let declaration = verilog::reg(&name, reg.ty.size());

                code! {
                    [0] &declaration;
                    [0] &format!("always @(posedge {}, posedge {}) begin", reg.clock.var_name(), rst_trig.var_name());
                    [1]     &format!("if ({}) begin", rst_trig.var_name());
                    [2]         &format!("{} <= {};", name, rst_val.var_name());
                    [1]     &"end";
                    [1]     &"else begin";
                    [2]         &format!("{} <= {};", name, reg.value.var_name());
                    [1]     &"end";
                    [0] &"end"
                }
            } else {
                let name = reg.name.var_name();
                let declaration = verilog::reg(&name, reg.ty.size());

                code! {
                    [0] &declaration;
                    [0] &format!("always @(posedge {}) begin", reg.clock.var_name());
                    [1]     &format!("{} <= {};", name, reg.value.var_name());
                    [0] &"end"
                }
            }
        }
        Statement::Constant(id, ty, value) => {
            let name = ValueName::Expr(*id).var_name();
            let declaration = wire(&name, ty.size());

            let expression = match value {
                ConstantValue::Int(val) => format!("{}", val),
                ConstantValue::Bool(val) => format!("{}", val),
            };

            let assignment = format!("assign {} = {};", name, expression);

            code! {
                [0] &declaration;
                [0] &assignment
            }
        }
    }
}

pub fn entity_code(entity: &Entity) -> Code {
    // Inputs are named _i_{name} and then translated to the name_id name for later use
    let inputs = entity.inputs.iter().map(|(name, value_name, ty)| {
        let input_name = format!("{}", name);
        let size = ty.size();
        (
            format!("input{} {},", size_spec(size), input_name),
            code! {
                [0] &wire(&value_name.var_name(), size);
                [0] &assign(&value_name.var_name(), &name)
            },
        )
    });

    let (inputs, input_assignments): (Vec<_>, Vec<_>) = inputs.unzip();

    let output_definition = format!("output{} __output", size_spec(entity.output_type.size()));

    let output_assignment = assign("__output", &entity.output.var_name());

    let mut body = Code::new();

    for stmt in &entity.statements {
        body.join(&statement_code(&stmt))
    }

    code! {
        [0] &format!("module {} (", entity.name);
                [2] &inputs;
                [2] &output_definition;
            [1] &");";
            [1] &input_assignments;
            [1] &body;
            [1] &output_assignment;
        [0] &"endmodule"
    }
}

#[macro_export]
macro_rules! assert_same_code {
    ($got:expr, $expected:expr) => {
        if $got != $expected {
            println!("{}:\n{}", "got".red(), $got);
            println!("{}", "==============================================".red());
            println!("{}:\n{}", "expected".green(), $expected);
            println!(
                "{}",
                "==============================================".green()
            );
            println!("{}", prettydiff::diff_chars($got, $expected));
            println!(
                "{}",
                "==============================================".yellow()
            );
            panic!("Code missmatch")
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use colored::Colorize;

    use crate as spade_mir;
    use crate::{entity, statement, types::Type};

    use indoc::indoc;

    #[test]
    fn size_1_wires_have_no_size_spec() {
        let binding = statement!(e(0); Type::Bool; Add; e(1), e(2));

        let expected = indoc!(
            r#"
            wire _e_0;
            assign _e_0 = _e_1 + _e_2;"#
        );

        assert_same_code!(&statement_code(&binding).to_string(), expected);
    }

    #[test]
    fn binding_code_works() {
        let binding = statement!(e(0); Type::Int(5); Add; e(1), e(2));

        let expected = indoc!(
            r#"
            wire[4:0] _e_0;
            assign _e_0 = _e_1 + _e_2;"#
        );

        assert_same_code!(&statement_code(&binding).to_string(), expected);
    }

    #[test]
    fn registers_without_reset_work() {
        let reg = statement!(reg n(0, "r"); Type::Int(7); clock (e(0)); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] _n0_r;
                always @(posedge _e_0) begin
                    _n0_r <= _e_1;
                end"#
        );

        assert_same_code!(&statement_code(&reg).to_string(), expected);
    }

    #[test]
    fn registers_with_reset_work() {
        let reg = statement!(reg n(0, "r"); Type::Int(7); clock (e(0)); reset (e(2), e(3)); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] _n0_r;
                always @(posedge _e_0, posedge _e_2) begin
                    if (_e_2) begin
                        _n0_r <= _e_3;
                    end
                    else begin
                        _n0_r <= _e_1;
                    end
                end"#
        );

        assert_same_code!(&statement_code(&reg).to_string(), expected);
    }

    #[test]
    fn entity_codegen_works() {
        let input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), e(1))
        } => e(0));

        let expected = indoc!(
            r#"
            module pong (
                    input[5:0] _i_op,
                    output[5:0] __output
                );
                wire[5:0] _n0_op;
                assign _n0_op = _i_op;
                wire[5:0] _e_0;
                assign _e_0 = _n0_op + _e_1;
                assign __output = _e_0;
            endmodule"#
        );

        assert_same_code!(&entity_code(&input).to_string(), expected);
    }

    #[test]
    fn constant_codegen_works() {
        let input = statement!(const 0; Type::Int(10); crate::ConstantValue::Int(6));

        let expected = indoc!(
            r#"
            wire[9:0] _e_0;
            assign _e_0 = 6;"#
        );

        assert_same_code!(&statement_code(&input).to_string(), expected)
    }
}

#[cfg(test)]
mod expression_tests {
    use super::*;
    use colored::Colorize;

    use crate as spade_mir;
    use crate::{statement, types::Type};

    use indoc::indoc;

    #[test]
    fn select_operator_works() {
        let stmt = statement!(e(0); Type::Int(2); Select; e(1), e(2), e(3));

        let expected = indoc!(
            r#"
            wire[1:0] _e_0;
            assign _e_0 = _e_1 ? _e_2 : _e_3;"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn tuple_assembly_operator_works() {
        let ty = Type::Tuple(vec![Type::Int(6), Type::Int(3)]);
        let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2));

        let expected = indoc!(
            r#"
            wire[8:0] _e_0;
            assign _e_0 = {_e_1, _e_2};"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }
}
