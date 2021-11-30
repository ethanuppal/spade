use crate::{
    enum_util,
    verilog::{self, assign, logic, size_spec},
    ConstantValue, Entity, Operator, Statement, ValueName,
};
use nesty::{code, Code};

impl ValueName {
    fn var_name(&self) -> String {
        match self {
            ValueName::Named(id, name) => {
                format!("{}_n{}", name, id)
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
            let declaration = logic(&name, binding.ty.size());

            let ops = &binding
                .operands
                .iter()
                .map(ValueName::var_name)
                .collect::<Vec<_>>();

            macro_rules! binop {
                ($verilog:expr) => {{
                    assert!(
                        binding.operands.len() == 2,
                        "expected 2 operands to binary operator"
                    );
                    if $verilog == ">" || $verilog == "<" {
                        format!("$signed({}) {} $signed({})", ops[0], $verilog, ops[1])
                    } else {
                        format!("{} {} {}", ops[0], $verilog, ops[1])
                    }
                }};
            }

            macro_rules! unop {
                ($verilog:expr) => {{
                    assert!(
                        binding.operands.len() == 1,
                        "expected 1 operands to binary operator"
                    );
                    format!("{}{}", $verilog, ops[0])
                }};
            }

            let expression = match &binding.operator {
                Operator::Add => binop!("+"),
                Operator::Sub => binop!("-"),
                Operator::Mul => binop!("*"),
                Operator::Eq => binop!("=="),
                Operator::Gt => binop!(">"),
                Operator::Lt => binop!("<"),
                Operator::Ge => binop!(">="),
                Operator::Le => binop!("<="),
                Operator::LeftShift => binop!("<<"),
                Operator::RightShift => binop!(">>"),
                Operator::LogicalAnd => binop!("&&"),
                Operator::LogicalOr => binop!("||"),
                Operator::LogicalNot => {
                    assert!(ops.len() == 1, "Expected exactly 1 operand to not operator");
                    format!("!{}", ops[0])
                }
                Operator::BitwiseAnd => binop!("&"),
                Operator::BitwiseOr => binop!("|"),
                Operator::Xor => binop!("^"),
                Operator::USub => unop!("-"),
                Operator::Not => unop!("!"),
                Operator::Match => {
                    assert!(
                        ops.len() % 2 == 0,
                        "Match statements must have an even number of operands"
                    );

                    let num_branches = ops.len() / 2;

                    let mut conditions = vec![];
                    let mut cases = vec![];
                    for i in 0..num_branches {
                        let cond = &ops[i * 2];
                        let result = &ops[i * 2 + 1];

                        conditions.push(cond.clone());

                        let zeros = (0..i).map(|_| '0').collect::<String>();
                        let unknowns = (0..(num_branches - i - 1)).map(|_| '?').collect::<String>();
                        cases.push(format!(
                            "{}'b{}1{}: {} = {};",
                            num_branches, zeros, unknowns, name, result
                        ))
                    }

                    code! (
                        [0] "always_comb begin";
                        [1]     format!("priority casez ({{{}}})", conditions.join(", "));
                        [2]         cases;
                        [1]     "endcase";
                        [0] "end";
                    )
                    .to_string()
                }
                Operator::Select => {
                    assert!(
                        binding.operands.len() == 3,
                        "expected 3 operands to Select operator"
                    );
                    format!("{} ? {} : {}", ops[0], ops[1], ops[2])
                }
                Operator::IndexTuple(idx, ref types) => {
                    // Compute the start index of the element we're looking for
                    let mut start_bit = 0;
                    for i in 0..*idx {
                        start_bit += types[i as usize].size();
                    }

                    let target_width = types[*idx as usize].size();
                    let end_bit = start_bit + target_width;

                    let total_width: u64 = types.iter().map(crate::types::Type::size).sum();

                    // Check if this is a single bit, if so, index using just it
                    let index = if target_width == 1 {
                        format!("{}", total_width - start_bit - 1)
                    } else {
                        format!("{}:{}", total_width - start_bit - 1, total_width - end_bit)
                    };

                    format!("{}[{}]", ops[0], index)
                }
                Operator::ConstructEnum {
                    variant,
                    variant_count,
                } => {
                    let tag_size = enum_util::tag_size(*variant_count);

                    // Compute the amount of undefined bits to put at the end of the literal.
                    // First compute the size of this variant
                    let variant_member_size = match &binding.ty {
                        crate::types::Type::Enum(options) => {
                            options[*variant].iter().map(|t| t.size()).sum::<u64>()
                        }
                        _ => panic!("Attempted enum construction of non-enum"),
                    };

                    let padding_size =
                        binding.ty.size() as usize - tag_size - variant_member_size as usize;

                    let padding_text = if padding_size != 0 {
                        format!(", {}'bX", padding_size)
                    } else {
                        String::new()
                    };

                    let ops_text = if ops.is_empty() {
                        String::new()
                    } else {
                        format!(", {}", ops.join(", "))
                    };

                    format!("{{{}'d{}{}{}}}", tag_size, variant, ops_text, padding_text)
                }
                Operator::IsEnumVariant { variant, enum_type } => {
                    let tag_size = enum_util::tag_size(enum_type.assume_enum().len());
                    let total_size = enum_type.size();

                    let tag_end = total_size - 1;
                    let tag_start = total_size - tag_size as u64;

                    if tag_end == tag_start {
                        format!("{}[{}] == {}'d{}", ops[0], tag_end, tag_size, variant)
                    } else {
                        format!(
                            "{}[{}:{}] == {}'d{}",
                            ops[0], tag_end, tag_start, tag_size, variant
                        )
                    }
                }
                Operator::EnumMember {
                    variant,
                    member_index,
                    enum_type,
                } => {
                    let variant_list = enum_type.assume_enum();
                    let tag_size = enum_util::tag_size(variant_list.len());
                    let full_size = enum_type.size();

                    let member_start = (tag_size as u64)
                        + variant_list[*variant][0..*member_index]
                            .iter()
                            .map(|t| t.size() as u64)
                            .sum::<u64>();

                    let member_end = member_start + variant_list[*variant][*member_index].size();

                    format!(
                        "{}[{}:{}]",
                        ops[0],
                        full_size - member_start - 1,
                        full_size - member_end
                    )
                }
                Operator::ConstructTuple => {
                    // To make index calculations easier, we will store tuples in "inverse order".
                    // i.e. the left-most element is stored to the right in the bit vector.
                    // TODO: is this comment even correct?
                    format!("{{{}}}", ops.join(", "))
                }
                Operator::Instance(_) => {
                    format!("") // NOTE: dummy. Set in the next match statement
                }
                Operator::Alias => {
                    format!("{}", ops[0])
                }
            };

            // Unless this is a special operator, we just use assign value = expression
            let assignment = match &binding.operator {
                Operator::Instance(module_name) => {
                    // Input args
                    let mut args = ops.join(", ");
                    // Output arg
                    args += ", ";
                    args += &name;

                    let instance_name = format!("{}_{}", module_name, name);

                    format!("{} {}({});", module_name, instance_name, args)
                }
                Operator::Match => format!("{}", expression),
                _ => format!("assign {} = {};", name, expression),
            };

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
            let declaration = logic(&name, ty.size());

            let expression = match value {
                ConstantValue::Int(val) => format!("{}", val),
                ConstantValue::Bool(val) => format!("{}", if *val { 1 } else { 0 }),
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
                [0] &logic(&value_name.var_name(), size);
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
            panic!("Code mismatch")
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
            logic _e_0;
            assign _e_0 = _e_1 + _e_2;"#
        );

        assert_same_code!(&statement_code(&binding).to_string(), expected);
    }

    #[test]
    fn binding_code_works() {
        let binding = statement!(e(0); Type::Int(5); Add; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[4:0] _e_0;
            assign _e_0 = _e_1 + _e_2;"#
        );

        assert_same_code!(&statement_code(&binding).to_string(), expected);
    }

    #[test]
    fn registers_without_reset_work() {
        let reg = statement!(reg n(0, "r"); Type::Int(7); clock (e(0)); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] r_n0;
                always @(posedge _e_0) begin
                    r_n0 <= _e_1;
                end"#
        );

        assert_same_code!(&statement_code(&reg).to_string(), expected);
    }

    #[test]
    fn registers_with_reset_work() {
        let reg = statement!(reg n(0, "r"); Type::Int(7); clock (e(0)); reset (e(2), e(3)); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] r_n0;
                always @(posedge _e_0, posedge _e_2) begin
                    if (_e_2) begin
                        r_n0 <= _e_3;
                    end
                    else begin
                        r_n0 <= _e_1;
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
                logic[5:0] op_n0;
                assign op_n0 = _i_op;
                logic[5:0] _e_0;
                assign _e_0 = op_n0 + _e_1;
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
            logic[9:0] _e_0;
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

    use indoc::{formatdoc, indoc};

    macro_rules! binop_test {
        ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
            #[test]
            fn $name() {
                let stmt = statement!(e(0); $ty; $op; e(1), e(2));

                let expected = formatdoc!(
                    r#"
                    logic{} _e_0;
                    assign _e_0 = _e_1 {} _e_2;"#, $verilog_ty, $verilog_op
                );

                assert_same_code!(&statement_code(&stmt).to_string(), &expected)
            }
        }
    }

    macro_rules! signed_binop_test {
        ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
            #[test]
            fn $name() {
                let stmt = statement!(e(0); $ty; $op; e(1), e(2));

                let expected = formatdoc!(
                    r#"
                    logic{} _e_0;
                    assign _e_0 = $signed(_e_1) {} $signed(_e_2);"#, $verilog_ty, $verilog_op
                );

                assert_same_code!(&statement_code(&stmt).to_string(), &expected)
            }
        }
    }

    macro_rules! unop_test {
        ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
            #[test]
            fn $name() {
                let stmt = statement!(e(0); $ty; $op; e(1));

                let expected = formatdoc!(
                    r#"
                    logic{} _e_0;
                    assign _e_0 = {}_e_1;"#, $verilog_ty, $verilog_op
                );

                assert_same_code!(&statement_code(&stmt).to_string(), &expected)
            }
        }
    }

    binop_test!(binop_add_works, Type::Int(2), "[1:0]", Add, "+");
    binop_test!(binop_sub_works, Type::Int(2), "[1:0]", Sub, "-");
    binop_test!(binop_mul_works, Type::Int(2), "[1:0]", Mul, "*");
    binop_test!(
        binop_left_shift_works,
        Type::Int(2),
        "[1:0]",
        LeftShift,
        "<<"
    );
    binop_test!(
        binop_right_shift_works,
        Type::Int(2),
        "[1:0]",
        RightShift,
        ">>"
    );
    binop_test!(binop_eq_works, Type::Bool, "", Eq, "==");
    binop_test!(binop_ge_works, Type::Bool, "", Ge, ">=");
    binop_test!(binop_le_works, Type::Bool, "", Le, "<=");
    signed_binop_test!(binop_gt_works, Type::Bool, "", Gt, ">");
    signed_binop_test!(binop_lt_works, Type::Bool, "", Lt, "<");
    binop_test!(binop_logical_and_works, Type::Bool, "", LogicalAnd, "&&");
    binop_test!(binop_logical_or_works, Type::Bool, "", LogicalOr, "||");
    binop_test!(xor_works, Type::Bool, "", Xor, "^");
    unop_test!(not_works, Type::Bool, "", Not, "!");
    unop_test!(usub_works, Type::Int(2), "[1:0]", USub, "-");

    #[test]
    fn select_operator_works() {
        let stmt = statement!(e(0); Type::Int(2); Select; e(1), e(2), e(3));

        let expected = indoc!(
            r#"
            logic[1:0] _e_0;
            assign _e_0 = _e_1 ? _e_2 : _e_3;"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn not_operator_works() {
        let stmt = statement!(e(0); Type::Bool; LogicalNot; e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = !_e_1;"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn match_operator_works() {
        let stmt = statement!(e(0); Type::Int(2); Match; e(1), e(2), e(3), e(4));

        let expected = indoc!(
            r#"
            logic[1:0] _e_0;
            always_comb begin
                priority casez ({_e_1, _e_3})
                    2'b1?: _e_0 = _e_2;
                    2'b01: _e_0 = _e_4;
                endcase
            end"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn boolean_constants_are_1_and_0() {
        let stmt = statement!(const 0; Type::Bool; ConstantValue::Bool(true));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = 1;"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn tuple_assembly_operator_works() {
        let ty = Type::Tuple(vec![Type::Int(6), Type::Int(3)]);
        let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[8:0] _e_0;
            assign _e_0 = {_e_1, _e_2};"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn enum_construction_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::Int(10), Type::Int(5)]]);
        let stmt = statement!(e(0); ty; ConstructEnum({variant: 2, variant_count: 3}); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[16:0] _e_0;
            assign _e_0 = {2'd2, _e_1, _e_2};"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn is_enum_variant_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::Int(10), Type::Int(5)]]);
        let stmt = statement!(e(0); Type::Bool; IsEnumVariant({variant: 2, enum_type: ty}); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[16:15] == 2'd2;"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn is_enum_variant_operator_works_for_1_wide_tags() {
        let ty = Type::Enum(vec![vec![], vec![Type::Int(10), Type::Int(5)]]);
        let stmt = statement!(e(0); Type::Bool; IsEnumVariant({variant: 1, enum_type: ty}); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[15] == 1'd1;"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn enum_member_access_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::Int(10), Type::Int(5)]]);
        let stmt = statement!(e(0); Type::Int(5); EnumMember({variant: 2, member_index: 1, enum_type: ty}); e(1));

        let expected = indoc!(
            r#"
            logic[4:0] _e_0;
            assign _e_0 = _e_1[4:0];"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn enum_construction_inserts_padding_undef_where_needed() {
        let ty = Type::Enum(vec![
            vec![],
            vec![Type::Int(5)],
            vec![Type::Int(10), Type::Int(5)],
        ]);
        let stmt = statement!(e(0); ty; ConstructEnum({variant: 1, variant_count: 3}); e(1));

        let expected = indoc!(
            r#"
            logic[16:0] _e_0;
            assign _e_0 = {2'd1, _e_1, 10'bX};"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn tuple_indexing_works_for_first_value() {
        let ty = vec![Type::Int(6), Type::Int(3)];
        let stmt = statement!(e(0); Type::Int(6); IndexTuple((0, ty)); e(1));

        let expected = indoc!(
            r#"
            logic[5:0] _e_0;
            assign _e_0 = _e_1[8:3];"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }
    #[test]
    fn tuple_indexing_works() {
        let ty = vec![Type::Int(6), Type::Int(3)];
        let stmt = statement!(e(0); Type::Int(6); IndexTuple((1, ty)); e(1));

        let expected = indoc!(
            r#"
            logic[5:0] _e_0;
            assign _e_0 = _e_1[2:0];"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn tuple_indexing_works_for_bools() {
        let ty = vec![Type::Bool, Type::Int(3)];
        let stmt = statement!(e(0); Type::Bool; IndexTuple((0, ty)); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[3];"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }

    #[test]
    fn entity_instanciation_works() {
        let stmt = statement!(e(0); Type::Bool; Instance(("test".to_string())); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            test test__e_0(_e_1, _e_2, _e_0);"#
        );

        assert_same_code!(&statement_code(&stmt).to_string(), expected);
    }
}
