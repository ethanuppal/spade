use crate::{
    aliasing::flatten_aliases,
    assertion_codegen::AssertedExpression,
    enum_util,
    verilog::{self, assign, logic, size_spec},
    ConstantValue, Entity, Operator, Statement, ValueName,
};
use codespan_reporting::term::termcolor;
use itertools::Itertools;
use nesty::{code, Code};
use spade_common::error_reporting::{CodeBundle, CompilationError};

impl ValueName {
    pub fn var_name(&self) -> String {
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

pub fn escape_path(path: String) -> String {
    path.replace("::", "_")
}

fn mangle_entity(module: &str) -> String {
    format!("e_{}", module)
}

fn mangle_input(input: &str) -> String {
    format!("_i_{}", input)
}

fn statement_code(statement: &Statement, source_code: &CodeBundle) -> Code {
    match statement {
        Statement::Binding(binding) => {
            let name = binding.name.var_name();

            let declaration = match &binding.ty {
                crate::types::Type::Memory { inner, length } => {
                    let inner_w = inner.size();
                    if inner_w > 1 {
                        format!("logic[{inner_w}-1:0] {name}[{length}-1:0];")
                    } else {
                        logic(&name, binding.ty.size())
                    }
                }
                _ => logic(&name, binding.ty.size()),
            };

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
                    format!("{} {} {}", ops[0], $verilog, ops[1])
                }};
            }

            macro_rules! signed_binop {
                ($verilog:expr) => {{
                    assert!(
                        binding.operands.len() == 2,
                        "expected 2 operands to binary operator"
                    );
                    format!("$signed({}) {} $signed({})", ops[0], $verilog, ops[1])
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
                Operator::Mul => signed_binop!("*"),
                Operator::Eq => binop!("=="),
                Operator::Gt => signed_binop!(">"),
                Operator::Lt => signed_binop!("<"),
                Operator::Ge => signed_binop!(">="),
                Operator::Le => signed_binop!("<="),
                Operator::LeftShift => binop!("<<"),
                Operator::RightShift => binop!(">>"),
                Operator::LogicalAnd => binop!("&&"),
                Operator::LogicalOr => binop!("||"),
                Operator::LogicalNot => {
                    assert!(ops.len() == 1, "Expected exactly 1 operand to not operator");
                    format!("!{}", ops[0])
                }
                Operator::BitwiseNot => {
                    assert!(
                        ops.len() == 1,
                        "Expected exactly 1 operand to bitwise not operator"
                    );
                    format!("~{}", ops[0])
                }
                Operator::BitwiseAnd => binop!("&"),
                Operator::BitwiseOr => binop!("|"),
                Operator::Xor => binop!("^"),
                Operator::USub => unop!("-"),
                Operator::Not => unop!("!"),
                Operator::DivPow2 => format!("$signed({}) / (1 << {})", ops[0], ops[1]),
                Operator::Truncate => {
                    format!("{}[{}:0]", ops[0], binding.ty.size() - 1)
                }
                Operator::Concat => {
                    format!("{{{}}}", ops.iter().map(|op| format!("{op}")).join(", "))
                }
                Operator::SignExtend {
                    extra_bits,
                    operand_size,
                } => match extra_bits {
                    0 => format!("{}", ops[0]),
                    1 => format!("{{{}[{}], {}}}", ops[0], operand_size - 1, ops[0]),
                    2.. => format!(
                        "#[#[ {extra_bits} #[ {op}[{last_index}] #]#], {op}#]",
                        op = ops[0],
                        last_index = operand_size - 1,
                    )
                    // For readability with the huge amount of braces that both
                    // rust and verilog want here, we'll insert them at the end
                    // like this
                    .replace("#[", "{")
                    .replace("#]", "}"),
                },
                Operator::ZeroExtend { extra_bits } => match extra_bits {
                    0 => format!("{}", ops[0]),
                    1.. => format!("{{{}'b0, {}}}", extra_bits, ops[0]),
                },
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
                Operator::ConstructArray { .. } => {
                    // NOTE: Reversing because we declare the array as logic[SIZE:0] and
                    // we want the [x*width+:width] indexing to work
                    format!(
                        "{{{}}}",
                        ops.iter().cloned().rev().collect::<Vec<_>>().join(", ")
                    )
                }
                Operator::IndexArray(member_size) => {
                    if *member_size == 1 {
                        format!("{}[{}]", ops[0], ops[1])
                    } else {
                        let end_index = format!("{} * {}", ops[1], member_size);
                        let offset = member_size;

                        // Strange indexing explained here https://stackoverflow.com/questions/18067571/indexing-vectors-and-arrays-with#18068296
                        format!("{}[{}+:{}]", ops[0], end_index, offset)
                    }
                }
                Operator::IndexMemory => {
                    format!("{}[{}]", ops[0], ops[1])
                }
                Operator::DeclClockedMemory {
                    write_ports,
                    addr_w,
                    inner_w,
                    elems: _,
                } => {
                    let full_port_width = 1 + addr_w + inner_w;
                    let update_blocks = (0..*write_ports)
                        .map(|port| {
                            let we_index = full_port_width * (port + 1) - 1;

                            let addr_start = full_port_width * port + inner_w;
                            let addr = if *addr_w == 1 {
                                format!("{}[{}]", ops[1], addr_start)
                            } else {
                                format!("{}[{}:{}]", ops[1], addr_start + addr_w - 1, addr_start)
                            };

                            let write_value_start = port * full_port_width;
                            let (write_index, write_value) = if *inner_w == 1 {
                                (
                                    format!("{}[{addr}]", name),
                                    format!("{}[{write_value_start}]", ops[1]),
                                )
                            } else {
                                (
                                    format!("{}[{addr}]", name),
                                    format!(
                                        "{}[{end}:{write_value_start}]",
                                        ops[1],
                                        end = write_value_start + inner_w - 1
                                    ),
                                )
                            };
                            let we_signal = format!("{}[{we_index}]", ops[1]);

                            code! {
                                [0] format!("if ({we_signal}) begin");
                                [1]     format!("{write_index} <= {write_value};");
                                [0] "end"
                            }
                            .to_string()
                        })
                        .join("\n");

                    code! {
                        [0] format!("always @(posedge {clk}) begin", clk = ops[0]);
                        [1]     update_blocks;
                        [0] "end";
                    }
                    .to_string()
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
                    format!("{{{}}}", ops.join(", "))
                }
                Operator::Instance(_) => {
                    // NOTE: dummy. Set in the next match statement
                    format!("")
                }
                Operator::Alias => {
                    // NOTE Dummy. Set in the next match statement
                    format!("") //format!("{}", ops[0])
                }
            };

            // Unless this is a special operator, we just use assign value = expression
            let assignment = match &binding.operator {
                Operator::Instance(module_name) => {
                    // Input args
                    let mut args = ops.join(", ");

                    if !ops.is_empty() {
                        // Output arg
                        args += ", ";
                    }
                    args += &name;

                    let module_name = escape_path(module_name.to_string());

                    let instance_name = format!("{}_{}", module_name, name);

                    format!(
                        "{} {}({});",
                        mangle_entity(&module_name),
                        instance_name,
                        args
                    )
                }
                Operator::Alias => match binding.ty {
                    crate::types::Type::Memory { .. } => {
                        format!("`define {} {}", name, ops[0])
                    }
                    _ => format!("assign {} = {};", name, ops[0]),
                },
                Operator::Match => format!("{}", expression),
                Operator::DeclClockedMemory { .. } => format!("{}", expression),
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
        Statement::Assert(val) => {
            let mut msg_buf = termcolor::Buffer::ansi();

            AssertedExpression(val.clone()).report(&mut msg_buf, source_code);

            let msg = String::from_utf8(msg_buf.as_slice().into())
                .map_err(|e| {
                    println!("Internal error {e}: Failed to generate assert message, invalid utf-8 returned by codespan");
                })
                .unwrap_or_else(|_| String::new())
                .lines()
                .map(|line| {
                    format!(r#"$display("{line}");"#)
                })
                .join("\n");

            let val_var = val.var_name();
            code! {
                [0] format!("always @({val_var}) begin");
                    // This #0 is a bit unintiutive, but it seems to prevent assertions
                    // triggering too early. For example, in the case of !(x == 1 && y == 2)
                    // if x 1 and updated to 2 in the time step as y is updated to not be 2,
                    // an assertion might still trigger without #0 if the update of x triggers
                    // the always block before x is updated. See for more details
                    // https://electronics.stackexchange.com/questions/99223/relation-between-delta-cycle-and-event-scheduling-in-verilog-simulation
                    [1] "#0";
                    [1] format!("assert ({val_var})");
                    [1] "else begin";
                        [2] msg;
                        [2] r#"$error("Assertion failed");"#;
                        [2] r#"$fatal(1);"#;
                    [1] "end";
                [0] "end";
            }
        }
    }
}

pub fn entity_code(mut entity: Entity, source_code: &CodeBundle) -> Code {
    flatten_aliases(&mut entity);

    let entity_name = mangle_entity(&escape_path(entity.name));

    let inputs: Vec<_> = entity
        .inputs
        .into_iter()
        .map(|(name, value_name, ty)| {
            let name = mangle_input(&escape_path(name));
            (name, value_name, ty)
        })
        .collect();

    let inputs = inputs.iter().map(|(name, value_name, ty)| {
        let size = ty.size();
        (
            format!("input{} {},", size_spec(size), name),
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
        body.join(&statement_code(stmt, source_code))
    }

    code! {
        [0] &format!("module {} (", entity_name);
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

        assert_same_code!(
            &statement_code(&binding, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn binding_code_works() {
        let binding = statement!(e(0); Type::Int(5); Add; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[4:0] _e_0;
            assign _e_0 = _e_1 + _e_2;"#
        );

        assert_same_code!(
            &statement_code(&binding, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&reg, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&reg, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn entity_codegen_works() {
        let input = entity!("pong"; ("op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), e(1))
        } => e(0));

        let expected = indoc!(
            r#"
            module e_pong (
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

        assert_same_code!(
            &entity_code(input.clone(), &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn constant_codegen_works() {
        let input = statement!(const 0; Type::Int(10); crate::ConstantValue::Int(6));

        let expected = indoc!(
            r#"
            logic[9:0] _e_0;
            assign _e_0 = 6;"#
        );

        assert_same_code!(
            &statement_code(&input, &CodeBundle::new("".to_string())).to_string(),
            expected
        )
    }

    #[test]
    fn pipeline_with_stage_references_codegens_correctly() {
        let input = entity!("pl"; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::Int(16); {
                (reg n(10, "x__s1"); Type::Int(16); clock(n(3, "clk")); n(0, "x_"));
                // Stage 0
                (e(0); Type::Int(16); Instance(("A".to_string())););
                (n(0, "x_"); Type::Int(16); Alias; e(0));
                // Stage 1
                (n(1, "x"); Type::Int(16); Alias; n(0, "x_"));
            } => n(1, "x")
        );

        // This test removes a lot of variables through alias resolution
        let expected = indoc!(
            r#"
            module e_pl (
                    input _i_clk,
                    output[15:0] __output
                );
                logic clk_n3;
                assign clk_n3 = _i_clk;
                reg[15:0] x__s1_n10;
                always @(posedge clk_n3) begin
                    x__s1_n10 <= x_n1;
                end
                logic[15:0] x_n1;
                e_A A_x_n1(x_n1);
                assign __output = x_n1;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(input.clone(), &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }
}

#[cfg(test)]
mod expression_tests {
    use super::*;
    use codespan::Span;
    use colored::Colorize;
    use spade_common::location_info::WithLocation;

    use crate::{self as spade_mir, value_name};
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

                assert_same_code!(&statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(), &expected)
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

                assert_same_code!(&statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(), &expected)
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

                assert_same_code!(&statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(), &expected)
            }
        }
    }

    binop_test!(binop_add_works, Type::Int(2), "[1:0]", Add, "+");
    binop_test!(binop_sub_works, Type::Int(2), "[1:0]", Sub, "-");
    signed_binop_test!(binop_mul_works, Type::Int(2), "[1:0]", Mul, "*");
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
    signed_binop_test!(binop_gt_works, Type::Bool, "", Gt, ">");
    signed_binop_test!(binop_lt_works, Type::Bool, "", Lt, "<");
    signed_binop_test!(binop_ge_works, Type::Bool, "", Ge, ">=");
    signed_binop_test!(binop_le_works, Type::Bool, "", Le, "<=");
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn not_operator_works() {
        let stmt = statement!(e(0); Type::Bool; LogicalNot; e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = !_e_1;"#
        );

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn boolean_constants_are_1_and_0() {
        let stmt = statement!(const 0; Type::Bool; ConstantValue::Bool(true));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = 1;"#
        );

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
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

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn array_literals_work() {
        let ty = Type::Array {
            inner: Box::new(Type::Int(3)),
            length: 3,
        };
        let statement = statement!(e(0); ty; ConstructArray; e(1), e(2), e(3));

        let expected = indoc!(
            r#"
            logic[8:0] _e_0;
            assign _e_0 = {_e_3, _e_2, _e_1};"#
        );

        assert_same_code!(
            &statement_code(&statement, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn array_indexing_works() {
        let statement = statement!(e(0); Type::Int(3); IndexArray((3)); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1[_e_2 * 3+:3];"#
        );

        assert_same_code!(
            &statement_code(&statement, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn array_indexing_works_for_1_bit_values() {
        let statement = statement!(e(0); Type::Bool; IndexArray((1)); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[_e_2];"#
        );

        assert_same_code!(
            &statement_code(&statement, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn entity_instanciation_works() {
        let stmt = statement!(e(0); Type::Bool; Instance(("test".to_string())); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            e_test test__e_0(_e_1, _e_2, _e_0);"#
        );

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_works() {
        let t = Type::Array {
            inner: Box::new(Type::Int(6)),
            length: 4,
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({write_ports: 2, addr_w: 4, inner_w: 6, elems: 16}); e(1), e(2));

        // Total write array length: 2 * (1 + 4 + 6)

        let expected = indoc!(
            r#"
            logic[23:0] _e_0;
            always @(posedge _e_1) begin
                if (_e_2[10]) begin
                    _e_0[_e_2[9:6]] <= _e_2[5:0];
                end
                if (_e_2[21]) begin
                    _e_0[_e_2[20:17]] <= _e_2[16:11];
                end
            end"#
        );

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_with_1_bit_address_works() {
        let t = Type::Array {
            inner: Box::new(Type::Int(6)),
            length: 4,
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({write_ports: 1, addr_w: 1, inner_w: 6, elems: 16}); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[23:0] _e_0;
            always @(posedge _e_1) begin
                if (_e_2[7]) begin
                    _e_0[_e_2[6]] <= _e_2[5:0];
                end
            end"#
        );

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_with_1_bit_data_works() {
        let t = Type::Array {
            inner: Box::new(Type::Bool),
            length: 4,
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({write_ports: 1, addr_w: 4, inner_w: 1, elems: 16}); e(1), e(2));

        // Total write array length: 2 * (1 + 4 + 6)

        let expected = indoc!(
            r#"
            logic[3:0] _e_0;
            always @(posedge _e_1) begin
                if (_e_2[5]) begin
                    _e_0[_e_2[4:1]] <= _e_2[0];
                end
            end"#
        );

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn truncate_works() {
        let stmt = statement!(e(0); Type::Int(5); Truncate; e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = _e_1[4:0];"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn sext_works_for_many_bits() {
        let stmt =
            statement!(e(0); Type::Int(5); SignExtend({extra_bits: 2, operand_size: 3}); e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = {{ 2 { _e_1[2] }}, _e_1};"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }
    #[test]
    fn sext_works_for_one_bits() {
        let stmt =
            statement!(e(0); Type::Int(4); SignExtend({extra_bits: 1, operand_size: 3}); e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0;
            assign _e_0 = {_e_1[2], _e_1};"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }
    #[test]
    fn sext_works_for_zero_bits() {
        let stmt =
            statement!(e(0); Type::Int(3); SignExtend({extra_bits: 0, operand_size: 3}); e(1));

        let expected = indoc! {
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1;"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn zext_works_for_many_bits() {
        let stmt = statement!(e(0); Type::Int(5); ZeroExtend({extra_bits: 2}); e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = {2'b0, _e_1};"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }
    #[test]
    fn zext_works_for_one_bits() {
        let stmt = statement!(e(0); Type::Int(4); ZeroExtend({extra_bits: 1}); e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0;
            assign _e_0 = {1'b0, _e_1};"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }
    #[test]
    fn zext_works_for_zero_bits() {
        let stmt = statement!(e(0); Type::Int(3); ZeroExtend({extra_bits: 0}); e(1));

        let expected = indoc! {
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1;"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn div_pow2_wokrs() {
        let stmt = statement!(e(0); Type::Int(3); DivPow2; e(1), e(2));

        let expected = indoc! {
            r#"
            logic[2:0] _e_0;
            assign _e_0 = $signed(_e_1) / (1 << _e_2);"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        )
    }

    #[test]
    fn concat_works() {
        let stmt = statement!(e(0); Type::Int(8); Concat; e(1), e(2));

        let expected = indoc! {
            r#"
            logic[7:0] _e_0;
            assign _e_0 = {_e_1, _e_2};"#
        };

        assert_same_code!(
            &statement_code(&stmt, &CodeBundle::new("".to_string())).to_string(),
            expected
        );
    }

    #[test]
    fn assertion_codegen_works() {
        let stmt = Statement::Assert(value_name!(e(0)).at(0, &Span::new(1, 2)));

        // NOTE: The escape sequences here are a bit annoying when this test failes,
        // but where to add an option to turn them off isn't obvious. To update this test
        // verify that the output is correct, then run `cargo test | sed -e 's/\x1b/_x1b_/g'`
        // and copy paste the output here. Escape the " characters and replace _x1b_ with \x1b
        let expected = indoc! {
            "
            always @(_e_0) begin
                #0
                assert (_e_0)
                else begin
                    $display(\"\x1b[0m\x1b[1m\x1b[38;5;9merror\x1b[0m\x1b[1m: Assertion failed\x1b[0m\");
                    $display(\"  \x1b[0m\x1b[34m┌─\x1b[0m <str>:1:2\");
                    $display(\"  \x1b[0m\x1b[34m│\x1b[0m\");
                    $display(\"\x1b[0m\x1b[34m1\x1b[0m \x1b[0m\x1b[34m│\x1b[0m a\x1b[0m\x1b[38;5;9mb\x1b[0mcd\");
                    $display(\"  \x1b[0m\x1b[34m│\x1b[0m  \x1b[0m\x1b[38;5;9m^\x1b[0m \x1b[0m\x1b[38;5;9mThis expression is false\x1b[0m\");
                    $display(\"\");
                    $error(\"Assertion failed\");
                    $fatal(1);
                end
            end"
        };

        let source_code = CodeBundle::new("abcd".to_string());

        assert_same_code!(&statement_code(&stmt, &source_code).to_string(), expected);
    }
}
