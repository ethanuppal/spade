use crate::{build_items, build_items_with_stdlib, snapshot_error};

#[test]
fn type_inference_works_for_arrays() {
    let code = r#"
        entity x() -> [int<3>; 3] {
            [0, 1, 2]
        }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_generics() {
    let code = r#"
    enum Option<T> {
        Some{value: T},
        None
    }
    entity name() -> Option<int<16>> {
        Option::Some(0)
    }
    "#;
    build_items(code);
}

#[test]
fn type_inference_works_for_int_patterns() {
    let code = r#"
    entity name(x: int<16>) -> int<16> {
        match x {
            0 => 0,
            _ => 1
        }
    }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_array_indexing() {
    let code = r#"
    entity name(x: [int<16>; 10]) -> int<16> {
        x[0]
    }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_declared_variables() {
    let code = r#"
    entity name() -> int<16> {
        decl x;
        let a = x;
        let x = 0;
        a
    }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_usub_on_literals() {
    let code = r#"
    entity name() -> int<16> {
        -1
    }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_bools_with_not_operator() {
    let code = r#"
    entity name() -> int<16> {
        let test = !false;
        0
    }
    "#;

    build_items(code);
}

snapshot_error!(
    backward_tuple_indexing_with_type_error_errors_nicely,
    "entity name(x: &mut (bool, bool)) -> int<32> {
        x#0
    }"
);

snapshot_error!(
    tuple_input_as_index,
    "fn a(y: int<1>) -> int<32> {
        let t = (3, 5);
        t#y
    }"
);

snapshot_error!(
    useful_error_if_indexing_backward_array,
    "
    entity name(x: &mut [bool; 10]) -> int<32> {
        x[0]
    }
    "
);

snapshot_error!(
    int_as_if_argument,
    "fn a(y: int<1>) -> int<32> {
        if y {3} else {5}
    }"
);

snapshot_error! {
    type_error_on_port_set_mismatch,
    "
    // NOTE: returning bool because we don't support unit types
    entity set_port(p: &mut int<10>, v: int<9>) -> bool {
        set p = v;
        false
    }
    "
}

snapshot_error! {
    type_error_on_port_set_to_port,
    "
    // NOTE: returning bool because we don't support unit types
    entity set_port(p: &mut int<10>, v: &mut int<10>) -> bool {
        set p = v;
        false
    }
    "
}

snapshot_error!(
    return_type_mismatch,
    r#"
    entity main() -> int<1> {
        let a: int<2> = 0;
        a
    }
    "#
);

snapshot_error!(
    type_error_when_overflow_is_possible,
    "
    entity main(a: int<16>, b: int<16>) -> int<16> {
        a + b
    }
    "
);

snapshot_error! {
    multiplication_errors_if_overflow,
    "
    entity main(a: int<14>, b: int<16>) -> int<32> {
        a * b
    }
    "
}

snapshot_error! {
    counter_without_trunc_causes_type_error,
    "
        entity counter(clk: clock, rst: bool) -> int<8> {
            reg(clk) x reset (rst: 0) = x + 1;
            x
        }
    "
}

snapshot_error! {
    type_error_has_replacements_applied,
    "
        entity counter(clk: clock, rst: bool) -> (int<8>, int<8>) {
            decl x, y;

            let x_at_max = x == 8;
            let y_at_max = y == 6;

            reg(clk) x reset (rst: 0) =
                if x_at_max {
                    x
                }
                else {
                    x + 1
                };

            reg(clk) y reset (rst: 0) = {
                    y
                };

            (x, y)
        }
        "
}

snapshot_error! {
    array_index_errors_look_good,
    "
        entity counter(x: [int<8>; 10], idx: int<7>) -> int<8> {
            x[idx]
        }
        "
}

snapshot_error! {
    concatenation_errors_look_good,
    "
    entity counter(x: int<4>, y:int<3>) -> int<8> {
        x `std::conv::concat` y
    }
    "
}

snapshot_error! {
    variable_declarations_are_typechecked_correctly,
    "
        entity counter() -> int<8> {
            decl x;
            let a = x;
            let x: int<9> = 0;
            x
        }
        "
}

snapshot_error! {
    assertions_require_bools,
    "
        fn test(x: int<32>) -> bool {
            assert x;
            true
        }"
}

snapshot_error! {
    good_error_message_for_reg_with_explicit_type,
    "
        entity test(clk: clock) -> bool {
            reg(clk) (sample_i, audio_val): (int<9>, int<16>) = {
                true
            };

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_reg_pattern_type_mismatch,
    "
        entity test(clk: clock) -> bool {
            reg(clk) (sample_i, audio_val): bool = {
                true
            };

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_reg_pattern_type_mismatch_with_implicit_type,
    "
        entity test(clk: clock) -> bool {
            reg(clk) (sample_i, audio_val) = {
                true
            };

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_let_pattern_type_mismatch_with_implicit_type,
    "
        entity test(clk: clock) -> bool {
            let (x, y) = true;

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_let_pattern_type_mismatch_with_explicit_type,
    "
        entity test(clk: clock) -> bool {
            let (x, y): bool = true;

            true
        }
        "
}

snapshot_error! {
    fields_on_declared_vars_can_be_used,
    "
        struct X {a: bool}

        entity a() -> bool {
            decl x;
            let _: int<32> = x.a;
            let x = X(false);
            true
        }
    "
}

#[test]
fn fields_on_declared_variables_can_be_accessed_in_pipelines() {
    let code = "
        struct A {
            x: bool
        }
        pipeline(1) a(clk: clock) -> int<32> {
                let _ = stage(+1).x.x;
            reg;
                let x = A(false);
                0
        }
        ";

    build_items(code);
}

snapshot_error! {
    field_based_type_inference_works,
    "
        struct A {
            x: bool
        }
        fn a() -> int<32> {
            let a: int<32> = A(true).x;
            a
        }
    "
}

snapshot_error! {
    non_existing_fields_on_declared_variables_in_pipelines,
    "
        struct X {a: bool}

        pipeline(1) a(clk: clock) -> bool {
                let y = stage(+1).x.b;
            reg;
                let x = X(false);
                y
        }
        "
}

snapshot_error! {
    non_existing_fields_on_normal_variables_in_pipelines,
    "
        struct X {a: bool}

        pipeline(1) a(clk: clock) -> bool {
            reg;
                let x = X(false);
                let y = x.b;
                y
        }
        "
}

snapshot_error! {
    field_access_on_declared_non_struct_is_error,
    "
        fn a() -> int<32> {
            decl x;
            let a = x.a;
            let x = 0;
            a
        }
    "
}

#[test]
fn accessing_a_generic_fixed_field_works() {
    let code = "
        struct A<T> {
            a: T
        }

        fn x(a: A<bool>) -> bool {
            a.a
        }
        ";
    build_items(code);
}

snapshot_error! {
    backward_type_in_generic_is_an_error,
    "
    entity takes_generic<T>(x: T) -> bool {true}

    entity x(b: &mut bool) -> bool {
        inst takes_generic(b)
    }
    "
}

snapshot_error! {
    port_type_in_generic_is_an_error,
    "
    struct port X {
        x: &mut bool
    }
    entity takes_generic<T>(x: T) -> bool {true}

    entity x(b: X) -> bool {
        inst takes_generic(b)
    }
    "
}

#[test]
fn destructuring_a_read_mut_wire_gives_real_values() {
    let code = "
    mod std {mod ports { entity read_mut_wire<T>(t: &mut T) -> T __builtin__ }}
    struct A {
        x: bool,
        y: int<3>
    }

    struct port HasA {
        inner: &mut A
    }

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity consumer(x: HasA) -> bool __builtin__

    entity uut(val: HasA) -> bool {
        let A$(x, y) = inst std::ports::read_mut_wire(val.inner);
        let _ = inst consumer(val);
        takes_normal(x, y)
    }
    ";

    build_items(code);
}

snapshot_error! {
    reading_from_port_members_is_a_type_error,
    "
    use std::ports::read_mut_wire;

    struct A {
        x: bool,
        y: int<3>
    }

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity uut(val: &mut A) -> bool {
        let x = inst read_mut_wire(val.x);
        let y = inst read_mut_wire(val.y);
        takes_normal(x, y)
    }
    "
}

snapshot_error! {
    reading_from_tuple_members_is_an_error,
    "
    use std::ports::read_mut_wire;

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity uut(val: &mut (bool, int<3>)) -> bool {
        let x = inst read_mut_wire(val#0);
        let y = inst read_mut_wire(val#1);
        takes_normal(x, y)
    }
    "
}

snapshot_error! {
    dereference_requires_target_type,
    "
    entity x(a: &bool) -> int<8> {
        *a
    }
    "
}

snapshot_error! {
    type_error_on_registers_are_useful,
    "
    entity test(clk: clock, rst: bool) -> bool {
        let shift_clock_initial: int<10> = 0b0000011111;
        reg(clk) shift_clock: int<10> reset(rst: shift_clock_initial) = {
            let upper: int<2> = trunc(shift_clock);
            let rest: int<8> = shift_clock >> 2;
            upper `concat` rest
        };
        true
    }"
}

snapshot_error! {
    wrong_index_size_on_memory_write_port_is_error,
    "
        use std::mem::clocked_memory;
        entity test(clk: clock, idx: int<32>) -> int<8> {
            let mem: Memory<int<8>, 16> = inst clocked_memory(clk, [(true, idx, 0)]);
            0
        }
    "
}

snapshot_error! {
    wrong_index_size_on_memory_read_port_is_error,
    "
        use std::mem::clocked_memory;
        use std::mem::read_memory;

        entity test(clk: clock, idx: int<32>) -> int<8> {
            let mem: Memory<int<8>, 32> = inst clocked_memory(clk, []);
            inst read_memory(mem, idx)
        }
    "
}

snapshot_error! {
    too_small_index_size_on_memory_read_port_is_error,
    "
        use std::mem::clocked_memory;
        use std::mem::read_memory;

        entity test(clk: clock, idx: int<3>) -> int<8> {
            let mem: Memory<int<8>, 16> = inst clocked_memory(clk, [(true, idx, 0)]);
            0
        }
    "
}

#[test]
fn rom_is_describable() {
    let code = "
        use std::mem::clocked_memory_init;
        use std::mem::read_memory;

        entity test(clk: clock, idx: int<1>) -> int<8> {
            let mem: Memory<int<8>, 2> = inst clocked_memory_init(clk, [(true, 0, 0)], [1, 2]);
            inst read_memory(mem, idx)
        }
    ";
    build_items_with_stdlib(code);
}

snapshot_error! {
    different_types_in_if,
    "
        fn test(b: int<4>) -> int<8> {
            let a = if b == 4 { 3 } else { true };
            7
        }
    "
}

snapshot_error! {
    clock_must_be_of_type_clock,
    "
        entity test(b: int<4>) -> int<8> {
            reg(b) a = 3;
            a
        }
    "
}

snapshot_error! {
    reset_must_be_of_type_bool,
    "
        entity test(clk: clock, b: int<4>) -> int<8> {
            reg(clk) a reset (b: 0) = 3;
            a
        }
    "
}

snapshot_error! {
    reset_mismatch,
    "
        entity test(clk: clock, rst: bool) -> int<8> {
            reg(clk) a reset (rst: true) = 3;
            a
        }
    "
}

snapshot_error! {
    array_type_mismatch,
    "
        fn x() -> bool  {
            let a = [0, true, 2];
            false
        }
    "
}

snapshot_error! {
    // NOTE: This test should be removed once we support unsigned ints properly
    unsigned_literals_error_on_overflow,
    "
        fn test() -> int<8> {
            256u
        }
    "
}

#[test]
fn unsigned_literals_fit_in_negative_region() {
    let code = "fn test() -> int<8> {
        255u
    }";

    build_items(code);
}

#[test]
fn accessing_fields_of_structs_in_inverted_ports_works() {
    let code = "
        struct port Inner {
            x: &bool
        }
        struct port Outer {
            inner: Inner
        }

        entity test(p: ~Outer) -> &mut bool {
            p.inner.x
        }
    ";

    build_items(code);
}

snapshot_error! {
    wal_trace_clk_must_be_clock,
    "
        #[wal_suffix(__)]
        struct T {}
        fn test(t: T, x: bool) -> bool {
            #[wal_trace(clk=x)]
            let t = t;
            false
        }
    "
}

snapshot_error! {
    wal_trace_rst_must_be_clock,
    "
        #[wal_suffix(__)]
        struct T {}
        fn test(t: T, x: int<10>) -> bool {
            #[wal_trace(rst=x)]
            let t = t;
            false
        }
    "
}

snapshot_error! {
    pipeline_stage_valid_is_a_bool,
    "pipeline(1) x(clk: clock) -> bool {
            let a: int<8> = stage.valid;
        reg;
            true
    }"
}

snapshot_error! {
    pipeline_stage_ready_is_a_bool,
    "pipeline(1) x(clk: clock) -> bool {
            let a: int<8> = stage.ready;
        reg;
            true
    }"
}
