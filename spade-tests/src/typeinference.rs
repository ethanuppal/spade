use crate::{build_items, snapshot_error};

#[test]
fn type_inference_works_for_arrays() {
    let code = r#"
        entity x() -> [int<2>; 3] {
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
            0 => 0
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
        entity counter(clk: clk, rst: bool) -> int<8> {
            reg(clk) x reset (rst: 0) = x + 1;
            x
        }
    "
}

snapshot_error! {
    type_error_has_replacements_applied,
    "
        entity counter(clk: clk, rst: bool) -> (int<8>, int<8>) {
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
    // FIXME: Figure out a way to include stdlib in tests
    // lifeguard spade#125
    "
    mod std{mod conv{ 
        fn concat<#N, #M, #K>(x: int<N>, y: int<M>) -> int<K> __builtin__
    }}
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
        entity test(clk: clk) -> bool {
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
        entity test(clk: clk) -> bool {
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
        entity test(clk: clk) -> bool {
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
        entity test(clk: clk) -> bool {
            let (x, y) = true;

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_let_pattern_type_mismatch_with_explicit_type,
    "
        entity test(clk: clk) -> bool {
            let (x, y): bool = true;

            true
        }
        "
}
