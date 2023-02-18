use crate::{build_items, snapshot_error};

snapshot_error! {
    stage_outside_pipeline,
    "
    entity main(x: X) -> int<8> {
        reg;
    }
    "
}

snapshot_error! {
    register_count_is_required,
    "
    pipeline(3) main(x: X) -> int<8> {
        reg *;
    }
    "
}

snapshot_error! {
    wrong_enum_variant_items_opener,
    "
    enum foo {
        A(int: int<4>),
    }
    "
}

snapshot_error! {
    wrong_enum_variant_items_opener_but_very_wrong,
    "
    enum foo {
        B|bool|,
    }
    "
}

snapshot_error! {
    wrong_argument_list_points_to_correct_token,
    "
    entity foo(clk: clk, a: bool) -> bool {
        reg(clk) a = a;
        a
    }

    entity main(clk: clk) -> bool {
        inst foo{clk, true}
    }
    "
}

snapshot_error! {
    functions_do_not_allow_inst_entity,
    "
    entity Y() -> bool { false }

    fn X() -> bool {
        inst Y()
    }
    "
}

snapshot_error! {
    functions_do_not_allow_inst_pipeline,
    "
    pipeline(2) P() -> bool {
        reg;
            false
    }

    fn X() -> bool {
        inst(2) Y()
    }
    "
}

snapshot_error! {
    unit_value_fails_gracefully,
    "fn a() -> bool {
        ()
    }"
}

snapshot_error! {
    missing_pipeline_depth_parens_is_an_error,
    "pipeline a(clk: clock) -> bool {
        true
    }"
}

#[test]
fn three_generic_end_chars_work() {
    let code = r#"
        struct A<T> {}
        struct X {
            a: A<A<A<bool>>>
        }
        "#;

    build_items(code);
}
