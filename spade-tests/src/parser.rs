use crate::snapshot_error;

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
