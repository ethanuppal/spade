use crate::snapshot_error;

snapshot_error!(
    suggest_add_array_size,
    r#"
    entity main() {
        let _: [bool] = [true, false];
    }
    "#
);

snapshot_error!(
    suggest_make_function_an_entity,
    r#"
    entity foo() -> int<1> {
        0
    }

    fn bar() -> int<1> {
        inst foo()
    }
    "#
);
