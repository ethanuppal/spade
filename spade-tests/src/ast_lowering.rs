use crate::{build_items, snapshot_error};

snapshot_error! {
    duplicate_definition_of_decl_triggers_errors,
    "
    entity X() -> int<8> {
        decl x;
        let x = 0;
        let x = 1;
        x
    }
    "
}

snapshot_error! {
    declaration_without_definition_triggers_error,
    "
    entity X() -> int<8> {
        decl x;
        x
    }
    "
}

snapshot_error! {
    declaration_after_let_requires_new_definition,
    "
    entity X() -> int<8> {
        let x: int<8> = 0;
        decl x;
        x
    }
    "
}

snapshot_error! {
    negative_stage_index,
    "
    pipeline(3) main(x: int<8>) -> int<8> {
            let a = stage(-1).x;
        reg;
        reg;
        reg;
            0
    }
    "
}

snapshot_error! {
    stage_index_overflow,
    "
    pipeline(3) main(x: int<8>) -> int<8> {
        reg;
        reg;
        reg;
            stage(+1).x
    }
    "
}

snapshot_error! {
    duplicate_label_error,
    "
    pipeline(3) main(clk: clk) -> int<8> {
        reg;
            'a
        reg;
            'a
        reg;
            0
    }"
}

snapshot_error! {
    undefined_label_error,
    "
    pipeline(3) main(clk: clk) -> int<8> {
        reg;
            'a
            let x = 0;
        reg;
        reg;
            stage(b).x
    }"
}

snapshot_error! {
    multiple_labels_for_same_stage,
    "
    pipeline(3) main(clk: clk) -> int<8> {
        reg;
            'a
            'b
        reg;
        reg;
            0
    }"
}

snapshot_error! {
    single_identifier_enum_lookups_pass_compiler,
    "
    enum X {
        A{x: int<5>},
        B
    }

    use X::A;
    use X::B;

    fn test(x: X) -> X {
        match x {
            A(_) => A(4),
            // If this test works, B, being in scope should not be a variable but remain
            // refering to X::B. In the incorrect behaviour, the single identifier path B
            // binds to X and B() is calling a variable as a function
            B => B(), 
        }
    }
    "
}

snapshot_error! {
    match_expressions_open_new_scopes,
    "
    fn test(x: int<32>) -> int<32> {
        let _: int<32> = match x {
            a => 0
        };

        a
    }
    "
}

snapshot_error! {
    unused_attribute_errors_on_builtin_entity,
    "
        #[uwu]
        entity a() -> bool __builtin__
    "
}

snapshot_error! {
    unused_attribute_errors_on_builtin_pipeline,
    "
        #[uwu]
        pipeline(1) a(clk: clk) -> bool __builtin__
    "
}

snapshot_error! {
    unused_attribute_errors_on_entity,
    "
        #[uwu]
        entity a() -> bool {true}
    "
}

snapshot_error! {
    unused_attribute_errors_on_pipeline,
    "
        #[uwu]
        pipeline(1) a(clk: clk) -> bool {reg; true}
    "
}

#[test]
fn nested_use_compiles_correctly() {
    let code = r#"
        mod A {
            struct X {x: bool}
        }

        mod B {
            use lib::A::X;

            fn a() -> X {
                X(true)
            }
        }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_declared_variables() {
    let code = r#"
    enum Option<T> {
        Some{val: T},
        None
    }
    fn test() -> bool {
        let x: Option<(int<8>, int<8>)> = Option::Some((0, 0));

        let _ = match x {
            Option::Some(x) => true,
            _ => false
        };

        match x {
            Option::Some((a, b)) => true,
            _ => false
        }
    }
    "#;

    build_items(code);
}

#[test]
fn use_of_namespace_works() {
    let code = r#"
        mod a {
            mod b {
                struct X {x: bool}
            }
        }

        use a::b;

        fn x() -> b::X {
            b::X(true)
        }
    "#;

    build_items(code);
}
