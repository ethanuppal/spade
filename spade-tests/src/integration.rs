use crate::{build_items, snapshot_error};

#[test]
fn namespacing_works() {
    let code = r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        entity top() -> int<2> {
            inst X::x()
        }
    "#;

    build_items(code);
}

snapshot_error!(
    namespacing_adds_to_the_correct_namespace,
    r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        entity top() -> int<2> {
            x()
        }
    "#
);

#[test]
fn use_statements_work() {
    let code = r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        use X::x;

        entity top() -> int<2> {
            inst x()
        }
        "#;

    build_items(code);
}

#[test]
fn renaming_use_statements_work() {
    let code = r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        use X::x as a;

        entity top() -> int<2> {
            inst a()
        }
        "#;

    build_items(code);
}

/// NOTE This test fails currently
#[test]
fn recursive_use_statements_work() {
    let code = r#"
        mod X {
            mod Y {
                entity x() -> int<2> {
                    1
                }
            }
            use Y::x;
        }

        use X::x as a;

        entity top() -> int<2> {
            inst a()
        }
    "#;

    build_items(code);
}

#[test]
fn using_names_in_namespaces_works() {
    let code = r#"
        mod X {
            enum A {X{a: bool}}

            entity x() -> A {
                A::X(true)
            }
        }
        "#;

    build_items(code);
}

#[test]
fn using_names_of_types_in_namespaces_works() {
    let code = r#"
        mod X {
            struct A {}
            struct B{a: A}
        }
        "#;

    build_items(code);
}

// NOTE: this is an awful error message at the moment, but it is strange code
// and fixing it would take quite a bit of effort, so we'll leave it be and
// create an issue for it
snapshot_error! {
    pipeline_shadowing_does_not_fail_silently,
    "
    pipeline(2) main(clk: clock, x: int<8>) -> int<8> {
            let x: int<8> = 0;
        reg;
            let x: int<8> = 1;
        reg;
            stage(-2).x
    }
    "
}

#[cfg(test)]
mod trait_tests {
    use crate::{build_items, snapshot_error};

    snapshot_error! {
        ast_lowering_errors_are_caught_in_impl_blocks,
        "
        struct X {}

        impl X {
            fn x(self) {
                a
            }
        }
        "
    }

    snapshot_error! {
        type_errors_are_caught_in_impl_blocks,
        "
        struct X {}

        impl X {
            fn x(self) -> bool {
                1
            }
        }
        "
    }

    #[test]
    fn accessing_fields_on_self_works() {
        let code = "
            struct X {
                a: int<8>
            }

            impl X {
                fn x(self) -> int<8> {
                    self.a
                }
            }
        ";

        build_items(code);
    }

    snapshot_error! {
        multiple_anonymous_impls_of_same_function_is_an_error,
        "
            struct X {}

            impl X {
                fn a(self) -> bool {true}
            }

            impl X {
                fn a(self) -> bool {false}
            }
        "
    }

    snapshot_error! {
        entities_in_impl_blocks_are_graceuflly_disallowed,
        "
            struct X {}

            impl X {
                entity a(self) -> bool {true}
            }
        "
    }

    snapshot_error! {
        pipelines_in_impl_blocks_are_graceuflly_disallowed,
        "
            struct X {}

            impl X {
                pipeline(0) a(self) -> bool {true}
            }
        "
    }

    #[test]
    fn calling_method_does_not_error() {
        let code = "
            struct X {}
            impl X {
                fn test(self) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test()
            }
        ";
        build_items(code);
    }

    snapshot_error! {
        multiple_same_named_methods_errors,
        "
            struct X {}
            impl X {
                fn test(self) -> bool {true}
            }
            impl X {
                fn test(self) -> bool {false}
            }

            fn main(x: X) -> bool {
                x.test()
            }
            "
    }

    snapshot_error! {
        calling_methods_with_the_wrong_number_of_params_errors,
        "
            struct X {}
            impl X {
                fn test(self) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test(1)
            }
        "
    }

    snapshot_error! {
        calling_methods_with_the_wrong_named_args,
        "
            struct X {}
            impl X {
                fn test(self, x: bool) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test$(y: 1)
            }
        "
    }

    snapshot_error! {
        method_which_does_not_take_self_is_an_error,
        "
            struct X {}
            impl X {
                fn test(x: bool) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test$(y: 1)
            }
        "
    }

    snapshot_error! {
        binding_self_causes_reasonable_error,
        "
            struct X {}
            impl X {
                fn test(self, x: bool) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test$(self: X())
            }
        "
    }

    snapshot_error! {
        duplicate_method_causes_error,
        "
            struct X {}

            impl X {
                fn a(self) -> bool {true}
            }

            impl X {
                fn a(self) -> bool {true}
            }

            fn test(x: X) -> bool {
                x.a()
            }

        "
    }

    snapshot_error! {
        tuple_has_no_methods,
        "fn a(x: (bool, bool)) -> bool {x.test()}"
    }
}
