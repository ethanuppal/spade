//! For tests that ensure that type inference does not fail when it shouldnt

#[cfg(test)]
mod namespace_tests {
    use crate::build_items;

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

    // Once we get failing tests up and running, this should be tested
    #[ignore]
    #[test]
    fn namespacing_adds_to_the_correct_namespace() {
        let code = r#"
            mod X {
                entity x() -> int<2> {
                    1
                }
            }

            entity top() -> int<2> {
                x()
            }
        "#;

        build_items(code);
    }

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
}
