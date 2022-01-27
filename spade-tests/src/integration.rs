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
}
