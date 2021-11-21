//! For tests that ensure that type inference does not fail when it shouldnt

#[cfg(test)]
mod tests {
    use crate::build_items;

    #[test]
    fn type_inference_works_for_generics() {
        let code = r#"
        enum Option<T> {
            Some(value: T),
            None
        }
        entity name() -> int<16> {
            let x: Option<int<8>> = Option::Some(0);
            0
        }
        "#;

        build_items(code);
    }

    #[test]
    #[should_panic]
    fn tuple_pattern_type_missmatch_is_an_error() {
        let code = r#"
            entity name(x: int<16>) -> int<16> {
                let (true, var) = (x, x);
                0
            }
        "#;

        build_items(code);
    }

    #[test]
    #[should_panic]
    fn tuple_pattern_type_missmatch_is_an_error_part2() {
        let code = r#"
            enum X {
                Member
            }
            entity name(x: X) -> int<16> {
                let a: bool = x;
                0
            }
        "#;

        build_items(code);
    }
}
