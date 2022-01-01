//! For tests that ensure that type inference does not fail when it shouldnt

#[cfg(test)]
mod tests {
    use crate::build_items;

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
            Some(value: T),
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
}
