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
}
