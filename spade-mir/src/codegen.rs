use crate::{util::Code, Statement};

fn statement_code(statement: &Statement) -> Code {
    match statement {
        Statement::Binding(binding) => {
            let size = size_spec(binding.ty.size());
        }
        Statement::Register(_) => {
            unimplemented!{}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{types::Type, statement};
    use crate as spade_mir;
    use indoc::indoc;

    #[test]
    fn binding_code_works() {
        let binding = statement!(e(0); Type::Int(5); Add; e(1), e(2));

        let expected = indoc!(r#"
            wire[4:0] _e_0;
            assign _e_0 = _e_1 + _e_2;
        "#);

        assert_eq!(statement_code(&binding).to_string(), expected);
    }
}
