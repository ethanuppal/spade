/// Macros for writing mir.
/// Requires the crate to be in scope, i.e. `use spade_mir;`

#[macro_export]
macro_rules! value_name {
    (n($id:expr, $debug_name:expr)) => {
        spade_mir::ValueName::Named($id, $debug_name.to_string())
    };
    (e($id:expr)) => {
        spade_mir::ValueName::Expr($id)
    };
}

#[macro_export]
macro_rules! statement {
    // Normal constants
    (
        const $id:expr; $ty:expr; $value:expr
    ) => {
        spade_mir::Statement::Constant($id, $ty, $value)
    };
    // Bindings
    (
        $name_kind:ident $name:tt;
        $type:expr;
        $operator:ident $(($operator_args:tt))?;
        $($arg_kind:ident $arg_name:tt),*
    ) => {
        spade_mir::Statement::Binding(spade_mir::Binding {
            name: spade_mir::value_name!($name_kind $name),
            operator: spade_mir::Operator::$operator$($operator_args)?,
            operands: vec![
                $(spade_mir::value_name!($arg_kind $arg_name)),*
            ],
            ty: $type
        })
    };
    //register with async reset
    (
        reg $name_kind:ident $name:tt;
        $type:expr;
        clock ($clk_name_kind:ident $clk_name:tt);
        reset ($rst_trig_kind:ident $rst_trig_name:tt, $rst_val_kind:ident $rst_val_name:tt);
        $val_kind:ident $val_name:tt
    ) => {
        spade_mir::Statement::Register(spade_mir::Register {
            name: spade_mir::value_name!($name_kind $name),
            ty: $type,
            clock: spade_mir::value_name!($clk_name_kind $clk_name),
            reset: Some((
                spade_mir::value_name!($rst_trig_kind $rst_trig_name),
                spade_mir::value_name!($rst_val_kind $rst_val_name)
            )),
            value: spade_mir::value_name!($val_kind $val_name)
        })
    };
    // Register without reset
    (
        reg $name_kind:ident $name:tt;
        $type:expr;
        clock ($clk_name_kind:ident $clk_name:tt);
        $val_kind:ident $val_name:tt
    ) => {
        spade_mir::Statement::Register(spade_mir::Register {
            name: spade_mir::value_name!($name_kind $name),
            ty: $type,
            clock: spade_mir::value_name!($clk_name_kind $clk_name),
            reset: None,
            value: spade_mir::value_name!($val_kind $val_name)
        })
    };
}

/// Example
/// ```
/// use spade_mir as mir;
/// use spade_mir::entity;
/// use spade_mir::types::Type;
/// entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::Int(6); {
///     (e(0); Type::Int(6); Add; n(1, "value"));
///     (const 0; Type::Int(10); ConstantValue::Int(6));
///     (reg n(1, "value"); Type::Int(6); clock (n(0, "clk")); e(0))
/// } => n(1, "value"));
/// ```
#[macro_export]
macro_rules! entity {
    ($name:expr; (
            $( $arg_name:expr, $arg_intern_kind:ident $arg_intern_name:tt, $arg_type:expr ),* $(,)?
        ) -> $output_type:expr; {
            $( $statement:tt );*
            $(;)?
        } => $output_name_kind:ident $output_name:tt
    ) => {
        spade_mir::Entity {
            name: $name.to_string(),
            inputs: vec![
                $( (
                    $arg_name.to_string(),
                    spade_mir::value_name!($arg_intern_kind $arg_intern_name),
                    $arg_type
                )),*
            ],
            output: spade_mir::value_name!($output_name_kind $output_name),
            output_type: $output_type,
            statements: vec![
                $( spade_mir::statement! $statement ),*
            ],
        }
    }
}

#[cfg(test)]
mod tests {
    use crate as spade_mir;
    use crate::{types::Type, Binding, ConstantValue, Operator, Register, Statement, ValueName};

    #[test]
    fn value_name_parsing_works() {
        assert_eq!(
            value_name!(n(0, "test")),
            ValueName::Named(0, "test".to_string())
        );
        assert_eq!(value_name!(e(0)), ValueName::Expr(0));
    }

    #[test]
    fn binding_parsing_works() {
        let expected = Statement::Binding(Binding {
            name: ValueName::Expr(0),
            operator: Operator::Add,
            operands: vec![ValueName::Expr(1), ValueName::Named(1, "test".to_string())],
            ty: Type::Bool,
        });

        assert_eq!(
            statement!(e(0); Type::Bool; Add; e(1), n(1, "test")),
            expected
        );
    }

    #[test]
    fn named_parsing_works() {
        let expected = Statement::Binding(Binding {
            name: ValueName::Named(0, "string".to_string()),
            operator: Operator::Add,
            operands: vec![ValueName::Expr(1), ValueName::Named(1, "test".to_string())],
            ty: Type::Bool,
        });

        assert_eq!(
            statement!(n(0, "string"); Type::Bool; Add; e(1), n(1, "test")),
            expected
        );
    }

    #[test]
    fn register_parsing_works() {
        let expected = Statement::Register(Register {
            name: ValueName::Named(0, "test".into()),
            ty: Type::Int(5),
            clock: ValueName::Named(1, "clk".into()),
            reset: None,
            value: ValueName::Expr(0),
        });

        assert_eq!(
            statement!(reg n(0, "test"); Type::Int(5); clock (n(1, "clk")); e(0)),
            expected
        );
    }

    #[test]
    fn register_with_reset_parsing_works() {
        let expected = Statement::Register(Register {
            name: ValueName::Named(0, "test".into()),
            ty: Type::Int(5),
            clock: ValueName::Named(1, "clk".into()),
            reset: Some((ValueName::Expr(1), ValueName::Expr(2))),
            value: ValueName::Expr(0),
        });

        assert_eq!(
            statement!(reg n(0, "test"); Type::Int(5); clock (n(1, "clk")); reset (e(1), e(2)); e(0)),
            expected
        );
    }

    #[test]
    fn entity_parsing_works() {
        let expected = crate::Entity {
            name: "pong".to_string(),
            inputs: vec![(
                "_i_clk".to_string(),
                ValueName::Named(0, "clk".to_string()),
                Type::Bool,
            )],
            output: ValueName::Named(1, "value".to_string()),
            output_type: Type::Int(6),
            statements: vec![
                statement!(e(0); Type::Int(6); Add; n(1, "value")),
                statement!(reg n(1, "value"); Type::Int(6); clock (n(0, "clk")); e(0)),
            ],
        };

        let result = entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::Int(6); {
                (e(0); Type::Int(6); Add; n(1, "value"));
                (reg n(1, "value"); Type::Int(6); clock (n(0, "clk")); e(0))
            } => n(1, "value"));

        assert_eq!(result, expected);
    }

    #[test]
    fn constant_parsing_works() {
        let expected = Statement::Constant(0, Type::Int(10), ConstantValue::Int(6));

        let result = statement!(const 0; Type::Int(10); ConstantValue::Int(6));

        assert_eq!(result, expected);
    }
}
