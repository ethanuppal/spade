use spade_common::{
    id_tracker::{ExprIdTracker, NameIdTracker},
    name::{NameID, Path},
};

use crate::{types::Type, Binding, ConstantValue, Entity, Operator, Statement, ValueName};

pub fn wal_alias(
    source: &ValueName,
    prefix: &str,
    suffix: &str,
    ty: &Type,
    idtracker: &mut Option<&mut NameIdTracker>,
) -> Statement {
    let source_nameid = match source {
        ValueName::Named(_, _, source) => source.clone(),
        // TODO: This is a horrible hack, but we are now generating a name_id from
        // an expression which doesn't have a source
        ValueName::Expr(_) => NameID(0, Path::from_strs(&["__unknown__"])),
    };
    // Because we know that traced_name is now unique, we also
    // know that any signals we generate with that name will be unique.
    // Therefore, we are free to generate `n(0, <name>_...)`
    let new_name = ValueName::Named(
        idtracker.as_mut().map(|t| t.next()).unwrap_or_default(),
        format!("{prefix}{suffix}"),
        source_nameid.clone(),
    );
    Statement::Binding(Binding {
        name: new_name,
        operator: Operator::Alias,
        operands: vec![source.clone()],
        ty: ty.clone(),
        loc: None,
    })
}

// NOTE: This pass must run after both flatten_aliases and make_names_predictable
// after the pass is run.
// NOTE: idtracker must be set to None for *codegen* to be correct, but it can be set
// to an ID tracker for testing purposes, for mir diffing to work
pub fn insert_wal_signals(
    entity: &mut Entity,
    expr_idtracker: &mut ExprIdTracker,
    name_idtracker: &mut Option<&mut NameIdTracker>,
) {
    let new_statements = entity
        .statements
        .iter()
        .flat_map(|s| {
            match s {
                Statement::Register(reg) => {
                    if let Some(traced_name) = &reg.traced {
                        let prefix = traced_name.unescaped_var_name();
                        let mut result = vec![
                            // Emit the register itself
                            s.clone(),
                            wal_alias(
                                &traced_name,
                                &prefix,
                                "__wal_fsm_state",
                                &reg.ty,
                                name_idtracker,
                            ),
                            wal_alias(
                                &reg.clock,
                                &prefix,
                                "__wal_fsm_clk",
                                &Type::Bool,
                                name_idtracker,
                            ),
                        ];
                        let rst_signal = if let Some(rst) = &reg.reset {
                            rst.0.clone()
                        } else {
                            let id = expr_idtracker.next();
                            result.push(Statement::Constant(
                                id,
                                Type::Bool,
                                ConstantValue::Bool(false),
                            ));
                            ValueName::Expr(id)
                        };
                        result.push(wal_alias(
                            &rst_signal,
                            &prefix,
                            "__wal_fsm_rst",
                            &Type::Bool,
                            name_idtracker,
                        ));
                        result
                    } else {
                        vec![s.clone()]
                    }
                }
                other => vec![other.clone()],
            }
        })
        .collect();
    entity.statements = new_statements;
}

#[cfg(test)]
mod test {
    use spade_common::id_tracker::{ExprIdTracker, NameIdTracker};

    use crate::{self as spade_mir, assert_same_mir, ConstantValue};
    use crate::{entity, types::Type};

    use super::insert_wal_signals;
    use colored::Colorize;

    #[test]
    fn traced_register_has_wal_tracing_applied() {
        let mut input = entity!(&["name"]; (
            "clk", n(1, "clk"), Type::Bool,
            "x", n(2, "x"), Type::Bool,
            "rst", n(3, "rst"), Type::Bool,
        ) -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true));
            (traced(n(0, "state"))
                reg n(0, "state"); Type::int(5); clock(n(1, "clk")); reset (n(3, "rst"), e(0)); n(2, "x"));
        } => n(2, "x"));

        let expected = entity!(&["name"]; (
            "clk", n(0, "clk"), Type::Bool,
            "x", n(2, "x"), Type::Bool,
            "rst", n(3, "rst"), Type::Bool,
        ) -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true));
            (traced(n(1, "state"))
                reg n(1, "state"); Type::int(5); clock(n(0, "clk")); reset (n(3, "rst"), e(0)); n(2, "x"));
            (n(10, "state__wal_fsm_state"); Type::int(5); Alias; n(1, "state"));
            (n(11, "state__wal_fsm_clk"); Type::Bool; Alias; n(0, "clk"));
            (n(12, "state__wal_fsm_rst"); Type::Bool; Alias; n(3, "rst"));
        } => n(2, "x"));

        insert_wal_signals(
            &mut input,
            &mut ExprIdTracker::new(),
            &mut Some(&mut NameIdTracker::new_at(100)),
        );

        assert_same_mir!(&input, &expected);
    }

    #[test]
    fn traced_register_without_reset_has_wal_tracing_applied() {
        let mut input = entity!(&["name"]; (
            "clk", n(0, "clk"), Type::Bool,
            "x", n(2, "x"), Type::Bool,
        ) -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true));
            (traced(n(1, "state"))
                reg n(1, "state"); Type::int(5); clock(n(0, "clk")); n(2, "x"));
        } => n(2, "x"));

        let expected = entity!(&["name"]; (
            "clk", n(0, "clk"), Type::Bool,
            "x", n(2, "x"), Type::Bool,
        ) -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true));
            (traced(n(1, "state"))
                reg n(1, "state"); Type::int(5); clock(n(0, "clk")); n(2, "x"));
            (n(10, "state_n1__wal_fsm_state"); Type::int(5); Alias; n(1, "state"));
            (n(11, "state_n1__wal_fsm_clk"); Type::Bool; Alias; n(0, "clk"));
            (const 10; Type::Bool; ConstantValue::Bool(false));
            (n(12, "state_n1__wal_fsm_rst"); Type::Bool; Alias; e(10));
        } => n(2, "x"));

        insert_wal_signals(
            &mut input,
            &mut ExprIdTracker::new_at(10),
            &mut Some(&mut NameIdTracker::new_at(100)),
        );

        assert_same_mir!(&input, &expected);
    }
}
