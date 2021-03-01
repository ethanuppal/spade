use std::collections::HashMap;

use crate::{Statement, ValueName};

/// Functions for diffing and comparing mir code while ignoring exact variable IDs

struct VarMap {
    expr_map: HashMap<u64, u64>,
    name_map: HashMap<u64, u64>,
}

impl VarMap {
    pub fn new() -> Self {
        Self {
            expr_map: HashMap::new(),
            name_map: HashMap::new(),
        }
    }

    pub fn map_expr(&mut self, lhs: u64, rhs: u64) {
        self.expr_map.insert(lhs, rhs);
    }

    pub fn map_name(&mut self, lhs: u64, rhs: u64) {
        self.name_map.insert(lhs, rhs);
    }

    pub fn compare_name(
        &mut self,
        (lhs_id, lhs_name): (&u64, &str),
        (rhs_id, rhs_name): (&u64, &str),
    ) -> bool {
        if lhs_name != rhs_name {
            return false;
        }

        self.name_map
            .get(&lhs_id)
            .map(|v| rhs_id == v)
            .unwrap_or(false)
    }

    pub fn compare_exprs(&mut self, lhs: u64, rhs: u64) -> bool {
        self.expr_map.get(&lhs).map(|v| v == &rhs).unwrap_or(false)
    }
}

/// Compare statements, if they match, add the new mapping to the mapping table
fn compare_statements(s1: &Statement, s2: &Statement, var_map: &mut VarMap) -> bool {
    match (s1, s2) {
        (Statement::Binding(b1), Statement::Binding(b2)) => {
            // Compare the types and operators

            if b1.ty != b2.ty {
                return false;
            }
            if b1.operator != b2.operator {
                return false;
            }
            if b1.operands.len() != b2.operands.len() {
                return false;
            }
            // Check the params
            for pair in b1.operands.iter().zip(b2.operands.iter()) {
                match pair {
                    (ValueName::Named(id1, name1), ValueName::Named(id2, name2)) => {
                        if !var_map.compare_name((id1, name1), (id2, name2)) {
                            return false;
                        }
                    }
                    (ValueName::Expr(_), ValueName::Expr(_)) => {}
                    _ => return false,
                }
            }

            match (&b1.name, &b2.name) {
                (ValueName::Named(i1, n1), ValueName::Named(i2, n2)) => {
                    if n1 != n2 {
                        return false;
                    }
                    var_map.map_name(*i1, *i2)
                }
                (ValueName::Expr(i1), ValueName::Expr(i2)) => var_map.map_expr(*i1, *i2),
                _ => return false,
            }
            true
        }
        (Statement::Register(_), Statement::Register(_)) => {
            todo!()
        }
        (Statement::Constant(_, _, _), Statement::Constant(_, _, _)) => {
            todo!()
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{statement, types::Type};

    use crate as spade_mir;

    #[test]
    fn identical_bindings_update_expr_map() {
        let mut map = VarMap::new();

        map.map_expr(1, 2);
        map.map_name(2, 3);

        let lhs = statement!(e(0); Type::Int(5); Add; e(1), n(2, "test"));
        let rhs = statement!(e(3); Type::Int(5); Add; e(2), n(3, "test"));

        assert!(compare_statements(&lhs, &rhs, &mut map));

        assert!(map.compare_exprs(0, 3))
    }

    #[test]
    fn identical_bindings_update_name_map() {
        let mut map = VarMap::new();

        map.map_expr(1, 2);
        map.map_name(2, 3);

        let lhs = statement!(n(0, "a"); Type::Int(5); Add; e(1), n(2, "test"));
        let rhs = statement!(n(3, "a"); Type::Int(5); Add; e(2), n(3, "test"));

        assert!(compare_statements(&lhs, &rhs, &mut map));

        assert!(map.compare_name((&0, "a"), (&3, "a")))
    }

    #[test]
    fn identical_bindings_with_differing_string_name_diff() {
        let mut map = VarMap::new();

        map.map_expr(1, 2);
        map.map_name(2, 3);

        let lhs = statement!(n(0, "a"); Type::Int(5); Add; e(1), n(2, "test"));
        let rhs = statement!(n(3, "b"); Type::Int(5); Add; e(2), n(3, "test"));

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn bindings_with_missmatched_types_are_different() {
        let mut map = VarMap::new();

        map.map_expr(1, 1);
        map.map_expr(2, 2);

        let lhs = statement!(e(0); Type::Int(5); Add; e(1), e(2));
        let rhs = statement!(e(3); Type::Int(4); Add; e(1), e(2));

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }

    #[test]
    fn bindings_with_missmatched_operators_are_different() {
        let mut map = VarMap::new();

        map.map_expr(1, 1);
        map.map_expr(2, 2);

        let lhs = statement!(e(0); Type::Int(5); Add; e(1), e(2));
        let rhs = statement!(e(3); Type::Int(5); Select; e(1), e(2));

        assert!(!compare_statements(&lhs, &rhs, &mut map));
    }
}
