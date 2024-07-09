pub trait MirPass {
    fn transform_statements(stmts: &[Statement], expr_idtracker: &mut ExprIdTracker) -> Vec<Statement> {
        stmts.clone()
    }
}
