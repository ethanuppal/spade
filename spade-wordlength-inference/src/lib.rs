use spade_hir::{
    ArgumentList, Block, ExprKind, Expression, ItemList, Pattern, PatternArgument, Register,
    Statement, TypeParam, Unit,
};
use spade_typeinference::TypeState;

mod error;

pub fn infer_and_check(a: &mut TypeState, b: &Unit) -> error::Result<()> {
    Err(error::Error::Unit)
}
