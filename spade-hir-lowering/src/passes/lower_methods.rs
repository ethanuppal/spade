use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_hir::{Expression, ItemList, Statement};
use spade_typeinference::{method_resolution::select_method, HasType, TypeState};

use crate::pass::Pass;

pub struct LowerMethods<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
}

impl<'a> Pass for LowerMethods<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> crate::error::Result<()> {
        let replacement_kind = match &mut expression.kind {
            spade_hir::ExprKind::MethodCall(self_, method, args) => {
                let self_type = self_.get_type(self.type_state).map_err(|e| {
                    Diagnostic::bug(self_.as_ref(), format!("did not find a type ({e})"))
                })?;

                let type_name = self_type.expect_named(
                    |name, _params| Ok(name.clone()),
                    || Err(Diagnostic::bug(self_.as_ref(), "Generic type")),
                    |other| {
                        Err(Diagnostic::bug(
                            self_.as_ref(),
                            format!("{other} can not have methods"),
                        ))
                    },
                )?;

                let method = select_method(self_.loc(), &type_name, method, self.items)?;

                Some(spade_hir::ExprKind::FnCall(method, args.clone()))
            }
            _ => None,
        };

        match replacement_kind {
            Some(new) => expression.kind = new,
            None => {}
        }
        Ok(())
    }

    fn visit_statement(&mut self, _statement: &mut Loc<Statement>) -> crate::error::Result<()> {
        Ok(())
    }
}
