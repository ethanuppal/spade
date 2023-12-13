use local_impl::local_impl;
use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_hir::{Attribute, AttributeList};

use crate::Result;

#[local_impl]
impl AttributeListExt for AttributeList {
    fn report_unused(&self, on: &str) -> Result<()> {
        if let Some(attr) = self.0.first() {
            Err(attr.report_unused(on).into())
        } else {
            Ok(())
        }
    }

    fn lower(&self, handler: &mut impl FnMut(&Loc<Attribute>) -> Result<()>) -> Result<()> {
        self.0.iter().try_for_each(handler)
    }
}

#[local_impl]
impl LocAttributeExt for Loc<Attribute> {
    /// Report this attribute as unused on `on`
    /// on should be written not fit in the sentecnce {} is not a valid attribute for {on},
    /// i.e. `a thing` or `an item` should probably be used
    fn report_unused(&self, on: &str) -> Diagnostic {
        Diagnostic::error(
            self,
            format!("{} is not a valid attribute for {on}", self.name()),
        )
        .primary_label("Unrecognised attribute")
    }
}
