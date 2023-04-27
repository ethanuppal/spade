use ast::{Attribute, AttributeList};
use local_impl::local_impl;
use spade_ast as ast;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID},
};
use spade_diagnostics::Diagnostic;
use spade_hir as hir;

use crate::error::Result;

#[local_impl]
impl AttributeListExt for AttributeList {
    /// Walks through the attribute list to get the unit name. Removes the attributes
    /// used to determine that
    fn unit_name(
        &mut self,
        name_id: &Loc<NameID>,
        identifier: &Loc<Identifier>,
        type_params: &Vec<Loc<ast::TypeParam>>,
    ) -> Result<hir::UnitName> {
        let attr = self.consume_no_mangle();

        if let Some(attribute) = attr {
            if !type_params.is_empty() {
                let generic_list =
                    ().between_locs(type_params.first().unwrap(), type_params.last().unwrap());
                Err(
                    Diagnostic::error(attribute, "no_mangle is not allowed on generic units")
                        .primary_label("no_mangle not allowed here")
                        .secondary_label(generic_list, "Because this unit is generic")
                        .into(),
                )
            } else {
                Ok(hir::UnitName::Unmangled(
                    identifier.0.clone(),
                    name_id.inner.clone().at_loc(identifier),
                ))
            }
        } else {
            if !type_params.is_empty() {
                Ok(hir::UnitName::WithID(name_id.clone()))
            } else {
                Ok(hir::UnitName::FullPath(name_id.clone()))
            }
        }
    }

    /// Removes #[no_mangle] from the attribute list and returns it if
    /// it was present
    fn consume_no_mangle(&mut self) -> Option<Loc<()>> {
        let mut mangle_attribute = None;
        self.0.retain(|attr| match attr.inner {
            Attribute::NoMangle => {
                mangle_attribute = Some(attr.loc());
                false
            }
        });
        mangle_attribute
    }

    fn report_unused(&self) -> Result<()> {
        if let Some(attr) = self.0.first() {
            return Err(Diagnostic::error(attr, "Unrecognised attribute")
                .primary_label("Unrecognised attribute")
                .into());
        }
        Ok(())
    }
}
