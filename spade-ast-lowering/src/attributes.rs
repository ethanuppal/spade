use spade_ast as ast;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID},
};
use spade_diagnostics::Diagnostic;
use spade_hir as hir;

use crate::error::{Error, Result};

/// Walks through the attribute list to get the unit name. Removes the attributes
/// used to determine that
pub fn unit_name(
    attrs: &mut ast::AttributeList,
    name_id: &Loc<NameID>,
    identifier: &Loc<Identifier>,
    type_params: &Vec<Loc<ast::TypeParam>>,
) -> Result<hir::UnitName> {
    let mut mangle_attribute = None;
    attrs.0.retain(|attr| {
        if attr.inner.0 == "no_mangle" {
            mangle_attribute = Some(attr.clone());
            false
        } else {
            println!("Unused parameter");
            true
        }
    });

    if let Some(attribute) = mangle_attribute {
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

pub fn report_unused_attributes(attributes: &ast::AttributeList) -> Result<()> {
    if let Some(attr) = attributes.0.first() {
        return Err(Error::UnrecognisedAttribute {
            attribute: attr.clone(),
        });
    }
    Ok(())
}
