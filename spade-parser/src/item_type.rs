use parse_tree_macros::local_impl;
use spade_common::location_info::{Loc, WithLocation};

use crate::error::{Error, Result};

#[derive(Clone, Copy, Debug)]
pub enum ItemType {
    Function,
    Entity,
    Pipeline,
}
impl WithLocation for ItemType {}

#[local_impl]
impl ItemTypeLocal for Option<Loc<ItemType>> {
    fn allows_reg(&self, at: Loc<()>) -> Result<()> {
        match self.as_ref().map(|s| &s.inner) {
            Some(ItemType::Function) => Err(Error::RegInFunction {
                at,
                fn_keyword: self.as_ref().unwrap().loc(),
            }),
            Some(ItemType::Entity) => Ok(()),
            Some(ItemType::Pipeline) => Ok(()),
            None => Err(Error::InternalExpectedItemContext { at }),
        }
    }

    fn allows_inst(&self, at: Loc<()>) -> Result<()> {
        match self.as_ref().map(|s| &s.inner) {
            Some(ItemType::Function) => Err(Error::InstInFunction {
                at,
                fn_keyword: self.as_ref().unwrap().loc(),
            }),
            Some(ItemType::Entity) => Ok(()),
            Some(ItemType::Pipeline) => Ok(()),
            None => Err(Error::InternalExpectedItemContext { at }),
        }
    }

    fn allows_pipeline_ref(&self, at: Loc<()>) -> Result<()> {
        match self.as_ref().map(|s| &s.inner) {
            Some(ItemType::Function) => Err(Error::PipelineRefInFunction {
                at,
                fn_keyword: self.as_ref().unwrap().loc(),
            }),
            Some(ItemType::Entity) => Err(Error::PipelineRefInEntity {
                at,
                entity_keyword: self.as_ref().unwrap().loc(),
            }),
            Some(ItemType::Pipeline) => Ok(()),
            None => Err(Error::InternalExpectedItemContext { at }),
        }
    }
}
