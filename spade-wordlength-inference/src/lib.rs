use std::collections::BTreeMap;

use inferer::{Equation, Inferer};
use num::{BigInt, ToPrimitive};
use range::Range;
use spade_common::location_info::Loc;
use spade_hir::{symbol_table::FrozenSymtab, Unit};
use spade_typeinference::{equation::TypeVar, TypeState};
use spade_types::KnownType;

#[derive(Copy, Clone, Debug)]
pub enum InferMethod {
    IA,
    AA,
}

pub mod error;

mod affine;
mod inferer;
mod range;

pub type Res = error::Result<Option<Equation>>;

pub fn infer_and_check(
    infer_method: InferMethod,
    type_state: &mut TypeState,
    frozen_symtab: &FrozenSymtab,
    unit: &Unit,
) -> error::Result<()> {
    let mut inferer = inferer::Inferer::new(type_state, frozen_symtab.symtab());
    inferer.expression(&unit.body)?;

    let mut known = BTreeMap::new();
    //
    for (ty, var) in inferer.mappings.iter() {
        match &ty.inner {
            TypeVar::Known(KnownType::Integer(size), _) => {
                let x = (size.to_u128().unwrap() - 1).try_into().unwrap(); // This is assumed to be small
                known.insert(
                    *var,
                    Range {
                        lo: -BigInt::from(2).pow(x) + 1,
                        hi: BigInt::from(2).pow(x) - 2,
                    },
                );
            }
            TypeVar::Known(KnownType::Type(n), _) => panic!("How do I handle a type? {:?}", n),
            TypeVar::Unknown(_) => {
                // known.insert(var, Range { lo: 0, hi: 0 });
            }

            TypeVar::Tuple(_)
            | TypeVar::Array { .. }
            | TypeVar::Backward(_)
            | TypeVar::Wire(_)
            | TypeVar::Inverted(_) => panic!("Wat? {:?} {:?}", ty, var),
        }
    }

    let known = Inferer::infer(infer_method, &inferer.equations, known, &inferer.locs)?;

    for (ty, var) in inferer.mappings.iter() {
        // println!("{:?} = {:?}", var, known.get(&var));
        // None errors are checked when mir-lowering, this isn't necessarily an error
        if let Some(infered_wl) = known.get(&var).and_then(|guess| guess.to_wordlength()) {
            let loc = inferer.locs.get(var).cloned().unwrap_or(Loc::nowhere(()));
            match &ty.inner {
                TypeVar::Known(KnownType::Integer(size), _) => {
                    let typechecker_wl = loc.map(|_| size.to_u32().unwrap());
                    if typechecker_wl.inner != infered_wl {
                        // NOTE: To make these types better, the known types need to have a Loc on
                        // them, something I really don't feel like doing right now.
                        // TODO: Print the actual ranges of values, since that's nice!
                        return Err(error::Error::WordlengthMismatch {
                            typechecked: ty.give_loc(*typechecker_wl),
                            infered: loc.give_loc(infered_wl),
                        });
                    }
                }
                _ => {}
            }
            to_wordlength_error(
                inferer.type_state.unify(
                    ty,
                    &TypeVar::Known(KnownType::Integer(infered_wl.into()), Vec::new()),
                    inferer.symtab,
                ),
                loc,
            )?;
        }
    }

    Ok(())
}

fn to_wordlength_error<A>(
    ty_err: Result<A, spade_typeinference::error::UnificationError>,
    loc: Loc<()>,
) -> error::Result<A> {
    match ty_err {
        Ok(v) => Ok(v),
        Err(e) => Err(error::Error::TypeError(loc.map(|_| e.clone()))),
    }
}
