use std::collections::BTreeMap;

use inferer::{Equation, Inferer, Range};
use num::ToPrimitive;
use spade_hir::Unit;
use spade_typeinference::{equation::TypeVar, Context, TypeState};
use spade_types::KnownType;

mod error;
mod inferer;

pub type Res = error::Result<Option<Equation>>;

pub fn infer_and_check(
    type_state: &mut TypeState,
    context: &Context,
    unit: &Unit,
) -> error::Result<()> {
    let mut inferer = inferer::Inferer::new(type_state, context);
    inferer.expression(&unit.body)?;

    let mut known = BTreeMap::new();
    //
    for (ty, var) in inferer.mappings.iter() {
        match &ty {
            TypeVar::Known(KnownType::Integer(size), _) => {
                let x = size.to_u32().unwrap(); // This is assumed to be small
                known.insert(
                    *var,
                    Range {
                        lo: -2_i128.pow(x - 1) + 1,
                        hi: 2_i128.pow(x - 1) - 2,
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

    let known = Inferer::infer(&inferer.equations, known)?;

    // TODO: Location information isn't really a thing... Maybe it can be solved some other way?
    for (ty, var) in inferer.mappings.iter() {
        // println!("{:?} = {:?}", var, known.get(&var));
        // None errors are checked when mir-lowering, this isn't necessarily an error
        if let Some(infered_wl) = known.get(&var).and_then(|guess| guess.to_wordlength()) {
            match &ty {
                TypeVar::Known(KnownType::Integer(size), _) => {
                    let typechecker_wl = size.to_u32().unwrap();
                    if typechecker_wl != infered_wl {
                        return Err(error::Error::WordlengthMismatch(typechecker_wl, infered_wl));
                    }
                }
                _ => {}
            }
            to_wordlength_error(inferer.type_state.unify(
                ty,
                &TypeVar::Known(KnownType::Integer(infered_wl.into()), Vec::new()),
                inferer.context.symtab,
            ))?;
        }
    }

    Ok(())
}

fn to_wordlength_error<A>(
    ty_err: Result<A, spade_typeinference::error::UnificationError>,
) -> error::Result<A> {
    match ty_err {
        Ok(v) => Ok(v),
        Err(e) => Err(error::Error::TypeError(e)),
    }
}
