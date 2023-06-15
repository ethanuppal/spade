use spade::Artefacts;
use spade_common::{location_info::WithLocation, name::Path, num_ext::InfallibleToBigUint};
use spade_hir_lowering::MirLowerable;
use spade_mir::{renaming::VerilogNameSource, types::Type};
use spade_typeinference::{equation::TypedExpression, TypeState};

use crate::build_artifacts;

fn get_field_type(artefacts: &Artefacts, target_name: &str) -> Type {
    let (name, _) = artefacts
        .state
        .symtab
        .symtab()
        .lookup_unit(&Path::from_strs(&["main"]).nowhere())
        .unwrap();

    // Look up the mir context of the unit we are observing
    let mir_ctx = artefacts
        .state
        .mir_context
        .get(&name)
        .expect(&format!("Did not find information a unit named `main`"));

    let source = mir_ctx
        .verilog_name_map
        .lookup_name(target_name)
        .expect(&format!(
            "Did not find spade variable for verilog identifier '{target_name}'"
        ));

    let typed_expr = match source {
        VerilogNameSource::ForwardName(n) => TypedExpression::Name(n.clone()),
        VerilogNameSource::ForwardExpr(id) => TypedExpression::Id(*id),
        VerilogNameSource::BackwardName(_) | VerilogNameSource::BackwardExpr(_) => {
            panic!("Translation of backward port types is unsupported")
        }
    };

    let ty = mir_ctx
        .type_map
        .type_of(&typed_expr)
        .expect(&format!("Did not find a type for {typed_expr}"));

    let mir_ty = TypeState::ungenerify_type(
        ty,
        artefacts.state.symtab.symtab(),
        &artefacts.state.item_list.types,
    )
    .expect(&format!("Tried to ungenerify generic type {ty}"))
    .to_mir_type();

    mir_ty
}

// NOTE: This tests do_wal_trace_lowering, in particular some hacky code being performed
// there. If these tests fail, it might be time to clean stuff up
#[test]
fn wal_traced_struct_with_multiple_backward_ports_has_type_information() {
    let code = r#"
        #[wal_traceable(suffix = wal_suffix__)]
        struct port Test {
            a: &int<8>,
            b: &mut int<4>,
            c: &int<16>,
            d: &mut int<7>
        }

        entity main(x: Test) -> Test {
            #[wal_trace]
            let y = x;
            y
        }
    "#;

    let artefacts = build_artifacts(code, true);

    assert_eq!(
        get_field_type(&artefacts, "y__a__wal_suffix__"),
        Type::Int(8u64.to_biguint())
    );
    assert_eq!(
        get_field_type(&artefacts, "y__b__wal_suffix__"),
        Type::Int(4u64.to_biguint())
    );
    assert_eq!(
        get_field_type(&artefacts, "y__c__wal_suffix__"),
        Type::Int(16u64.to_biguint())
    );
    assert_eq!(
        get_field_type(&artefacts, "y__d__wal_suffix__"),
        Type::Int(7u64.to_biguint())
    );
}
