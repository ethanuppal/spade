use crate::build_entity;
use crate::build_items;

macro_rules! snapshot_verilator_wrapper {
    ($name:ident, $code:expr) => {
    #[test]
        fn $name() {
            let e = build_entity!($code);

            let code = e.verilator_wrapper().unwrap_or_default();

            insta::with_settings!({
                // FIXME: Why can't we set 'description => source' here?
                omit_expression => true,
            }, {
                insta::assert_snapshot!(format!(
                    "{}",
                    code
                ));
            });
        }
    }
}

snapshot_verilator_wrapper! {no_mangle_unit_has_no_wrapper,
    r#"
        fn mangle() {}
    "#
}

snapshot_verilator_wrapper! {wrapper_works,
    r#"
        #[no_mangle]
        fn no_mangle() {}
    "#
}

snapshot_verilator_wrapper! {wrapper_with_input_works,
    r#"
        #[no_mangle]
        fn no_mangle(short: int<32>, wide: int<128>) {}
    "#
}
