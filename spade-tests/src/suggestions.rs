use crate::snapshot_error;

snapshot_error!(
    suggest_add_array_size,
    r#"
    entity main() {
        let _: [bool] = [true, false];
    }
    "#
);
