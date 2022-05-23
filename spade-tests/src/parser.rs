use crate::snapshot_error;

snapshot_error! {
    stage_outside_pipeline,
    "
    entity main(x: X) -> int<8> {
        reg;
    }
    "
}

snapshot_error! {
    register_count_is_required,
    "
    pipeline(3) main(x: X) -> int<8> {
        reg *;
    }
    "
}
