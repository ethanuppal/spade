use crate::snapshot_error;

snapshot_error! {
    stage_outside_pipeline,
    "
    entity main(x: X) -> int<8> {
        reg;
    }
    "
}
