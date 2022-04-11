use crate::snapshot_error;

snapshot_error! {
    duplicate_definition_of_decl_triggers_errors,
    "
    entity X() -> int<8> {
        decl x;
        let x = 0;
        let x = 1;
        x
    }
    "
}

snapshot_error! {
    declaration_without_definition_triggers_error,
    "
    entity X() -> int<8> {
        decl x;
        x
    }
    "
}

snapshot_error! {
    declaration_after_let_requires_new_definition,
    "
    entity X() -> int<8> {
        let x: int<8> = 0;
        decl x;
        x
    }
    "
}

snapshot_error! {
    negative_stage_index,
    "
    pipeline(3) main(x: int<8>) -> int<8> {
            let a = stage(-1).x;
        reg;
        reg;
        reg;
            0
    }
    "
}

snapshot_error! {
    stage_index_overflow,
    "
    pipeline(3) main(x: int<8>) -> int<8> {
        reg;
        reg;
        reg;
            stage(+1).x
    }
    "
}

snapshot_error! {
    duplicate_label_error,
    "
    pipeline(3) main(clk: clk) -> int<8> {
        reg;
            'a
        reg;
            'a
        reg;
            0
    }"
}

snapshot_error! {
    undefined_label_error,
    "
    pipeline(3) main(clk: clk) -> int<8> {
        reg;
            'a
            let x = 0;
        reg;
        reg;
            stage(b).x
    }"
}

snapshot_error! {
    multiple_labels_for_same_stage,
    "
    pipeline(3) main(clk: clk) -> int<8> {
        reg;
            'a
            'b
        reg;
        reg;
            0
    }"
}
