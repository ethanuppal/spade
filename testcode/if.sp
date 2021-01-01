entity select(cond: bool, a: int[16], b: int[16]) -> int[16] {
    if cond {
        a
    }
    else {
        b
    }
}
