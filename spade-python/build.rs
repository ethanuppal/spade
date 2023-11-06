fn main() {
    if std::env::var_os("SPADE_PYTHON_REBUILD_PROBE").is_some() {
        panic!("Python rebuild probe was run");
    }
}
