pub fn assign(target: &str, value: &str) -> String {
    format!("assign {} = {};", target, value)
}

pub fn size_spec(size: u64) -> String {
    if size == 1 {
        format!("")
    } else {
        format!("[{}:0]", size - 1)
    }
}

pub fn logic(name: &str, size: u64) -> String {
    format!("logic{} {};", size_spec(size), name)
}
pub fn reg(name: &str, size: u64) -> String {
    format!("reg{} {};", size_spec(size), name)
}
