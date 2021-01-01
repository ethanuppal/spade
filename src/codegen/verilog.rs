pub fn assign(target: &str, value: &str) -> String {
    format!("assign {} = {};", target, value)
}

pub fn size_spec(size: u128) -> String {
    if size == 1 {
        format!("")
    } else {
        format!("[{}:0]", size - 1)
    }
}

pub fn wire(name: &str, size: u128) -> String {
    format!("wire{} {};", size_spec(size), name)
}
