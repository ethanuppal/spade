pub trait Indentable {
    fn indent(&self, amount: usize) -> String;
}

impl Indentable for String {
    fn indent(&self, amount: usize) -> String {
        let indentation = (0..amount).map(|_| "    ").collect::<Vec<_>>().join("");
        format!(
            "{}{}",
            indentation,
            self.replace("\n", &format!("\n{}", indentation))
        )
    }
}

pub fn verilog_assign(target: &str, value: &str) -> String {
    format!("assign {} = {};", target, value)
}

pub fn verilog_size(size: u128) -> String {
    if size == 1 {
        format!("")
    } else {
        format!("[{}:0]", size - 1)
    }
}
pub fn verilog_wire(name: &str, size: u128) -> String {
    format!("wire{} {};", verilog_size(size), name)
}
