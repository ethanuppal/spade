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

pub fn verilog_wire(name: &str, size: u128) -> String {
    format!("wire[{}:0] {};", size - 1, name)
}
