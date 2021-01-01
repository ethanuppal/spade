pub trait Indentable {
    fn indent(&self, amount: usize) -> Vec<String>;

    fn indent_chars(amount: usize) -> String {
        (0..amount).map(|_| "    ").collect::<Vec<_>>().join("")
    }
}

impl Indentable for String {
    fn indent(&self, amount: usize) -> Vec<String> {
        self.get_lines().indent(amount)
    }
}

impl Indentable for Vec<String> {
    fn indent(&self, amount: usize) -> Vec<String> {
        let indentation = Self::indent_chars(amount);
        self.iter()
            .cloned()
            .map(|l| format!("{}{}", indentation, l))
            .collect()
    }
}

pub trait HasLines {
    fn get_lines(&self) -> Vec<String>;
}
impl HasLines for String {
    fn get_lines(&self) -> Vec<String> {
        self.split("\n").map(String::from).collect()
    }
}
impl HasLines for &str {
    fn get_lines(&self) -> Vec<String> {
        self.split("\n").map(String::from).collect()
    }
}
impl HasLines for Vec<String> {
    fn get_lines(&self) -> Vec<String> {
        self.clone()
    }
}
impl HasLines for Code {
    fn get_lines(&self) -> Vec<String> {
        self.lines.clone()
    }
}

pub struct Code {
    lines: Vec<String>,
}

impl Code {
    pub fn new() -> Self {
        Code { lines: vec![] }
    }

    pub fn to_string(&self) -> String {
        self.lines.join("\n")
    }

    pub fn join(&mut self, other: &impl HasLines) {
        self.lines.append(&mut other.get_lines())
    }

    pub fn join_indent(&mut self, amount: usize, other: &impl HasLines) {
        self.lines.append(&mut other.get_lines().indent(amount))
    }
}

#[macro_export]
macro_rules! code {
    ($code:ident, [$amount:expr] $lines:expr) => {
        $code.join_indent($amount, $lines);
    };
    ($code:ident, [$amount:expr] $lines:expr$(; $([$r_amount:expr] $r_lines:expr);*)?) => {
        code!{$code, [$amount] $lines};
        $(code!{$code, $([$r_amount] $r_lines);*})?
    };
    ($([$r_amount:expr] $r_lines:expr);*) =>{
        {
            let mut code = Code::new();
            code!{code, $([$r_amount] $r_lines);*};
            code
        }
    }
}
