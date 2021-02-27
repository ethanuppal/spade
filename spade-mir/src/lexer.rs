/*
use logos::Logos;

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum TokenKind {
    // Unholy regex for unicode identifiers. Stolen from Repnop who stole it from Evrey
    #[regex(r#"(?x:
        [\p{XID_Start}_]
        \p{XID_Continue}*
        (\u{3F} | \u{21} | (\u{3F}\u{21}) | \u{2048})? # ? ! ?! ⁈
    )"#, |lex| lex.slice().to_string())]
    Identifier(String),

    #[regex(r"n(0x|0b)?[0-9][0-9_]*", |lex| {
        u64::from_str_radix(&lex.slice(), 10)
    })]
    NameID(u64),
    #[regex(r"e(0x|0b)?[0-9][0-9_]*", |lex| {
        u64::from_str_radix(&lex.slice(), 10)
    })]
    ExprID(u64),

    #[regex(r"(0x|0b)?[0-9][0-9_]*", |lex| {
        let without_under = lex.slice().replace("_", "");

        if without_under.starts_with("0x") {
            u128::from_str_radix(&without_under[2..], 16)
        }
        else if without_under.starts_with("0b") {
            u128::from_str_radix(&without_under[2..], 2)
        }
        else {
            u128::from_str_radix(&without_under, 10)
        }
    })]
    Integer(u128),

    #[token("true")]
    True,
    #[token("false")]
    False,

    // Keywords
    #[token("reg")]
    Reg,

    // Other operators
    #[token("=")]
    Assignment,

    /// Ignoring whitespace
    #[regex("[ \t\n\r]", logos::skip)]
    Whitespace,

    #[regex("//[^\n]*\n", logos::skip)]
    Comment,

    #[error]
    Error,
}

impl TokenKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            TokenKind::Identifier(_) => "identifier",
            TokenKind::Integer(_) => "integer",
            TokenKind::True => "true",
            TokenKind::False => "false",

            TokenKind::Reg => "reg",

            TokenKind::Assignment => "=",

            TokenKind::Whitespace => "whitespace",
            TokenKind::Comment => "comment",
            TokenKind::Error => "error",
        }
    }

    pub fn is_reg_id(&self) -> bool {
        matches!(self, TokenKind::ExprID(_))
    }
    pub fn is_name_id(&self) -> bool {
        matches!(self, TokenKind::NameID(_))
    }

    pub fn is_identifier(&self) -> bool {
        matches!(self, TokenKind::Identifier(_))
    }
    pub fn is_integer(&self) -> bool {
        matches!(self, TokenKind::Integer(_))
    }

    pub fn is_ident(&self) -> bool {
        if let TokenKind::Identifier(_) = self {
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifiers_work() {
        let mut lex = TokenKind::lexer("abc123_");

        assert_eq!(
            lex.next(),
            Some(TokenKind::Identifier("abc123_".to_string()))
        );
    }

    #[test]
    fn integer_literals_work() {
        let mut lex = TokenKind::lexer("123");

        assert_eq!(lex.next(), Some(TokenKind::Integer(123)));
        assert_eq!(lex.next(), None);
    }
}
*/
