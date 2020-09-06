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

    #[regex(r"\d+", |lex| lex.slice().parse())]
    Integer(u128),

    // Keywords
    #[token("let")]
    Let,

    // Math operators
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Multiplication,
    #[token("/")]
    Division,

    // Other operators
    #[token("=")]
    Assignment,


    #[token("(")]
    OpenParen,
    #[token(")")]
    CloseParen,

    #[token(";")]
    Semi,
    #[token(":")]
    Colon,

    #[regex("[ \t\n\r]", logos::skip)]
    Whitespace,

    // Ignoring whitespace
    #[error]
    Error,
}

impl TokenKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            TokenKind::Identifier(_) => "identifier",
            TokenKind::Integer(_) => "integer",
            TokenKind::Let => "let",
            TokenKind::Assignment => "=",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Multiplication => "*",
            TokenKind::Division => "/",
            TokenKind::OpenParen => "(",
            TokenKind::CloseParen => ")",
            TokenKind::Semi => ";",
            TokenKind::Colon => ":",
            TokenKind::Whitespace => "whitespace",
            TokenKind::Error => "error",
        }
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
        }
        else {
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

        assert_eq!(lex.next(), Some(TokenKind::Identifier("abc123_".to_string())));
    }

    #[test]
    fn integer_literals_work() {
        let mut lex = TokenKind::lexer("123");

        assert_eq!(lex.next(), Some(TokenKind::Integer(123)));
        assert_eq!(lex.next(), None);
    }
}
