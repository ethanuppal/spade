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
    #[token("let")]
    Let,
    #[token("reset")]
    Reset,
    #[token("if")]
    If,
    #[token("else")]
    Else,

    #[token("entity")]
    Entity,
    #[token("trait")]
    Trait,
    #[token("fn")]
    Function,

    // Math operators
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Asterisk,
    #[token("/")]
    Slash,
    #[token("==")]
    Equals,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token(">>")]
    RightShift,
    #[token("<<")]
    LeftShift,
    #[token("||")]
    LogicalOr,
    #[token("&&")]
    LogicalAnd,

    // Other operators
    #[token("=")]
    Assignment,

    #[token("(")]
    OpenParen,
    #[token(")")]
    CloseParen,

    #[token("{")]
    OpenBrace,
    #[token("}")]
    CloseBrace,

    #[token("[")]
    OpenBracket,
    #[token("]")]
    CloseBracket,

    #[token("->")]
    SlimArrow,
    #[token(",")]
    Comma,
    #[token(";")]
    Semi,
    #[token(":")]
    Colon,
    #[token("::")]
    PathSeparator,
    #[token("#")]
    Hash,

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

            TokenKind::Let => "let",
            TokenKind::Reg => "reg",
            TokenKind::Entity => "entity",
            TokenKind::Reset => "reset",
            TokenKind::If => "if",
            TokenKind::Else => "else",
            TokenKind::Trait => "trait",
            TokenKind::Function => "fn",

            TokenKind::Assignment => "=",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Asterisk => "*",
            TokenKind::Slash => "/",
            TokenKind::Equals => "==",
            TokenKind::Lt => "<",
            TokenKind::Gt => ">",
            TokenKind::LeftShift => "<<",
            TokenKind::RightShift => ">>",
            TokenKind::LogicalOr => "||",
            TokenKind::LogicalAnd => "&&",

            TokenKind::OpenParen => "(",
            TokenKind::CloseParen => ")",
            TokenKind::OpenBrace => "{",
            TokenKind::CloseBrace => "}",
            TokenKind::OpenBracket => "[",
            TokenKind::CloseBracket => "]",

            TokenKind::SlimArrow => "->",
            TokenKind::Semi => ";",
            TokenKind::Colon => ":",
            TokenKind::Comma => ",",
            TokenKind::PathSeparator => "::",

            TokenKind::Hash => "#",

            TokenKind::Whitespace => "whitespace",
            TokenKind::Comment => "comment",
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
