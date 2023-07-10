//! # Parser BNF
//!
//! ```ignore
//! <prog> ::= <stmt>*
//! <stmt> ::= <type_def> | <decl> | <expr> ";" | <return_stmt>
//!
//! <return_stmt> ::= "return" <expr> ";"
//!
//! # Expressions
//! <expr> ::= <fn_expr> | <block> | <cons_expr> | <match_expr> | <call_expr> | <access_expr> | <ref_expr> | <lit_expr> | <bin_expr>
//! <fn_expr> ::= "fn" <ident> ":" <fn_type> <block>
//! <fn_type> ::= <type> "->" <type>
//! <block> ::= "{" <stmt>* "}"
//! <match_expr> ::= "if" <expr> "is" <match_arm>*
//! <match_arm> ::= <pattern> "=>" <expr>
//! <cons_expr> ::= <cons_structure> | <cons_tag>
//! <cons_tag> ::= <ident> <expr>
//! <cons_structure> ::= "{" <cons_field_list> "}"
//! <cons_field_list> ::= <cons_field> <cons_field_list_tail>?
//! <cons_field_list_tail> ::= "," <cons_field_list>?
//! <cons_field> ::= <ident> <cons_field_rename>?
//! <cons_field_rename> ::= ":" <ident>
//! <tag_pattern> ::= <ident> <pattern>?
//! <call_expr> ::= <expr> "(" <expr> ")"
//! <access_expr> ::= <expr> "." <ident>
//! <ref_expr> ::= <ident>
//! <bin_expr> ::= <expr> <bin_op> <expr>
//! <bin_op> ::= "+" | "-" | "*" | "/" | "%" | "and" | "or" | "&" | "|" | "<<" | ">>" | "<" | "<=" | ">" | ">=" | "==" | "!="
//!
//! # Patterns
//! <pattern> ::= <structure_pattern> | <tag_pattern>
//! <structure_pattern> ::= "{" <field_pattern_list> "}"
//!
//! # Type definitions
//! <type_def> ::= "type" <ident> "=" "alias"? <structural_type> ";"
//! <structural_type> ::= <tag_union> | <structure>
//!
//! <tag_union> ::= "[" <tag_list> "]"
//! <tag_list> ::= <tag> <tag_list_tail>?
//! <tag_list_tail> ::= "," <tag_list>?
//! <tag> ::= <ident> <type>
//!
//! <structure> ::= "{" <field_list> "}"
//! <field_list> ::= <field> <field_list_tail>?
//! <field_list_tail> ::= "," <field_list>?
//! <field> ::= <ident> ":" <type>
//!
//! # Variable declarations
//! <decl> ::= <const_decl>
//! <const_decl> ::= "const" <ident> "=" <expr> ";"
//! ```


use logos::Logos;

#[derive(Logos, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+")]
pub enum Token<'a> {
    // #[token("mut")]
    // Mut,
    #[token("const")]
    Const,

    #[token("=")]
    Assing,
    #[token(".")]
    Dot,

    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token(";")]
    Semi,

    #[token("+")]
    Add,
    #[token("-")]
    Sub,
    #[token("*")]
    Mul,
    #[token("/")]
    Div,
    #[token("%")]
    Mod,
    // #[token("**")]
    // Pow,

    #[token("<")]
    Less,
    #[token("<=")]
    LessEqual,
    #[token(">")]
    Greater,
    #[token(">=")]
    GreaterEqual,
    #[token("==")]
    Equal,
    #[token("!=")]
    NotEqual,

    // #[token("not")]
    // Not,
    #[token("and")]
    And,
    #[token("or")]
    Or,

    // #[token("~")]
    // BitNot,
    #[token("&")]
    BitAnd,
    #[token("|")]
    BitOr,
    // #[token("^")]
    // Xor,
    #[token("<<")]
    ShiftLeft,
    #[token(">>")]
    ShiftRight,

    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token("[")]
    LeftBracket,
    #[token("]")]
    RightBracket,
    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,

    #[token("is")]
    Is,
    #[token("=>")]
    Match,

    #[token("if")]
    If,
    // #[token("else")]
    // Else,

    #[token("->")]
    Arrow,

    #[token("fn")]
    Fn,
    #[token("return")]
    Return,

    #[token("type")]
    Type,
    #[token("alias")]
    Alias,

    // #[token("true")]
    // True,
    // #[token("false")]
    // False,

    // #[token("//")]
    // Comment,

    #[regex("[_a-zA-Z][_a-zA-Z0-9]*")]
    Ident(&'a str),

    #[regex("[0-9]+(\\.[0-9]+)?(e[+-]?[0-9]+)?", |lex| lex.slice().parse().ok())]
    Number(f64),
}


#[cfg(test)]
mod test {
    use super::*;


    #[test]
    fn math_ops() {
        assert_eq!(Token::lexer("\t+\t-\t*\t/\t%\t").collect::<Result<Vec<_>, _>>().unwrap(), [
            Token::Add,
            Token::Sub,
            Token::Mul,
            Token::Div,
            Token::Mod,
        ]);
    }

    #[test]
    fn compare_ops() {
        assert_eq!(Token::lexer("\n<\n<=\n>\n>=\n==\n!=\n").collect::<Result<Vec<_>, _>>().unwrap(), [
            Token::Less,
            Token::LessEqual,
            Token::Greater,
            Token::GreaterEqual,
            Token::Equal,
            Token::NotEqual,
        ]);
    }

    #[test]
    fn boolean_ops() {
        assert_eq!(Token::lexer(" and or ").collect::<Result<Vec<_>, _>>().unwrap(), [
            Token::And,
            Token::Or,
        ]);
    }

    #[test]
    fn bit_ops() {
        assert_eq!(Token::lexer("&\r\n|\r\n<<\r\n>>").collect::<Result<Vec<_>, _>>().unwrap(), [
            Token::BitAnd,
            Token::BitOr,
            Token::ShiftLeft,
            Token::ShiftRight,
        ]);
    }

    #[test]
    fn idents() {
        assert_eq!(Token::lexer("_ __ a bc DE_ _0 F_1").collect::<Result<Vec<_>, _>>().unwrap(), [
            Token::Ident("_"),
            Token::Ident("__"),
            Token::Ident("a"),
            Token::Ident("bc"),
            Token::Ident("DE_"),
            Token::Ident("_0"),
            Token::Ident("F_1"),
        ]);
    }

    #[test]
    fn numbers() {
        assert_eq!(Token::lexer("0 10.01 5e2 0e+10 3.5e-5").collect::<Result<Vec<_>, _>>().unwrap(), [
                Token::Number(0.0),
                Token::Number(10.01),
                Token::Number(5e2),
                Token::Number(0e+10),
                Token::Number(3.5e-5),
        ]);
    }

    #[test]
    fn pseudo_numbers() {
        assert_eq!(Token::lexer("1. .2 3e e4 5_").collect::<Result<Vec<_>, _>>().unwrap(), [
            Token::Number(1.0),
            Token::Dot,

            Token::Dot,
            Token::Number(2.0),

            Token::Number(3.0),
            Token::Ident("e"),

            Token::Ident("e4"),

            Token::Number(5.0),
            Token::Ident("_")
        ]);
    }

    #[test]
    fn fn_decl() {
        assert_eq!(Token::lexer("fn func : Number -> Number {\nreturn 0;\n}").collect::<Result<Vec<_>, _>>().unwrap(), [
                Token::Fn,
                Token::Ident("func"),
                Token::Colon,
                Token::Ident("Number"),
                Token::Arrow,
                Token::Ident("Number"),
                Token::LeftBrace,
                Token::Return,
                Token::Number(0.0),
                Token::Semi,
                Token::RightBrace,
        ]);
    }

    #[test]
    fn call() {
        assert_eq!(Token::lexer("math.lerp(1.5, 3, 0.2);").collect::<Result<Vec<_>, _>>().unwrap(), [
            Token::Ident("math"),
            Token::Dot,
            Token::Ident("lerp"),
            Token::LeftParen,
            Token::Number(1.5),
            Token::Comma,
            Token::Number(3.0),
            Token::Comma,
            Token::Number(0.2),
            Token::RightParen,
            Token::Semi,
        ]);
    }

    #[test]
    fn if_match() {
        assert_eq!(Token::lexer("if age is 18 => return -1;").collect::<Result<Vec<_>, _>>().unwrap(), [
            Token::If,
            Token::Ident("age"),
            Token::Is,
            Token::Number(18.0),
            Token::Match,
            Token::Return,
            Token::Sub,
            Token::Number(1.0),
            Token::Semi,
        ]);
    }

    #[test]
    fn const_decl() {
        assert_eq!(Token::lexer("const result = 1 and 0;").collect::<Result<Vec<_>, _>>().unwrap(), [
                Token::Const,
                Token::Ident("result"),
                Token::Assing,
                Token::Number(1.0),
                Token::And,
                Token::Number(0.0),
                Token::Semi,
        ]);
    }

    #[test]
    fn type_def() {
        assert_eq!(Token::lexer("type Info = [\nname String, age Number\n];").collect::<Result<Vec<_>, _>>().unwrap(), [
                Token::Type,
                Token::Ident("Info"),
                Token::Assing,
                Token::LeftBracket,
                Token::Ident("name"),
                Token::Ident("String"),
                Token::Comma,
                Token::Ident("age"),
                Token::Ident("Number"),
                Token::RightBracket,
                Token::Semi,
        ]);
    }
}
