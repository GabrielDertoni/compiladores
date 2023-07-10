use logos::Logos;

/// <prog> ::= <stmt>*
/// <stmt> ::= <type_def> | <decl> | <expr> ";" | <return_stmt>
///
/// <return_stmt> ::= "return" <expr> ";"
///
/// # Expressions
/// <expr> ::= <fn_expr> | <block> | <cons_expr> | <match_expr> | <call_expr> | <access_expr> | <ref_expr> | <lit_expr> | <bin_expr>
/// <fn_expr> ::= "fn" <ident> ":" <fn_type> <block>
/// <fn_type> ::= <type> "->" <type>
/// <block> ::= "{" <stmt>* "}"
/// <match_expr> ::= "if" <expr> "is" <match_arm>*
/// <match_arm> ::= <pattern> "=>" <expr>
/// <cons_expr> ::= <cons_structure> | <cons_tag>
/// <cons_tag> ::= <ident> <expr>
/// <cons_structure> ::= "{" <cons_field_list> "}"
/// <cons_field_list> ::= <cons_field> <cons_field_list_tail>?
/// <cons_field_list_tail> ::= "," <cons_field_list>?
/// <cons_field> ::= <ident> <cons_field_rename>?
/// <cons_field_rename> ::= ":" <ident>
/// <tag_pattern> ::= <ident> <pattern>?
/// <call_expr> ::= <expr> "(" <expr> ")"
/// <access_expr> ::= <expr> "." <ident>
/// <ref_expr> ::= <ident>
/// <bin_expr> ::= <expr> <bin_op> <expr>
/// <bin_op> ::= "+" | "-" | "*" | "/" | "%" | "and" | "or" | "&" | "|" | "<<" | ">>" | "<" | "<=" | ">" | ">=" | "==" | "!="
///
/// # Patterns
/// <pattern> ::= <structure_pattern> | <tag_pattern>
/// <structure_pattern> ::= "{" <field_pattern_list> "}"
///
/// # Type definitions
/// <type_def> ::= "type" <ident> "=" "alias"? <structural_type> ";"
/// <structural_type> ::= <tag_union> | <structure>
///
/// <tag_union> ::= "[" <tag_list> "]"
/// <tag_list> ::= <tag> <tag_list_tail>?
/// <tag_list_tail> ::= "," <tag_list>?
/// <tag> ::= <ident> <type>
///
/// <structure> ::= "{" <field_list> "}"
/// <field_list> ::= <field> <field_list_tail>?
/// <field_list_tail> ::= "," <field_list>?
/// <field> ::= <ident> ":" <type>
///
/// # Variable declarations
/// <decl> ::= <const_decl>
/// <const_decl> ::= "const" <ident> "=" <expr> ";"
///
#[derive(Logos, Debug, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
enum Token<'a> {
    #[token("return")]
    Return,
    #[token("const")]
    Const,
    #[regex("[a-zA-Z_][a-zA-Z_0-9]*")]
    Ident(&'a str),
    #[regex("[0-9]+", |lex| lex.slice().parse().ok())]
    Number(f64),
    #[token(":")]
    Colon,
    #[token(";")]
    Semi,
    #[token("=")]
    Equal,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test1() {
        let lexer = Token::lexer("const a: Number = 3;");
        let tokens = lexer.collect::<Result<Vec<_>, _>>().unwrap();
        assert_eq!(
            tokens,
            [
                Token::Const,
                Token::Ident("a"),
                Token::Colon,
                Token::Ident("Number"),
                Token::Equal,
                Token::Number(3.0),
                Token::Semi
            ]
        )
    }
}
