# AST - Defines the AST types

## BNF

```bnf
<prog> ::= <stmt>*
<stmt> ::= <type_def> | <decl> | <expr> ";"

# Expressions
<expr> ::= <fn_expr> | <block> | <cons_expr> | <match_expr> | <return_expr>
<fn_expr> ::= "fn" <ident> ":" <fn_type> <block>
<fn_type> ::= <type> "->" <type>
<block> ::= "{" <stmt>* "}"
<return_expr> ::= "return" <expr>
<match_expr> ::= "if" <expr> "is" <match_arm>*
<match_arm> ::= <pattern> "=>" <expr>
<cons_expr> ::= <cons_structure> | <cons_tag>
<cons_tag> ::= <ident> <expr>
<cons_structure> ::= "{" <cons_field_list> "}"
<cons_field_list> ::= <cons_field> <cons_field_list_tail>?
<cons_field_list_tail> ::= "," <cons_field_list>?
<cons_field> ::= <ident> <cons_field_rename>?
<cons_field_rename> ::= ":" <ident>
<tag_pattern> ::= <ident> <pattern>?

# Patterns
<pattern> ::= <structure_pattern> | <tag_pattern>
<structure_pattern> ::= "{" <field_pattern_list> "}"

# Type definitions
<type_def> ::= "type" <ident> "=" "alias"? <structural_type> ";"
<structural_type> ::= <tag_union> | <structure>

<tag_union> ::= "[" <tag_list> "]"
<tag_list> ::= <tag> <tag_list_tail>?
<tag_list_tail> ::= "," <tag_list>?
<tag> ::= <ident> <type>

<structure> ::= "{" <field_list> "}"
<field_list> ::= <field> <field_list_tail>?
<field_list_tail> ::= "," <field_list>?
<field> ::= <ident> ":" <type>

# Variable declarations
<decl> ::= <const_decl>
<const_decl> ::= "const" <ident> "=" <expr> ";"
```

## Examples

```txt
type Person = alias {
    name: String,
    age: U32,
};

type Queue a = {
    elems: *a,
    len: Usize,
    cap: Usize,
};

const alves = .{
    name: "Alves",
    age: 23,
};

type Tuple2 = alias { 0: String, 1: U32 };

const greet = fn p : Person -> String {
    return `Hello, ${p.name}`;
};

const add = fn p : {0: U32, 1: U32} -> U32 {
    if p is {
        {0: lhs, 1: rhs} => return lhs + rhs,
    }
};

type Option a = alias [ Some a, None ];

const parseInt = fn s : String -> Option U32 {
    /* ... */
    return None;
    return (Some i)
};

if (parseInt "123") is {
    None => "oh wie shade",
    Some i => "value is " ++ (toString i),
}

const test = fn a : [Some U32, None, OtherShit] -> Unit {
    Unit
};

const ret = test (parseInt "123");

type Result t e = [ Ok t, Err e ];

type MyError = alias [ FileError, NetworkError, ParsingError ];
type MyResult = Result U32 MyError;
```