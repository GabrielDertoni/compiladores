//! Impls for AST types

use std::borrow::Borrow;

use crate::*;

impl BinOp {
    // Largely copied from https://en.cppreference.com/w/c/language/operator_precedence
    pub fn precedence(&self) -> u8 {
        use BinOp::*;

        match self {
            Mul | Div | Mod => 3,
            Add | Sub => 4,
            ShiftLeft | ShiftRight => 5,
            Less | LessEqual | Greater | GreaterEqual => 6,
            Equal | NotEqual => 7,
            BitAnd => 8,
            BitOr => 10,
            And => 11,
            Or => 12,
        }
    }
}

impl Type {
    pub fn unit() -> Self {
        TypeRef::unit().into()
    }

    pub fn string() -> Self {
        TypeRef::string().into()
    }

    pub fn number() -> Self {
        TypeRef::number().into()
    }

    pub fn bool() -> Self {
        TypeRef::bool().into()
    }
}

impl From<TypeRef> for Type {
    fn from(value: TypeRef) -> Self {
        Type::Ref(value)
    }
}

impl From<TagUnionDef> for Type {
    fn from(value: TagUnionDef) -> Self {
        Type::TagUnion(value)
    }
}

impl From<StructureDef> for Type {
    fn from(value: StructureDef) -> Self {
        Type::Structure(value)
    }
}

impl From<FnType> for Type {
    fn from(value: FnType) -> Self {
        Type::Fn(value)
    }
}

impl TypeRef {
    pub fn unit() -> Self {
        TypeRef {
            name: "Unit".into(),
            generic_args: Vec::new(),
        }
    }

    pub fn string() -> Self {
        TypeRef {
            name: "String".into(),
            generic_args: Vec::new(),
        }
    }

    pub fn number() -> Self {
        TypeRef {
            name: "Number".into(),
            generic_args: Vec::new(),
        }
    }

    pub fn bool() -> Self {
        TypeRef {
            name: "Bool".into(),
            generic_args: Vec::new(),
        }
    }
}

impl TagUnionDef {
    pub fn singleton(tag: TagDef) -> Self {
        TagUnionDef {
            variants: vec![tag],
        }
    }
}

impl From<StructurePattern> for Pattern {
    fn from(value: StructurePattern) -> Self {
        Pattern::Structure(value)
    }
}

impl From<TagPattern> for Pattern {
    fn from(value: TagPattern) -> Self {
        Pattern::Tag(value)
    }
}

impl From<String> for Ident {
    fn from(value: String) -> Self {
        Ident(value)
    }
}

impl From<&str> for Ident {
    fn from(value: &str) -> Self {
        Ident(value.to_string())
    }
}

impl Borrow<str> for Ident {
    fn borrow(&self) -> &str {
        self.0.as_str()
    }
}
