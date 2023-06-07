//! Impls for AST types

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
