//! The type checker
//!
//! This module is responsible for checking and resolving the types of a program.

use std::{borrow::Borrow, collections::HashMap, hash::Hash};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Scope(usize);

impl Scope {
    pub fn enter(&mut self) {
        self.0 += 1;
    }

    pub fn exit(&mut self) {
        self.0 -= 1;
    }
}

// Very inspired by https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html
pub struct TyCx {
    types: HashMap<ast::Ident, (ast::TypeDef, Scope)>,
    variables: HashMap<ast::Ident, (ast::TypeRef, Scope)>,
    curr_scope: Scope,
}

impl TyCx {
    pub fn new() -> Self {
        TyCx {
            types: HashMap::new(),
            variables: HashMap::new(),
            curr_scope: Scope(0),
        }
    }

    pub fn scope<T>(&mut self, cont: impl FnOnce(&mut Self) -> T) -> T {
        self.curr_scope.enter();
        let ret = cont(self);
        // Remove everything added for the exited scope
        self.curr_scope.exit();
        self.types
            .retain(|_, &mut (_, scope)| scope <= self.curr_scope);
        self.variables
            .retain(|_, &mut (_, scope)| scope <= self.curr_scope);
        ret
    }

    pub fn lookup_var<'a, Q>(&'a self, name: &Q) -> Result<&'a ast::TypeRef>
    where
        ast::Ident: Borrow<Q>,
        Q: Into<ast::Ident> + Clone + Eq + Hash,
    {
        self.variables
            .get(name)
            .map(|(ty, _)| ty)
            .ok_or_else(|| Error::UndefinedVar(name.clone().into()))
    }

    pub fn add_var(&mut self, name: &ast::Ident, ty: &ast::TypeRef) -> Result<()> {
        self.check_type_ref(ty)?;
        self.variables
            .insert(name.clone(), (ty.clone(), self.curr_scope));
        Ok(())
    }

    pub fn add_type_def(&mut self, def: &ast::TypeDef) -> Result<()> {
        self.check_type_def(def)?;
        self.types
            .insert(def.name.clone(), (def.clone(), self.curr_scope));
        Ok(())
    }

    pub fn check_expr(&mut self, expr: &ast::Expr) -> Result<ast::Type> {
        match expr.kind.as_ref() {
            ast::ExprKind::Fn(expr) => self.check_fn_expr(expr),
            ast::ExprKind::Block(expr) => self.check_block_expr(expr),
            ast::ExprKind::Cons(expr) => self.check_cons_expr(expr),
            ast::ExprKind::Match(expr) => self.check_match_expr(expr),
            ast::ExprKind::Call(expr) => self.check_call_expr(expr),
            ast::ExprKind::Access(expr) => self.check_access_expr(expr),
            ast::ExprKind::Ref(expr) => self.check_ref_expr(expr),
            ast::ExprKind::Literal(expr) => self.check_literal_expr(expr),
            ast::ExprKind::Bin(expr) => self.check_bin_expr(expr),
        }
    }

    pub fn check_fn_expr(&mut self, expr: &ast::FnExpr) -> Result<ast::Type> {
        self.scope(|tcx| {
            tcx.add_var(&expr.arg, &expr.ty.argument)?;
            let actual_ret_type = tcx.check_block_expr(&expr.body)?;
            let ret_ty = tcx.deref_type(&expr.ty.ret)?;
            tcx.assert_same_type(&actual_ret_type, &ret_ty)?;
            Ok(())
        })?;
        Ok(ast::Type::Fn(expr.ty.clone()))
    }

    pub fn check_block_expr(&mut self, expr: &ast::BlockExpr) -> Result<ast::Type> {
        let ret_type = None;
        for stmt in &expr.stmts {
            if let ast::Stmt::Return(ret) = stmt {
                let ty = self.check_expr(&ret.expr)?;
                if let Some(ret_type) = ret_type.as_ref() {
                    self.assert_same_type(ret_type, &ty)?;
                }
            } else {
                self.check_stmt(stmt)?;
            }
        }
        Ok(ret_type.unwrap_or(ast::Type::unit()))
    }

    pub fn check_cons_expr(&mut self, expr: &ast::ConsExpr) -> Result<ast::Type> {
        match expr {
            ast::ConsExpr::ConsStructure(structure) => self.check_cons_structure(structure),
            ast::ConsExpr::ConsTag(tag) => self.check_cons_tag(tag),
        }
    }

    pub fn check_cons_structure(&mut self, structure: &ast::ConsStructure) -> Result<ast::Type> {
        Ok(ast::Type::Structure(ast::StructureDef {
            fields: structure
                .fields
                .iter()
                .map(|field| {
                    Ok(ast::StructureFieldDef {
                        field: field.name.clone(),
                        ty: Box::new(self.check_expr(&field.value)?),
                    })
                })
                .collect::<Result<_>>()?,
        }))
    }

    pub fn check_cons_tag(&mut self, tag: &ast::ConsTag) -> Result<ast::Type> {
        Ok(ast::Type::TagUnion(ast::TagUnionDef::singleton(
            ast::TagDef {
                name: tag.tag.clone(),
                value: tag
                    .value
                    .as_ref()
                    .map(|value| self.check_expr(value))
                    .transpose()?
                    .map(Box::new),
            },
        )))
    }

    pub fn check_match_expr(&mut self, expr: &ast::MatchExpr) -> Result<ast::Type> {
        let scrutinee_ty = self.check_expr(&expr.scrutinee)?;
        let ty = None;
        for arm in &expr.arms {
            self.check_pattern(&arm.pattern, &scrutinee_ty)?;
            let expr_ty = self.check_expr(&arm.expr)?;
            if let Some(ty) = ty.as_ref() {
                self.assert_same_type(&expr_ty, ty)?;
            }
        }
        ty.ok_or_else(|| Error::EmptyMatch)
    }

    fn check_call_expr(&mut self, expr: &ast::CallExpr) -> Result<ast::Type> {
        let fn_ty = self.check_expr(&expr.callee)?;
        let fn_ty = match fn_ty {
            ast::Type::Fn(fn_ty) => fn_ty,
            otherwise => return Err(Error::ExpectedFnType(otherwise)),
        };
        let arg_ty = self.check_expr(&expr.arg)?;
        let expected_arg_ty = self.deref_type(&fn_ty.argument)?;
        self.assert_same_type(&expected_arg_ty, &arg_ty)?;
        self.deref_type(&fn_ty.ret).map(ToOwned::to_owned)
    }

    fn check_access_expr(&mut self, expr: &ast::AccessExpr) -> Result<ast::Type> {
        let mut struct_ty = self.check_expr(&expr.value)?;
        loop {
            match struct_ty {
                ast::Type::Ref(ty_ref) => {
                    struct_ty = self.deref_type(&ty_ref).map(ToOwned::to_owned)?
                }
                ast::Type::TagUnion(_) | ast::Type::Fn(_) => {
                    return Err(Error::InvalidAccess(struct_ty, expr.field.to_owned()))
                }
                ast::Type::Structure(structure) => {
                    return {
                        if let Some(field) = structure
                            .fields
                            .iter()
                            .find(|field| field.field == expr.field)
                        {
                            Ok(field.ty.as_ref().clone())
                        } else {
                            Err(Error::InvalidAccess(
                                structure.into(),
                                expr.field.to_owned(),
                            ))
                        }
                    }
                }
            }
        }
    }

    fn check_ref_expr(&self, expr: &ast::RefExpr) -> Result<ast::Type> {
        let ty = self.lookup_var(&expr.ident)?;
        self.deref_type(ty).map(ToOwned::to_owned)
    }

    fn check_literal_expr(&self, expr: &ast::LiteralExpr) -> Result<ast::Type> {
        match expr {
            ast::LiteralExpr::String(_) => Ok(ast::Type::string()),
            ast::LiteralExpr::Number(_) => Ok(ast::Type::number()),
        }
    }

    fn check_bin_expr(&mut self, expr: &ast::BinExpr) -> Result<ast::Type> {
        use ast::BinOp::*;
        use BuiltinType::*;

        let lhs_ty = self.check_expr(&expr.lhs)?;
        let rhs_ty = self.check_expr(&expr.rhs)?;
        match (lhs_ty.try_into()?, &expr.op, rhs_ty.try_into()?) {
            (Number, Add, Number)
            | (Number, Sub, Number)
            | (Number, Mul, Number)
            | (Number, Div, Number)
            | (Number, Mod, Number)
            | (Number, BitAnd, Number)
            | (Number, BitOr, Number)
            | (Number, ShiftLeft, Number)
            | (Number, ShiftRight, Number) => Ok(Number.into()),
            (Bool, And, Bool) | (Bool, Or, Bool) => Ok(Bool.into()),
            (Number, Less, Number)
            | (Number, LessEqual, Number)
            | (Number, Greater, Number)
            | (Number, GreaterEqual, Number)
            | (Number, Equal, Number)
            | (Number, NotEqual, Number) => Ok(Bool.into()),
            (lhs, _, rhs) => Err(Error::IncompatibleTypes(lhs.into(), rhs.into())),
        }
    }

    /// Tries to get a type from a pattern. If the pattern is catchall, any type is valid, and so it returns `None`.
    fn check_pattern(&self, patt: &ast::Pattern, expected: &ast::Type) -> Result<()> {
        match (patt, expected) {
            (ast::Pattern::Structure(patt), ast::Type::Structure(expected)) => {
                self.check_structure_pattern(patt, expected)
            }
            (ast::Pattern::Tag(patt), ast::Type::TagUnion(expected)) => {
                self.check_tag_pattern(patt, expected)
            }
            (ast::Pattern::Catchall, _) => Ok(()),
            (patt, expected) => Err(Error::IncompatiblePattern(
                patt.to_owned(),
                expected.to_owned(),
            )),
        }
    }

    fn check_structure_pattern(
        &self,
        patt: &ast::StructurePattern,
        expected: &ast::StructureDef,
    ) -> Result<()> {
        use std::collections::HashSet;

        let fields_pat = patt.fields.iter().collect::<HashSet<_>>();
        let fields_expected = expected
            .fields
            .iter()
            .map(|field| &field.field)
            .collect::<HashSet<_>>();

        if fields_pat == fields_expected {
            Ok(())
        } else {
            Err(Error::IncompatiblePattern(
                patt.to_owned().into(),
                expected.to_owned().into(),
            ))
        }
    }

    fn check_tag_pattern(&self, patt: &ast::TagPattern, expected: &ast::TagUnionDef) -> Result<()> {
        if let Some(_) = expected
            .variants
            .iter()
            .find(|variant| variant.name == patt.name)
        {
            Ok(())
        } else {
            Err(Error::IncompatiblePattern(
                patt.to_owned().into(),
                expected.to_owned().into(),
            ))
        }
    }

    pub fn check_stmt(&mut self, stmt: &ast::Stmt) -> Result<()> {
        match stmt {
            ast::Stmt::TypeDef(def) => self.check_type_def(def),
            ast::Stmt::Expr(expr) => {
                self.check_expr(expr)?;
                // Ignore the type here, since we are in a statement, the result of the expression will be ignored.
                Ok(())
            }
            ast::Stmt::Decl(decl) => self.check_decl(decl),
            ast::Stmt::Return(ret) => self.check_return_stmt(ret),
        }
    }

    fn check_decl(&mut self, decl: &ast::Decl) -> Result<()> {
        let ty = self.check_expr(&decl.value)?;
        self.assert_same_type(&ty, self.deref_type(decl.ty.as_ref())?)?;
        self.add_var(&decl.name, &decl.ty)
    }

    fn check_return_stmt(&mut self, ret: &ast::ReturnStmt) -> Result<()> {
        self.check_expr(&ret.expr)?;
        Ok(())
    }

    pub fn check_type_def(&self, def: &ast::TypeDef) -> Result<()> {
        self.check_type(&def.structural_type)
    }

    pub fn check_type(&self, ty: &ast::Type) -> Result<()> {
        match ty {
            ast::Type::Ref(ty) => self.check_type_ref(ty)?,
            ast::Type::TagUnion(tag_union) => {
                for variant in &tag_union.variants {
                    self.check_tag_def(variant)?;
                }
            }
            ast::Type::Structure(structure) => {
                for field in &structure.fields {
                    self.check_structure_field_def(field)?;
                }
            }
            ast::Type::Fn(fn_ty) => {
                self.check_type_ref(&fn_ty.argument)?;
                self.check_type_ref(&fn_ty.ret)?;
            }
        }
        Ok(())
    }

    pub fn check_tag_def(&self, def: &ast::TagDef) -> Result<()> {
        if let Some(value) = &def.value {
            self.check_type(&value)?;
        }
        Ok(())
    }

    pub fn check_structure_field_def(&self, def: &ast::StructureFieldDef) -> Result<()> {
        self.check_type(&def.ty)
    }

    pub fn check_type_ref(&self, ty_ref: &ast::TypeRef) -> Result<()> {
        // TODO: Check generics
        // TODO: Allow recursive types and refer to types before they are mentioned.
        if !self.types.contains_key(&ty_ref.name) {
            return Err(Error::UndefinedType(ty_ref.name.clone()));
        };
        Ok(())
    }

    fn assert_same_type(&self, lhs: &ast::Type, rhs: &ast::Type) -> Result<()> {
        if !self.type_eq(lhs, rhs)? {
            Err(Error::IncompatibleTypes(
                lhs.to_owned().into(),
                rhs.to_owned().into(),
            ))
        } else {
            Ok(())
        }
    }

    fn type_eq(&self, lhs: &ast::Type, rhs: &ast::Type) -> Result<bool> {
        match (lhs, rhs) {
            (ast::Type::Ref(lhs), rhs) => {
                let lhs = self.deref_type(lhs)?;
                self.type_eq(lhs, rhs)
            }
            (_, ast::Type::Ref(rhs)) => {
                let rhs = self.deref_type(rhs)?;
                self.type_eq(lhs, rhs)
            }
            (ast::Type::Structure(lhs), ast::Type::Structure(rhs)) => {
                // Structural equality

                for lhs_field in &lhs.fields {
                    let Some(rhs_field) = rhs.fields.iter().find(|field| field.field == lhs_field.field) else {
                        return Ok(false);
                    };
                    if !self.type_eq(&lhs_field.ty, &rhs_field.ty)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (ast::Type::TagUnion(lhs), ast::Type::TagUnion(rhs)) => {
                for lhs_variant in &lhs.variants {
                    let Some(rhs_variant) = rhs.variants.iter().find(|variant| variant.name == lhs_variant.name) else {
                        return Ok(false);
                    };

                    match (&lhs_variant.value, &rhs_variant.value) {
                        (Some(lhs_ty), Some(rhs_ty)) => {
                            if !self.type_eq(lhs_ty.as_ref(), rhs_ty.as_ref())? {
                                return Ok(false);
                            }
                        }
                        _ => return Ok(false),
                    }
                }
                Ok(true)
            }
            _ => return Ok(false),
        }
    }

    fn deref_type(&self, ty_ref: &ast::TypeRef) -> Result<&ast::Type> {
        if let Some((ty_def, _scope)) = self.types.get(&ty_ref.name) {
            Ok(ty_def.structural_type.as_ref())
        } else {
            Err(Error::UndefinedType(ty_ref.name.to_owned()))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuiltinType {
    String,
    Unit,
    Number,
    Bool,
}

impl TryFrom<ast::Type> for BuiltinType {
    type Error = Error;

    fn try_from(value: ast::Type) -> Result<Self> {
        if let ast::Type::Ref(ty_ref) = &value {
            match ty_ref.name.0.as_str() {
                "Unit" => Ok(BuiltinType::Unit),
                "String" => Ok(BuiltinType::String),
                "Number" => Ok(BuiltinType::Number),
                "Bool" => Ok(BuiltinType::Bool),
                _ => Err(Error::ExpectedBuiltinType(value)),
            }
        } else {
            Err(Error::ExpectedBuiltinType(value))
        }
    }
}

impl Into<ast::Type> for BuiltinType {
    fn into(self) -> ast::Type {
        match self {
            BuiltinType::String => ast::Type::string(),
            BuiltinType::Unit => ast::Type::unit(),
            BuiltinType::Number => ast::Type::number(),
            BuiltinType::Bool => ast::Type::bool(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Error {
    UndefinedType(ast::Ident),
    UndefinedVar(ast::Ident),
    IncompatibleTypes(ast::Type, ast::Type),
    ExpectedFnType(ast::Type),
    ExpectedBuiltinType(ast::Type),
    EmptyMatch,

    /// Example: `({ a: "hello" }).b`
    InvalidAccess(ast::Type, ast::Ident),

    /// # Example
    ///
    /// ```
    /// if ({ a: "hello" }) is {
    ///     { b } => print(b),
    /// }
    /// ```
    IncompatiblePattern(ast::Pattern, ast::Type),
}
