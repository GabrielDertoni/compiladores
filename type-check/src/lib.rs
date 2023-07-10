//! The type checker
//!
//! This module is responsible for checking and resolving the types of a program.

use std::{borrow::Borrow, collections::HashMap, hash::Hash};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, Default)]
pub struct Scope {
    /// Types defined in this scope
    types: HashMap<ast::Ident, ast::TypeDef>,
    /// Variables defined in this scope
    variables: HashMap<ast::Ident, ast::Type>,
}

impl Scope {
    pub fn new() -> Self {
        Scope {
            types: HashMap::new(),
            variables: HashMap::new(),
        }
    }
}

// Very inspired by https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html
pub struct TyCx {
    scopes: Vec<Scope>,
    type_cache: HashMap<ast::NodeId, ast::Type>,
}

impl TyCx {
    pub fn new() -> Self {
        let mut tcx = TyCx {
            scopes: vec![Scope::new()],
            type_cache: HashMap::new(),
        };
        for ty in BUILTIN_TYPES {
            tcx.add_type_def(ty.def());
        }
        tcx
    }

    pub fn type_of_tag(&self, tag: &ast::Ident) -> Result<ast::TagUnionDef> {
        self.scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.types.values())
            .find_map(|ty| {
                if let ast::Type::TagUnion(tags) = ty.structural_type.as_ref() {
                    if tags.variants.iter().find(|var| &var.name == tag).is_some() {
                        return Some(tags.to_owned());
                    }
                }
                None
            })
            .ok_or_else(|| Error::TagNotFound(tag.to_owned()))
    }

    pub fn scope<T>(&mut self, cont: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push(Scope::new());
        let ret = cont(self);
        self.scopes.pop();
        ret
    }

    pub fn lookup_type(&self, name: &ast::Ident) -> Result<&ast::TypeDef> {
        for scope in self.scopes.iter().rev() {
            if let Some(ty_def) = scope.types.get(name) {
                return Ok(ty_def);
            }
        }
        Err(Error::UndefinedType(name.to_owned()))
    }

    pub fn lookup_var<'a, Q>(&'a self, name: &Q) -> Result<&'a ast::Type>
    where
        ast::Ident: Borrow<Q>,
        Q: Into<ast::Ident> + Clone + Eq + Hash,
    {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.variables.get(name))
            .ok_or_else(|| Error::UndefinedVar(name.clone().into()))
    }

    pub fn curr_scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    pub fn curr_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    pub fn add_var(&mut self, name: &ast::Ident, ty: &ast::Type) -> Result<()> {
        self.check_type(ty)?;
        self.curr_scope_mut()
            .variables
            .insert(name.clone(), ty.clone());
        Ok(())
    }

    pub fn add_type_def(&mut self, def: ast::TypeDef) {
        self.curr_scope_mut().types.insert(def.name.clone(), def);
    }

    pub fn cache_type(&mut self, id: ast::NodeId, ty: ast::Type) {
        self.type_cache.insert(id, ty);
    }

    pub fn is_cached(&self, id: ast::NodeId) -> Option<&ast::Type> {
        self.type_cache.get(&id)
    }

    pub fn check_expr(&mut self, expr: &ast::Expr) -> Result<ast::Type> {
        if let Some(cached) = self.is_cached(expr.id) {
            return Ok(cached.to_owned());
        }
        let ty = match expr.kind.as_ref() {
            ast::ExprKind::Fn(expr) => self.check_fn_expr(expr)?,
            ast::ExprKind::Block(expr) => self.check_block_expr(expr)?,
            ast::ExprKind::Cons(expr) => self.check_cons_expr(expr)?,
            ast::ExprKind::Match(expr) => self.check_match_expr(expr)?,
            ast::ExprKind::Call(expr) => self.check_call_expr(expr)?,
            ast::ExprKind::Access(expr) => self.check_access_expr(expr)?,
            ast::ExprKind::Ref(expr) => self.check_ref_expr(expr)?,
            ast::ExprKind::Literal(expr) => self.check_literal_expr(expr)?,
            ast::ExprKind::Bin(expr) => self.check_bin_expr(expr)?,
        };
        self.cache_type(expr.id, ty.clone());
        Ok(ty)
    }

    pub fn check_fn_expr(&mut self, expr: &ast::FnExpr) -> Result<ast::Type> {
        self.scope(|tcx| {
            tcx.add_var(&expr.arg, &expr.ty.argument)?;
            let actual_ret_type = tcx.check_block_expr(&expr.body)?;
            tcx.assert_same_type(&actual_ret_type, &expr.ty.ret)?;
            Ok(())
        })?;
        Ok(ast::Type::Fn(expr.ty.clone()))
    }

    pub fn check_block_expr(&mut self, expr: &ast::BlockExpr) -> Result<ast::Type> {
        let mut ret_type = None;
        for stmt in &expr.stmts {
            if let ast::Stmt::Return(ret) = stmt {
                let ty = self.check_expr(&ret.expr)?;
                if let Some(ret_type) = ret_type.as_ref() {
                    self.assert_same_type(ret_type, &ty)?;
                } else {
                    ret_type.replace(ty);
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
        let ty = self.type_of_tag(&tag.tag)?;
        let val_ty = tag
            .value
            .as_ref()
            .map(|value| self.check_expr(value))
            .transpose()?;
        let expected_val_ty = ty
            .variants
            .iter()
            .find(|ty| ty.name == tag.tag)
            .expect("`type_of_tag()` already checks the tag is in the type");
        match (&expected_val_ty.value, &val_ty) {
            (Some(expected), Some(ty)) => self.assert_same_type(expected, ty)?,
            _ => return Err(Error::IncompatibleTag(tag.tag.clone(), ty.into())),
        }
        Ok(ty.into())
    }

    pub fn check_match_expr(&mut self, expr: &ast::MatchExpr) -> Result<ast::Type> {
        // TODO: Check if the arm matches don't overlay and that they are non-exhaustive and valid (only tag union matches for tag union scrutinee, etc.)
        let scrutinee_ty = self.check_expr(&expr.scrutinee)?;
        let mut ty = None;
        for arm in &expr.arms {
            // Create a scope for each match arm
            self.scope(|tcx| -> Result<()> {
                let expr_ty = tcx.check_match_arm(&arm, &scrutinee_ty)?;
                if let Some(ty) = ty.as_ref() {
                    tcx.assert_same_type(&expr_ty, ty)?;
                } else {
                    ty.replace(expr_ty);
                }
                Ok(())
            })?;
        }
        ty.ok_or_else(|| Error::EmptyMatch)
    }

    pub fn check_match_arm(
        &mut self,
        arm: &ast::MatchArm,
        scrutinee_ty: &ast::Type,
    ) -> Result<ast::Type> {
        self.check_pattern(&arm.pattern, &scrutinee_ty)?;
        self.check_expr(&arm.expr)
    }

    fn check_call_expr(&mut self, expr: &ast::CallExpr) -> Result<ast::Type> {
        let fn_ty = self.check_expr(&expr.callee)?;
        let fn_ty = match fn_ty {
            ast::Type::Fn(fn_ty) => fn_ty,
            otherwise => return Err(Error::ExpectedFnType(otherwise)),
        };
        let arg_ty = self.check_expr(&expr.arg)?;
        self.assert_same_type(&fn_ty.argument, &arg_ty)?;
        Ok(*fn_ty.ret)
    }

    fn check_access_expr(&mut self, expr: &ast::AccessExpr) -> Result<ast::Type> {
        let mut struct_ty = self.check_expr(&expr.value)?;
        loop {
            match struct_ty {
                ast::Type::Ref(ty_ref) => struct_ty = self.deref_type(&ty_ref)?,
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
        self.lookup_var(&expr.ident).map(ToOwned::to_owned)
    }

    fn check_literal_expr(&self, expr: &ast::Literal) -> Result<ast::Type> {
        match expr {
            ast::Literal::String(_) => Ok(ast::Type::string()),
            ast::Literal::Number(_) => Ok(ast::Type::number()),
            ast::Literal::Bool(_) => Ok(ast::Type::bool()),
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
    fn check_pattern(&mut self, patt: &ast::Pattern, expected: &ast::Type) -> Result<()> {
        match (patt, expected) {
            (ast::Pattern::Structure(patt), ast::Type::Structure(expected)) => {
                self.check_structure_pattern(patt, expected)
            }
            (ast::Pattern::Tag(patt), ast::Type::TagUnion(expected)) => {
                self.check_tag_pattern(patt, expected)
            }
            (ast::Pattern::Literal(lit_pat), ast::Type::Ref(expected)) => {
                let Some(builtin) = BuiltinType::from_name(&expected.name.0) else {
                    return Err(Error::ExpectedBuiltinType(expected.to_owned().into()))
                };
                match (lit_pat, builtin) {
                    (ast::Literal::String(_), BuiltinType::String)
                    | (ast::Literal::Number(_), BuiltinType::Number)
                    | (ast::Literal::Bool(_), BuiltinType::Bool) => Ok(()),
                    (pat, builtin) => Err(Error::IncompatiblePattern(
                        pat.to_owned().into(),
                        builtin.into(),
                    )),
                }
            }
            (ast::Pattern::Catchall(binding), _) => {
                self.add_var(binding, expected)?;
                Ok(())
            }
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
        self.check_type(&decl.ty)?;
        self.add_var(&decl.name, &decl.ty)?;
        let ty = self.check_expr(&decl.value)?;
        self.assert_same_type(&ty, decl.ty.as_ref())?;
        Ok(())
    }

    fn check_return_stmt(&mut self, ret: &ast::ReturnStmt) -> Result<()> {
        self.check_expr(&ret.expr)?;
        Ok(())
    }

    pub fn check_type_def(&mut self, def: &ast::TypeDef) -> Result<()> {
        self.check_type(&def.structural_type)?;
        self.add_type_def(def.clone());
        Ok(())
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
                self.check_type(&fn_ty.argument)?;
                self.check_type(&fn_ty.ret)?;
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
        if !self.curr_scope().types.contains_key(&ty_ref.name) {
            if BuiltinType::from_name(&ty_ref.name.0).is_some() {
                Ok(())
            } else {
                Err(Error::UndefinedType(ty_ref.name.clone()))
            }
        } else {
            Ok(())
        }
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
            // (ast::Type::Ref(lhs), rhs) => {
            //     let lhs = self.lookup_type(lhs)?;
            //     self.type_eq(&lhs, rhs)
            // }
            // (_, ast::Type::Ref(rhs)) => {
            //     let rhs = self.deref_type(rhs)?;
            //     self.type_eq(lhs, &rhs)
            // }
            (ast::Type::Ref(lhs), ast::Type::Ref(rhs)) => Ok(lhs.name == rhs.name),
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
            (ast::Type::Fn(lhs), ast::Type::Fn(rhs)) => Ok(self
                .type_eq(&lhs.argument, &rhs.argument)?
                && self.type_eq(&lhs.ret, &rhs.ret)?),
            _ => return Ok(false),
        }
    }

    fn deref_type(&self, ty_ref: &ast::TypeRef) -> Result<ast::Type> {
        let ty_def = self.lookup_type(&ty_ref.name)?;
        Ok(ty_def.structural_type.as_ref().to_owned())
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    frame: Frame,
    code: Vec<Instr>,
}

#[derive(Debug, Clone, Default)]
pub struct Frame {
    locals: Vec<ast::Ident>,
}

impl Frame {
    pub fn new() -> Frame {
        Frame { locals: Vec::new() }
    }

    pub fn lookup_local(&self, name: &ast::Ident) -> Option<usize> {
        self.locals.iter().position(|local| local == name)
    }

    pub fn add_local(&mut self, name: ast::Ident) -> usize {
        let idx = self.locals.len();
        self.locals.push(name);
        idx
    }
}

#[derive(Debug, Clone)]
pub enum Const {
    String(String),
    Num(f64),
    Bool(bool),
    Function(Function),
}

impl From<Function> for Const {
    fn from(v: Function) -> Self {
        Self::Function(v)
    }
}

impl From<bool> for Const {
    fn from(v: bool) -> Self {
        Self::Bool(v)
    }
}

impl From<f64> for Const {
    fn from(v: f64) -> Self {
        Self::Num(v)
    }
}

impl From<String> for Const {
    fn from(v: String) -> Self {
        Self::String(v)
    }
}

pub struct Codegen {
    globals: HashMap<ast::Ident, usize>,
    consts: Vec<Const>,
    curr_frame: Frame,
    next_label: usize,
    tcx: TyCx,
}

impl Codegen {
    pub fn type_size(&self, ty: &ast::Type) -> usize {
        match ty {
            ast::Type::Ref(_) => unreachable!("should be already resolved"),
            // One word for the variant and enought space to fit the biggest variant inner type
            ast::Type::TagUnion(tag) => {
                1 + tag
                    .variants
                    .iter()
                    .map(|variant| {
                        variant
                            .value
                            .as_ref()
                            .map(|ty| self.type_size(ty))
                            .unwrap_or(0)
                    })
                    .max()
                    .unwrap_or(0)
            }
            ast::Type::Structure(structure) => structure
                .fields
                .iter()
                .map(|field| self.type_size(&field.ty))
                .sum::<usize>(),
            ast::Type::Fn(_) => 1,
        }
    }

    pub fn label(&mut self) -> usize {
        let lbl = self.next_label;
        self.next_label += 1;
        lbl
    }

    pub fn push_const(&mut self, c: impl Into<Const>) -> usize {
        let idx = self.consts.len();
        self.consts.push(c.into());
        idx
    }

    pub fn codegen_expr(&mut self, expr: &ast::Expr, instrs: &mut Vec<Instr>) -> Result<()> {
        match expr.kind.as_ref() {
            ast::ExprKind::Fn(expr) => self.codegen_fn_expr(expr, instrs),
            ast::ExprKind::Block(expr) => self.codegen_block_expr(expr, instrs),
            ast::ExprKind::Cons(expr) => self.codegen_cons_expr(expr, instrs),
            ast::ExprKind::Match(expr) => self.codegen_match_expr(expr, instrs),
            ast::ExprKind::Call(expr) => self.codegen_call_expr(expr, instrs),
            ast::ExprKind::Access(expr) => self.codegen_access_expr(expr, instrs),
            ast::ExprKind::Ref(expr) => self.codegen_ref_expr(expr, instrs),
            ast::ExprKind::Literal(expr) => self.codegen_literal(expr, instrs),
            ast::ExprKind::Bin(expr) => self.codegen_bin_expr(expr, instrs),
        }
    }

    pub fn codegen_fn_expr(&mut self, expr: &ast::FnExpr, instrs: &mut Vec<Instr>) -> Result<()> {
        let mut code = Vec::new();

        // Create a new frame and register the `arg` value as having index `0` in the function stack.
        let mut frame = Frame::new();
        let idx = frame.add_local(expr.arg.to_owned());

        // This is a temporary placeholder, we'll overwrite it later
        code.push(Instr::AllocLocals(0));

        // Load the argument from the stack onto the function locals
        code.push(Instr::StoreLocal(idx));

        let prev_frame = std::mem::replace(&mut self.curr_frame, frame);
        self.codegen_block_expr(&expr.body, &mut code)?;
        let frame = std::mem::replace(&mut self.curr_frame, prev_frame);
        resolve_labels(&mut code);

        code[0] = Instr::AllocLocals(frame.locals.len());
        let idx = self.push_const(Const::Function(Function { frame, code }));
        instrs.push(Instr::LoadConst(idx));

        Ok(())
    }

    pub fn codegen_block_expr(
        &mut self,
        expr: &ast::BlockExpr,
        instrs: &mut Vec<Instr>,
    ) -> Result<()> {
        for stmt in &expr.stmts {
            self.codegen_stmt(stmt, &mut *instrs)?;
        }
        Ok(())
    }

    fn codegen_stmt(&mut self, stmt: &ast::Stmt, instrs: &mut Vec<Instr>) -> Result<()> {
        match stmt {
            // No code is generated for type definitions
            ast::Stmt::TypeDef(_) => Ok(()),
            ast::Stmt::Expr(expr) => self.codegen_expr(expr, instrs),
            ast::Stmt::Decl(decl) => {
                let idx = self.curr_frame.add_local(decl.name.to_owned());
                self.codegen_expr(&decl.value, &mut *instrs)?;
                instrs.push(Instr::StoreLocal(idx));
                Ok(())
            }
            ast::Stmt::Return(ret) => {
                self.codegen_expr(&ret.expr, &mut *instrs)?;
                instrs.push(Instr::Ret);
                Ok(())
            }
        }
    }

    pub fn codegen_cons_expr(
        &mut self,
        expr: &ast::ConsExpr,
        instrs: &mut Vec<Instr>,
    ) -> Result<()> {
        let ty = self.tcx.check_cons_expr(expr)?;
        let size = self.type_size(&ty);
        match expr {
            ast::ConsExpr::ConsStructure(structure) => {
                for field in &structure.fields {
                    self.codegen_expr(&field.value, &mut *instrs)?;
                }
            }
            ast::ConsExpr::ConsTag(tag) => {
                let ty = self.tcx.type_of_tag(&tag.tag)?;
                let idx = ty
                    .variants
                    .iter()
                    .position(|var| var.name == tag.tag)
                    .unwrap();
                // Push the tag
                instrs.push(Instr::Idx(LinkValue::Value(idx)));
                if let Some(expr) = tag.value.as_ref() {
                    self.codegen_expr(expr, instrs)?;
                }
            }
        }
        instrs.push(Instr::BuildType(size));
        Ok(())
    }

    pub fn codegen_match_expr(
        &mut self,
        expr: &ast::MatchExpr,
        instrs: &mut Vec<Instr>,
    ) -> Result<()> {
        self.codegen_expr(&expr.scrutinee, &mut *instrs)?;
        let ty = self.tcx.check_expr(&expr.scrutinee)?;
        match ty {
            ast::Type::Fn(_) => todo!("this should be an error"),
            ast::Type::Ref(ty_ref) => {
                if let Some(ty) = BuiltinType::from_name(&ty_ref.name.0) {
                    let mut labels = Vec::new();
                    match ty {
                        BuiltinType::String => todo!(),
                        BuiltinType::Unit => todo!(),
                        BuiltinType::Number => {
                            for arm in &expr.arms {
                                match &arm.pattern {
                                    ast::Pattern::Structure(_) | ast::Pattern::Tag(_) => {
                                        todo!("error")
                                    }
                                    ast::Pattern::Literal(lit) => {
                                        let &ast::Literal::Number(num) = lit else {
                                            todo!();
                                        };
                                        instrs.push(Instr::LoadConst(
                                            self.push_const(Const::Num(num)),
                                        ));
                                        instrs.push(Instr::EqualNum);
                                        let lbl = self.label();
                                        labels.push(lbl);
                                        instrs.push(Instr::BranchIfTrue(LinkValue::Ref(lbl)));
                                    }
                                    ast::Pattern::Catchall(ident) => {
                                        let lbl = self.label();
                                        labels.push(lbl);
                                        let binding = self.curr_frame.add_local(ident.to_owned());
                                        instrs.push(Instr::StoreLocal(binding));
                                        instrs.push(Instr::Jump(LinkValue::Ref(lbl)));
                                    }
                                }
                            }
                        }
                        BuiltinType::Bool => todo!(),
                    }
                    for (arm, lbl) in expr.arms.iter().zip(labels) {
                        instrs.push(Instr::Label(lbl));
                        self.codegen_expr(&arm.expr, instrs)?;
                    }
                } else {
                    todo!()
                }
            }
            ast::Type::TagUnion(tags) => {
                let labels = (0..tags.variants.len())
                    .map(|_| self.label())
                    .collect::<Vec<_>>();
                instrs.extend(
                    labels
                        .iter()
                        .copied()
                        .map(|lbl| Instr::Idx(LinkValue::Ref(lbl))),
                );
                instrs.push(Instr::Branch(tags.variants.len()));
                // Should have one arm for each tag
                for (tag, lbl) in tags.variants.iter().zip(labels) {
                    let arm = expr
                        .arms
                        .iter()
                        .find(|arm| match &arm.pattern {
                            ast::Pattern::Structure(_) | ast::Pattern::Literal(_) => unreachable!(),
                            ast::Pattern::Tag(pat) => pat.name == tag.name,
                            ast::Pattern::Catchall(_) => true,
                        })
                        .ok_or_else(|| Error::NonExhaustiveMatch(tag.name.to_owned()))?;
                    instrs.push(Instr::Label(lbl));
                    self.codegen_expr(&arm.expr, &mut *instrs)?;
                }
            }
            ast::Type::Structure(_) => todo!(),
        }
        Ok(())
    }

    pub fn codegen_call_expr(
        &mut self,
        expr: &ast::CallExpr,
        instrs: &mut Vec<Instr>,
    ) -> Result<()> {
        self.codegen_expr(&expr.arg, &mut *instrs)?;
        self.codegen_expr(&expr.callee, &mut *instrs)?;
        instrs.push(Instr::Call);
        Ok(())
    }

    pub fn codegen_access_expr(
        &mut self,
        expr: &ast::AccessExpr,
        instrs: &mut Vec<Instr>,
    ) -> Result<()> {
        let ty = self.tcx.check_expr(&expr.value)?;
        let ast::Type::Structure(structure) = ty else {
            return Err(Error::ExpectedStructure(ty));
        };
        let idx = structure
            .fields
            .iter()
            .position(|field| field.field == expr.field)
            .expect("type checking should catch this");
        instrs.push(Instr::ReadField(idx));
        Ok(())
    }

    pub fn codegen_ref_expr(&self, expr: &ast::RefExpr, instrs: &mut Vec<Instr>) -> Result<()> {
        dbg!(&self.curr_frame);
        let idx = self
            .curr_frame
            .lookup_local(dbg!(&expr.ident))
            .expect("type checking should catch this");
        instrs.push(Instr::LoadLocal(idx));
        Ok(())
    }

    pub fn codegen_literal(&mut self, lit: &ast::Literal, instrs: &mut Vec<Instr>) -> Result<()> {
        match lit {
            ast::Literal::String(s) => instrs.push(Instr::LoadConst(
                self.push_const(Const::String(s.to_owned())),
            )),
            &ast::Literal::Number(n) => instrs.push(Instr::LoadConst(self.push_const(n))),
            &ast::Literal::Bool(b) => instrs.push(Instr::LoadConst(self.push_const(b))),
        }
        Ok(())
    }

    pub fn codegen_bin_expr(&mut self, expr: &ast::BinExpr, instrs: &mut Vec<Instr>) -> Result<()> {
        let ty = BuiltinType::try_from(self.tcx.check_bin_expr(expr)?)?;
        self.codegen_expr(&expr.lhs, &mut *instrs)?;
        self.codegen_expr(&expr.rhs, &mut *instrs)?;
        match (&expr.op, ty) {
            /* Arithmetic operations */
            (ast::BinOp::Add, BuiltinType::Number) => instrs.push(Instr::Add),
            (ast::BinOp::Sub, BuiltinType::Number) => instrs.push(Instr::Sub),
            (ast::BinOp::Mul, BuiltinType::Number) => instrs.push(Instr::Mul),
            (ast::BinOp::Div, BuiltinType::Number) => instrs.push(Instr::Div),
            (ast::BinOp::Mod, BuiltinType::Number) => instrs.push(Instr::Mod),

            /* Bit operations */
            (ast::BinOp::BitAnd, BuiltinType::Number) => instrs.push(Instr::BitAnd),
            (ast::BinOp::BitOr, BuiltinType::Number) => instrs.push(Instr::BitOr),
            (ast::BinOp::ShiftLeft, BuiltinType::Number) => instrs.push(Instr::ShiftLeft),
            (ast::BinOp::ShiftRight, BuiltinType::Number) => instrs.push(Instr::ShiftRight),

            /* Logical boolean operations */
            (ast::BinOp::And, BuiltinType::Bool) => instrs.push(Instr::And),
            (ast::BinOp::Or, BuiltinType::Bool) => instrs.push(Instr::Or),

            /* Comparison for numbers */
            (ast::BinOp::Less, BuiltinType::Number) => instrs.push(Instr::LessNum),
            (ast::BinOp::LessEqual, BuiltinType::Number) => instrs.push(Instr::LessEqualNum),
            (ast::BinOp::Greater, BuiltinType::Number) => instrs.push(Instr::GreaterNum),
            (ast::BinOp::GreaterEqual, BuiltinType::Number) => instrs.push(Instr::GreaterEqualNum),
            (ast::BinOp::Equal, BuiltinType::Number) => instrs.push(Instr::EqualNum),
            (ast::BinOp::NotEqual, BuiltinType::Number) => {
                instrs.push(Instr::EqualNum);
                instrs.push(Instr::Not);
            }

            /* Comparison for strings */
            (ast::BinOp::LessEqual, BuiltinType::String) => instrs.push(Instr::LessEqualStr),
            (ast::BinOp::Greater, BuiltinType::String) => instrs.push(Instr::GreaterStr),
            (ast::BinOp::GreaterEqual, BuiltinType::String) => instrs.push(Instr::GreaterEqualStr),
            (ast::BinOp::Equal, BuiltinType::String) => instrs.push(Instr::EqualStr),
            (ast::BinOp::NotEqual, BuiltinType::String) => {
                instrs.push(Instr::EqualStr);
                instrs.push(Instr::Not);
            }

            /* Catchall */
            _ => unreachable!("type checking should have cought this case"),
        }
        Ok(())
    }

    pub fn write_binary<W: std::io::Write>(
        &self,
        top_level: &[Instr],
        mut w: W,
    ) -> std::io::Result<()> {
        write_instructions_bin(top_level, &mut w)?;
        Ok(())
    }
}

pub fn resolve_labels(instrs: &mut Vec<Instr>) {
    let labels = instrs
        .iter()
        .enumerate()
        .filter_map(|(i, instr)| {
            if let &Instr::Label(l) = instr {
                Some((l, i))
            } else {
                None
            }
        })
        .collect::<HashMap<_, _>>();
    let mut i = 0;
    for j in 0..instrs.len() {
        instrs.swap(i, j);
        match &instrs[j] {
            // Skip
            Instr::Label(_) => (),
            Instr::Idx(LinkValue::Ref(idx)) => {
                instrs[i] = Instr::Idx(LinkValue::Value(labels[idx]))
            }
            _ => i += 1,
        }
    }
    instrs.truncate(i);
}

pub fn write_instructions_text<W: std::io::Write>(
    instrs: &[Instr],
    mut w: W,
) -> std::io::Result<()> {
    use Instr::*;

    for instr in instrs {
        match instr {
            StoreLocal(arg) => writeln!(w, "STORE_LOCAL {arg}")?,
            LoadLocal(arg) => writeln!(w, "LOAD_LOCAL {arg}")?,
            LoadConst(arg) => writeln!(w, "LOAD_CONST {arg}")?,
            ReadField(arg) => writeln!(w, "READ_FIELD {arg}")?,
            BuildType(arg) => writeln!(w, "BUILD_TYPE {arg}")?,
            AllocLocals(arg) => writeln!(w, "ALLOC_LOCALS {arg}")?,
            Ret => writeln!(w, "RETURN")?,
            Call => writeln!(w, "CALL")?,
            Branch(arg) => writeln!(w, "BRANCH {arg}")?,
            BranchIfTrue(arg) => writeln!(w, "BRANCH_IF_TRU {}", arg.as_value().unwrap())?,
            Jump(arg) => writeln!(w, "JUMP {}", arg.as_value().unwrap())?,
            Add => writeln!(w, "ADD")?,
            Sub => writeln!(w, "SUB")?,
            Mul => writeln!(w, "MUL")?,
            Div => writeln!(w, "DIV")?,
            Mod => writeln!(w, "MOD")?,
            And => writeln!(w, "AND")?,
            Or => writeln!(w, "OR")?,
            Not => writeln!(w, "NOT")?,
            BitAnd => writeln!(w, "BIT_AND")?,
            BitOr => writeln!(w, "BIT_OR")?,
            ShiftLeft => writeln!(w, "SHIFT_LEFT")?,
            ShiftRight => writeln!(w, "SHIFT_RIGHT")?,
            LessNum => writeln!(w, "LESS_NUM")?,
            LessEqualNum => writeln!(w, "LESS_EQUAL_NUM")?,
            GreaterNum => writeln!(w, "GREATER_NUM")?,
            GreaterEqualNum => writeln!(w, "GREATER_EQUAL_NUM")?,
            EqualNum => writeln!(w, "EQUAL_NUM")?,
            LessStr => writeln!(w, "LESS_STR")?,
            LessEqualStr => writeln!(w, "LESS_EQUAL_STR")?,
            GreaterStr => writeln!(w, "GREATER_STR")?,
            GreaterEqualStr => writeln!(w, "GREATER_EQUAL_STR")?,
            EqualStr => writeln!(w, "EQUAL_STR")?,
            Label(_) => panic!("instructions don't have all labels resolved"),
            Idx(arg) => writeln!(w, "psh {}", arg.as_value().unwrap())?,
        }
    }
    Ok(())
}

pub fn write_instructions_bin<W: std::io::Write>(
    instrs: &[Instr],
    mut w: W,
) -> std::io::Result<()> {
    use Instr::*;

    for instr in instrs {}
    Ok(())
}

#[derive(Debug, Clone, Copy)]
pub enum LinkValue {
    Value(usize),
    Ref(usize),
}

impl LinkValue {
    pub fn as_value(&self) -> Option<&usize> {
        if let Self::Value(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Instr {
    /* Read write operations */
    /// Operation: `locals[$0] = pop()`
    StoreLocal(usize),
    /// Operation: `push(locals[$0])`
    LoadLocal(usize),
    /// Operation: `push(consts[$0])`
    LoadConst(usize),
    /// Operation: `push(((void**)pop())[$0])`
    ReadField(usize),

    /* Allocation operations */
    /// Operation:
    /// ```c
    /// void** obj = malloc($0 * sizeof(void*));
    /// for (int i = 0; i < $0; i++)
    ///     obj[i] = pop();
    /// push(obj);
    /// ```
    BuildType(usize),
    AllocLocals(usize),

    /* Control flow operations */
    Ret,
    Call,
    /// Operation:
    /// ```c
    /// int idx = pop();
    /// ip = top[-idx];
    /// discard($0);
    /// ```
    Branch(usize),
    BranchIfTrue(LinkValue),
    Jump(LinkValue),
    // Arithmetic operations
    /// Operation: `push(pop() + pop())`
    Add,
    /// Operation: `push(pop() - pop())`
    Sub,
    /// Operation: `push(pop() * pop())`
    Mul,
    /// Operation: `push(pop() / pop())`
    Div,
    /// Operation: `push(pop() % pop())`
    Mod,
    // Boolean operations
    /// Operation: `push(pop() && pop())`
    And,
    /// Operation: `push(pop() || pop())`
    Or,
    /// Operation: `push(!pop())`
    Not,
    // Bitwise operations
    /// Operation: `push(pop() & pop())`
    BitAnd,
    /// Operation: `push(pop() | pop())`
    BitOr,
    /// Operation: `push(pop() << pop())`
    ShiftLeft,
    /// Operation: `push(pop() >> pop())`
    ShiftRight,
    // Numeric comparisons
    /// Operation: `push(pop() < pop())`
    LessNum,
    /// Operation: `push(pop() <= pop())`
    LessEqualNum,
    /// Operation: `push(pop() > pop())`
    GreaterNum,
    /// Operation: `push(pop() >= pop())`
    GreaterEqualNum,
    /// Operation: `push(pop() == pop())`
    EqualNum,
    // String comparisons
    /// Operation: `push(strcmp(pop(), pop()) < 0)`
    LessStr,
    /// Operation: `push(strcmp(pop(), pop()) <= 0)`
    LessEqualStr,
    /// Operation: `push(strcmp(pop(), pop()) > 0)`
    GreaterStr,
    /// Operation: `push(strcmp(pop(), pop()) >= 0)`
    GreaterEqualStr,
    /// Operation: `push(strcmp(pop(), pop()) == 0)`
    EqualStr,
    Label(usize),
    /// Operation: `push($0)`
    Idx(LinkValue),
}

impl Instr {
    pub fn op(&self) -> u8 {
        // SAFETY: https://doc.rust-lang.org/std/mem/fn.discriminant.html
        unsafe { *<*const _>::from(self).cast::<u8>() }
    }

    pub fn arg(&self) -> u8 {
        use Instr::*;

        match self {
            /* Instructions with argument */
            &StoreLocal(arg)
            | &LoadLocal(arg)
            | &LoadConst(arg)
            | &ReadField(arg)
            | &BuildType(arg)
            | &AllocLocals(arg)
            | &Branch(arg)
            | &BranchIfTrue(LinkValue::Value(arg))
            | &Jump(LinkValue::Value(arg))
            | &Idx(LinkValue::Value(arg)) => arg as u8,
            /* Instructions without arguments */
            Ret | Call | Add | Sub | Mul | Div | Mod | And | Or | Not | BitAnd | BitOr
            | ShiftLeft | ShiftRight | LessNum | LessEqualNum | GreaterNum | GreaterEqualNum
            | EqualNum | LessStr | LessEqualStr | GreaterStr | GreaterEqualStr | EqualStr => 0,
            /* Errors */
            BranchIfTrue(LinkValue::Ref(_))
            | Jump(LinkValue::Ref(_))
            | Label(_)
            | Idx(LinkValue::Ref(_)) => panic!("all labels must be resolved"),
        }
    }
}

const BUILTIN_TYPES: &'static [BuiltinType] = &[
    BuiltinType::String,
    BuiltinType::Unit,
    BuiltinType::Number,
    BuiltinType::Bool,
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuiltinType {
    String,
    Unit,
    Number,
    Bool,
}

impl BuiltinType {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Unit" => Some(BuiltinType::Unit),
            "String" => Some(BuiltinType::String),
            "Number" => Some(BuiltinType::Number),
            "Bool" => Some(BuiltinType::Bool),
            _ => None,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            BuiltinType::String => "String",
            BuiltinType::Unit => "Unit",
            BuiltinType::Number => "Number",
            BuiltinType::Bool => "Bool",
        }
    }

    pub fn def(&self) -> ast::TypeDef {
        ast::TypeDef {
            id: 0.into(),
            name: self.name().into(),
            is_alias: false,
            generics: Vec::new(),
            structural_type: Box::new(self.to_owned().into()),
        }
    }
}

impl TryFrom<ast::Type> for BuiltinType {
    type Error = Error;

    fn try_from(value: ast::Type) -> Result<Self> {
        if let ast::Type::Ref(ty_ref) = &value {
            match BuiltinType::from_name(ty_ref.name.0.as_str()) {
                Some(ty) => Ok(ty),
                None => Err(Error::ExpectedBuiltinType(value)),
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
    /// ```txt
    /// if ({ a: "hello" }) is {
    ///     { b } => print(b),
    /// }
    /// ```
    IncompatiblePattern(ast::Pattern, ast::Type),

    TagNotFound(ast::Ident),
    IncompatibleTag(ast::Ident, ast::Type),
    NonExhaustiveMatch(ast::Ident),
    ExpectedStructure(ast::Type),
}

#[cfg(test)]
mod test {
    use super::*;

    // ```
    //  1 | const fib: Number -> Number = fn n : Number -> Number {
    //  2 |     return if n is {
    //  3 |         0 => 1,
    //  4 |         1 => 1,
    //  5 |         n1 => fib (n1-1) + fib (n1-2),
    //  6 |     };
    //  7 | }
    // ```
    #[test]
    pub fn fib() {
        let code = {
            use ast::*;

            let line_5 = Expr {
                id: 8.into(),
                kind: Box::new(ExprKind::Bin(BinExpr {
                    op: BinOp::Add,
                    lhs: Expr {
                        id: 9.into(),
                        kind: Box::new(ExprKind::Call(CallExpr {
                            callee: Expr {
                                id: 10.into(),
                                kind: Box::new(ExprKind::Ref(RefExpr {
                                    ident: "fib".into(),
                                })),
                            },
                            arg: Expr {
                                id: 11.into(),
                                kind: Box::new(ExprKind::Bin(BinExpr {
                                    op: BinOp::Sub,
                                    lhs: Expr {
                                        id: 12.into(),
                                        kind: Box::new(ExprKind::Ref(RefExpr {
                                            ident: "n1".into(),
                                        })),
                                    },
                                    rhs: Expr {
                                        id: 13.into(),
                                        kind: Box::new(ExprKind::Literal(Literal::Number(1.))),
                                    },
                                })),
                            },
                        })),
                    },
                    rhs: Expr {
                        id: 14.into(),
                        kind: Box::new(ExprKind::Call(CallExpr {
                            callee: Expr {
                                id: 15.into(),
                                kind: Box::new(ExprKind::Ref(RefExpr {
                                    ident: "fib".into(),
                                })),
                            },
                            arg: Expr {
                                id: 16.into(),
                                kind: Box::new(ExprKind::Bin(BinExpr {
                                    op: BinOp::Sub,
                                    lhs: Expr {
                                        id: 17.into(),
                                        kind: Box::new(ExprKind::Ref(RefExpr {
                                            ident: "n1".into(),
                                        })),
                                    },
                                    rhs: Expr {
                                        id: 18.into(),
                                        kind: Box::new(ExprKind::Literal(Literal::Number(2.))),
                                    },
                                })),
                            },
                        })),
                    },
                })),
            };

            Stmt::Decl(Decl {
                is_const: true,
                ty: Box::new(Type::Fn(FnType {
                    argument: Box::new(Type::number()),
                    ret: Box::new(Type::number()),
                })),
                name: "fib".into(),
                value: Expr {
                    id: 1.into(),
                    kind: Box::new(ExprKind::Fn(FnExpr {
                        id: 2.into(),
                        arg: "n".into(),
                        ty: FnType {
                            argument: Box::new(Type::number()),
                            ret: Box::new(Type::number()),
                        },
                        body: BlockExpr {
                            id: 3.into(),
                            stmts: [Stmt::Return(ReturnStmt {
                                expr: Expr {
                                    id: 4.into(),
                                    kind: Box::new(ExprKind::Match(MatchExpr {
                                        scrutinee: Expr {
                                            id: 5.into(),
                                            kind: Box::new(ExprKind::Ref(RefExpr {
                                                ident: "n".into(),
                                            })),
                                        },
                                        arms: [
                                            MatchArm {
                                                pattern: Pattern::Literal(Literal::Number(0.)),
                                                expr: Expr {
                                                    id: 6.into(),
                                                    kind: Box::new(ExprKind::Literal(
                                                        Literal::Number(1.),
                                                    )),
                                                },
                                            },
                                            MatchArm {
                                                pattern: Pattern::Literal(Literal::Number(1.)),
                                                expr: Expr {
                                                    id: 7.into(),
                                                    kind: Box::new(ExprKind::Literal(
                                                        Literal::Number(1.),
                                                    )),
                                                },
                                            },
                                            MatchArm {
                                                pattern: Pattern::Catchall("n1".into()),
                                                expr: line_5,
                                            },
                                        ]
                                        .to_vec(),
                                    })),
                                },
                            })]
                            .to_vec(),
                        },
                    })),
                },
            })
        };

        let mut tcx = TyCx::new();
        let res = tcx.check_stmt(&code);
        assert!(res.is_ok(), "{res:?}");

        let mut codegen = Codegen {
            globals: HashMap::new(),
            consts: Vec::new(),
            curr_frame: Frame::new(),
            next_label: 0,
            tcx,
        };
        let mut instrs = Vec::new();
        let res = codegen.codegen_stmt(&code, &mut instrs);
        assert!(res.is_ok(), "{res:?}");
        resolve_labels(&mut instrs);
        dbg!(instrs);
        for c in &codegen.consts {
            dbg!(c);
        }
    }

    // ```
    //  1 | const add1: Number -> Number = fn n : Number -> Number {
    //  2 |     return n + 1;
    //  7 | }
    // ```
    #[test]
    pub fn add1() {
        let code = {
            use ast::*;

            Stmt::Decl(Decl {
                is_const: true,
                ty: Box::new(Type::Fn(FnType {
                    argument: Box::new(Type::number()),
                    ret: Box::new(Type::number()),
                })),
                name: "add1".into(),
                value: Expr {
                    id: 1.into(),
                    kind: Box::new(ExprKind::Fn(FnExpr {
                        id: 2.into(),
                        arg: "n".into(),
                        ty: FnType {
                            argument: Box::new(Type::number()),
                            ret: Box::new(Type::number()),
                        },
                        body: BlockExpr {
                            id: 3.into(),
                            stmts: [Stmt::Return(ReturnStmt {
                                expr: Expr {
                                    id: 4.into(),
                                    kind: Box::new(ExprKind::Bin(BinExpr {
                                        op: BinOp::Add,
                                        lhs: Expr {
                                            id: 5.into(),
                                            kind: Box::new(ExprKind::Ref(RefExpr {
                                                ident: "n".into(),
                                            })),
                                        },
                                        rhs: Expr {
                                            id: 6.into(),
                                            kind: Box::new(ExprKind::Literal(Literal::Number(1.0))),
                                        },
                                    })),
                                },
                            })]
                            .to_vec(),
                        },
                    })),
                },
            })
        };

        let mut tcx = TyCx::new();
        let res = tcx.check_stmt(&code);
        assert!(res.is_ok(), "{res:?}");

        let mut codegen = Codegen {
            globals: HashMap::new(),
            consts: Vec::new(),
            curr_frame: Frame::new(),
            next_label: 0,
            tcx,
        };
        let mut instrs = Vec::new();
        let res = codegen.codegen_stmt(&code, &mut instrs);
        assert!(res.is_ok(), "{res:?}");
        resolve_labels(&mut instrs);
        dbg!(&instrs);
        for c in &codegen.consts {
            dbg!(c);
        }
        {
            use std::io::Write;

            let mut writer = Vec::new();
            write_instructions_text(&instrs, &mut writer).unwrap();
            writeln!(writer, "\n--- CONSTS ---").unwrap();
            for (i, c) in codegen.consts.iter().enumerate() {
                writeln!(writer, "\n= CONST {i} =").unwrap();
                match c {
                    Const::String(s) => writeln!(writer, "STR \"{s}\""),
                    Const::Function(func) => write_instructions_text(&func.code, &mut writer),
                    Const::Num(n) => writeln!(writer, "NUM {n}"),
                    Const::Bool(b) => writeln!(writer, "BOOL {b}"),
                }
                .unwrap()
            }
            let s = String::from_utf8(writer).unwrap();
            println!("{s}");
        }
    }
}
