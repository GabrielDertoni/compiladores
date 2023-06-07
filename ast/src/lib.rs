mod impls;

pub type Program = Vec<Stmt>;

#[derive(Debug, Clone)]
pub enum Stmt {
    TypeDef(TypeDef),
    Expr(Expr),
    Decl(Decl),
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    pub name: Ident,
    pub is_alias: bool,
    pub generic: Vec<Variable>,
    pub structural_type: Box<Type>,
}

// Always boxed
#[derive(Debug, Clone)]
pub enum Type {
    /// Reference to another type
    Ref(TypeRef),
    /// Tag union, like `[ Some A, None ]`
    TagUnion(TagUnionDef),
    /// Structure, like `{ field: Type }`
    Structure(StructureDef),
}

#[derive(Debug, Clone)]
pub struct TypeRef {
    pub ty: Box<Type>,
    pub generic_args: Vec<GenericArg>,
}

#[derive(Debug, Clone)]
pub enum GenericArg {
    Variable(Variable),
    Type(Box<Type>),
}

#[derive(Debug, Clone)]
pub struct TagUnionDef {
    pub variants: Vec<TagDef>,
}

#[derive(Debug, Clone)]
pub struct TagDef {
    pub name: Ident,
    pub value: Option<Box<Type>>,
}

#[derive(Debug, Clone)]
pub struct StructureDef {
    pub field: Vec<StructureFieldDef>,
}

#[derive(Debug, Clone)]
pub struct StructureFieldDef {
    pub field: Ident,
    pub ty: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: Box<ExprKind>,
    pub id: NodeId,
}

// Always boxed
#[derive(Debug, Clone)]
pub enum ExprKind {
    Fn(FnExpr),
    Block(BlockExpr),
    Cons(ConsExpr),
    Match(MatchExpr),
    Call(CallExpr),
    Access(AccessExpr),
    Ref(RefExpr),
    Literal(LiteralExpr),
    Bin(BinExpr),
    Return(ReturnExpr),
}

#[derive(Debug, Clone)]
pub struct FnExpr {
    pub id: NodeId,
    pub arg: Ident,
    pub arg_ty: Box<Type>,
    pub ret_ty: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct BlockExpr {
    pub id: NodeId,
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub enum ConsExpr {
    ConsStructure(ConsStructure),
    ConsTag(ConsTag),
}

#[derive(Debug, Clone)]
pub struct ConsStructure {
    pub fields: Vec<ConsField>,
}

#[derive(Debug, Clone)]
pub struct ConsField {
    pub name: Ident,
    pub value: Expr,
}

#[derive(Debug, Clone)]
pub struct ConsTag {
    pub tag: Ident,
    pub value: Option<Expr>,
}

#[derive(Debug, Clone)]
pub struct MatchExpr {
    pub scrutinee: Expr,
    pub arms: Vec<MatchArm>,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Structure(StructurePattern),
    Tag(TagPattern),
    Catchall,
}

#[derive(Debug, Clone)]
pub struct StructurePattern {
    // Only allows one level of nesting
    pub fields: Vec<Ident>,
}

#[derive(Debug, Clone)]
pub struct TagPattern {
    pub name: Ident,
    // Only allows one level of nesting
    pub value: Option<Ident>,
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub callee: Expr,
    pub arg: Expr,
}

#[derive(Debug, Clone)]
pub struct AccessExpr {
    pub value: Expr,
    pub field: Ident,
}

#[derive(Debug, Clone)]
pub struct RefExpr {
    pub ident: Ident,
}

#[derive(Debug, Clone)]
pub enum LiteralExpr {
    String(String),
    Number(f64),
}

#[derive(Debug, Clone)]
pub struct BinExpr {
    pub op: BinOp,
    pub lhs: Expr,
    pub rhs: Expr,
}

/// Binary operations
#[derive(Debug, Clone)]
pub enum BinOp {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `%`
    Mod,
    /// `and`
    And,
    /// `or`
    Or,
    /// `&`
    BitAnd,
    /// `|`
    BitOr,
    /// `<<`
    ShiftLeft,
    /// `>>`
    ShiftRight,
    /// `<`
    Less,
    /// `<=`
    LessEqual,
    /// `>`
    Greater,
    /// `>=`
    GreaterEqual,
    /// `==`
    Equal,
    /// `!=`
    NotEqual,
}

#[derive(Debug, Clone)]
pub struct ReturnExpr {
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct Decl {
    pub is_const: bool,
    pub name: Ident,
    pub value: Expr,
}

#[derive(Debug, Clone)]
pub struct Variable(Ident);

#[derive(Debug, Clone)]
pub struct Ident(String);

/// Uniquely identifies the AST node in the compiler tables
#[derive(Debug, Clone)]
pub struct NodeId(u64);
