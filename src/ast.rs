#![allow(clippy::upper_case_acronyms)]

use pest::Span;

#[derive(Debug, Clone)]
pub struct Ident<'a> {
    pub name: &'a str,
    pub span: Span<'a>,
}

impl<'a> Ident<'a> {
    pub fn is_underscore(&self) -> bool {
        self.name == "_"
    }
}

impl<'a> PartialEq for Ident<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl<'a> Eq for Ident<'a> {}
#[derive(Debug, Clone)]
pub enum Item<'a> {
    Node(Node<'a>),
    Def(Def<'a>),
}

impl<'a> Item<'a> {
    pub fn span(&self) -> &Span<'a> {
        match self {
            Item::Node(node) => node.span(),
            Item::Def(def) => &def.ident.span,
        }
    }
}

pub type Items<'a> = Vec<Item<'a>>;

#[derive(Debug, Clone)]
pub struct Param<'a> {
    pub ident: Ident<'a>,
}

pub type Params<'a> = Vec<Param<'a>>;

#[derive(Debug, Clone)]
pub struct Def<'a> {
    pub ident: Ident<'a>,
    pub params: Params<'a>,
    pub items: Items<'a>,
}

#[derive(Debug, Clone)]
pub enum Node<'a> {
    Term(Term<'a>, Span<'a>),
    BinExpr(BinExpr<'a>),
    UnExpr(UnExpr<'a>),
    Call(CallExpr<'a>),
}

impl<'a> Node<'a> {
    pub fn span(&self) -> &Span<'a> {
        match self {
            Node::Term(_, span) => span,
            Node::BinExpr(expr) => &expr.span,
            Node::UnExpr(expr) => &expr.span,
            Node::Call(expr) => &expr.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BinExpr<'a> {
    pub left: Box<Node<'a>>,
    pub right: Box<Node<'a>>,
    pub op: BinOp,
    pub span: Span<'a>,
    pub op_span: Span<'a>,
}

impl<'a> BinExpr<'a> {
    pub fn new(
        left: Node<'a>,
        right: Node<'a>,
        op: BinOp,
        span: Span<'a>,
        op_span: Span<'a>,
    ) -> Self {
        BinExpr {
            left: left.into(),
            right: right.into(),
            op,
            span,
            op_span,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Or,
    And,
    Equals,
    NotEquals,
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Debug, Clone)]
pub struct UnExpr<'a> {
    pub inner: Box<Node<'a>>,
    pub op: UnOp,
    pub span: Span<'a>,
}

impl<'a> UnExpr<'a> {
    pub fn new(inner: Node<'a>, op: UnOp, span: Span<'a>) -> Self {
        UnExpr {
            inner: inner.into(),
            op,
            span,
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnOp {
    Neg,
}

#[derive(Debug, Clone)]
pub struct CallExpr<'a> {
    pub caller: Box<Node<'a>>,
    pub args: Vec<Node<'a>>,
    pub span: Span<'a>,
}

#[derive(Debug, Clone)]
pub struct PushExpr<'a> {
    pub head: Box<Node<'a>>,
    pub tail: Box<Node<'a>>,
    pub span: Span<'a>,
}

#[derive(Debug, Clone)]
pub enum Term<'a> {
    Expr(Items<'a>),
    Int(i64),
    Real(f64),
    Ident(Ident<'a>),
    String(String),
    Closure(Box<Closure<'a>>),
}

#[derive(Debug, Clone)]
pub struct Closure<'a> {
    pub span: Span<'a>,
    pub params: Params<'a>,
    pub body: Items<'a>,
}
