#![allow(clippy::upper_case_acronyms)]

use std::fmt;

use pest::Span;

pub type IdentId = u64;
pub type TagId = u64;

#[derive(Clone)]
pub struct Ident<'i> {
    pub name: &'i str,
    pub span: Span<'i>,
    pub id: IdentId,
}

impl<'i> Ident<'i> {
    pub fn is_underscore(&self) -> bool {
        self.name == "_"
    }
}

impl<'i> PartialEq for Ident<'i> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl<'i> fmt::Debug for Ident<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.name.fmt(f)
    }
}

impl<'i> fmt::Display for Ident<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.name.fmt(f)
    }
}

impl<'i> Eq for Ident<'i> {}
#[derive(Debug, Clone)]
pub enum Item<'i> {
    Node(Node<'i>),
    Def(Def<'i>),
}

impl<'i> Item<'i> {
    pub fn span(&self) -> &Span<'i> {
        match self {
            Item::Node(node) => node.span(),
            Item::Def(def) => &def.ident.span,
        }
    }
}

pub type Items<'i> = Vec<Item<'i>>;

#[derive(Debug, Clone)]
pub struct Param<'i> {
    pub ident: Ident<'i>,
}

pub type Params<'i> = Vec<Param<'i>>;

#[derive(Debug, Clone)]
pub struct Def<'i> {
    pub ident: Ident<'i>,
    pub params: Params<'i>,
    pub items: Items<'i>,
}

#[derive(Debug, Clone)]
pub enum Node<'i> {
    Term(Term<'i>, Span<'i>),
    BinExpr(BinExpr<'i>),
    UnExpr(UnExpr<'i>),
    Call(CallExpr<'i>),
}

impl<'i> Node<'i> {
    pub fn span(&self) -> &Span<'i> {
        match self {
            Node::Term(_, span) => span,
            Node::BinExpr(expr) => &expr.span,
            Node::UnExpr(expr) => &expr.span,
            Node::Call(expr) => &expr.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BinExpr<'i> {
    pub left: Box<Node<'i>>,
    pub right: Box<Node<'i>>,
    pub op: BinOp,
    pub span: Span<'i>,
    pub op_span: Span<'i>,
}

impl<'i> BinExpr<'i> {
    pub fn new(
        left: Node<'i>,
        right: Node<'i>,
        op: BinOp,
        span: Span<'i>,
        op_span: Span<'i>,
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
pub struct UnExpr<'i> {
    pub inner: Box<Node<'i>>,
    pub op: UnOp,
    pub span: Span<'i>,
}

impl<'i> UnExpr<'i> {
    pub fn new(inner: Node<'i>, op: UnOp, span: Span<'i>) -> Self {
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
pub struct CallExpr<'i> {
    pub caller: Box<Node<'i>>,
    pub args: Vec<Node<'i>>,
    pub span: Span<'i>,
}

#[derive(Debug, Clone)]
pub struct PushExpr<'i> {
    pub head: Box<Node<'i>>,
    pub tail: Box<Node<'i>>,
    pub span: Span<'i>,
}

#[derive(Debug, Clone)]
pub enum Entry<'i> {
    Field(IdentId, Node<'i>),
    Tag(TagId),
    Index(Node<'i>, Node<'i>),
}

#[derive(Debug, Clone)]
pub enum Term<'i> {
    Nil,
    Bool(bool),
    Expr(Items<'i>),
    Int(i64),
    Real(f64),
    Ident(Ident<'i>),
    Tag(TagId),
    String(String),
    List(Vec<Node<'i>>),
    Entity {
        entries: Vec<Entry<'i>>,
        default: Option<Box<Node<'i>>>,
    },
    Closure(Box<Closure<'i>>),
}

#[derive(Debug, Clone)]
pub struct Closure<'i> {
    pub span: Span<'i>,
    pub params: Params<'i>,
    pub body: Items<'i>,
}
