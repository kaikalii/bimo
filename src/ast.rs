#![allow(clippy::upper_case_acronyms)]

use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
};

use pest::Span;

#[derive(Clone)]
pub struct Ident<'i> {
    pub name: &'i str,
    pub span: Span<'i>,
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

impl<'i> PartialOrd for Ident<'i> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.name.partial_cmp(other.name)
    }
}

impl<'i> Ord for Ident<'i> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.name.cmp(other.name)
    }
}

impl<'i> Hash for Ident<'i> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.name.hash(state);
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
    Access(AccessExpr<'i>),
}

impl<'i> Node<'i> {
    pub fn span(&self) -> &Span<'i> {
        match self {
            Node::Term(_, span) => span,
            Node::BinExpr(expr) => &expr.span,
            Node::UnExpr(expr) => &expr.span,
            Node::Call(expr) => &expr.span,
            Node::Access(expr) => &expr.span,
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

#[derive(Debug, Clone, Copy)]
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
pub enum Accessor<'i> {
    Field(&'i str),
}

#[derive(Debug, Clone)]
pub struct AccessExpr<'i> {
    pub root: Box<Node<'i>>,
    pub accessor: Accessor<'i>,
    pub span: Span<'i>,
}

#[derive(Debug, Clone)]
pub enum Entry<'i> {
    Field(Ident<'i>, Node<'i>),
    Tag(Ident<'i>),
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
    Tag(Ident<'i>),
    String(Rc<str>),
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
