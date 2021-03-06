use std::{
    cmp::Ordering,
    ffi::OsStr,
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
};

use pest::Span;

use crate::{entity::Key, pattern::Pattern};

#[derive(Debug, Clone)]
pub struct FileSpan<'i> {
    pub span: Span<'i>,
    pub file: Option<Rc<OsStr>>,
}

impl<'i> FileSpan<'i> {
    pub fn new(span: Span<'i>, file: impl AsRef<OsStr>) -> Self {
        let file = file.as_ref();
        let file = if file.is_empty() {
            None
        } else {
            Some(file.into())
        };
        FileSpan { span, file }
    }
    pub fn as_str(&self) -> &'i str {
        self.span.as_str()
    }
}

#[derive(Clone)]
pub struct Ident<'i> {
    pub name: &'i str,
    pub span: FileSpan<'i>,
}

impl<'i> Ident<'i> {
    pub fn new(name: &'i str, span: FileSpan<'i>) -> Self {
        Ident { name, span }
    }
    pub fn unspanned(name: &'i str) -> Self {
        Ident {
            name,
            span: FileSpan::new(Span::new("", 0, 0).unwrap(), ""),
        }
    }
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
    FunctionDef(FunctionDef<'i>),
}

impl<'i> Item<'i> {
    pub fn span(&self) -> &FileSpan<'i> {
        match self {
            Item::Node(node) => node.span(),
            Item::FunctionDef(def) => &def.ident.span,
        }
    }
}

pub type Items<'i> = Vec<Item<'i>>;

pub type Param<'i> = Pattern<'i>;
pub type Params<'i> = Vec<Param<'i>>;

#[derive(Debug, Clone)]
pub struct FunctionDef<'i> {
    pub ident: Ident<'i>,
    pub params: Params<'i>,
    pub body: Node<'i>,
}

#[derive(Debug, Clone)]
pub enum Node<'i> {
    Term(Term<'i>, FileSpan<'i>),
    BinExpr(BinExpr<'i>),
    UnExpr(UnExpr<'i>),
    Call(CallExpr<'i>),
    Access(AccessExpr<'i>),
    If(IfExpr<'i>),
    Match(MatchExpr<'i>),
    Bind(BindExpr<'i>),
}

impl<'i> Node<'i> {
    pub fn span(&self) -> &FileSpan<'i> {
        match self {
            Node::Term(_, span) => span,
            Node::BinExpr(expr) => &expr.span,
            Node::UnExpr(expr) => &expr.span,
            Node::Call(expr) => &expr.span,
            Node::Access(expr) => &expr.span,
            Node::If(expr) => &expr.span,
            Node::Match(expr) => &expr.span,
            Node::Bind(expr) => &expr.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BindExpr<'i> {
    pub pattern: Pattern<'i>,
    pub body: Box<Node<'i>>,
    pub span: FileSpan<'i>,
}

#[derive(Debug, Clone)]
pub struct IfExpr<'i> {
    pub condition: Box<Node<'i>>,
    pub if_true: Box<Node<'i>>,
    pub if_false: Box<Node<'i>>,
    pub span: FileSpan<'i>,
}

#[derive(Debug, Clone)]
pub struct Case<'i> {
    pub pattern: Pattern<'i>,
    pub body: Node<'i>,
}

#[derive(Debug, Clone)]
pub struct MatchExpr<'i> {
    pub matched: Box<Node<'i>>,
    pub cases: Vec<Case<'i>>,
    pub span: FileSpan<'i>,
}

#[derive(Debug, Clone)]
pub struct BinExpr<'i> {
    pub left: Box<Node<'i>>,
    pub right: Box<Node<'i>>,
    pub op: BinOp,
    pub span: FileSpan<'i>,
    pub op_span: FileSpan<'i>,
}

impl<'i> BinExpr<'i> {
    pub fn new(
        left: Node<'i>,
        right: Node<'i>,
        op: BinOp,
        span: FileSpan<'i>,
        op_span: FileSpan<'i>,
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
    pub span: FileSpan<'i>,
}

impl<'i> UnExpr<'i> {
    pub fn new(inner: Node<'i>, op: UnOp, span: FileSpan<'i>) -> Self {
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
    pub span: FileSpan<'i>,
}

#[derive(Debug, Clone)]
pub enum Accessor<'i> {
    Key(Key<'i>),
}

#[derive(Debug, Clone)]
pub struct AccessExpr<'i> {
    pub root: Box<Node<'i>>,
    pub accessor: Accessor<'i>,
    pub span: FileSpan<'i>,
}

#[derive(Debug, Clone)]
pub enum Entry<'i> {
    SameName(Ident<'i>),
    Bind(BindExpr<'i>),
    FunctionDef(FunctionDef<'i>),
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
    String(Vec<Vec<StringPart<'i>>>),
    List(Vec<Node<'i>>),
    Entity {
        entries: Vec<Entry<'i>>,
        default: Option<Box<Node<'i>>>,
    },
    Closure(Box<Closure<'i>>),
    Pattern(Rc<Pattern<'i>>),
}

#[derive(Debug, Clone)]
pub enum StringPart<'i> {
    Raw(Rc<str>),
    Format(Node<'i>),
}

#[derive(Debug, Clone)]
pub struct Closure<'i> {
    pub span: FileSpan<'i>,
    pub params: Params<'i>,
    pub body: Node<'i>,
}
