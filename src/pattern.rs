use std::rc::Rc;

use pest::Span;

use crate::ast::Ident;

#[derive(Debug, Clone)]
pub enum Pattern<'i> {
    Single(Ident<'i>),
    List {
        patterns: Vec<Pattern<'i>>,
        span: Span<'i>,
    },
    Entity {
        patterns: Vec<FieldPattern<'i>>,
        span: Span<'i>,
    },
    Nil(Span<'i>),
    Bool {
        b: bool,
        span: Span<'i>,
    },
    Int {
        int: i64,
        span: Span<'i>,
    },
    String {
        string: Rc<str>,
        span: Span<'i>,
    },
}

impl<'i> Pattern<'i> {
    pub fn span(&self) -> &Span<'i> {
        match self {
            Pattern::Single(ident) => &ident.span,
            Pattern::List { span, .. } => span,
            Pattern::Entity { span, .. } => span,
            Pattern::Nil(span) => span,
            Pattern::Bool { span, .. } => span,
            Pattern::Int { span, .. } => span,
            Pattern::String { span, .. } => span,
        }
    }
}

#[derive(Debug, Clone)]
pub enum FieldPattern<'i> {
    SameName(Ident<'i>),
    Pattern {
        field: Ident<'i>,
        pattern: Pattern<'i>,
        span: Span<'i>,
    },
}
