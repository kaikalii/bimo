use std::rc::Rc;

use pest::Span;

use crate::ast::Ident;

#[derive(Debug, Clone)]
pub enum PatternType<'i> {
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

#[derive(Debug, Clone)]
pub struct Pattern<'i> {
    pub ty: PatternType<'i>,
    pub required: bool,
}

impl<'i> Pattern<'i> {
    pub fn span(&self) -> &Span<'i> {
        match &self.ty {
            PatternType::Single(ident) => &ident.span,
            PatternType::List { span, .. } => span,
            PatternType::Entity { span, .. } => span,
            PatternType::Nil(span) => span,
            PatternType::Bool { span, .. } => span,
            PatternType::Int { span, .. } => span,
            PatternType::String { span, .. } => span,
        }
    }
}

#[derive(Debug, Clone)]
pub enum FieldPatternType<'i> {
    SameName(Ident<'i>),
    Pattern {
        field: Ident<'i>,
        pattern: Pattern<'i>,
        span: Span<'i>,
    },
}

#[derive(Debug, Clone)]
pub struct FieldPattern<'i> {
    pub ty: FieldPatternType<'i>,
    pub required: bool,
}
