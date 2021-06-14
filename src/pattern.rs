use std::{cell::RefCell, fmt, rc::Rc};

use pest::Span;
use regex::Regex;

use crate::{
    ast::{Ident, StringPart},
    format::FormatSettings,
};

#[derive(Clone)]
pub struct StringPattern<'i> {
    pub is_regex: bool,
    pub parts: Vec<StringPart<'i>>,
    pub resolved: Option<Rc<Regex>>,
}

#[derive(Clone)]
pub enum Pattern<'i> {
    Single(Ident<'i>),
    Bound {
        left: Box<Pattern<'i>>,
        right: Box<Pattern<'i>>,
        span: Span<'i>,
    },
    Value(Ident<'i>),
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
        pattern: RefCell<StringPattern<'i>>,
        span: Span<'i>,
    },
}

impl<'i> Pattern<'i> {
    pub fn span(&self) -> &Span<'i> {
        match self {
            Pattern::Single(ident) | Pattern::Value(ident) => &ident.span,
            Pattern::Bound { span, .. } => span,
            Pattern::List { span, .. } => span,
            Pattern::Entity { span, .. } => span,
            Pattern::Nil(span) => span,
            Pattern::Bool { span, .. } => span,
            Pattern::Int { span, .. } => span,
            Pattern::String { span, .. } => span,
        }
    }
}

#[derive(Clone)]
pub enum FieldPattern<'i> {
    SameName(Ident<'i>),
    Pattern {
        field: Ident<'i>,
        pattern: Pattern<'i>,
        span: Span<'i>,
    },
}

impl<'i> fmt::Debug for Pattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FormatSettings::default().format(self).fmt(f)
    }
}

impl<'i> fmt::Display for Pattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FormatSettings::default().format(self).fmt(f)
    }
}

impl<'i> fmt::Debug for FieldPattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FormatSettings::default().format(self).fmt(f)
    }
}

impl<'i> fmt::Display for FieldPattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FormatSettings::default().format(self).fmt(f)
    }
}
