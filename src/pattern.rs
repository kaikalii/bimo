use std::{cell::RefCell, fmt, rc::Rc};

use pest::Span;
use regex::Regex;

use crate::{
    ast::{Ident, StringPart},
    format::FormatSettings,
    runtime::RuntimeResult,
    value::Value,
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
    Builtin {
        f: Rc<dyn Fn(&Value<'i>) -> RuntimeResult<'i>>,
        name: String,
    },
}

impl<'i> Pattern<'i> {
    pub fn builtin(
        name: impl Into<String>,
        f: impl Fn(&Value<'i>) -> RuntimeResult<'i> + 'static,
    ) -> Self {
        Pattern::Builtin {
            name: name.into(),
            f: Rc::new(f),
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
