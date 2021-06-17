#![allow(clippy::upper_case_acronyms)]

use std::{collections::HashSet, ffi::OsStr, fmt, rc::Rc};

use itertools::Itertools;
use pest::{
    error::{Error as PestError, ErrorVariant},
    iterators::Pair,
    Parser, RuleType, Span,
};

use crate::{
    ast::*,
    entity::Key,
    pattern::{FieldPattern, Pattern, StringPattern},
    runtime::Runtime,
};

#[derive(Debug)]
pub enum CheckError<'i> {
    UnknownDef(Ident<'i>),
    Parse(PestError<Rule>),
    InvalidLiteral(FileSpan<'i>),
    DefUnderscoreTerminus(FileSpan<'i>),
    FunctionNamedUnderscore(FileSpan<'i>),
    ForbiddenRedefinition(Ident<'i>),
    LastItemNotExpression(FileSpan<'i>),
    InvalidStringPattern(FileSpan<'i>),
    EntityDefaultNotAtEnd(FileSpan<'i>),
}

impl<'i> fmt::Display for CheckError<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CheckError::UnknownDef(ident) => {
                format_span(format!("Unknown def: {:?}", ident.name), &ident.span, f)
            }
            CheckError::Parse(e) => e.fmt(f),
            CheckError::InvalidLiteral(span) => format_span("Invalid literal", span, f),
            CheckError::DefUnderscoreTerminus(span) => {
                format_span("Def names may not start or end with '_'", span, f)
            }
            CheckError::FunctionNamedUnderscore(span) => {
                format_span("Function cannot be named '_'", span, f)
            }
            CheckError::ForbiddenRedefinition(ident) => format_span(
                format!("{} cannot be redefined", ident.name),
                &ident.span,
                f,
            ),
            CheckError::LastItemNotExpression(span) => {
                format_span("The last item in a block must be an expression", span, f)
            }
            CheckError::InvalidStringPattern(span) => {
                format_span("Invalid string pattern", span, f)
            }
            CheckError::EntityDefaultNotAtEnd(span) => {
                format_span("Entity default must be at the end", span, f)
            }
        }
    }
}

pub(crate) fn format_span(
    message: impl Into<String>,
    span: &FileSpan,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let error = PestError::<Rule>::new_from_span(
        ErrorVariant::CustomError {
            message: message.into(),
        },
        span.span.clone(),
    );
    if let Some(file) = &span.file {
        write!(f, "{}", file.to_string_lossy())?;
    }
    write!(f, "{}", error)
}

fn only<R>(pair: Pair<R>) -> Pair<R>
where
    R: RuleType,
{
    pair.into_inner().next().unwrap()
}

static FORBIDDEN_REDIFINITIONS: &[&str] = &["nil", "true", "false"];

#[derive(pest_derive::Parser)]
#[grammar = "grammar.pest"]
struct BimoParser;

pub(crate) fn parse<'i>(
    _runtime: &mut Runtime<'i>,
    input: &'i str,
    file: impl AsRef<OsStr>,
) -> Result<Items<'i>, Vec<CheckError<'i>>> {
    match BimoParser::parse(Rule::file, input) {
        Ok(mut pairs) => {
            let mut state = ParseState {
                input,
                file: file.as_ref().into(),
                scopes: vec![FunctionScope::default()],
                errors: Vec::new(),
            };
            for (name, _) in &*crate::builtin::FUNCTIONS {
                state.bind(&Ident::unspanned(*name));
            }
            crate::builtin::PATTERNS.with(|patterns| {
                for (name, _) in patterns {
                    state.bind(&Ident::unspanned(*name));
                }
            });
            let items = state.items(only(pairs.next().unwrap()));
            if state.errors.is_empty() {
                Ok(items)
            } else {
                Err(state.errors)
            }
        }
        Err(e) => Err(vec![CheckError::Parse(e)]),
    }
}

#[derive(Debug, Default)]
struct ParenScope<'i> {
    bindings: HashSet<&'i str>,
}

struct FunctionScope<'i> {
    scopes: Vec<ParenScope<'i>>,
}

impl<'i> Default for FunctionScope<'i> {
    fn default() -> Self {
        FunctionScope {
            scopes: vec![ParenScope::default()],
        }
    }
}

trait PairSpan<'i> {
    fn span(&self, state: &ParseState<'i>) -> FileSpan<'i>;
}

impl<'i> PairSpan<'i> for Pair<'i, Rule> {
    fn span(&self, state: &ParseState<'i>) -> FileSpan<'i> {
        FileSpan::new(self.as_span(), &state.file)
    }
}

pub struct ParseState<'i> {
    input: &'i str,
    file: Rc<OsStr>,
    scopes: Vec<FunctionScope<'i>>,
    errors: Vec<CheckError<'i>>,
}

impl<'i> ParseState<'i> {
    fn push_function_scope(&mut self) {
        self.scopes.push(FunctionScope::default());
    }
    fn pop_function_scope(&mut self) {
        self.scopes.pop().unwrap();
    }
    fn push_paren_scope(&mut self) {
        self.function_scope().scopes.push(ParenScope::default());
    }
    fn pop_paren_scope(&mut self) {
        self.function_scope().scopes.pop();
    }
    fn function_scope(&mut self) -> &mut FunctionScope<'i> {
        self.scopes.last_mut().unwrap()
    }
    fn span(&self, start: usize, end: usize) -> FileSpan<'i> {
        FileSpan::new(Span::new(self.input, start, end).unwrap(), &self.file)
    }
    fn depth(&self) -> u16 {
        self.scopes.iter().map(|fs| fs.scopes.len() as u16).sum()
    }
    fn bind(&mut self, ident: &Ident<'i>) {
        if FORBIDDEN_REDIFINITIONS.contains(&ident.name) {
            self.errors
                .push(CheckError::ForbiddenRedefinition(ident.clone()));
        } else if ident.name != "_" {
            self.function_scope()
                .scopes
                .last_mut()
                .unwrap()
                .bindings
                .insert(ident.name);
        }
    }
    fn bind_pattern(&mut self, pattern: &Pattern<'i>) {
        match pattern {
            Pattern::Single(ident) => self.bind(ident),
            Pattern::Value(_) => {}
            Pattern::Bound { left, .. } => self.bind_pattern(left),
            Pattern::List { patterns, .. } => {
                for pattern in patterns {
                    self.bind_pattern(pattern);
                }
            }
            Pattern::Entity { patterns, .. } => {
                for pattern in patterns {
                    match pattern {
                        FieldPattern::SameName(ident) => self.bind(ident),
                        FieldPattern::Pattern { pattern, .. } => self.bind_pattern(pattern),
                    }
                }
            }
            Pattern::Nil(_)
            | Pattern::Bool { .. }
            | Pattern::Int { .. }
            | Pattern::String { .. }
            | Pattern::Builtin { .. } => {}
        }
    }
    fn items(&mut self, pair: Pair<'i, Rule>) -> Items<'i> {
        let mut items = Vec::new();
        for pair in pair.into_inner() {
            match pair.as_rule() {
                Rule::item => items.push(self.item(pair)),
                Rule::EOI => {}
                rule => unreachable!("{:?}", rule),
            }
        }
        if let Some(last_item) = items.last() {
            if self.depth() > 1 && !matches!(last_item, Item::Node(_)) {
                self.errors
                    .push(CheckError::LastItemNotExpression(last_item.span().clone()));
            }
        }
        items
    }
    fn item(&mut self, pair: Pair<'i, Rule>) -> Item<'i> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::expr => Item::Node(self.expr(pair)),
            Rule::function_def => Item::FunctionDef(self.function_def(pair)),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn ident(&mut self, pair: Pair<'i, Rule>) -> Ident<'i> {
        let name = pair.as_str();
        let span = pair.span(self);
        if (name.starts_with('_') || name.ends_with('_')) && name != "_" {
            self.errors
                .push(CheckError::DefUnderscoreTerminus(span.clone()));
        }
        Ident { name, span }
    }
    fn bound_param(&mut self, pair: Pair<'i, Rule>) -> Param<'i> {
        let pattern = self.rebindable_pattern(only(pair));
        self.bind_pattern(&pattern);
        pattern
    }
    fn function_def(&mut self, pair: Pair<'i, Rule>) -> FunctionDef<'i> {
        let mut pairs = pair.into_inner();
        let ident = self.ident(pairs.next().unwrap());
        if ident.is_underscore() {
            self.errors
                .push(CheckError::FunctionNamedUnderscore(ident.span.clone()));
        }
        let mut params = Vec::new();
        let mut body = None;
        self.push_function_scope();
        for pair in pairs {
            match pair.as_rule() {
                Rule::param => {
                    let param = self.bound_param(pair);
                    params.push(param)
                }
                Rule::expr => {
                    self.bind(&ident);
                    body = Some(self.expr(pair));
                    break;
                }
                rule => unreachable!("{:?}", rule),
            }
        }
        self.pop_function_scope();
        self.bind(&ident);
        FunctionDef {
            ident,
            params,
            body: body.unwrap(),
        }
    }
    fn rebindable_pattern(&mut self, pair: Pair<'i, Rule>) -> Pattern<'i> {
        let span = pair.span(self);
        let mut pairs = pair.into_inner();
        let first = pairs.next().unwrap();
        let left = self.pattern(first);
        if let Some(second) = pairs.next() {
            let right = self.pattern_impl(second, true);
            Pattern::Bound {
                left: left.into(),
                right: right.into(),
                span,
            }
        } else {
            left
        }
    }
    fn pattern(&mut self, pair: Pair<'i, Rule>) -> Pattern<'i> {
        self.pattern_impl(pair, false)
    }
    fn pattern_impl(&mut self, pair: Pair<'i, Rule>, right: bool) -> Pattern<'i> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::ident if pair.as_str() == "nil" => Pattern::Nil(pair.span(self)),
            Rule::ident if pair.as_str() == "true" => Pattern::Bool {
                b: true,
                span: pair.span(self),
            },
            Rule::ident if pair.as_str() == "false" => Pattern::Bool {
                b: false,
                span: pair.span(self),
            },
            Rule::ident if right => {
                let ident = self.ident(pair);
                self.verify_ident(&ident);
                Pattern::Value(ident)
            }
            Rule::ident => Pattern::Single(self.ident(pair)),
            Rule::list_pattern => {
                let span = pair.span(self);
                let mut patterns = Vec::new();
                for pair in pair.into_inner() {
                    patterns.push(self.pattern(pair));
                }
                Pattern::List { patterns, span }
            }
            Rule::entity_pattern => {
                let span = pair.span(self);
                let mut patterns = Vec::new();
                for pair in pair.into_inner() {
                    patterns.push(self.field_pattern(pair));
                }
                Pattern::Entity { patterns, span }
            }
            Rule::int => {
                let span = pair.span(self);
                Pattern::Int {
                    int: self.int(pair),
                    span,
                }
            }
            Rule::quoted_string | Rule::format_string => {
                let span = pair.span(self);
                Pattern::String {
                    pattern: StringPattern {
                        is_regex: false,
                        parts: self.either_string(pair),
                        resolved: None,
                    }
                    .into(),
                    span,
                }
            }
            Rule::regex => self.regex(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn field_pattern(&mut self, pair: Pair<'i, Rule>) -> FieldPattern<'i> {
        let span = pair.span(self);
        let mut pairs = pair.into_inner();
        let ident = self.ident(pairs.next().unwrap());
        if let Some(pair) = pairs.next() {
            FieldPattern::Pattern {
                field: ident,
                pattern: self.pattern(pair),
                span,
            }
        } else {
            FieldPattern::SameName(ident)
        }
    }
    fn regex(&mut self, pair: Pair<'i, Rule>) -> Pattern<'i> {
        let span = pair.span(self);
        Pattern::String {
            pattern: StringPattern {
                is_regex: false,
                parts: self.either_string(only(pair)),
                resolved: None,
            }
            .into(),
            span,
        }
    }
    fn expr(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::expr_or => self.expr_or(pair),
            Rule::expr_if => self.expr_if(pair),
            Rule::expr_match => self.expr_match(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn expr_if(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.span(self);
        let mut pairs = pair.into_inner();
        self.push_paren_scope();
        let condition = self.expr(pairs.next().unwrap());
        let if_true = self.expr(pairs.next().unwrap());
        self.pop_paren_scope();
        Node::If(IfExpr {
            condition: condition.into(),
            if_true: if_true.into(),
            if_false: self.expr(pairs.next().unwrap()).into(),
            span,
        })
    }
    fn expr_match(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.span(self);
        let mut pairs = pair.into_inner();
        let matched = self.expr(pairs.next().unwrap());
        let mut cases = Vec::new();
        while let Some(pattern) = pairs.next() {
            if pattern.as_rule() == Rule::EOI {
                break;
            }
            let body = pairs.next().unwrap();
            self.push_paren_scope();
            let pattern = self.rebindable_pattern(pattern);
            self.bind_pattern(&pattern);
            let body = self.expr(body);
            cases.push(Case { pattern, body });
            self.pop_paren_scope();
        }
        Node::Match(MatchExpr {
            matched: matched.into(),
            cases,
            span,
        })
    }
    fn expr_or(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.span(self);
        let mut left = self.expr_and(left);
        let start_depth = self.depth();
        for (op, right) in pairs.tuples() {
            self.push_paren_scope();
            let op_span = op.span(self);
            let op = match op.as_str() {
                "or" => BinOp::Or,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.span.start(), right.as_span().end());
            let right = self.expr_and(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        while self.depth() > start_depth {
            self.pop_paren_scope();
        }
        left
    }
    fn expr_and(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.span(self);
        let mut left = self.expr_bind(left);
        let start_depth = self.depth();
        for (op, right) in pairs.tuples() {
            self.push_paren_scope();
            let op_span = op.span(self);
            let op = match op.as_str() {
                "and" => BinOp::And,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.span.start(), right.as_span().end());
            let right = self.expr_bind(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        while self.depth() > start_depth {
            self.pop_paren_scope();
        }
        left
    }
    fn expr_bind(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::binding => Node::Bind(self.binding(pair)),
            Rule::expr_cmp => self.expr_cmp(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn binding(&mut self, pair: Pair<'i, Rule>) -> BindExpr<'i> {
        let span = pair.span(self);
        let mut pairs = pair.into_inner();
        let first = pairs.next().unwrap();
        let pattern = self.rebindable_pattern(first);
        let body = pairs.next().unwrap();
        let body = match body.as_rule() {
            Rule::expr_cmp => self.expr_cmp(body),
            Rule::expr_match => self.expr_match(body),
            Rule::expr_if => self.expr_if(body),
            rule => unreachable!("{:?}", rule),
        };
        self.bind_pattern(&pattern);
        BindExpr {
            pattern,
            body: body.into(),
            span,
        }
    }
    fn expr_cmp(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.span(self);
        let mut left = self.expr_as(left);
        for (op, right) in pairs.tuples() {
            let op_span = op.span(self);
            let op = match op.as_str() {
                "==" => BinOp::Equals,
                "!=" => BinOp::NotEquals,
                "<=" => BinOp::LessOrEqual,
                ">=" => BinOp::GreaterOrEqual,
                "<" => BinOp::Less,
                ">" => BinOp::Greater,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.span.start(), right.as_span().end());
            let right = self.expr_as(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        left
    }
    fn expr_as(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.span(self);
        let mut left = self.expr_mdr(left);
        for (op, right) in pairs.tuples() {
            let op_span = op.span(self);
            let op = match op.as_str() {
                "+" => BinOp::Add,
                "-" => BinOp::Sub,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.span.start(), right.as_span().end());
            let right = self.expr_mdr(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        left
    }
    fn expr_mdr(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.span(self);
        let mut left = self.expr_neg(left);
        for (op, right) in pairs.tuples() {
            let op_span = op.span(self);
            let op = match op.as_str() {
                "*" => BinOp::Mul,
                "/" => BinOp::Div,
                "%" => BinOp::Rem,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.span.start(), right.as_span().end());
            let right = self.expr_neg(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        left
    }
    fn expr_neg(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.span(self);
        let mut pairs = pair.into_inner();
        let first = pairs.next().unwrap();
        let op = match first.as_str() {
            "-" => Some(UnOp::Neg),
            _ => None,
        };
        let inner = if op.is_some() {
            pairs.next().unwrap()
        } else {
            first
        };
        let inner = self.expr_access(inner);
        if let Some(op) = op {
            Node::UnExpr(UnExpr::new(inner, op, span))
        } else {
            inner
        }
    }
    fn expr_access(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let mut root = self.term(pairs.next().unwrap());
        for pair in pairs {
            let pair = only(pair);
            match pair.as_rule() {
                Rule::method_call => {
                    let span = pair.span(self);
                    let mut pairs = pair.into_inner();
                    let ident = self.ident(pairs.next().unwrap());
                    self.verify_ident(&ident);
                    let mut args = self.call_args(pairs.next().unwrap());
                    args.insert(0, root);
                    let ident_span = ident.span.clone();
                    root = Node::Call(CallExpr {
                        caller: Node::Term(Term::Ident(ident), ident_span).into(),
                        args,
                        span,
                    });
                }
                Rule::field_access => {
                    let span = pair.span(self);
                    let ident = self.ident(only(pair));
                    root = Node::Access(AccessExpr {
                        root: root.into(),
                        accessor: Accessor::Key(Key::Field(ident.name)),
                        span,
                    })
                }
                Rule::call_args => {
                    let span = pair.span(self);
                    let args = self.call_args(pair);
                    root = Node::Call(CallExpr {
                        caller: root.into(),
                        args,
                        span,
                    })
                }
                rule => unreachable!("{:?}", rule),
            }
        }
        root
    }
    fn call_args(&mut self, pair: Pair<'i, Rule>) -> Vec<Node<'i>> {
        pair.into_inner().map(|pair| self.expr(pair)).collect()
    }
    fn int(&mut self, pair: Pair<'i, Rule>) -> i64 {
        match pair.as_str().parse::<i64>() {
            Ok(i) => i,
            Err(_) => {
                self.errors
                    .push(CheckError::InvalidLiteral(pair.span(self)));
                0
            }
        }
    }
    fn term(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.span(self);
        let pair = only(pair);
        let term = match pair.as_rule() {
            Rule::int => Term::Int(self.int(pair)),
            Rule::real => match pair.as_str().parse::<f64>() {
                Ok(i) => Term::Real(i),
                Err(_) => {
                    self.errors
                        .push(CheckError::InvalidLiteral(pair.span(self)));
                    Term::Real(0.0)
                }
            },
            Rule::ident => self.ident_term(pair),
            Rule::paren_expr => {
                let pair = only(pair);
                self.push_paren_scope();
                let items = self.items(pair);
                self.pop_paren_scope();
                Term::Expr(items)
            }
            Rule::string => {
                let parts = self.string(pair);
                Term::String(parts)
            }
            Rule::list_literal => {
                Term::List(pair.into_inner().map(|pair| self.expr(pair)).collect())
            }
            Rule::tag_literal => Term::Tag(self.ident(only(pair))),
            Rule::closure => {
                let span = pair.span(self);
                let mut pairs = pair.into_inner();
                let params_pairs = pairs.next().unwrap().into_inner();
                let params: Vec<Param> = params_pairs.map(|pair| self.bound_param(pair)).collect();
                self.push_function_scope();
                for param in &params {
                    self.bind_pattern(param);
                }
                let pair = pairs.next().unwrap();
                let body = self.function_body(pair);
                self.pop_function_scope();
                Term::Closure(Closure { span, params, body }.into())
            }
            Rule::entity_literal => {
                let mut entries = Vec::new();
                let mut default: Option<Box<Node>> = None;
                self.push_paren_scope();
                for pair in pair.into_inner() {
                    if let Some(default) = &default {
                        self.errors
                            .push(CheckError::EntityDefaultNotAtEnd(default.span().clone()));
                    }
                    match pair.as_rule() {
                        Rule::entity_item => {
                            let mut pairs = pair.into_inner();
                            let first = pairs.next().unwrap();
                            match first.as_rule() {
                                Rule::tag_literal => {
                                    entries.push(Entry::Tag(self.ident(only(first))))
                                }
                                Rule::binding => {
                                    let binding = self.binding(first);
                                    entries.push(Entry::Bind(binding));
                                }
                                Rule::function_def => {
                                    entries.push(Entry::FunctionDef(self.function_def(first)))
                                }
                                Rule::expr => {
                                    let key = self.expr(first.clone());
                                    let value = self.expr(pairs.next().unwrap());
                                    entries.push(Entry::Index(key, value));
                                }
                                Rule::entity_default => {
                                    self.pop_paren_scope();
                                    default = Some(self.expr(only(first)).into())
                                }
                                Rule::ident => {
                                    let ident = self.ident(first);
                                    self.verify_ident(&ident);
                                    entries.push(Entry::SameName(ident));
                                }
                                rule => unreachable!("{:?}", rule),
                            }
                        }
                        rule => unreachable!("{:?}", rule),
                    }
                }
                if default.is_none() {
                    self.pop_paren_scope();
                }
                Term::Entity { entries, default }
            }
            Rule::pattern_literal => {
                let pair = only(pair);
                match pair.as_rule() {
                    Rule::regex => Term::Pattern(self.regex(pair).into()),
                    Rule::pattern => Term::Pattern(self.pattern(pair).into()),
                    rule => unreachable!("{:?}", rule),
                }
            }
            rule => unreachable!("{:?}", rule),
        };
        Node::Term(term, span)
    }
    fn ident_term(&mut self, pair: Pair<'i, Rule>) -> Term<'i> {
        match pair.as_str() {
            "nil" => Term::Nil,
            "true" => Term::Bool(true),
            "false" => Term::Bool(false),
            _ => {
                let ident = self.ident(pair);
                self.verify_ident(&ident);
                Term::Ident(ident)
            }
        }
    }
    fn lookup_name<'b>(scopes: &'b [FunctionScope<'i>], name: &str) -> bool {
        scopes.iter().rev().any(|fscope| {
            fscope
                .scopes
                .iter()
                .rev()
                .any(|pscope| pscope.bindings.contains(name))
        })
    }
    /// Verify that a binding with the given ident exists
    fn verify_ident(&mut self, ident: &Ident<'i>) {
        let exists = Self::lookup_name(&self.scopes, ident.name);
        if !exists {
            self.errors.push(CheckError::UnknownDef(ident.clone()));
        }
    }
    fn function_body(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        match pair.as_rule() {
            Rule::expr => self.expr(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn string(&mut self, pair: Pair<'i, Rule>) -> Vec<Vec<StringPart<'i>>> {
        let mut parts = Vec::new();
        for pair in pair.into_inner() {
            parts.push(self.either_string(pair));
        }
        parts
    }
    fn either_string(&mut self, pair: Pair<'i, Rule>) -> Vec<StringPart<'i>> {
        let mut parts = Vec::new();
        let mut s = String::new();
        for pair in only(pair).into_inner() {
            match pair.as_rule() {
                Rule::string_text | Rule::format_string_text => s.push_str(pair.as_str()),
                Rule::predefined => s.push(match pair.as_str() {
                    "0" => '\0',
                    "r" => '\r',
                    "t" => '\t',
                    "n" => '\n',
                    "\\" => '\\',
                    "'" => '\'',
                    "\"" => '"',
                    s => unreachable!("{}", s),
                }),
                Rule::byte => {
                    let byte = pair
                        .into_inner()
                        .map(|pair| pair.as_str())
                        .collect::<String>()
                        .parse::<u8>()
                        .unwrap();
                    s.push(byte as char);
                }
                Rule::unicode => {
                    let u = pair
                        .into_inner()
                        .map(|pair| pair.as_str())
                        .collect::<String>()
                        .parse::<u32>()
                        .unwrap();
                    s.push(
                        std::char::from_u32(u).unwrap_or_else(|| panic!("invalid unicode {}", u)),
                    );
                }
                Rule::format_arg => {
                    if !s.is_empty() {
                        parts.push(StringPart::Raw(s.into()));
                        s = String::new();
                    }
                    parts.push(StringPart::Format(self.expr(only(pair))));
                }
                Rule::escaped_left_curly => s.push('{'),
                Rule::escaped_right_curly => s.push('}'),
                rule => unreachable!("{:?}", rule),
            }
        }
        if !s.is_empty() {
            parts.push(StringPart::Raw(s.into()))
        }
        parts
    }
}
