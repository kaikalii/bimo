#![allow(clippy::upper_case_acronyms)]

use std::{collections::HashSet, fmt};

use itertools::Itertools;
use pest::{
    error::{Error as PestError, ErrorVariant},
    iterators::Pair,
    Parser, RuleType, Span,
};

use crate::{
    ast::*,
    entity::Key,
    pattern::{FieldPattern, Pattern},
    runtime::Runtime,
};

#[derive(Debug)]
pub enum CheckError<'i> {
    UnknownDef(Ident<'i>),
    Parse(PestError<Rule>),
    InvalidLiteral(Span<'i>),
    DefUnderscoreTerminus(Span<'i>),
    FunctionNamedUnderscore(Span<'i>),
    ForbiddenRedefinition(Ident<'i>),
    LastItemNotExpression(Span<'i>),
    InvalidStringPattern(Span<'i>),
}

impl<'i> fmt::Display for CheckError<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CheckError::UnknownDef(ident) => format_span(
                format!("Unknown def: {:?}", ident.name),
                ident.span.clone(),
                f,
            ),
            CheckError::Parse(e) => e.fmt(f),
            CheckError::InvalidLiteral(span) => format_span("Invalid literal", span.clone(), f),
            CheckError::DefUnderscoreTerminus(span) => {
                format_span("Def names may not start or end with '_'", span.clone(), f)
            }
            CheckError::FunctionNamedUnderscore(span) => {
                format_span("Function cannot be named '_'", span.clone(), f)
            }
            CheckError::ForbiddenRedefinition(ident) => format_span(
                format!("{} cannot be redefined", ident.name),
                ident.span.clone(),
                f,
            ),
            CheckError::LastItemNotExpression(span) => format_span(
                "The last item in a block must be an expression",
                span.clone(),
                f,
            ),
            CheckError::InvalidStringPattern(span) => {
                format_span("Invalid string pattern", span.clone(), f)
            }
        }
    }
}

fn format_span(message: impl Into<String>, span: Span, f: &mut fmt::Formatter) -> fmt::Result {
    let error = PestError::<Rule>::new_from_span(
        ErrorVariant::CustomError {
            message: message.into(),
        },
        span.clone(),
    );
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
struct KinParser;

pub(crate) fn parse<'i>(
    _runtime: &mut Runtime<'i>,
    input: &'i str,
) -> Result<Items<'i>, Vec<CheckError<'i>>> {
    match KinParser::parse(Rule::file, input) {
        Ok(mut pairs) => {
            let mut state = ParseState {
                input,
                scopes: vec![FunctionScope::default()],
                errors: Vec::new(),
            };
            for (name, _) in &*crate::builtin::FUNCTIONS {
                state.bind(&Ident::unspanned(*name));
            }
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

pub struct ParseState<'i> {
    input: &'i str,
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
    fn span(&self, start: usize, end: usize) -> Span<'i> {
        Span::new(self.input, start, end).unwrap()
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
            | Pattern::String { .. } => {}
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
            Rule::function_def => self.function_def(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn ident(&mut self, pair: Pair<'i, Rule>) -> Ident<'i> {
        let name = pair.as_str();
        let span = pair.as_span();
        if (name.starts_with('_') || name.ends_with('_')) && name != "_" {
            self.errors
                .push(CheckError::DefUnderscoreTerminus(span.clone()));
        }
        Ident { name, span }
    }
    fn bound_param(&mut self, pair: Pair<'i, Rule>) -> Param<'i> {
        let pattern = self.pattern(only(pair));
        self.bind_pattern(&pattern);
        pattern
    }
    fn function_def(&mut self, pair: Pair<'i, Rule>) -> Item<'i> {
        let mut pairs = pair.into_inner();
        let ident = self.ident(pairs.next().unwrap());
        if ident.is_underscore() {
            self.errors
                .push(CheckError::FunctionNamedUnderscore(ident.span.clone()));
        }
        self.bind(&ident);
        self.push_function_scope();
        let mut params = Vec::new();
        let mut body = None;
        for pair in pairs {
            match pair.as_rule() {
                Rule::param => {
                    let param = self.bound_param(pair);
                    params.push(param)
                }
                Rule::expr => body = Some(self.expr(pair)),
                rule => unreachable!("{:?}", rule),
            }
        }
        self.pop_function_scope();
        Item::FunctionDef(FunctionDef {
            ident,
            params,
            body: body.unwrap(),
        })
    }
    fn pattern(&mut self, pair: Pair<'i, Rule>) -> Pattern<'i> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::ident if pair.as_str() == "nil" => Pattern::Nil(pair.as_span()),
            Rule::ident if pair.as_str() == "true" => Pattern::Bool {
                b: true,
                span: pair.as_span(),
            },
            Rule::ident if pair.as_str() == "false" => Pattern::Bool {
                b: false,
                span: pair.as_span(),
            },
            Rule::ident => Pattern::Single(self.ident(pair)),
            Rule::list_pattern => {
                let span = pair.as_span();
                let mut patterns = Vec::new();
                for pair in pair.into_inner() {
                    patterns.push(self.pattern(pair));
                }
                Pattern::List { patterns, span }
            }
            Rule::entity_pattern => {
                let span = pair.as_span();
                let mut patterns = Vec::new();
                for pair in pair.into_inner() {
                    patterns.push(self.field_pattern(pair));
                }
                Pattern::Entity { patterns, span }
            }
            Rule::int => {
                let span = pair.as_span();
                Pattern::Int {
                    int: self.int(pair),
                    span,
                }
            }
            Rule::string => {
                let span = pair.as_span();
                Pattern::String {
                    string: self.raw_string(pair).into(),
                    span,
                }
            }
            rule => unreachable!("{:?}", rule),
        }
    }
    fn field_pattern(&mut self, pair: Pair<'i, Rule>) -> FieldPattern<'i> {
        let span = pair.as_span();
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
    fn expr(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::expr_or => self.expr_or(pair),
            Rule::expr_if => self.expr_if(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn expr_if(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.as_span();
        let mut pairs = pair.into_inner();
        Node::If(IfExpr {
            condition: self.expr(pairs.next().unwrap()).into(),
            if_true: self.expr(pairs.next().unwrap()).into(),
            if_false: self.expr(pairs.next().unwrap()).into(),
            span,
        })
    }
    fn expr_or(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.as_span();
        let mut left = self.expr_and(left);
        let start_depth = self.depth();
        for (op, right) in pairs.tuples() {
            self.push_paren_scope();
            let op_span = op.as_span();
            let op = match op.as_str() {
                "or" => BinOp::Or,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.start(), right.as_span().end());
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
        let mut span = left.as_span();
        let mut left = self.expr_bind(left);
        let start_depth = self.depth();
        for (op, right) in pairs.tuples() {
            self.push_paren_scope();
            let op_span = op.as_span();
            let op = match op.as_str() {
                "and" => BinOp::And,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.start(), right.as_span().end());
            let right = self.expr_bind(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        while self.depth() > start_depth {
            self.pop_paren_scope();
        }
        left
    }
    fn expr_bind(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.as_span();
        let mut pairs = pair.into_inner();
        let first = pairs.next().unwrap();
        match first.as_rule() {
            Rule::pattern => {
                let pattern = self.pattern(first);
                let body = self.expr_access(pairs.next().unwrap());
                self.bind_pattern(&pattern);
                Node::Bind(BindExpr {
                    pattern,
                    body: body.into(),
                    span,
                })
            }
            Rule::expr_cmp => self.expr_cmp(first),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn expr_cmp(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.as_span();
        let mut left = self.expr_as(left);
        for (op, right) in pairs.tuples() {
            let op_span = op.as_span();
            let op = match op.as_str() {
                "==" => BinOp::Equals,
                "!=" => BinOp::NotEquals,
                "<=" => BinOp::LessOrEqual,
                ">=" => BinOp::GreaterOrEqual,
                "<" => BinOp::Less,
                ">" => BinOp::Greater,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.start(), right.as_span().end());
            let right = self.expr_as(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        left
    }
    fn expr_as(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.as_span();
        let mut left = self.expr_mdr(left);
        for (op, right) in pairs.tuples() {
            let op_span = op.as_span();
            let op = match op.as_str() {
                "+" => BinOp::Add,
                "-" => BinOp::Sub,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.start(), right.as_span().end());
            let right = self.expr_mdr(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        left
    }
    fn expr_mdr(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.as_span();
        let mut left = self.expr_neg(left);
        for (op, right) in pairs.tuples() {
            let op_span = op.as_span();
            let op = match op.as_str() {
                "*" => BinOp::Mul,
                "/" => BinOp::Div,
                "%" => BinOp::Rem,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.start(), right.as_span().end());
            let right = self.expr_neg(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        left
    }
    fn expr_neg(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.as_span();
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
                    let span = pair.as_span();
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
                    let span = pair.as_span();
                    let ident = self.ident(only(pair));
                    root = Node::Access(AccessExpr {
                        root: root.into(),
                        accessor: Accessor::Key(Key::Field(ident)),
                        span,
                    })
                }
                Rule::call_args => {
                    let span = pair.as_span();
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
                self.errors.push(CheckError::InvalidLiteral(pair.as_span()));
                0
            }
        }
    }
    fn term(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.as_span();
        let pair = only(pair);
        let term = match pair.as_rule() {
            Rule::int => Term::Int(self.int(pair)),
            Rule::real => match pair.as_str().parse::<f64>() {
                Ok(i) => Term::Real(i),
                Err(_) => {
                    self.errors.push(CheckError::InvalidLiteral(pair.as_span()));
                    Term::Real(0.0)
                }
            },
            Rule::ident => self.ident_term(pair),
            Rule::paren_expr => {
                let pair = only(pair);
                self.push_paren_scope();
                let items = self.items(pair);
                self.pop_paren_scope();
                if items.len() == 1 && matches!(items[0], Item::Node(_)) {
                    if let Item::Node(node) = items.into_iter().next().unwrap() {
                        return node;
                    } else {
                        unreachable!()
                    }
                }
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
                let span = pair.as_span();
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
                let mut default = None;
                for pair in pair.into_inner() {
                    match pair.as_rule() {
                        Rule::entity_item => {
                            let mut pairs = pair.into_inner();
                            let first = pairs.next().unwrap();
                            match first.as_rule() {
                                Rule::tag_literal => {
                                    entries.push(Entry::Tag(self.ident(only(first))))
                                }
                                Rule::ident => {
                                    let ident = self.ident(first.clone());
                                    let value = if let Some(second) = pairs.next() {
                                        self.expr(second)
                                    } else {
                                        let span = first.as_span();
                                        Node::Term(self.ident_term(first), span)
                                    };
                                    entries.push(Entry::Field(ident, value));
                                }
                                Rule::expr => {
                                    let key = self.expr(first.clone());
                                    let value = self.expr(pairs.next().unwrap());
                                    entries.push(Entry::Index(key, value));
                                }
                                rule => unreachable!("{:?}", rule),
                            }
                        }
                        Rule::expr => default = Some(Box::new(self.expr(pair))),
                        rule => unreachable!("{:?}", rule),
                    }
                }
                Term::Entity { entries, default }
            }
            Rule::pattern_literal => Term::Pattern(self.pattern(only(pair)).into()),
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
    fn string(&mut self, pair: Pair<'i, Rule>) -> Vec<StringPart<'i>> {
        let mut parts = Vec::new();
        for pair in pair.into_inner() {
            parts.extend(self.quoted_string(pair));
        }
        parts
    }
    fn raw_string(&mut self, pair: Pair<'i, Rule>) -> String {
        let mut s = String::new();
        let span = pair.as_span();
        'pair_loop: for pair in pair.into_inner() {
            for part in self.quoted_string(pair) {
                match part {
                    StringPart::Raw(part) => s.push_str(&*part),
                    StringPart::Format(_) => {
                        self.errors.push(CheckError::InvalidStringPattern(span));
                        break 'pair_loop;
                    }
                }
            }
        }
        s
    }
    fn quoted_string(&mut self, pair: Pair<'i, Rule>) -> Vec<StringPart<'i>> {
        let mut parts = Vec::new();
        let mut s = String::new();
        for pair in pair.into_inner() {
            match pair.as_rule() {
                Rule::string_text => s.push_str(pair.as_str()),
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
                rule => unreachable!("{:?}", rule),
            }
        }
        if !s.is_empty() {
            parts.push(StringPart::Raw(s.into()))
        }
        parts
    }
}
