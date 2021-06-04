#![allow(clippy::upper_case_acronyms)]

use std::{collections::HashMap, fmt};

use bimap::BiMap;
use itertools::Itertools;
use pest::{
    error::{Error as PestError, ErrorVariant},
    iterators::Pair,
    Parser, RuleType, Span,
};

use crate::{ast::*, interpret::Runtime};

#[derive(Debug)]
pub enum CheckError<'i> {
    UnknownDef(Ident<'i>),
    Parse(PestError<Rule>),
    InvalidLiteral(Span<'i>),
    DefUnderscoreTerminus(Span<'i>),
    FunctionNamedUnderscore(Span<'i>),
    ForbiddenRedefinition(Ident<'i>),
    LastItemNotExpression(Span<'i>),
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

pub(crate) fn parse<'i, 'r>(
    runtime: &'r mut Runtime<'i>,
    input: &'i str,
) -> Result<Items<'i>, Vec<CheckError<'i>>> {
    match KinParser::parse(Rule::file, input) {
        Ok(mut pairs) => {
            let mut state = ParseState {
                input,
                scopes: vec![FunctionScope::default()],
                errors: Vec::new(),
                ids: &mut runtime.ids,
            };
            for (name, _) in crate::builtin::FUNCTIONS {
                state.scope().bindings.insert(name, Binding::Builtin);
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

#[derive(Debug, Clone)]
enum Binding<'i> {
    Def(Def<'i>),
    Param(u8),
    Builtin,
    Unfinished(u8),
}

#[derive(Default)]
struct ParenScope<'i> {
    bindings: HashMap<&'i str, Binding<'i>>,
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

#[derive(Clone, Default)]
pub struct Ids<'i> {
    tags: BiMap<&'i str, TagId>,
    idents: BiMap<&'i str, IdentId>,
    next_tag: TagId,
    next_ident: IdentId,
}

impl<'i> Ids<'i> {
    pub fn ident(&mut self, name: &'i str) -> IdentId {
        if !self.idents.contains_left(name) {
            self.idents.insert(name, self.next_ident);
            self.next_ident += 1;
        }
        *self.idents.get_by_left(name).unwrap()
    }
    pub fn tag(&mut self, name: &'i str) -> TagId {
        if !self.tags.contains_left(name) {
            self.tags.insert(name, self.next_tag);
            self.next_tag += 1;
        }
        *self.tags.get_by_left(name).unwrap()
    }
    pub fn ident_name(&self, id: IdentId) -> &'i str {
        self.idents.get_by_right(&id).unwrap()
    }
    pub fn tag_name(&self, id: TagId) -> &'i str {
        self.tags.get_by_right(&id).unwrap()
    }
}

pub struct ParseState<'i, 'r> {
    input: &'i str,
    scopes: Vec<FunctionScope<'i>>,
    errors: Vec<CheckError<'i>>,
    ids: &'r mut Ids<'i>,
}

impl<'i, 'r> ParseState<'i, 'r> {
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
    fn scope(&mut self) -> &mut ParenScope<'i> {
        self.function_scope().scopes.last_mut().unwrap()
    }
    fn span(&self, start: usize, end: usize) -> Span<'i> {
        Span::new(self.input, start, end).unwrap()
    }
    fn depth(&self) -> u8 {
        self.scopes.len() as u8
    }
    fn bind_def(&mut self, def: Def<'i>) {
        self.scope()
            .bindings
            .insert(def.ident.name, Binding::Def(def));
    }
    fn bind_param(&mut self, name: &'i str) {
        let depth = self.depth() - 1;
        self.scope().bindings.insert(name, Binding::Param(depth));
    }
    fn bind_unfinished(&mut self, name: &'i str) {
        let depth = self.depth();
        self.scope()
            .bindings
            .insert(name, Binding::Unfinished(depth));
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
            Rule::def => self.def(pair),
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
        Ident {
            name,
            span,
            id: self.ids.ident(name),
        }
    }
    fn bound_ident(&mut self, pair: Pair<'i, Rule>) -> Ident<'i> {
        let ident = self.ident(pair);
        if FORBIDDEN_REDIFINITIONS.contains(&ident.name) {
            self.errors
                .push(CheckError::ForbiddenRedefinition(ident.clone()));
        }
        ident
    }
    fn param(&mut self, pair: Pair<'i, Rule>) -> Param<'i> {
        let mut pairs = pair.into_inner();
        let ident = self.bound_ident(pairs.next().unwrap());
        Param { ident }
    }
    fn def(&mut self, pair: Pair<'i, Rule>) -> Item<'i> {
        let mut pairs = pair.into_inner();
        let ident = self.bound_ident(pairs.next().unwrap());
        let mut params = Vec::new();
        for pair in pairs.by_ref() {
            if let Rule::param = pair.as_rule() {
                params.push(self.param(pair));
            } else {
                break;
            }
        }
        let is_function = !params.is_empty();
        if is_function {
            if ident.is_underscore() {
                self.errors
                    .push(CheckError::FunctionNamedUnderscore(ident.span.clone()));
            }
            self.bind_unfinished(ident.name);
            self.push_function_scope();
            for param in &params {
                self.bind_param(param.ident.name);
            }
        }
        let pair = pairs.next().unwrap();
        let items = self.function_body(pair);
        if is_function {
            self.pop_function_scope();
        }
        let def = Def {
            ident,
            params,
            items,
        };
        self.bind_def(def.clone());
        Item::Def(def)
    }
    fn expr(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::expr_or => self.expr_or(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn expr_or(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.as_span();
        let mut left = self.expr_and(left);
        for (op, right) in pairs.tuples() {
            let op_span = op.as_span();
            let op = match op.as_str() {
                "or" => BinOp::Or,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.start(), right.as_span().end());
            let right = self.expr_and(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        left
    }
    fn expr_and(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let mut pairs = pair.into_inner();
        let left = pairs.next().unwrap();
        let mut span = left.as_span();
        let mut left = self.expr_cmp(left);
        for (op, right) in pairs.tuples() {
            let op_span = op.as_span();
            let op = match op.as_str() {
                "and" => BinOp::And,
                rule => unreachable!("{:?}", rule),
            };
            span = self.span(span.start(), right.as_span().end());
            let right = self.expr_cmp(right);
            left = Node::BinExpr(BinExpr::new(left, right, op, span.clone(), op_span));
        }
        left
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
        let inner = self.expr_method_call(inner);
        if let Some(op) = op {
            Node::UnExpr(UnExpr::new(inner, op, span))
        } else {
            inner
        }
    }
    fn expr_method_call(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.as_span();
        let mut pairs = pair.into_inner();
        let mut node = self.expr_call(pairs.next().unwrap());
        while let Some(pair) = pairs.next() {
            let ident = self.ident(pair);
            self.verify_ident(&ident);
            let mut args = self.call_args(pairs.next().unwrap());
            args.insert(0, node);
            let ident_span = ident.span.clone();
            node = Node::Call(CallExpr {
                caller: Node::Term(Term::Ident(ident), ident_span).into(),
                args,
                span: span.clone(),
            });
        }
        node
    }
    fn expr_call(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.as_span();
        let mut pairs = pair.into_inner();
        let caller = self.term(pairs.next().unwrap());
        if let Some(pair) = pairs.next() {
            Node::Call(CallExpr {
                caller: caller.into(),
                args: self.call_args(pair),
                span,
            })
        } else {
            caller
        }
    }
    fn call_args(&mut self, pair: Pair<'i, Rule>) -> Vec<Node<'i>> {
        pair.into_inner().map(|pair| self.expr(pair)).collect()
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
    fn term(&mut self, pair: Pair<'i, Rule>) -> Node<'i> {
        let span = pair.as_span();
        let pair = only(pair);
        let term = match pair.as_rule() {
            Rule::int => match pair.as_str().parse::<i64>() {
                Ok(i) => Term::Int(i),
                Err(_) => {
                    self.errors.push(CheckError::InvalidLiteral(pair.as_span()));
                    Term::Int(0)
                }
            },
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
                Term::Expr(items)
            }
            Rule::string => {
                let string = self.string_literal(pair);
                Term::String(string)
            }
            Rule::list_literal => {
                Term::List(pair.into_inner().map(|pair| self.expr(pair)).collect())
            }
            Rule::tag_literal => Term::Tag(self.ids.tag(only(pair).as_str())),
            Rule::closure => {
                let span = pair.as_span();
                let mut pairs = pair.into_inner();
                let params_pairs = pairs.next().unwrap().into_inner();
                let params: Vec<Param> = params_pairs.map(|pair| self.param(pair)).collect();
                self.push_function_scope();
                for param in &params {
                    self.bind_param(param.ident.name);
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
                                    entries.push(Entry::Tag(self.ids.tag(only(first).as_str())))
                                }
                                Rule::ident => {
                                    let ident = self.ident(first.clone());
                                    let value = if let Some(second) = pairs.next() {
                                        self.expr(second)
                                    } else {
                                        Node::Term(self.ident_term(first), ident.span)
                                    };
                                    entries.push(Entry::Field(ident.id, value));
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
            rule => unreachable!("{:?}", rule),
        };
        Node::Term(term, span)
    }
    fn lookup_name<'b>(scopes: &'b [FunctionScope<'i>], name: &str) -> Option<&'b Binding<'i>> {
        scopes.iter().rev().find_map(|fscope| {
            fscope
                .scopes
                .iter()
                .rev()
                .find_map(|pscope| pscope.bindings.get(name))
        })
    }
    fn verify_ident(&mut self, ident: &Ident<'i>) -> Option<&Binding<'i>> {
        let binding = Self::lookup_name(&self.scopes, ident.name);
        if binding.is_none() {
            self.errors.push(CheckError::UnknownDef(ident.clone()));
        }
        binding
    }
    fn function_body(&mut self, pair: Pair<'i, Rule>) -> Items<'i> {
        match pair.as_rule() {
            Rule::items => self.items(pair),
            Rule::expr => {
                vec![Item::Node(self.expr(pair))]
            }
            rule => unreachable!("{:?}", rule),
        }
    }
    fn string_literal(&mut self, pair: Pair<'i, Rule>) -> String {
        let mut s = String::new();
        for pair in pair.into_inner() {
            match pair.as_rule() {
                Rule::raw_string => s.push_str(pair.as_str()),
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
                rule => unreachable!("{:?}", rule),
            }
        }
        s
    }
}
