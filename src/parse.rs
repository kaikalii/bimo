#![allow(clippy::upper_case_acronyms)]

use std::{collections::HashMap, fmt};

use itertools::Itertools;
use pest::{
    error::{Error as PestError, ErrorVariant},
    iterators::Pair,
    Parser, RuleType, Span,
};

use crate::ast::*;

#[derive(Debug)]
pub enum TranspileError<'a> {
    UnknownDef(Ident<'a>),
    Parse(PestError<Rule>),
    InvalidLiteral(Span<'a>),
    DefUnderscoreTerminus(Span<'a>),
    FunctionNamedUnderscore(Span<'a>),
    ForbiddenRedefinition(Ident<'a>),
    LastItemNotExpression(Span<'a>),
}

impl<'a> fmt::Display for TranspileError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TranspileError::UnknownDef(ident) => format_span(
                format!("Unknown def: {:?}", ident.name),
                ident.span.clone(),
                f,
            ),
            TranspileError::Parse(e) => e.fmt(f),
            TranspileError::InvalidLiteral(span) => format_span("Invalid literal", span.clone(), f),
            TranspileError::DefUnderscoreTerminus(span) => {
                format_span("Def names may not start or end with '_'", span.clone(), f)
            }
            TranspileError::FunctionNamedUnderscore(span) => {
                format_span("Function cannot be named '_'", span.clone(), f)
            }
            TranspileError::ForbiddenRedefinition(ident) => format_span(
                format!("{} cannot be redefined", ident.name),
                ident.span.clone(),
                f,
            ),
            TranspileError::LastItemNotExpression(span) => format_span(
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

pub fn parse(input: &str) -> Result<Items, Vec<TranspileError>> {
    match KinParser::parse(Rule::file, input) {
        Ok(mut pairs) => {
            let mut state = ParseState {
                input,
                scopes: vec![FunctionScope::default()],
                errors: Vec::new(),
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
        Err(e) => Err(vec![TranspileError::Parse(e)]),
    }
}

#[derive(Debug, Clone)]
enum Binding<'a> {
    Def(Def<'a>),
    Param(u8),
    Builtin,
    Unfinished(u8),
}

#[derive(Default)]
struct ParenScope<'a> {
    bindings: HashMap<&'a str, Binding<'a>>,
}

struct FunctionScope<'a> {
    scopes: Vec<ParenScope<'a>>,
}

impl<'a> Default for FunctionScope<'a> {
    fn default() -> Self {
        FunctionScope {
            scopes: vec![ParenScope::default()],
        }
    }
}

struct ParseState<'a> {
    input: &'a str,
    scopes: Vec<FunctionScope<'a>>,
    errors: Vec<TranspileError<'a>>,
}

impl<'a> ParseState<'a> {
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
    fn function_scope(&mut self) -> &mut FunctionScope<'a> {
        self.scopes.last_mut().unwrap()
    }
    fn scope(&mut self) -> &mut ParenScope<'a> {
        self.function_scope().scopes.last_mut().unwrap()
    }
    fn span(&self, start: usize, end: usize) -> Span<'a> {
        Span::new(self.input, start, end).unwrap()
    }
    fn depth(&self) -> u8 {
        self.scopes.len() as u8
    }
    fn bind_def(&mut self, def: Def<'a>) {
        self.scope()
            .bindings
            .insert(def.ident.name, Binding::Def(def));
    }
    fn bind_param(&mut self, name: &'a str) {
        let depth = self.depth() - 1;
        self.scope().bindings.insert(name, Binding::Param(depth));
    }
    fn bind_unfinished(&mut self, name: &'a str) {
        let depth = self.depth();
        self.scope()
            .bindings
            .insert(name, Binding::Unfinished(depth));
    }
    fn items(&mut self, pair: Pair<'a, Rule>) -> Items<'a> {
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
                self.errors.push(TranspileError::LastItemNotExpression(
                    last_item.span().clone(),
                ));
            }
        }
        items
    }
    fn item(&mut self, pair: Pair<'a, Rule>) -> Item<'a> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::expr => Item::Node(self.expr(pair)),
            Rule::def => self.def(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn ident(&mut self, pair: Pair<'a, Rule>) -> Ident<'a> {
        let name = pair.as_str();
        let span = pair.as_span();
        if (name.starts_with('_') || name.ends_with('_')) && name != "_" {
            self.errors
                .push(TranspileError::DefUnderscoreTerminus(span.clone()));
        }
        Ident { name, span }
    }
    fn bound_ident(&mut self, pair: Pair<'a, Rule>) -> Ident<'a> {
        let ident = self.ident(pair);
        if FORBIDDEN_REDIFINITIONS.contains(&ident.name) {
            self.errors
                .push(TranspileError::ForbiddenRedefinition(ident.clone()));
        }
        ident
    }
    fn param(&mut self, pair: Pair<'a, Rule>) -> Param<'a> {
        let mut pairs = pair.into_inner();
        let ident = self.bound_ident(pairs.next().unwrap());
        Param { ident }
    }
    fn def(&mut self, pair: Pair<'a, Rule>) -> Item<'a> {
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
                    .push(TranspileError::FunctionNamedUnderscore(ident.span.clone()));
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
    fn expr(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
        let pair = only(pair);
        match pair.as_rule() {
            Rule::expr_or => self.expr_or(pair),
            rule => unreachable!("{:?}", rule),
        }
    }
    fn expr_or(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
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
    fn expr_and(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
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
    fn expr_cmp(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
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
    fn expr_as(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
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
    fn expr_mdr(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
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
    fn expr_neg(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
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
    fn expr_method_call(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
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
    fn expr_call(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
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
    fn call_args(&mut self, pair: Pair<'a, Rule>) -> Vec<Node<'a>> {
        pair.into_inner().map(|pair| self.expr(pair)).collect()
    }
    fn term(&mut self, pair: Pair<'a, Rule>) -> Node<'a> {
        let span = pair.as_span();
        let pair = only(pair);
        let term = match pair.as_rule() {
            Rule::int => match pair.as_str().parse::<i64>() {
                Ok(i) => Term::Int(i),
                Err(_) => {
                    self.errors
                        .push(TranspileError::InvalidLiteral(pair.as_span()));
                    Term::Int(0)
                }
            },
            Rule::real => match pair.as_str().parse::<f64>() {
                Ok(i) => Term::Real(i),
                Err(_) => {
                    self.errors
                        .push(TranspileError::InvalidLiteral(pair.as_span()));
                    Term::Real(0.0)
                }
            },
            Rule::ident => {
                let ident = self.ident(pair);
                self.verify_ident(&ident);
                Term::Ident(ident)
            }
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
            rule => unreachable!("{:?}", rule),
        };
        Node::Term(term, span)
    }
    fn lookup_name<'b>(scopes: &'b [FunctionScope<'a>], name: &str) -> Option<&'b Binding<'a>> {
        scopes.iter().rev().find_map(|fscope| {
            fscope
                .scopes
                .iter()
                .rev()
                .find_map(|pscope| pscope.bindings.get(name))
        })
    }
    fn verify_ident(&mut self, ident: &Ident<'a>) -> Option<&Binding<'a>> {
        let binding = Self::lookup_name(&self.scopes, ident.name);
        if binding.is_none() {
            self.errors.push(TranspileError::UnknownDef(ident.clone()));
        }
        binding
    }
    fn function_body(&mut self, pair: Pair<'a, Rule>) -> Items<'a> {
        match pair.as_rule() {
            Rule::items => self.items(pair),
            Rule::expr => {
                vec![Item::Node(self.expr(pair))]
            }
            rule => unreachable!("{:?}", rule),
        }
    }
    fn string_literal(&mut self, pair: Pair<'a, Rule>) -> String {
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
