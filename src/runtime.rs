use std::{
    cell::RefCell, collections::HashMap, error::Error, fmt, iter::repeat, mem::swap,
    mem::transmute, rc::Rc,
};

use itertools::Itertools;
use pest::{
    error::{Error as PestError, ErrorVariant},
    Span,
};
use regex::Regex;

use crate::{
    ast::*,
    builtin::FUNCTIONS,
    entity::{Entity, Key},
    num::Num,
    parse::{parse, CheckError, Rule},
    pattern::{FieldPattern, Pattern},
    value::*,
};

pub type BimoFn<'i> = fn(&mut Runtime<'i>, &Span<'i>) -> RuntimeResult<'i>;

#[derive(Debug, Clone)]
pub struct RuntimeError<'i> {
    pub message: String,
    pub spans: Vec<Span<'i>>,
}

impl<'i> RuntimeError<'i> {
    pub fn new(message: impl Into<String>, span: Span<'i>) -> Self {
        RuntimeError::multispan(message, Some(span))
    }
    pub fn multispan(
        message: impl Into<String>,
        spans: impl IntoIterator<Item = Span<'i>>,
    ) -> Self {
        RuntimeError {
            message: message.into(),
            spans: spans.into_iter().collect(),
        }
    }
    pub fn unspanned(message: impl Into<String>) -> Self {
        RuntimeError::multispan(message, None)
    }
}

impl<'i> fmt::Display for RuntimeError<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.spans.is_empty() {
            write!(f, "{}", self.message)
        } else {
            let mut message = Some(&self.message);
            for (i, span) in self.spans.iter().enumerate() {
                if i > 0 {
                    writeln!(f)?;
                }
                write!(
                    f,
                    "{}",
                    PestError::<Rule>::new_from_span(
                        ErrorVariant::CustomError {
                            message: message.take().cloned().unwrap_or_default()
                        },
                        span.clone()
                    )
                )?
            }
            Ok(())
        }
    }
}

impl<'i> Error for RuntimeError<'i> {}

pub type RuntimeResult<'i, T = Value<'i>> = Result<T, RuntimeError<'i>>;

impl<'i> From<Vec<CheckError<'i>>> for RuntimeError<'i> {
    #[allow(unstable_name_collisions)]
    fn from(errors: Vec<CheckError<'i>>) -> Self {
        RuntimeError::unspanned(
            errors
                .iter()
                .map(ToString::to_string)
                .intersperse("\n".into())
                .collect::<String>(),
        )
    }
}

pub struct Runtime<'i> {
    pub(crate) scope: Scope<'i>,
}

#[derive(Debug, Clone, Default)]
pub struct Scope<'i> {
    parent: Option<Rc<Self>>,
    pub values: Rc<RefCell<HashMap<&'i str, Value<'i>>>>,
}

impl<'i> Scope<'i> {
    pub fn push(&mut self, mut scope: Scope<'i>) {
        swap(self, &mut scope);
        self.parent = Some(Rc::new(scope));
    }
    pub fn pop(&mut self) {
        let parent = self.parent.take().unwrap();
        *self = Rc::try_unwrap(parent).unwrap_or_else(|parent| (*parent).clone());
    }
    pub fn val(&self, name: &str) -> Option<Value<'i>> {
        self.values
            .borrow()
            .get(name)
            .cloned()
            .or_else(|| self.parent.as_ref().and_then(|parent| parent.val(name)))
    }
    fn bind(&self, ident: &Ident<'i>, val: Value<'i>) {
        if !ident.is_underscore() {
            self.values.borrow_mut().insert(ident.name, val);
        }
    }
    fn bind_pattern(
        &mut self,
        pattern: &Pattern<'i>,
        val: &Value<'i>,
        required: Option<&Span<'i>>,
    ) -> RuntimeResult<'i> {
        Ok(match pattern {
            Pattern::Single(ident) => {
                self.bind(ident, val.clone());
                val.clone()
            }
            Pattern::Bound { left, right, .. } => {
                let val = self.bind_pattern(right, &val, required)?;
                self.bind_pattern(left, &val, required)?
            }
            Pattern::List { patterns, span } => {
                if let Value::List(list) = val {
                    if let Some(value_span) = required {
                        if list.len() < patterns.len() {
                            return Err(RuntimeError::multispan(
                                format!("List is too short to match pattern: {}", pattern),
                                vec![span.clone(), value_span.clone()],
                            ));
                        }
                    }
                    let mut bound_all = true;
                    for (pattern, val) in
                        patterns.iter().zip(list.iter().chain(repeat(&Value::Nil)))
                    {
                        bound_all =
                            self.bind_pattern(pattern, val, required)?.is_truthy() && bound_all;
                    }
                    if bound_all {
                        val.clone()
                    } else {
                        Value::Nil
                    }
                } else if let Some(value_span) = required {
                    return Err(RuntimeError::multispan(
                        format!(
                            "Attempted to match {} against list pattern: {}",
                            val.type_name(),
                            pattern
                        ),
                        vec![span.clone(), value_span.clone()],
                    ));
                } else {
                    for pattern in patterns {
                        self.bind_pattern(pattern, &Value::Nil, required)?;
                    }
                    Value::Nil
                }
            }
            Pattern::Entity { patterns, span } => {
                if let Value::Entity(map) = val {
                    let mut bound_all = true;
                    for pattern in patterns {
                        bound_all = self
                            .bind_field_pattern(pattern, Some(&map), required)?
                            .is_truthy()
                            && bound_all;
                    }
                    if bound_all {
                        val.clone()
                    } else {
                        Value::Nil
                    }
                } else if let Some(value_span) = required {
                    return Err(RuntimeError::multispan(
                        format!(
                            "Attempted to match {} against entity pattern: {}",
                            val.type_name(),
                            pattern
                        ),
                        vec![span.clone(), value_span.clone()],
                    ));
                } else {
                    for pattern in patterns {
                        self.bind_field_pattern(pattern, None, required)?;
                    }
                    Value::Bool(false)
                }
            }
            Pattern::Nil(span) => {
                if let Value::Nil = val {
                    Value::Bool(true)
                } else if let Some(value_span) = required {
                    return Err(RuntimeError::multispan(
                        format!("Attempted to match {} against nil pattern", val.type_name()),
                        vec![span.clone(), value_span.clone()],
                    ));
                } else {
                    Value::Bool(false)
                }
            }
            Pattern::Bool { b: b1, span } => {
                if let Value::Bool(b2) = val {
                    if let (Some(value_span), true) = (required, b1 != b2) {
                        return Err(RuntimeError::multispan(
                            format!("Bool value does not match bool pattern: {}", pattern),
                            vec![span.clone(), value_span.clone()],
                        ));
                    } else {
                        Value::Bool(b1 == b2)
                    }
                } else if let Some(value_span) = required {
                    return Err(RuntimeError::multispan(
                        format!(
                            "Attempted to match {} against bool pattern: {}",
                            val.type_name(),
                            pattern
                        ),
                        vec![span.clone(), value_span.clone()],
                    ));
                } else {
                    Value::Bool(false)
                }
            }
            Pattern::Int { int, span } => {
                if let Value::Num(num) = val {
                    let num = num.to_i64();
                    if let (Some(value_span), true) = (required, int != &num) {
                        return Err(RuntimeError::multispan(
                            format!("Num value does not match int pattern: {}", pattern),
                            vec![span.clone(), value_span.clone()],
                        ));
                    } else {
                        Value::Bool(int == &num)
                    }
                } else if let Some(value_span) = required {
                    return Err(RuntimeError::multispan(
                        format!(
                            "Attempted to match {} against int pattern: {}",
                            val.type_name(),
                            pattern
                        ),
                        vec![span.clone(), value_span.clone()],
                    ));
                } else {
                    Value::Bool(false)
                }
            }
            Pattern::String {
                pattern: string_pattern,
                span,
            } => {
                let regex = string_pattern
                    .borrow()
                    .resolved
                    .clone()
                    .expect("Unresolved string pattern");
                if let Value::String(s) = val {
                    let captures = regex.captures(s);
                    if let (Some(value_span), None) = (required, captures.as_ref()) {
                        return Err(RuntimeError::multispan(
                            format!("String value does not match string pattern: {}", pattern),
                            vec![span.clone(), value_span.clone()],
                        ));
                    }
                    if let Some(captures) = captures {
                        Value::List(
                            captures
                                .iter()
                                .map(|capture| match capture {
                                    Some(capture) => capture.as_str().into(),
                                    None => Value::Nil,
                                })
                                .collect(),
                        )
                    } else {
                        Value::Nil
                    }
                } else if let Some(value_span) = required {
                    return Err(RuntimeError::multispan(
                        format!(
                            "Attempted to match {} against string pattern: {}",
                            val.type_name(),
                            pattern
                        ),
                        vec![span.clone(), value_span.clone()],
                    ));
                } else {
                    Value::Nil
                }
            }
        })
    }
    fn bind_field_pattern(
        &mut self,
        pattern: &FieldPattern<'i>,
        source: Option<&Entity<'i>>,
        required: Option<&Span<'i>>,
    ) -> RuntimeResult<'i> {
        Ok(match pattern {
            FieldPattern::SameName(field) => {
                let val = source.and_then(|map| map.try_get(Key::Field(field.clone())));
                if let (Some(value_span), true) = (required, val.is_none()) {
                    return Err(RuntimeError::multispan(
                        format!("Entity does not contain field '{}' from pattern", field),
                        vec![field.span.clone(), value_span.clone()],
                    ));
                }
                self.bind(&field, val.cloned().unwrap_or(Value::Nil));
                Value::Bool(val.is_some())
            }
            FieldPattern::Pattern {
                field,
                pattern,
                span,
            } => {
                let val = source.and_then(|map| map.try_get(Key::Field(field.clone())));
                if let (Some(value_span), true) = (required, val.is_none()) {
                    return Err(RuntimeError::multispan(
                        format!("Entity does not contain field '{}' from pattern", field),
                        vec![span.clone(), value_span.clone()],
                    ));
                }
                Value::Bool(
                    self.bind_pattern(pattern, val.unwrap_or(&Value::Nil), required)?
                        .is_truthy(),
                )
            }
        })
    }
}

impl<'i> Default for Runtime<'i> {
    fn default() -> Self {
        Runtime::new()
    }
}

impl<'i> Runtime<'i> {
    pub fn new() -> Self {
        let base_scope = Scope::default();
        Runtime {
            scope: Scope {
                parent: None,
                values: Rc::new(RefCell::new(
                    FUNCTIONS
                        .iter()
                        .cloned()
                        .map(|(name, rf)| {
                            (name, unsafe {
                                transmute::<_, Value<'i>>(Value::Function(
                                    Function::Rust(rf, base_scope.clone()).into(),
                                ))
                            })
                        })
                        .collect(),
                )),
            },
        }
    }
    pub fn val(&self, name: &str) -> Value<'i> {
        self.scope
            .val(name)
            .unwrap_or_else(|| panic!("Unknown value: {}", name))
    }
    pub fn eval<'r>(&'r mut self, input: &'i str) -> RuntimeResult<'i> {
        let items = parse(self, input)?;
        self.eval_items(&items)
    }
    pub fn check<'r>(&'r mut self, input: &'i str) -> Result<(), Vec<CheckError<'i>>> {
        parse(self, input)?;
        Ok(())
    }
    fn eval_items(&mut self, items: &[Item<'i>]) -> RuntimeResult<'i> {
        let mut res = Value::Nil;
        for item in items {
            res = self.eval_item(item)?;
        }
        Ok(res)
    }
    fn eval_item(&mut self, item: &Item<'i>) -> RuntimeResult<'i> {
        match item {
            Item::Node(node) => self.eval_node(node),
            Item::FunctionDef(def) => {
                let val = Value::Function(
                    Function::Bimo(BimoFunction {
                        scope: self.scope.clone(),
                        params: def.params.clone(),
                        body: def.body.clone().into(),
                    })
                    .into(),
                );
                self.scope.bind(&def.ident, val);
                Ok(Value::Nil)
            }
        }
    }
    fn eval_node(&mut self, node: &Node<'i>) -> RuntimeResult<'i> {
        match node {
            Node::Term(term, _) => self.eval_term(term),
            Node::BinExpr(expr) => self.eval_bin_expr(expr),
            Node::UnExpr(expr) => self.eval_un_expr(expr),
            Node::Call(expr) => self.eval_call(expr),
            Node::Access(expr) => self.eval_access_expr(expr),
            Node::If(expr) => self.eval_if_expr(expr),
            Node::Bind(expr) => self.eval_bind_expr(expr),
        }
    }
    fn resolve_pattern(&mut self, pattern: &Pattern<'i>) -> RuntimeResult<'i, ()> {
        match pattern {
            Pattern::Bound { left, right, .. } => {
                self.resolve_pattern(right)?;
                self.resolve_pattern(left)?;
            }
            Pattern::String { pattern, span } => {
                let mut pattern = pattern.borrow_mut();
                if pattern.resolved.is_none() {
                    let mut s = String::new();
                    for part in &pattern.parts {
                        match part {
                            StringPart::Raw(raw) => s.push_str(raw),
                            StringPart::Format(node) => {
                                let val_as_string = self.eval_node(node)?.to_string();
                                s.push_str(&regex::escape(&val_as_string));
                            }
                        }
                    }
                    match Regex::new(&s) {
                        Ok(regex) => pattern.resolved = Some(regex.into()),
                        Err(e) => return Err(RuntimeError::new(format!("{}", e), span.clone())),
                    }
                }
            }
            Pattern::Entity { patterns, .. } => {
                for pattern in patterns {
                    self.resolve_field_pattern(pattern)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    fn resolve_field_pattern(&mut self, pattern: &FieldPattern<'i>) -> RuntimeResult<'i, ()> {
        if let FieldPattern::Pattern { pattern, .. } = pattern {
            self.resolve_pattern(pattern)?;
        }
        Ok(())
    }
    fn eval_bind_expr(&mut self, expr: &BindExpr<'i>) -> RuntimeResult<'i> {
        let val = self.eval_node(&expr.body)?;
        self.resolve_pattern(&expr.pattern)?;
        self.scope.bind_pattern(&expr.pattern, &val, None)
    }
    fn eval_if_expr(&mut self, expr: &IfExpr<'i>) -> RuntimeResult<'i> {
        let condition = self.eval_node(&expr.condition)?;
        self.eval_node(if condition.is_truthy() {
            &expr.if_true
        } else {
            &expr.if_false
        })
    }
    fn eval_term(&mut self, term: &Term<'i>) -> RuntimeResult<'i> {
        Ok(match term {
            Term::Nil => Value::Nil,
            Term::Bool(b) => Value::Bool(*b),
            Term::Int(i) => Value::Num((*i).into()),
            Term::Real(r) => Value::Num((*r).into()),
            Term::String(parts) => {
                let mut s = String::new();
                for part in parts {
                    match part {
                        StringPart::Raw(part) => s.push_str(part),
                        StringPart::Format(node) => s.push_str(&self.eval_node(node)?.to_string()),
                    }
                }
                Value::String(s.into())
            }
            Term::List(nodes) => Value::List(
                nodes
                    .iter()
                    .map(|node| self.eval_node(node))
                    .collect::<Result<_, _>>()?,
            ),
            Term::Entity { entries, default } => {
                let mut entity = if let Some(default) = default {
                    let span = default.span();
                    match self.eval_node(default)? {
                        Value::Nil => Entity::with_capacity(entries.len()),
                        Value::Tag(id) => {
                            let mut entity = Entity::with_capacity(entries.len() + 1);
                            entity.set(Key::Tag(id), Value::Bool(true));
                            entity
                        }
                        Value::Entity(entity) => entity,
                        val => {
                            return Err(RuntimeError::new(
                                format!(
                                    "Entity cannot be default initialized from {}",
                                    val.type_name()
                                ),
                                span.clone(),
                            ))
                        }
                    }
                } else {
                    Entity::with_capacity(entries.len())
                };
                for entry in entries {
                    match entry {
                        Entry::Tag(ident) => entity.set(Key::Tag(ident.clone()), Value::Bool(true)),
                        Entry::Field(ident, node) => {
                            entity.set(Key::Field(ident.clone()), self.eval_node(node)?)
                        }
                        Entry::Index(key, val) => {
                            entity.set(Key::Value(self.eval_node(key)?), self.eval_node(val)?)
                        }
                    };
                }
                Value::Entity(entity)
            }
            Term::Expr(items) => {
                self.scope.push(Scope::default());
                let mut res = Value::Nil;
                for item in items {
                    res = self.eval_item(item)?;
                }
                self.scope.pop();
                res
            }
            Term::Tag(ident) => Value::Tag(ident.clone()),
            Term::Ident(ident) => self.val(ident.name),
            Term::Closure(closure) => Value::Function(Rc::new(Function::Bimo(BimoFunction {
                scope: self.scope.clone(),
                params: closure.params.clone(),
                body: closure.body.clone().into(),
            }))),
            Term::Pattern(pattern) => {
                self.resolve_pattern(pattern)?;
                Value::Pattern(pattern.clone())
            }
        })
    }
    fn eval_access_expr(&mut self, expr: &AccessExpr<'i>) -> RuntimeResult<'i> {
        let root = self.eval_node(&expr.root)?;
        Ok(match root {
            Value::Entity(map) => match &expr.accessor {
                Accessor::Key(key) => map.get(key).clone(),
            },
            val => {
                return Err(RuntimeError::new(
                    format!("{} does not have fields", val),
                    expr.span.clone(),
                ))
            }
        })
    }
    fn eval_bin_expr(&mut self, expr: &BinExpr<'i>) -> RuntimeResult<'i> {
        let left = self.eval_node(&expr.left)?;
        let mut right = || self.eval_node(&expr.right);
        let bin_fn: BinFn = match expr.op {
            BinOp::Or => return if left.is_truthy() { Ok(left) } else { right() },
            BinOp::And => return if left.is_truthy() { right() } else { Ok(left) },
            BinOp::Add => |a, b| Value::Num(a + b),
            BinOp::Sub => |a, b| Value::Num(a - b),
            BinOp::Mul => |a, b| Value::Num(a * b),
            BinOp::Div => |a, b| Value::Num(a / b),
            BinOp::Rem => |a, b| Value::Num(a % b),
            BinOp::Less => |a, b| Value::Bool(a < b),
            BinOp::LessOrEqual => |a, b| Value::Bool(a <= b),
            BinOp::Greater => |a, b| Value::Bool(a > b),
            BinOp::GreaterOrEqual => |a, b| Value::Bool(a >= b),
            BinOp::Equals => return Ok(Value::Bool(left == right()?)),
            BinOp::NotEquals => return Ok(Value::Bool(left != right()?)),
        };
        bin_op_impl(expr.op, left, right()?, &expr.span, bin_fn)
    }
    fn eval_un_expr(&mut self, expr: &UnExpr<'i>) -> RuntimeResult<'i> {
        let inner = self.eval_node(&expr.inner)?;
        Ok(match expr.op {
            UnOp::Neg => match inner {
                Value::Num(n) => Value::Num(-n),
                val => {
                    return Err(RuntimeError::new(
                        format!("Unable to negate {}", val.type_name()),
                        expr.span.clone(),
                    ))
                }
            },
        })
    }
    pub fn call<A>(&mut self, caller: &Value<'i>, args: &[A], span: &Span<'i>) -> RuntimeResult<'i>
    where
        A: Arg<'i>,
    {
        Ok(match caller {
            Value::Function(function) => match &**function {
                Function::Bimo(function) => {
                    let mut call_scope = function.scope.clone();
                    call_scope.push(Scope::default());
                    for (i, param) in function.params.iter().enumerate() {
                        let (val, val_span) = if let Some(arg) = args.get(i) {
                            (arg.eval(self)?, arg.span())
                        } else {
                            (Value::Nil, None)
                        };
                        self.resolve_pattern(param)?;
                        call_scope.bind_pattern(param, &val, Some(val_span.unwrap_or(span)))?;
                    }
                    swap(&mut self.scope, &mut call_scope);
                    let val = self.eval_node(&*function.body.borrow())?;
                    swap(&mut self.scope, &mut call_scope);
                    val
                }
                Function::Rust(function, scope) => {
                    let call_scope = scope.clone();
                    for (i, param) in function.params.iter().enumerate() {
                        let val = if let Some(arg) = args.get(i) {
                            arg.eval(self)?
                        } else {
                            Value::Nil
                        };
                        call_scope.values.borrow_mut().insert(param, val);
                    }
                    self.scope.push(call_scope);
                    let res = (function.f)(self, span);
                    self.scope.pop();
                    res?
                }
            },
            Value::Entity(map) => {
                let first_arg = args
                    .first()
                    .map(|node| node.eval(self))
                    .transpose()?
                    .unwrap_or(Value::Nil);
                map.get(&Key::Value(first_arg)).clone()
            }
            Value::List(list) => {
                let first_arg = args
                    .first()
                    .map(|node| node.eval(self))
                    .transpose()?
                    .unwrap_or(Value::Nil);
                if let Value::Num(num) = first_arg {
                    let index = num.to_i64();
                    if index >= 0 {
                        let index = index as usize;
                        if index < list.len() {
                            list.get(index).unwrap().clone()
                        } else {
                            Value::Nil
                        }
                    } else {
                        let rev_index = (-index) as usize;
                        if rev_index <= list.len() {
                            list.get(list.len() - rev_index).unwrap().clone()
                        } else {
                            Value::Nil
                        }
                    }
                } else {
                    return Err(RuntimeError::new(
                        format!("List cannot be indexed with {}", first_arg.type_name()),
                        span.clone(),
                    ));
                }
            }
            Value::Pattern(pattern) => {
                let first_arg = args
                    .first()
                    .map(|arg| arg.eval(self))
                    .transpose()?
                    .unwrap_or(Value::Nil);
                self.scope.push(Scope::default());
                self.scope.bind_pattern(pattern, &first_arg, None)?
            }
            val => {
                return Err(RuntimeError::new(
                    format!("Unable to call {}", val.type_name()),
                    span.clone(),
                ))
            }
        })
    }
    fn eval_call(&mut self, expr: &CallExpr<'i>) -> RuntimeResult<'i> {
        let caller = self.eval_node(&expr.caller)?;
        self.call(&caller, &expr.args, &expr.span)
    }
}

pub trait Arg<'i> {
    fn eval(&self, runtime: &mut Runtime<'i>) -> RuntimeResult<'i>;
    fn span(&self) -> Option<&Span<'i>>;
}

impl<'i> Arg<'i> for Value<'i> {
    fn eval(&self, _: &mut Runtime<'i>) -> RuntimeResult<'i> {
        Ok(self.clone())
    }
    fn span(&self) -> Option<&Span<'i>> {
        None
    }
}

impl<'i> Arg<'i> for Node<'i> {
    fn eval(&self, runtime: &mut Runtime<'i>) -> RuntimeResult<'i> {
        runtime.eval_node(self)
    }
    fn span(&self) -> Option<&Span<'i>> {
        Some(self.span())
    }
}

type BinFn<'i> = fn(Num, Num) -> Value<'i>;

fn bin_op_impl<'i>(
    op: BinOp,
    left: Value<'i>,
    right: Value<'i>,
    span: &Span<'i>,
    f: BinFn<'i>,
) -> RuntimeResult<'i> {
    Ok(match (left, right) {
        (Value::Num(a), Value::Num(b)) => f(a, b),
        (a, b) => {
            let a = a.type_name();
            let b = b.type_name();
            return Err(RuntimeError::new(
                match op {
                    BinOp::Add => format!("Unable to add {} and {}", a, b),
                    BinOp::Sub => format!("Unable to subtract {} from {}", b, a),
                    BinOp::Mul => format!("Unable to multiple {} and {}", a, b),
                    BinOp::Div | BinOp::Rem => format!("Unable to divide {} by {}", a, b),
                    BinOp::Less | BinOp::Greater | BinOp::LessOrEqual | BinOp::GreaterOrEqual => {
                        format!("Unable to compare {} and {}", a, b)
                    }
                    op => unreachable!("{:?} operation failed when it should not be able", op),
                },
                span.clone(),
            ));
        }
    })
}
