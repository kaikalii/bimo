use std::{
    cell::RefCell, collections::HashMap, error::Error, fmt, intrinsics::transmute, mem::swap,
    rc::Rc,
};

use itertools::Itertools;
use pest::{
    error::{Error as PestError, ErrorVariant},
    Span,
};

use crate::{
    ast::*,
    builtin::FUNCTIONS,
    num::Num,
    parse::{parse, CheckError, Rule},
    value::{BimoFunction, Function, HashState, Key, Value},
};

pub type BimoFn<'i> = fn(&mut Runtime<'i>, span: &Span<'i>) -> RuntimeResult<'i>;

#[derive(Debug)]
pub enum RuntimeErrorKind {
    InvalidBinaryOperation {
        left: String,
        right: String,
        op: BinOp,
    },
    InvalidUnaryOperation {
        operand: String,
        op: UnOp,
    },
    InvalidCall {
        called: String,
    },
    InvalidEntityDefault {
        default: String,
    },
    InvalidFieldAccess {
        root: String,
        field: Option<String>,
    },
    InvalidListIndex {
        index: String,
    },
    Generic(String),
}

impl RuntimeErrorKind {
    pub fn span(self, span: Span) -> RuntimeError {
        RuntimeError { kind: self, span }
    }
}

impl fmt::Display for RuntimeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RuntimeErrorKind::InvalidBinaryOperation { left, right, op } => match op {
                BinOp::Add => write!(f, "Unable to add {} and {}", left, right),
                BinOp::Sub => write!(f, "Unable to subtract {} from {}", right, left),
                BinOp::Mul => write!(f, "Unable to multiple {} and {}", left, right),
                BinOp::Div | BinOp::Rem => write!(f, "Unable to divide {} by {}", left, right),
                BinOp::Less | BinOp::Greater | BinOp::LessOrEqual | BinOp::GreaterOrEqual => {
                    write!(f, "Unable to compare {} and {}", left, right)
                }
                op => unreachable!("{:?} operation failed when it should not be able", op),
            },
            RuntimeErrorKind::InvalidUnaryOperation { operand, op } => match op {
                UnOp::Neg => write!(f, "Unable to negate {}", operand),
            },
            RuntimeErrorKind::InvalidCall { called } => write!(f, "Unable to call {}", called),
            RuntimeErrorKind::InvalidEntityDefault { default } => {
                write!(f, "Entity cannot be default initialized from {}", default)
            }
            RuntimeErrorKind::InvalidFieldAccess { root, field } => {
                if let Some(field) = field {
                    write!(f, "{} cannot has no field {}", root, field)
                } else {
                    write!(f, "{} does not have fields", root)
                }
            }
            RuntimeErrorKind::InvalidListIndex { index } => {
                write!(f, "List cannot be indexed with {}", index)
            }
            RuntimeErrorKind::Generic(message) => write!(f, "{}", message),
        }
    }
}

#[derive(Debug)]
pub struct RuntimeError<'i> {
    pub kind: RuntimeErrorKind,
    pub span: Span<'i>,
}

impl<'i> fmt::Display for RuntimeError<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            PestError::<Rule>::new_from_span(
                ErrorVariant::CustomError {
                    message: self.kind.to_string()
                },
                self.span.clone()
            )
        )
    }
}

impl<'i> Error for RuntimeError<'i> {}

pub type RuntimeResult<'i> = Result<Value<'i>, RuntimeError<'i>>;

#[derive(Debug)]
pub enum EvalError<'i> {
    Check(Vec<CheckError<'i>>),
    Runtime(RuntimeError<'i>),
}

impl<'i> fmt::Display for EvalError<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EvalError::Check(errors) => {
                for e in errors {
                    writeln!(f, "{}", e)?;
                }
                Ok(())
            }
            EvalError::Runtime(e) => e.fmt(f),
        }
    }
}

impl<'i> Error for EvalError<'i> {}

impl<'i> From<Vec<CheckError<'i>>> for EvalError<'i> {
    fn from(errors: Vec<CheckError<'i>>) -> EvalError<'i> {
        EvalError::Check(errors)
    }
}

impl<'i> From<RuntimeError<'i>> for EvalError<'i> {
    fn from(e: RuntimeError<'i>) -> EvalError<'i> {
        EvalError::Runtime(e)
    }
}

pub struct Runtime<'i> {
    scope: Scope<'i>,
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
}

impl<'i> Runtime<'i> {
    pub fn new() -> Self {
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
                                    Function::Rust(rf).into(),
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
    pub fn format<'r>(&'r self, value: &'r Value<'i>) -> ValueFormatter<'i, 'r> {
        ValueFormatter {
            value,
            runtime: self,
        }
    }
    pub fn eval<'r>(&'r mut self, input: &'i str) -> Result<Value<'i>, EvalError<'i>> {
        let items = parse(self, input)?;
        Ok(self.eval_items(&items)?)
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
            Item::Def(def) => {
                let val = if def.params.is_empty() {
                    self.eval_items(&def.items)?
                } else {
                    Value::Function(
                        Function::Bimo(BimoFunction {
                            scope: self.scope.clone(),
                            params: def.params.clone(),
                            items: def.items.clone().into(),
                        })
                        .into(),
                    )
                };
                self.scope.values.borrow_mut().insert(def.ident.name, val);
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
        }
    }
    fn eval_term(&mut self, term: &Term<'i>) -> RuntimeResult<'i> {
        Ok(match term {
            Term::Nil => Value::Nil,
            Term::Bool(b) => Value::Bool(*b),
            Term::Int(i) => Value::Num((*i).into()),
            Term::Real(r) => Value::Num((*r).into()),
            Term::String(s) => Value::String(s.clone()),
            Term::List(nodes) => Value::List(Rc::new(
                nodes
                    .iter()
                    .map(|node| self.eval_node(node))
                    .collect::<Result<_, _>>()?,
            )),
            Term::Entity { entries, default } => {
                let mut map = HashMap::with_capacity_and_hasher(entries.len(), HashState);
                for entry in entries {
                    match entry {
                        Entry::Tag(ident) => map.insert(Key::Tag(ident.clone()), Value::Bool(true)),
                        Entry::Field(ident, node) => {
                            map.insert(Key::Field(ident.clone()), self.eval_node(node)?)
                        }
                        Entry::Index(key, val) => {
                            map.insert(Key::Value(self.eval_node(key)?), self.eval_node(val)?)
                        }
                    };
                }
                if let Some(node) = default {
                    let span = node.span().clone();
                    let default = self.eval_node(node)?;
                    match default {
                        Value::Nil => {}
                        Value::Tag(id) => {
                            map.insert(Key::Tag(id), Value::Bool(true));
                        }
                        Value::Entity(default_map) => match Rc::try_unwrap(default_map) {
                            Ok(default_map) => {
                                for (k, v) in default_map {
                                    map.entry(k).or_insert(v);
                                }
                            }
                            Err(default_map) => {
                                for (k, v) in &*default_map {
                                    map.entry(k.clone()).or_insert_with(|| v.clone());
                                }
                            }
                        },
                        val => {
                            return Err(RuntimeErrorKind::InvalidEntityDefault {
                                default: val.type_name().into(),
                            }
                            .span(span))
                        }
                    }
                }
                Value::Entity(Rc::new(map))
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
                items: closure.body.clone().into(),
            }))),
        })
    }
    fn eval_access_expr(&mut self, expr: &AccessExpr<'i>) -> RuntimeResult<'i> {
        let root = self.eval_node(&expr.root)?;
        Ok(match root {
            Value::Entity(map) => match &expr.accessor {
                Accessor::Key(key) => {
                    if let Some(val) = map.get(key) {
                        val.clone()
                    } else {
                        Value::Nil
                    }
                }
            },
            val => {
                return Err(RuntimeErrorKind::InvalidFieldAccess {
                    root: self.format(&val).to_string(),
                    field: None,
                }
                .span(expr.span.clone()))
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
                    return Err(RuntimeErrorKind::InvalidUnaryOperation {
                        operand: val.type_name().into(),
                        op: expr.op,
                    }
                    .span(expr.span.clone()))
                }
            },
        })
    }
    fn eval_call(&mut self, expr: &CallExpr<'i>) -> RuntimeResult<'i> {
        let caller = self.eval_node(&expr.caller)?;
        Ok(match caller {
            Value::Function(function) => match &*function {
                Function::Bimo(function) => {
                    let mut call_scope = function.scope.clone();
                    call_scope.push(Scope::default());
                    for (i, param) in function.params.iter().enumerate() {
                        let val = if let Some(node) = expr.args.get(i) {
                            self.eval_node(node)?
                        } else {
                            Value::Nil
                        };
                        call_scope.values.borrow_mut().insert(param.ident.name, val);
                    }
                    swap(&mut self.scope, &mut call_scope);
                    let val = self.eval_items(&*function.items.borrow())?;
                    swap(&mut self.scope, &mut call_scope);
                    val
                }
                Function::Rust(function) => {
                    let call_scope = Scope::default();
                    for (i, param) in function.params.iter().enumerate() {
                        let val = if let Some(node) = expr.args.get(i) {
                            self.eval_node(node)?
                        } else {
                            Value::Nil
                        };
                        call_scope.values.borrow_mut().insert(param, val);
                    }
                    self.scope.push(call_scope);
                    let res = (function.f)(self, &expr.span);
                    self.scope.pop();
                    res?
                }
            },
            Value::Entity(map) => {
                let first_arg = expr
                    .args
                    .first()
                    .map(|node| self.eval_node(node))
                    .transpose()?
                    .unwrap_or(Value::Nil);
                if let Some(val) = map.get(&Key::Value(first_arg)) {
                    val.clone()
                } else {
                    Value::Nil
                }
            }
            Value::List(list) => {
                let first_arg = expr
                    .args
                    .first()
                    .map(|node| self.eval_node(node))
                    .transpose()?
                    .unwrap_or(Value::Nil);
                if let Value::Num(num) = first_arg {
                    let index = num.to_i64();
                    if index >= 0 {
                        let index = index as usize;
                        if index < list.len() {
                            list[index].clone()
                        } else {
                            Value::Nil
                        }
                    } else {
                        let rev_index = (-index) as usize;
                        if rev_index <= list.len() {
                            list[list.len() - rev_index].clone()
                        } else {
                            Value::Nil
                        }
                    }
                } else {
                    return Err(RuntimeErrorKind::InvalidListIndex {
                        index: first_arg.type_name().into(),
                    }
                    .span(expr.caller.span().clone()));
                }
            }
            val => {
                return Err(RuntimeErrorKind::InvalidCall {
                    called: val.type_name().into(),
                }
                .span(expr.caller.span().clone()))
            }
        })
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
            return Err(RuntimeErrorKind::InvalidBinaryOperation {
                left: a.type_name().into(),
                right: b.type_name().into(),
                op,
            }
            .span(span.clone()))
        }
    })
}

pub struct ValueFormatter<'i, 'r> {
    value: &'r Value<'i>,
    runtime: &'r Runtime<'i>,
}

impl<'i, 'r> fmt::Debug for ValueFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::String(s) => s.fmt(f),
            _ => write!(f, "{}", self),
        }
    }
}

impl<'i, 'r> fmt::Display for ValueFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::Nil => "nil".fmt(f),
            Value::Bool(b) => b.fmt(f),
            Value::Num(n) => n.fmt(f),
            Value::String(s) => s.fmt(f),
            Value::Tag(ident) => {
                write!(f, "#{}", ident.name)
            }
            Value::List(list) => {
                write!(f, "[")?;
                for (i, val) in list.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    self.runtime.format(val).fmt(f)?;
                }
                write!(f, "]")
            }
            Value::Entity(entity) => {
                write!(f, "{{")?;
                for (i, (key, val)) in entity.iter().sorted_by_key(|(key, _)| *key).enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    match key {
                        Key::Field(ident) => {
                            write!(f, "{}: {:?}", ident.name, self.runtime.format(val))?
                        }
                        Key::Tag(ident) => write!(f, "#{}", ident.name)?,
                        Key::Value(key) => write!(
                            f,
                            "{:?} => {:?}",
                            self.runtime.format(key),
                            self.runtime.format(val)
                        )?,
                    }
                }
                write!(f, "}}")
            }
            Value::Function(function) => write!(f, "function({:p})", Rc::as_ptr(function)),
        }
    }
}
