use std::{
    cell::RefCell, collections::HashMap, error::Error, fmt, iter::repeat, mem::swap,
    mem::transmute, rc::Rc,
};

use pest::{
    error::{Error as PestError, ErrorVariant},
    Span,
};

use crate::{
    ast::*,
    builtin::FUNCTIONS,
    entity::{Entity, Key},
    format::{FieldPatternFormatter, PatternFormatter, ValueFormatter},
    num::Num,
    parse::{parse, CheckError, Rule},
    pattern::{FieldPattern, FieldPatternType, Pattern, PatternType},
    value::*,
};

pub type BimoFn<'i> = fn(&mut Runtime<'i>, &Span<'i>) -> RuntimeResult<'i>;

#[derive(Debug)]
pub enum RuntimeErrorKind<'i> {
    Check(Vec<CheckError<'i>>),
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

impl<'i> RuntimeErrorKind<'i> {
    pub fn span(self, span: Span<'i>) -> RuntimeError<'i> {
        RuntimeError { kind: self, span }
    }
}

impl<'i> fmt::Display for RuntimeErrorKind<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RuntimeErrorKind::Check(errors) => {
                for error in errors {
                    writeln!(f, "{}", error)?;
                }
                Ok(())
            }
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
    pub kind: RuntimeErrorKind<'i>,
    pub span: Span<'i>,
}

impl<'i> fmt::Display for RuntimeError<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let RuntimeErrorKind::Check(_) = self.kind {
            write!(f, "{}", self.kind)
        } else {
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
}

impl<'i> Error for RuntimeError<'i> {}

pub type RuntimeResult<'i, T = Value<'i>> = Result<T, RuntimeError<'i>>;

impl<'i> From<Vec<CheckError<'i>>> for RuntimeError<'i> {
    fn from(errors: Vec<CheckError<'i>>) -> Self {
        RuntimeErrorKind::Check(errors).span(Span::new("", 0, 0).unwrap())
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
    fn bind_pattern(&mut self, pattern: &Pattern<'i>, val: Value<'i>) -> Value<'i> {
        match &pattern.ty {
            PatternType::Single(ident) => {
                self.bind(ident, val);
                Value::Bool(true)
            }
            PatternType::List { patterns, .. } => Value::Bool(if let Value::List(list) = val {
                patterns
                    .iter()
                    .zip(list.iter().chain(repeat(&Value::Nil)))
                    .fold(true, |acc, (pattern, item)| {
                        self.bind_pattern(pattern, item.clone()).is_truthy() && acc
                    })
            } else {
                for pattern in patterns {
                    self.bind_pattern(pattern, Value::Nil);
                }
                false
            }),
            PatternType::Entity { patterns, .. } => Value::Bool(if let Value::Entity(map) = val {
                patterns.iter().fold(true, |acc, pattern| {
                    self.bind_field_pattern(pattern, Some(&map)).is_truthy() && acc
                })
            } else {
                for pattern in patterns {
                    self.bind_field_pattern(pattern, None);
                }
                false
            }),
            PatternType::Nil(_) => Value::Bool(val == Value::Nil),
            PatternType::Bool { b: b1, .. } => Value::Bool(if let Value::Bool(b2) = val {
                b1 == &b2
            } else {
                false
            }),
            PatternType::Int { int, .. } => Value::Bool(if let Value::Num(num) = val {
                int == &num.to_i64()
            } else {
                false
            }),
            PatternType::String { string, .. } => Value::Bool(if let Value::String(s) = val {
                *s == **string
            } else {
                false
            }),
        }
    }
    fn bind_field_pattern(
        &mut self,
        pattern: &FieldPattern<'i>,
        source: Option<&Entity<'i>>,
    ) -> Value<'i> {
        match &pattern.ty {
            FieldPatternType::SameName(ident) => {
                let (val, found) = if let Some(val) =
                    source.and_then(|map| map.try_get(Key::Field(ident.clone())))
                {
                    (val.clone(), true)
                } else {
                    (Value::Nil, false)
                };
                self.bind(&ident, val);
                Value::Bool(found)
            }
            FieldPatternType::Pattern { field, pattern, .. } => {
                let (val, found) = if let Some(val) =
                    source.and_then(|map| map.try_get(Key::Field(field.clone())))
                {
                    (val.clone(), true)
                } else {
                    (Value::Nil, false)
                };
                Value::Bool(self.bind_pattern(pattern, val).is_truthy() && found)
            }
        }
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
    pub fn format<'r>(&'r self, value: &'r Value<'i>) -> ValueFormatter<'i, 'r> {
        ValueFormatter::new(self, value)
    }
    pub fn format_pattern<'r>(&'r self, pattern: &'r Pattern<'i>) -> PatternFormatter<'i, 'r> {
        PatternFormatter::new(self, pattern)
    }
    pub fn format_field_pattern<'r>(
        &'r self,
        pattern: &'r FieldPattern<'i>,
    ) -> FieldPatternFormatter<'i, 'r> {
        FieldPatternFormatter::new(self, pattern)
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
    fn eval_bind_expr(&mut self, expr: &BindExpr<'i>) -> RuntimeResult<'i> {
        let val = self.eval_node(&expr.body)?;
        Ok(self.scope.bind_pattern(&expr.pattern, val))
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
                        StringPart::Format(node) => {
                            let val = self.eval_node(node)?;
                            let formatted = self.format(&val).to_string();
                            s.push_str(&formatted)
                        }
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
                let mut entity = Entity::with_capacity(entries.len());
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
                if let Some(node) = default {
                    let span = node.span().clone();
                    let default = self.eval_node(node)?;
                    match default {
                        Value::Nil => {}
                        Value::Tag(id) => {
                            entity.set(Key::Tag(id), Value::Bool(true));
                        }
                        Value::Entity(default_map) => match default_map.try_into_iter() {
                            Ok(default) => {
                                for (k, v) in default {
                                    entity.entry(k).or_insert(v);
                                }
                            }
                            Err(default) => {
                                for (k, v) in &default {
                                    if entity.get(k) == &Value::Nil {
                                        entity.set(k.clone(), v.clone());
                                    }
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
            Term::Pattern(pattern) => Value::Pattern(pattern.clone()),
        })
    }
    fn eval_access_expr(&mut self, expr: &AccessExpr<'i>) -> RuntimeResult<'i> {
        let root = self.eval_node(&expr.root)?;
        Ok(match root {
            Value::Entity(map) => match &expr.accessor {
                Accessor::Key(key) => map.get(key).clone(),
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
                        let val = if let Some(arg) = args.get(i) {
                            arg.eval(self)?
                        } else {
                            Value::Nil
                        };
                        call_scope.bind_pattern(param, val);
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
                    return Err(RuntimeErrorKind::InvalidListIndex {
                        index: first_arg.type_name().into(),
                    }
                    .span(span.clone()));
                }
            }
            Value::Pattern(pattern) => {
                let first_arg = args
                    .first()
                    .map(|node| node.eval(self))
                    .transpose()?
                    .unwrap_or(Value::Nil);
                self.scope.push(Scope::default());
                self.scope.bind_pattern(pattern, first_arg)
            }
            val => {
                return Err(RuntimeErrorKind::InvalidCall {
                    called: val.type_name().into(),
                }
                .span(span.clone()))
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
}

impl<'i> Arg<'i> for Value<'i> {
    fn eval(&self, _: &mut Runtime<'i>) -> RuntimeResult<'i> {
        Ok(self.clone())
    }
}

impl<'i> Arg<'i> for Node<'i> {
    fn eval(&self, runtime: &mut Runtime<'i>) -> RuntimeResult<'i> {
        runtime.eval_node(self)
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
