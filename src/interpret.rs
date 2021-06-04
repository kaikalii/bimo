use std::{collections::HashMap, error::Error, fmt, mem::swap, rc::Rc};

use pest::{
    error::{Error as PestError, ErrorVariant},
    Span,
};

use crate::{
    ast::*,
    parse::{parse, CheckError, Ids, Rule},
    value::{Function, Key, Value},
};

pub type BimoFn = fn(&mut Runtime);

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
                _ => todo!(),
            },
            RuntimeErrorKind::InvalidUnaryOperation { operand, op } => match op {
                UnOp::Neg => write!(f, "Unable to negate {}", operand),
            },
            RuntimeErrorKind::InvalidCall { called } => write!(f, "Unable to call {}", called),
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
    pub(crate) ids: Ids<'i>,
    scope: Scope<'i>,
}

#[derive(Debug, Clone, Default)]
pub struct Scope<'i> {
    parent: Option<Rc<Self>>,
    pub values: HashMap<IdentId, Value<'i>>,
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
}

impl<'i> Runtime<'i> {
    pub fn new() -> Self {
        Runtime {
            scope: Scope::default(),
            ids: Ids::default(),
        }
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
                let id = self.ids.ident(def.ident.name);
                let val = if def.params.is_empty() {
                    self.eval_items(&def.items)?
                } else {
                    Value::Function(Rc::new(Function {
                        scope: self.scope.clone(),
                        params: def.params.clone(),
                        items: def.items.clone(),
                    }))
                };
                self.scope.values.insert(id, val);
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
        }
    }
    fn eval_term(&mut self, term: &Term<'i>) -> RuntimeResult<'i> {
        Ok(match term {
            Term::Nil => Value::Nil,
            Term::Bool(b) => Value::Bool(*b),
            Term::Int(i) => Value::Int(*i),
            Term::Real(r) => Value::Real(*r),
            Term::String(s) => Value::String(s.clone()),
            Term::List(nodes) => Value::List(Rc::new(
                nodes
                    .iter()
                    .map(|node| self.eval_node(node))
                    .collect::<Result<_, _>>()?,
            )),
            Term::Expr(items) => {
                self.scope.push(Scope::default());
                let res = items
                    .iter()
                    .map(|item| self.eval_item(item))
                    .last()
                    .transpose()?
                    .unwrap_or(Value::Nil);
                self.scope.pop();
                res
            }
            Term::Tag(id) => Value::Tag(*id),
            Term::Ident(ident) => self.scope.values[&ident.id].clone(),
            Term::Closure(closure) => Value::Function(Rc::new(Function {
                scope: self.scope.clone(),
                params: closure.params.clone(),
                items: closure.body.clone(),
            })),
        })
    }
    fn eval_bin_expr(&mut self, expr: &BinExpr<'i>) -> RuntimeResult<'i> {
        let left = self.eval_node(&expr.left)?;
        let right = &expr.right;
        let mut right = || self.eval_node(&right);
        let (int, real) = match expr.op {
            BinOp::Or => return if left.is_truthy() { Ok(left) } else { right() },
            BinOp::And => return if left.is_truthy() { right() } else { Ok(left) },
            BinOp::Add => (
                (|a, b| Value::Int(a + b)) as IntBinFn,
                (|a, b| Value::Real(a + b)) as RealBinFn,
            ),
            BinOp::Sub => (
                (|a, b| Value::Int(a - b)) as IntBinFn,
                (|a, b| Value::Real(a - b)) as RealBinFn,
            ),
            BinOp::Mul => (
                (|a, b| Value::Int(a * b)) as IntBinFn,
                (|a, b| Value::Real(a * b)) as RealBinFn,
            ),
            BinOp::Div => (
                (|a, b| Value::Int(a / b)) as IntBinFn,
                (|a, b| Value::Real(a / b)) as RealBinFn,
            ),
            BinOp::Rem => (
                (|a, b| Value::Int(a % b)) as IntBinFn,
                (|a, b| Value::Real(a % b)) as RealBinFn,
            ),
            BinOp::Less => (
                (|a, b| Value::Bool(a < b)) as IntBinFn,
                (|a, b| Value::Bool(a < b)) as RealBinFn,
            ),
            BinOp::LessOrEqual => (
                (|a, b| Value::Bool(a <= b)) as IntBinFn,
                (|a, b| Value::Bool(a <= b)) as RealBinFn,
            ),
            BinOp::Greater => (
                (|a, b| Value::Bool(a > b)) as IntBinFn,
                (|a, b| Value::Bool(a > b)) as RealBinFn,
            ),
            BinOp::GreaterOrEqual => (
                (|a, b| Value::Bool(a >= b)) as IntBinFn,
                (|a, b| Value::Bool(a >= b)) as RealBinFn,
            ),
            BinOp::Equals => return Ok(Value::Bool(left == right()?)),
            BinOp::NotEquals => return Ok(Value::Bool(left != right()?)),
        };
        bin_op_impl(expr.op, left, right()?, &expr.span, int, real)
    }
    fn eval_un_expr(&mut self, expr: &UnExpr<'i>) -> RuntimeResult<'i> {
        let inner = self.eval_node(&expr.inner)?;
        Ok(match expr.op {
            UnOp::Neg => match inner {
                Value::Int(i) => Value::Int(-i),
                Value::Real(r) => Value::Real(-r),
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
            Value::Function(function) => {
                let mut call_scope = function.scope.clone();
                for (i, param) in function.params.iter().enumerate() {
                    let val = if let Some(node) = expr.args.get(i) {
                        self.eval_node(node)?
                    } else {
                        Value::Nil
                    };
                    call_scope.values.insert(param.ident.id, val);
                }
                swap(&mut self.scope, &mut call_scope);
                let val = self.eval_items(&function.items)?;
                swap(&mut self.scope, &mut call_scope);
                val
            }
            val => {
                return Err(RuntimeErrorKind::InvalidCall {
                    called: val.type_name().into(),
                }
                .span(expr.span.clone()))
            }
        })
    }
}

type IntBinFn<'i> = fn(i64, i64) -> Value<'i>;
type RealBinFn<'i> = fn(f64, f64) -> Value<'i>;

fn bin_op_impl<'i>(
    op: BinOp,
    left: Value<'i>,
    right: Value<'i>,
    span: &Span<'i>,
    int: IntBinFn<'i>,
    real: RealBinFn<'i>,
) -> RuntimeResult<'i> {
    Ok(match (left, right) {
        (Value::Int(a), Value::Int(b)) => int(a, b),
        (Value::Int(a), Value::Real(b)) => real(a as f64, b),
        (Value::Real(a), Value::Int(b)) => real(a, b as f64),
        (Value::Real(a), Value::Real(b)) => real(a, b),
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

impl<'i, 'r> fmt::Display for ValueFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::Nil => "nil".fmt(f),
            Value::Bool(b) => b.fmt(f),
            Value::Int(i) => i.fmt(f),
            Value::Real(r) => r.fmt(f),
            Value::String(s) => s.fmt(f),
            Value::Tag(id) => {
                write!(f, "#{}", self.runtime.ids.tag_name(*id))
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
                for (i, (key, val)) in entity.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    match key {
                        Key::Field(id) => self.runtime.ids.ident_name(*id).fmt(f),
                        Key::Int(i) => i.fmt(f),
                        Key::String(s) => s.fmt(f),
                    }?;
                    write!(f, ": {}", self.runtime.format(val))?;
                }
                write!(f, "}}")
            }
            Value::Function(function) => write!(f, "function({:p})", Rc::as_ptr(function)),
        }
    }
}
