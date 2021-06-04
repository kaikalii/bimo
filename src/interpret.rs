use std::{collections::HashMap, error::Error, fmt, rc::Rc};

use pest::{
    error::{Error as PestError, ErrorVariant},
    Span,
};

use crate::{
    ast::*,
    parse::{parse, CheckError, Ids, Rule},
    value::{Key, Value},
};

pub type BimoFn = fn(&mut Runtime);

#[derive(Debug)]
pub enum RuntimeErrorKind {
    InvalidBinaryOperation {
        left: String,
        right: String,
        op: BinOp,
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

pub type RuntimeResult<'i> = Result<Value, RuntimeError<'i>>;

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
    scopes: Vec<Scope>,
}

#[derive(Default)]
pub struct Scope {
    pub values: HashMap<IdentId, Value>,
}

impl<'i> Runtime<'i> {
    pub fn new() -> Self {
        Runtime {
            scopes: vec![],
            ids: Ids::default(),
        }
    }
    pub fn format<'b>(&'b self, value: &'b Value) -> ValueFormatter<'i, 'b> {
        ValueFormatter {
            value,
            runtime: self,
        }
    }
    pub fn eval<'r>(&'r mut self, input: &'i str) -> Result<Value, EvalError<'i>> {
        let items = parse(self, input)?;
        let mut res = Value::Nil;
        for item in items {
            res = self.eval_item(item)?;
        }
        Ok(res)
    }
    pub fn check<'r>(&'r mut self, input: &'i str) -> Result<(), Vec<CheckError<'i>>> {
        parse(self, input)?;
        Ok(())
    }
    fn eval_item(&mut self, item: Item<'i>) -> RuntimeResult<'i> {
        match item {
            Item::Node(node) => self.eval_node(node),
            Item::Def(_) => todo!(),
        }
    }
    fn eval_node(&mut self, node: Node<'i>) -> RuntimeResult<'i> {
        match node {
            Node::Term(term, _) => self.eval_term(term),
            Node::BinExpr(expr) => self.eval_bin_expr(expr),
            _ => todo!(),
        }
    }
    fn eval_term(&mut self, term: Term<'i>) -> RuntimeResult<'i> {
        Ok(match term {
            Term::Nil => Value::Nil,
            Term::Bool(b) => Value::Bool(b),
            Term::Int(i) => Value::Int(i),
            Term::Real(r) => Value::Real(r),
            Term::String(s) => Value::String(s),
            Term::List(nodes) => Value::List(Rc::new(
                nodes
                    .into_iter()
                    .map(|node| self.eval_node(node))
                    .collect::<Result<_, _>>()?,
            )),
            Term::Expr(items) => {
                self.scopes.push(Scope::default());
                let res = items
                    .into_iter()
                    .map(|item| self.eval_item(item))
                    .last()
                    .transpose()?
                    .unwrap_or(Value::Nil);
                self.scopes.pop().unwrap();
                res
            }
            Term::Tag(id) => Value::Tag(id),
            Term::Ident(ident) => self.scopes.last().unwrap().values[&ident.id].clone(),
            Term::Closure(_) => todo!(),
        })
    }
    fn eval_bin_expr(&mut self, expr: BinExpr<'i>) -> RuntimeResult<'i> {
        let left = self.eval_node(*expr.left)?;
        let right = *expr.right;
        let right = || self.eval_node(right);
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
        bin_op_impl(expr.op, left, right()?, expr.span, int, real)
    }
}

type IntBinFn = fn(i64, i64) -> Value;
type RealBinFn = fn(f64, f64) -> Value;

fn bin_op_impl(
    op: BinOp,
    left: Value,
    right: Value,
    span: Span,
    int: IntBinFn,
    real: RealBinFn,
) -> RuntimeResult {
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
            .span(span))
        }
    })
}

pub struct ValueFormatter<'i, 'b> {
    value: &'b Value,
    runtime: &'b Runtime<'i>,
}

impl<'i, 'b> fmt::Display for ValueFormatter<'i, 'b> {
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
        }
    }
}