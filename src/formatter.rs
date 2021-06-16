use std::{fs, path::Path};

use crate::{
    ast::{FunctionDef, Item, Items, Node, Term, UnOp},
    error::{BimoError, BimoResult},
    runtime::Runtime,
};

#[derive(Debug, Clone)]
pub struct FormatSettings {
    pub max_width: usize,
}

impl Default for FormatSettings {
    fn default() -> Self {
        FormatSettings { max_width: 100 }
    }
}

impl FormatSettings {
    pub fn format<'i>(&self, path: impl AsRef<Path>) -> BimoResult<'i, ()> {
        let mut input = fs::read_to_string(&path)?;
        let mut runtime = Runtime::new();
        let items = runtime
            .parse(&input, path.as_ref())
            .map_err(BimoError::change_lifetime)?;
        fs::write(path, items.string(&mut 0, self).as_bytes())?;
        Ok(())
    }
}

enum Frag<'a> {
    Child(&'a dyn Formattable),
    String(String),
}

pub struct Fragment<'a> {
    frag: Frag<'a>,
    prefix: Option<String>,
    one_sep: Option<String>,
    multi_sep: Option<(String, bool)>,
}

impl<'a> Fragment<'a> {
    pub fn str(s: impl Into<String>) -> Self {
        Fragment {
            frag: Frag::String(s.into()),
            one_sep: None,
            multi_sep: None,
            prefix: None,
        }
    }
    pub fn child(child: &'a impl Formattable) -> Self {
        Fragment {
            frag: Frag::Child(child),
            one_sep: None,
            multi_sep: None,
            prefix: None,
        }
    }
    pub fn one_sep(self, sep: impl Into<String>) -> Self {
        Fragment {
            one_sep: Some(sep.into()),
            ..self
        }
    }
    pub fn multi_sep(self, same_line: impl Into<String>, indent: bool) -> Self {
        Fragment {
            multi_sep: Some((same_line.into(), indent)),
            ..self
        }
    }
    pub fn prefix(self, prefix: impl Into<String>) -> Self {
        Fragment {
            prefix: Some(prefix.into()),
            ..self
        }
    }
    pub fn either_sep(self, sep: impl Into<String>, indent: bool) -> Self {
        let sep = sep.into();
        self.one_sep(sep.clone()).multi_sep(sep, indent)
    }
}

pub trait Formattable {
    fn fragments(&self) -> Vec<Fragment>;
    fn string(&self, indent: &mut usize, settings: &FormatSettings) -> String {
        let mut line = format!("{:indent$}", "", indent = *indent * 4);
        for frag in self.fragments() {
            if let Some(prefix) = frag.prefix {
                line.push_str(&prefix);
            }
            match frag.frag {
                Frag::String(s) => line.push_str(&s),
                Frag::Child(child) => line.push_str(&child.string(&mut 0, settings)),
            }
            if let Some(sep) = frag.one_sep {
                line.push_str(&sep);
            }
        }
        line
    }
}

impl<T> Formattable for Box<T>
where
    T: Formattable,
{
    fn fragments(&self) -> Vec<Fragment> {
        (&**self).fragments()
    }
}

impl<'i> Formattable for Term<'i> {
    fn fragments(&self) -> Vec<Fragment> {
        let mut frags = Vec::new();
        match self {
            Term::Nil => frags.push(Fragment::str("nil")),
            Term::Bool(b) => frags.push(Fragment::str(b.to_string())),
            Term::Int(i) => frags.push(Fragment::str(i.to_string())),
            Term::Real(r) => frags.push(Fragment::str(r.to_string())),
            Term::String(_) => {
                todo!()
            }
            Term::Ident(ident) => frags.push(Fragment::str(ident.name)),
            Term::List(nodes) => {
                frags.push(Fragment::str("["));
                for node in nodes {
                    frags.push(Fragment::child(node).one_sep(","));
                }
                frags.push(Fragment::str("]"));
            }
            term => todo!("{:?}", term),
        }
        frags
    }
}

impl<'i> Formattable for Node<'i> {
    fn fragments(&self) -> Vec<Fragment> {
        let mut frags = Vec::new();
        match self {
            Node::Term(term, ..) => return term.fragments(),
            Node::If(expr) => {
                frags.push(Fragment::str("if"));
                frags.push(Fragment::child(&expr.condition).one_sep(" then "));
                frags.push(Fragment::child(&expr.if_true));
                frags.push(Fragment::str("else"));
                frags.push(Fragment::child(&expr.if_false));
            }
            Node::BinExpr(expr) => {
                frags.push(
                    Fragment::child(&expr.left)
                        .one_sep(format!(" {} ", expr.op_span.as_str()))
                        .multi_sep(format!(" {}", expr.op_span.as_str()), true),
                );
                frags.push(Fragment::child(&expr.right));
            }
            Node::UnExpr(expr) => frags.push(Fragment::child(&expr.inner).prefix(match expr.op {
                UnOp::Neg => "-",
            })),
            Node::Call(expr) => {
                frags.push(Fragment::child(&expr.caller).either_sep("(", true));
                for node in &expr.args {
                    frags.push(Fragment::child(node).one_sep(", ").multi_sep(",", false))
                }
                frags.push(Fragment::str(")"));
            }
            node => todo!("{:?}", node),
        }
        frags
    }
}

impl<'i> Formattable for FunctionDef<'i> {
    fn fragments(&self) -> Vec<Fragment> {
        todo!()
    }
}

impl<'i> Formattable for Item<'i> {
    fn fragments(&self) -> Vec<Fragment> {
        match self {
            Item::Node(node) => node.fragments(),
            Item::FunctionDef(def) => def.fragments(),
        }
    }
}

impl<'i> Formattable for Items<'i> {
    fn fragments(&self) -> Vec<Fragment> {
        self.iter()
            .map(|item| Fragment::child(item).either_sep("\n", false))
            .collect()
    }
}
