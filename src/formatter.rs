use std::{fs, path::Path};

use crate::{
    ast::{FunctionDef, Item, Items, Node, Term, UnOp},
    error::{BimoError, BimoResult},
    pattern::Pattern,
    runtime::Runtime,
};

#[derive(Debug, Clone)]
pub struct FormatSettings {
    pub max_width: usize,
    pub write: bool,
}

impl Default for FormatSettings {
    fn default() -> Self {
        // FormatSettings { max_width: 100 }
        FormatSettings {
            max_width: 30,
            write: false,
        }
    }
}

impl FormatSettings {
    pub fn format<'i>(&self, path: impl AsRef<Path>) -> BimoResult<'i, ()> {
        let input = fs::read_to_string(&path)?;
        let mut runtime = Runtime::new();
        let items = runtime
            .parse(&input, path.as_ref())
            .map_err(BimoError::change_lifetime)?;

        if let Some(text) = items.format(self.max_width) {
            if self.write {
                fs::write(path, text.as_bytes())?;
            } else {
                let path_str = path.as_ref().to_string_lossy();
                println!(
                    "{}\n{:-<width$}\n{}\n",
                    path_str,
                    "",
                    text,
                    width = path_str.len()
                );
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
struct Frag {
    string: String,
    depth: usize,
    on_multi: bool,
    on_single: bool,
    indent: bool,
    deindent: bool,
}

impl Frag {
    fn new(string: impl ToString, depth: usize) -> Self {
        Frag {
            string: string.to_string(),
            depth,
            on_multi: true,
            on_single: true,
            indent: false,
            deindent: false,
        }
    }
    fn open(depth: usize) -> Self {
        Frag::new("\n", depth).indent().multi_only()
    }
    fn close(depth: usize) -> Self {
        Frag::new("\n", depth).deindent().multi_only()
    }
    fn newline(depth: usize) -> Self {
        Frag::new("\n", depth).multi_only()
    }
    fn indent(self) -> Self {
        Frag {
            indent: true,
            ..self
        }
    }
    fn deindent(self) -> Self {
        Frag {
            deindent: true,
            ..self
        }
    }
    fn single_only(self) -> Self {
        Frag {
            on_multi: false,
            ..self
        }
    }
    fn multi_only(self) -> Self {
        Frag {
            on_single: false,
            ..self
        }
    }
}

trait Formattable {
    fn fragments(&self, depth: usize) -> Vec<Frag>;
    fn format(&self, max_width: usize) -> Option<String> {
        let frags = self.fragments(0);
        let mut formatted = None;
        for depth in 0..5 {
            println!("\ndepth: {}", depth);
            let mut indent = 0;
            let mut text = String::new();
            let mut push_indent = false;
            for frag in &frags {
                let multiline = depth > frag.depth;
                if multiline && !frag.on_multi || !multiline && !frag.on_single {
                    continue;
                }
                if push_indent && !frag.string.trim().is_empty() {
                    text.push_str(&tabs(indent));
                    push_indent = false;
                    println!("pushed indent");
                }
                println!("{:?}", frag);
                if frag.indent {
                    indent += 1;
                    println!("indent -> {}", indent);
                }
                if frag.deindent {
                    indent -= 1;
                    println!("deindent -> {}", indent);
                }
                text.push_str(&frag.string);
                if frag.string.contains('\n') {
                    push_indent = true;
                    println!("can push indent");
                }
            }

            text = text
                .lines()
                .map(|line| format!("{}\n", line.trim_end()))
                .collect();
            println!("text:\n{}\n", text);

            if text.lines().all(|line| line.len() < max_width) {
                formatted = Some(text);
                break;
            }
        }
        formatted
    }
}

fn tabs(n: usize) -> String {
    format!("{:tabs$}", "", tabs = n * 4)
}

impl<T> Formattable for Box<T>
where
    T: Formattable,
{
    fn fragments(&self, depth: usize) -> Vec<Frag> {
        (&**self).fragments(depth)
    }
}

fn sep_list<T>(frags: &mut Vec<Frag>, depth: usize, items: &[T])
where
    T: Formattable,
{
    frags.push(Frag::open(depth));
    for (i, item) in items.iter().enumerate() {
        frags.extend(item.fragments(depth));
        if i < items.len() - 1 {
            frags.push(Frag::new(",", depth));
            frags.push(Frag::new(" ", depth).single_only());
            frags.push(Frag::newline(depth).multi_only());
        } else {
            frags.push(Frag::new(",", depth).multi_only());
        }
    }
    frags.push(Frag::close(depth));
}

impl<'i> Formattable for Term<'i> {
    fn fragments(&self, depth: usize) -> Vec<Frag> {
        let mut frags = Vec::new();
        match self {
            Term::Nil => frags.push(Frag::new("nil", depth)),
            Term::Bool(b) => frags.push(Frag::new(b, depth)),
            Term::Int(i) => frags.push(Frag::new(i, depth)),
            Term::Real(r) => frags.push(Frag::new(r, depth)),
            Term::String(_) => {
                todo!()
            }
            Term::Ident(ident) => frags.push(Frag::new(ident.name, depth)),
            Term::List(nodes) => {
                frags.push(Frag::new("[", depth));
                sep_list(&mut frags, depth, nodes);
                frags.push(Frag::new("]", depth));
            }
            Term::Expr(items) => {
                frags.push(Frag::new("(", depth));
                frags.extend(items.fragments(depth));
                frags.push(Frag::new(")", depth));
            }
            term => todo!("{:?}", term),
        }
        frags
    }
}

impl<'i> Formattable for Pattern<'i> {
    fn fragments(&self, depth: usize) -> Vec<Frag> {
        let mut frags = Vec::new();
        match self {
            Pattern::Single(ident) | Pattern::Value(ident) => {
                frags.push(Frag::new(ident.name, depth))
            }
            Pattern::Bound { left, right, .. } => {
                frags.extend(left.fragments(depth));
                frags.push(Frag::new(": ", depth));
                frags.push(Frag::newline(depth + 1));
                frags.extend(right.fragments(depth));
            }
            Pattern::Nil(_) => frags.push(Frag::new("nil", depth)),
            Pattern::Bool { b, .. } => frags.push(Frag::new(b, depth)),
            Pattern::Int { int, .. } => frags.push(Frag::new(int, depth)),
            _ => todo!(),
        }
        frags
    }
}

impl<'i> Formattable for Node<'i> {
    fn fragments(&self, depth: usize) -> Vec<Frag> {
        let mut frags = Vec::new();
        match self {
            Node::Term(term, ..) => return term.fragments(depth),
            Node::If(expr) => {
                frags.push(Frag::new("if ", depth));
                frags.extend(expr.condition.fragments(depth + 3));
                frags.push(Frag::new(" then ", depth + 1).single_only());
                frags.push(Frag::open(depth + 1));
                frags.extend(expr.if_true.fragments(depth + 2));
                frags.push(Frag::close(depth + 1));
                frags.push(Frag::new(" ", depth).single_only());
                frags.push(Frag::new("else ", depth));
                frags.push(Frag::open(depth + 2));
                frags.extend(expr.if_false.fragments(depth + 2));
                frags.push(Frag::close(depth + 2));
            }
            Node::BinExpr(expr) => {
                frags.extend(expr.left.fragments(depth + 1));
                frags.push(Frag::open(depth));
                frags.push(Frag::new(format!(" {} ", expr.op_span.as_str()), depth));
                frags.extend(expr.right.fragments(depth + 1));
                frags.push(Frag::close(depth));
            }
            Node::UnExpr(expr) => {
                let op = match expr.op {
                    UnOp::Neg => "-",
                };
                frags.push(Frag::new(op, depth));
                frags.extend(expr.inner.fragments(depth));
            }
            Node::Call(expr) => {
                frags.extend(expr.caller.fragments(depth));
                frags.push(Frag::new("(", depth));
                sep_list(&mut frags, depth, &expr.args);
                frags.push(Frag::new(")", depth));
            }
            node => todo!("{:?}", node),
        }
        frags
    }
}

impl<'i> Formattable for FunctionDef<'i> {
    fn fragments(&self, depth: usize) -> Vec<Frag> {
        let mut frags = Vec::with_capacity(7);
        frags.push(Frag::new(self.ident.name, depth));
        frags.push(Frag::new("(", depth));
        sep_list(&mut frags, depth + 1, &self.params);
        frags.push(Frag::new(")", depth));
        frags.push(Frag::new(" = ", depth));
        frags.push(Frag::open(depth));
        frags.extend(self.body.fragments(depth + 1));
        frags.push(Frag::close(depth));
        frags
    }
}

impl<'i> Formattable for Item<'i> {
    fn fragments(&self, depth: usize) -> Vec<Frag> {
        match self {
            Item::Node(node) => node.fragments(depth),
            Item::FunctionDef(def) => def.fragments(depth),
        }
    }
}

impl<'i> Formattable for Items<'i> {
    fn fragments(&self, depth: usize) -> Vec<Frag> {
        let mut frags = Vec::new();
        for item in self {
            frags.extend(item.fragments(depth));
            frags.push(Frag::new("\n", depth));
        }
        frags
    }
}
