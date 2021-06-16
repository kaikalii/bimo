use std::{fs, path::Path};

use crate::{
    ast::{FunctionDef, Item, Items, Node, Term},
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
        FormatSettings {
            max_width: 25,
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

        let Permutation(lines) = items.best_permutation(0, self);

        let mut text = String::new();
        for line in lines {
            text.push_str(&tabs(line.indent));
            text.push_str(&line.string);
            text.push('\n');
        }
        text.push('\n');

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

        Ok(())
    }
}

#[derive(Debug, Clone)]
struct Line {
    string: String,
    indent: usize,
}

#[derive(Debug, Clone)]
struct Permutation(Vec<Line>);

impl From<Vec<Line>> for Permutation {
    fn from(lines: Vec<Line>) -> Permutation {
        Permutation(lines)
    }
}

impl Permutation {
    fn new() -> Self {
        Permutation(Vec::new())
    }
    fn len(&self) -> usize {
        self.0.len()
    }
    fn is_line(&self) -> bool {
        self.len() == 1
    }
    fn only(string: impl ToString, indent: usize) -> Vec<Self> {
        vec![Permutation::new().line(string, indent)]
    }
    fn line(mut self, string: impl ToString, indent: usize) -> Self {
        self.0.push(Line {
            string: string.to_string(),
            indent,
        });
        self
    }
    fn extend(mut self, mut other: Self) -> Self {
        self.0.append(&mut other.0);
        self
    }
    fn append_perm(mut self, perm: Permutation) -> Self {
        let mut lines = perm.0.into_iter();
        if let Some(line) = lines.next() {
            if let Some(last) = self.0.last_mut() {
                last.string.push_str(&line.string);
            } else {
                self.0.push(line);
            }
        }
        self.0.extend(lines);
        self
    }
    fn append_str(mut self, string: impl AsRef<str>) -> Self {
        if let Some(line) = self.0.last_mut() {
            line.string.push_str(string.as_ref());
        } else {
            panic!("no line to append to");
        }
        self
    }
    fn maybe_append(self, string: impl AsRef<str>, indent: usize, multiline: bool) -> Self {
        if multiline {
            self.line(string.as_ref(), indent)
        } else {
            self.append_str(string)
        }
    }
    fn max_width(&self) -> usize {
        self.0
            .iter()
            .map(|line| line.indent * 4 + line.string.trim().len())
            .max()
            .unwrap()
    }
    fn join<A, B, C, F>(a: A, b: B, join: F) -> Vec<Self>
    where
        A: IntoIterator<Item = Self>,
        B: IntoIterator<Item = Self> + Clone,
        C: IntoIterator<Item = Self>,
        F: Fn(Self, Self) -> C,
    {
        let mut joined = Vec::new();
        for a in a {
            for b in b.clone() {
                joined.extend(join(a.clone(), b));
            }
        }
        joined
    }
    fn sep_list<T, F>(
        self,
        indent: usize,
        settings: &FormatSettings,
        items: &[T],
        tail: F,
    ) -> Vec<Permutation>
    where
        T: Formattable,
        F: Fn(Permutation, bool) -> Vec<Permutation>,
    {
        let mut single = self.clone();
        for (i, item) in items.iter().enumerate() {
            if i > 0 {
                single = single.append_str(",");
                single = single.append_str(" ");
            }
            single = single.append_perm(item.best_permutation(indent, settings));
        }
        let mut multi = self;
        for item in items {
            multi = multi
                .extend(item.best_permutation(indent, settings))
                .append_str(",");
        }
        tail(single, false)
            .into_iter()
            .chain(tail(multi, true))
            .collect()
    }
}

trait Formattable {
    fn name() -> &'static str;
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation>;
    fn best_permutation(&self, indent: usize, settings: &FormatSettings) -> Permutation {
        let perms = self.permutations(indent, settings);
        let best = perms
            .iter()
            .filter(|perm| perm.max_width() <= settings.max_width)
            .cloned()
            .min_by(|a, b| {
                a.len()
                    .cmp(&b.len())
                    .then(a.max_width().cmp(&b.max_width()).reverse())
            });
        if let Some(best) = best {
            best
        } else {
            perms
                .into_iter()
                .min_by_key(Permutation::max_width)
                .unwrap()
        }
    }
}

fn tabs(n: usize) -> String {
    format!("{:tabs$}", "", tabs = n * 4)
}

impl<T> Formattable for Box<T>
where
    T: Formattable,
{
    fn name() -> &'static str {
        T::name()
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        (&**self).permutations(indent, settings)
    }
}

impl<'i> Formattable for Term<'i> {
    fn name() -> &'static str {
        "term"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Term::Nil => Permutation::only("nil", indent),
            Term::Bool(b) => Permutation::only(b, indent),
            Term::Int(i) => Permutation::only(i, indent),
            Term::Real(r) => Permutation::only(r, indent),
            Term::String(_) => {
                todo!()
            }
            Term::Ident(ident) => Permutation::only(ident.name, indent),
            Term::List(nodes) => Permutation::new().line("[", indent).sep_list(
                indent + 1,
                settings,
                nodes,
                |perm, multiline| vec![perm.maybe_append("]", indent, multiline)],
            ),
            Term::Expr(items) => vec![items
                .iter()
                .fold(Permutation::new().line("(", indent), |perm, item| {
                    perm.extend(item.best_permutation(indent + 1, settings))
                })
                .line(")", indent)],
            term => todo!("{:?}", term),
        }
    }
}

impl<'i> Formattable for Pattern<'i> {
    fn name() -> &'static str {
        "pattern"
    }
    fn permutations(&self, indent: usize, _settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Pattern::Single(ident) | Pattern::Value(ident) => Permutation::only(ident.name, indent),
            Pattern::Nil(_) => Permutation::only("nil", indent),
            Pattern::Bool { b, .. } => Permutation::only(b, indent),
            Pattern::Int { int, .. } => Permutation::only(int, indent),
            _ => todo!(),
        }
    }
}

impl<'i> Formattable for Node<'i> {
    fn name() -> &'static str {
        "node"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Node::Term(term, ..) => term.permutations(indent, settings),
            Node::BinExpr(expr) => Permutation::join(
                expr.left.permutations(indent, settings),
                expr.right.permutations(indent, settings),
                |left, right| {
                    let op = expr.op_span.as_str().trim();
                    vec![
                        left.clone()
                            .append_str(format!(" {} ", op))
                            .append_perm(right.clone()),
                        left.line(format!("{} ", op), indent + 1).append_perm(right),
                    ]
                },
            ),
            Node::Call(expr) => expr
                .caller
                .permutations(indent, settings)
                .into_iter()
                .flat_map(|perm| {
                    perm.append_str("(").sep_list(
                        indent + 1,
                        settings,
                        &expr.args,
                        |perm, multiline| vec![perm.maybe_append(")", indent, multiline)],
                    )
                })
                .collect(),
            node => todo!("{:?}", node),
        }
    }
}

impl<'i> Formattable for FunctionDef<'i> {
    fn name() -> &'static str {
        "function_def"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        let left = Permutation::new()
            .line(self.ident.name, indent)
            .append_str("(")
            .sep_list(indent + 1, settings, &self.params, |perm, multiline| {
                vec![perm.maybe_append(") = ", indent, multiline)]
            });
        let on_same_line = Permutation::join(
            left.clone(),
            self.body.permutations(indent, settings),
            |left, right| {
                if left.is_line() && right.is_line() {
                    Some(left.append_perm(right))
                } else {
                    None
                }
            },
        );
        let on_next_line = Permutation::join(
            left,
            self.body.permutations(indent + 1, settings),
            |left, right| {
                if left.is_line() {
                    Some(left.extend(right))
                } else {
                    None
                }
            },
        );
        on_same_line.into_iter().chain(on_next_line).collect()
    }
}

impl<'i> Formattable for Item<'i> {
    fn name() -> &'static str {
        "item"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Item::Node(node) => node.permutations(indent, settings),
            Item::FunctionDef(def) => def.permutations(indent, settings),
        }
    }
}

impl<'i> Formattable for Items<'i> {
    fn name() -> &'static str {
        "items"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        vec![self.iter().fold(Permutation::new(), |perm, item| {
            perm.extend(item.best_permutation(indent, settings))
        })]
    }
}
