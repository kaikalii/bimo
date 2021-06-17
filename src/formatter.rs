use std::{fs, path::Path, slice::from_ref};

use crate::{
    ast::{Accessor, BindExpr, Entry, FunctionDef, Item, Items, Node, StringPart, Term, UnOp},
    entity::Key,
    error::{BimoError, BimoResult},
    pattern::{FieldPattern, Pattern},
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
            max_width: 40,
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
            text.push_str(line.string.trim());
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
    fn join_with<B, C, F>(self, b: B, join: F) -> Vec<Self>
    where
        B: IntoIterator<Item = Self> + Clone,
        C: IntoIterator<Item = Self>,
        F: Fn(Self, Self) -> C,
    {
        Permutation::join(Some(self), b, join)
    }
    fn sep_list<T, F, I>(
        self,
        indent: usize,
        settings: &FormatSettings,
        (onesep, multisep): (&str, &str),
        items: &[T],
        tail: F,
    ) -> Vec<Permutation>
    where
        T: Formattable,
        F: Fn(Permutation, bool) -> I,
        I: IntoIterator<Item = Self>,
    {
        let mut single = self.clone();
        for (i, item) in items.iter().enumerate() {
            if i > 0 {
                single = single.append_str(onesep);
                single = single.append_str(" ");
            }
            single = single.append_perm(item.best_permutation(indent, settings));
        }
        let mut multi = self;
        for item in items {
            multi = multi
                .extend(item.best_permutation(indent, settings))
                .append_str(multisep);
        }
        tail(single, false)
            .into_iter()
            .chain(tail(multi, true))
            .collect()
    }
    fn body<L, R>(left: L, right: &R, indent: usize, settings: &FormatSettings) -> Vec<Permutation>
    where
        L: IntoIterator<Item = Self> + Clone,
        R: Bracketed + ?Sized,
    {
        let bracketed = right.is_bracketed();
        let oneline = Permutation::join(
            left.clone(),
            right.permutations(indent, settings),
            |left, right| {
                if bracketed || left.is_line() && right.is_line() {
                    Some(left.append_perm(right))
                } else {
                    None
                }
            },
        );
        let multiline = Permutation::join(
            left,
            right.permutations(indent + 1, settings),
            |left, right| {
                if left.is_line() && !bracketed {
                    Some(left.extend(right))
                } else {
                    None
                }
            },
        );
        oneline.into_iter().chain(multiline).collect()
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

trait Bracketed: Formattable {
    fn is_bracketed(&self) -> bool;
}

impl Formattable for Vec<Permutation> {
    fn name() -> &'static str {
        "permutations"
    }
    fn permutations(&self, _indent: usize, _settings: &FormatSettings) -> Vec<Permutation> {
        self.clone()
    }
}

impl Formattable for Permutation {
    fn name() -> &'static str {
        "permutation"
    }
    fn permutations(&self, _indent: usize, _settings: &FormatSettings) -> Vec<Permutation> {
        vec![self.clone()]
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
            Term::Ident(ident) => Permutation::only(ident.name, indent),
            Term::Tag(ident) => Permutation::only(format!("#{}", ident.name), indent),
            Term::String(lines) => lines.permutations(indent, settings),
            Term::List(nodes) => Permutation::new().line("[", indent).sep_list(
                indent + 1,
                settings,
                (",", ","),
                nodes,
                |perm, multiline| vec![perm.maybe_append("]", indent, multiline)],
            ),
            Term::Entity { entries, .. } => Permutation::new().line("{", indent).sep_list(
                indent + 1,
                settings,
                (",", ""),
                entries,
                |perm, multiline| vec![perm.maybe_append("}", indent, multiline)],
            ),
            Term::Expr(items) => {
                let open = Permutation::new().line("(", indent);
                if items.len() <= 1 {
                    let oneline = open
                        .clone()
                        .join_with(items[0].permutations(indent, settings), |a, b| {
                            b.is_line().then(|| a.append_perm(b).append_str(")"))
                        });
                    let multiline = open
                        .join_with(items[0].permutations(indent + 1, settings), |a, b| {
                            Some(a.extend(b).line(")", indent))
                        });
                    oneline.into_iter().chain(multiline).collect()
                } else {
                    vec![items
                        .iter()
                        .fold(open, |perm, item| {
                            perm.extend(item.best_permutation(indent + 1, settings))
                        })
                        .line(")", indent)]
                }
            }
            Term::Pattern(pattern) => {
                let mut init = "?";
                if let Pattern::String { pattern, .. } = &**pattern {
                    if pattern.borrow().is_regex {
                        init = "";
                    }
                }
                Permutation::new()
                    .line(init, indent)
                    .join_with(pattern.permutations(indent, settings), |init, body| {
                        Some(init.append_perm(body))
                    })
            }
            Term::Closure(closure) => {
                let params = if closure.params.len() == 1 {
                    closure.params[0]
                        .permutations(indent, settings)
                        .into_iter()
                        .map(|perm| perm.append_str("| "))
                        .collect()
                } else {
                    Permutation::new().line("|", indent).sep_list(
                        indent,
                        settings,
                        (",", ","),
                        &closure.params,
                        |perm, multiline| vec![perm.maybe_append("|", indent, multiline)],
                    )
                };
                Permutation::body(params, &closure.body, indent, settings)
            }
        }
    }
}

impl<'i> Formattable for Entry<'i> {
    fn name() -> &'static str {
        "entry"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Entry::SameName(ident) => Permutation::only(ident.name, indent),
            Entry::Bind(expr) => expr.permutations(indent, settings),
            Entry::Tag(ident) => vec![Permutation::new().line("#", indent).append_str(ident.name)],
            Entry::FunctionDef(def) => def.permutations(indent, settings),
            Entry::Index(left, right) => Permutation::body(
                left.permutations(indent, settings)
                    .into_iter()
                    .map(|perm| perm.append_str(" => ")),
                right,
                indent,
                settings,
            ),
        }
    }
}

impl<'i> Formattable for Vec<StringPart<'i>> {
    fn name() -> &'static str {
        "string"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        let is_format = self
            .iter()
            .any(|part| matches!(part, StringPart::Format(_)));
        let init = if is_format { "$\"" } else { "\"" };
        let string_inner = self.iter().fold(
            vec![Permutation::new().line(init, indent)],
            |perms, part| match part {
                StringPart::Raw(s) => perms.into_iter().map(|perm| perm.append_str(s)).collect(),
                StringPart::Format(node) => perms
                    .into_iter()
                    .flat_map(|perm| {
                        perm.append_str("{").sep_list(
                            indent + 1,
                            settings,
                            ("", ""),
                            from_ref(node),
                            |perm, multiline| vec![perm.maybe_append("}", indent, multiline)],
                        )
                    })
                    .collect(),
            },
        );
        string_inner
            .into_iter()
            .map(|perm| perm.append_str("\""))
            .collect()
    }
}

impl<'i> Formattable for Vec<Vec<StringPart<'i>>> {
    fn name() -> &'static str {
        "string"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        self.iter().fold(vec![Permutation::new()], |perms, parts| {
            Permutation::join(perms, parts.permutations(indent, settings), |a, b| {
                Some(a.extend(b))
            })
        })
    }
}

impl<'i> Formattable for Pattern<'i> {
    fn name() -> &'static str {
        "pattern"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Pattern::Single(ident) | Pattern::Value(ident) => Permutation::only(ident.name, indent),
            Pattern::Builtin { name, .. } => Permutation::only(name, indent),
            Pattern::Bound { left, right, .. } => Permutation::join(
                left.permutations(indent, settings),
                right.permutations(indent, settings),
                |left, right| Some(left.append_str(": ").append_perm(right)),
            ),
            Pattern::Nil(_) => Permutation::only("nil", indent),
            Pattern::Bool { b, .. } => Permutation::only(b, indent),
            Pattern::Int { int, .. } => Permutation::only(int, indent),
            Pattern::String { pattern, .. } => {
                let pattern = pattern.borrow();
                let perm = Permutation::new().line(if pattern.is_regex { "#" } else { "" }, indent);
                perm.join_with(
                    pattern.parts.permutations(indent, settings),
                    |init, body| Some(init.append_perm(body)),
                )
            }
            Pattern::List { patterns, .. } => Permutation::new().line("[", indent).sep_list(
                indent + 1,
                settings,
                (",", ","),
                patterns,
                |perm, multiline| vec![perm.maybe_append("]", indent, multiline)],
            ),
            Pattern::Entity { patterns, .. } => Permutation::new().line("{", indent).sep_list(
                indent + 1,
                settings,
                (",", ""),
                patterns,
                |perm, multiline| vec![perm.maybe_append("}", indent, multiline)],
            ),
        }
    }
}

impl<'i> Bracketed for Pattern<'i> {
    fn is_bracketed(&self) -> bool {
        matches!(self, Pattern::List { .. } | Pattern::Entity { .. })
    }
}

impl<'i> Formattable for FieldPattern<'i> {
    fn name() -> &'static str {
        "field_pattern"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            FieldPattern::SameName(ident) => Permutation::only(ident.name, indent),
            FieldPattern::Pattern { field, pattern, .. } => Permutation::body(
                Some(Permutation::new().line(field.name, indent).append_str(": ")),
                pattern,
                indent,
                settings,
            ),
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
            Node::UnExpr(expr) => {
                let op = match expr.op {
                    UnOp::Neg => "-",
                };
                Permutation::new()
                    .line(op, indent)
                    .join_with(expr.inner.permutations(indent, settings), |a, b| {
                        Some(a.append_perm(b))
                    })
            }
            Node::Call(expr) => expr
                .caller
                .permutations(indent, settings)
                .into_iter()
                .flat_map(|perm| {
                    perm.append_str("(").sep_list(
                        indent + 1,
                        settings,
                        (",", ","),
                        &expr.args,
                        |perm, multiline| vec![perm.maybe_append(")", indent, multiline)],
                    )
                })
                .collect(),
            Node::Bind(expr) => expr.permutations(indent, settings),
            Node::Access(expr) => {
                let root = expr.root.permutations(indent, settings);
                Permutation::body(root, &expr.accessor, indent, settings)
            }
            Node::If(expr) => {
                let condition = Permutation::new().line("if ", indent).join_with(
                    expr.condition.permutations(indent, settings),
                    |init, condition| Some(init.append_perm(condition).append_str(" then ")),
                );
                let condition_and_if_true =
                    Permutation::body(condition, &*expr.if_true, indent, settings);
                let else_and_if_false = Permutation::body(
                    Some(Permutation::new().line("else ", indent)),
                    &*expr.if_false,
                    indent,
                    settings,
                );
                Permutation::join(condition_and_if_true, else_and_if_false, |a, b| {
                    if a.is_line() && b.is_line() {
                        Permutation::new().sep_list(
                            indent,
                            settings,
                            ("", ""),
                            &[a, b],
                            |perm, _| Some(perm),
                        )
                    } else {
                        vec![a.extend(b)]
                    }
                })
            }
            _ => todo!(),
        }
    }
}

impl<'i> Bracketed for Node<'i> {
    fn is_bracketed(&self) -> bool {
        matches!(
            self,
            Node::Term(Term::Expr(_), _) | Node::Term(Term::Entity { .. }, _) | Node::Call(_)
        )
    }
}

impl<'i> Formattable for Accessor<'i> {
    fn name() -> &'static str {
        "accessor"
    }
    fn permutations(&self, indent: usize, _settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Accessor::Key(key) => match key {
                Key::Field(name) => vec![Permutation::new().line(".", indent).append_str(name)],
                key => unreachable!("key {:?} cannot be accessor", key),
            },
        }
    }
}

impl<'i> Bracketed for Accessor<'i> {
    fn is_bracketed(&self) -> bool {
        false
    }
}

impl Formattable for str {
    fn name() -> &'static str {
        "str"
    }
    fn permutations(&self, indent: usize, _settings: &FormatSettings) -> Vec<Permutation> {
        Permutation::only(self, indent)
    }
}

impl Bracketed for str {
    fn is_bracketed(&self) -> bool {
        false
    }
}

impl<'i> Formattable for BindExpr<'i> {
    fn name() -> &'static str {
        "bind"
    }
    fn permutations(&self, indent: usize, settings: &FormatSettings) -> Vec<Permutation> {
        let left = self
            .pattern
            .permutations(indent, settings)
            .into_iter()
            .map(|perm| perm.append_str(" = "));
        Permutation::body(left, &*self.body, indent, settings)
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
            .sep_list(
                indent + 1,
                settings,
                (",", ","),
                &self.params,
                |perm, multiline| vec![perm.maybe_append(") = ", indent, multiline)],
            );
        Permutation::body(left, &self.body, indent, settings)
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
