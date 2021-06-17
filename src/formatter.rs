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

        let Permutation(lines) = items.best_permutation(
            FormatState {
                indent: 0,
                chain_access: false,
            },
            self,
        );

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

#[derive(Clone, Copy)]
struct FormatState {
    indent: usize,
    chain_access: bool,
}

impl FormatState {
    fn indent(self, by: usize) -> Self {
        FormatState {
            indent: self.indent + by,
            ..self
        }
    }
    fn chain_access(self) -> Self {
        FormatState {
            chain_access: true,
            ..self
        }
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
    fn append_within(self, other: Self, max_width: usize) -> Self {
        if self.appended_max_width(&other) <= max_width {
            self.append_perm(other)
        } else {
            self.extend(other)
        }
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
    fn appended_max_width(&self, other: &Self) -> usize {
        if let Some((a, b)) = self.0.last().zip(other.0.first()) {
            self.max_width()
                .max(other.max_width())
                .max(a.indent * 4 + a.string.len() + b.string.len())
        } else {
            panic!("empty permutation")
        }
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
        state: FormatState,
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
            single = single.append_perm(item.best_permutation(state, settings));
        }
        let mut multi = self;
        for item in items {
            multi = multi
                .extend(item.best_permutation(state, settings))
                .append_str(multisep);
        }
        tail(single, false)
            .into_iter()
            .chain(tail(multi, true))
            .collect()
    }
    fn body<L, R>(
        left: L,
        right: &R,
        state: FormatState,
        settings: &FormatSettings,
    ) -> Vec<Permutation>
    where
        L: IntoIterator<Item = Self> + Clone,
        R: Bracketed + ?Sized,
    {
        let bracketed = right.is_bracketed();
        let oneline = Permutation::join(
            left.clone(),
            right.permutations(state, settings),
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
            right.permutations(state.indent(1), settings),
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
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation>;
    fn best_permutation(&self, state: FormatState, settings: &FormatSettings) -> Permutation {
        let perms = self.permutations(state, settings);
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
    fn permutations(&self, _state: FormatState, _settings: &FormatSettings) -> Vec<Permutation> {
        self.clone()
    }
}

impl Formattable for Permutation {
    fn permutations(&self, _state: FormatState, _settings: &FormatSettings) -> Vec<Permutation> {
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
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        (&**self).permutations(state, settings)
    }
}

impl<'i> Formattable for Term<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Term::Nil => Permutation::only("nil", state.indent),
            Term::Bool(b) => Permutation::only(b, state.indent),
            Term::Int(i) => Permutation::only(i, state.indent),
            Term::Real(r) => Permutation::only(r, state.indent),
            Term::Ident(ident) => Permutation::only(ident.name, state.indent),
            Term::Tag(ident) => Permutation::only(format!("#{}", ident.name), state.indent),
            Term::String(lines) => lines.permutations(state, settings),
            Term::List(nodes) => Permutation::new().line("[", state.indent).sep_list(
                state.indent(1),
                settings,
                (",", ","),
                nodes,
                |perm, multiline| vec![perm.maybe_append("]", state.indent, multiline)],
            ),
            Term::Entity { entries, .. } => Permutation::new().line("{", state.indent).sep_list(
                state.indent(1),
                settings,
                (",", ""),
                entries,
                |perm, multiline| vec![perm.maybe_append("}", state.indent, multiline)],
            ),
            Term::Expr(items) => {
                let open = Permutation::new().line("(", state.indent);
                if items.len() <= 1 {
                    let oneline = open
                        .clone()
                        .join_with(items[0].permutations(state, settings), |a, b| {
                            b.is_line().then(|| a.append_perm(b).append_str(")"))
                        });
                    let multiline = open
                        .join_with(items[0].permutations(state.indent(1), settings), |a, b| {
                            Some(a.extend(b).line(")", state.indent))
                        });
                    oneline.into_iter().chain(multiline).collect()
                } else {
                    vec![items
                        .iter()
                        .fold(open, |perm, item| {
                            perm.extend(item.best_permutation(state.indent(1), settings))
                        })
                        .line(")", state.indent)]
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
                    .line(init, state.indent)
                    .join_with(pattern.permutations(state, settings), |init, body| {
                        Some(init.append_perm(body))
                    })
            }
            Term::Closure(closure) => {
                let params = if closure.params.len() == 1 {
                    closure.params[0]
                        .permutations(state, settings)
                        .into_iter()
                        .map(|perm| perm.append_str("| "))
                        .collect()
                } else {
                    Permutation::new().line("|", state.indent).sep_list(
                        state,
                        settings,
                        (",", ","),
                        &closure.params,
                        |perm, multiline| vec![perm.maybe_append("|", state.indent, multiline)],
                    )
                };
                Permutation::body(params, &closure.body, state, settings)
            }
        }
    }
}

impl<'i> Formattable for Entry<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Entry::SameName(ident) => Permutation::only(ident.name, state.indent),
            Entry::Bind(expr) => expr.permutations(state, settings),
            Entry::Tag(ident) => vec![Permutation::new()
                .line("#", state.indent)
                .append_str(ident.name)],
            Entry::FunctionDef(def) => def.permutations(state, settings),
            Entry::Index(left, right) => Permutation::body(
                left.permutations(state, settings)
                    .into_iter()
                    .map(|perm| perm.append_str(" => ")),
                right,
                state,
                settings,
            ),
        }
    }
}

impl<'i> Formattable for Vec<StringPart<'i>> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        let is_format = self
            .iter()
            .any(|part| matches!(part, StringPart::Format(_)));
        let init = if is_format { "$\"" } else { "\"" };
        let string_inner = self.iter().fold(
            vec![Permutation::new().line(init, state.indent)],
            |perms, part| match part {
                StringPart::Raw(s) => perms.into_iter().map(|perm| perm.append_str(s)).collect(),
                StringPart::Format(node) => perms
                    .into_iter()
                    .flat_map(|perm| {
                        perm.append_str("{").sep_list(
                            state.indent(1),
                            settings,
                            ("", ""),
                            from_ref(node),
                            |perm, multiline| vec![perm.maybe_append("}", state.indent, multiline)],
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
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        self.iter().fold(vec![Permutation::new()], |perms, parts| {
            Permutation::join(perms, parts.permutations(state, settings), |a, b| {
                Some(a.extend(b))
            })
        })
    }
}

impl<'i> Formattable for Pattern<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Pattern::Single(ident) | Pattern::Value(ident) => {
                Permutation::only(ident.name, state.indent)
            }
            Pattern::Builtin { name, .. } => Permutation::only(name, state.indent),
            Pattern::Bound { left, right, .. } => Permutation::join(
                left.permutations(state, settings),
                right.permutations(state, settings),
                |left, right| Some(left.append_str(": ").append_perm(right)),
            ),
            Pattern::Nil(_) => Permutation::only("nil", state.indent),
            Pattern::Bool { b, .. } => Permutation::only(b, state.indent),
            Pattern::Int { int, .. } => Permutation::only(int, state.indent),
            Pattern::String { pattern, .. } => {
                let pattern = pattern.borrow();
                let perm =
                    Permutation::new().line(if pattern.is_regex { "#" } else { "" }, state.indent);
                perm.join_with(pattern.parts.permutations(state, settings), |init, body| {
                    Some(init.append_perm(body))
                })
            }
            Pattern::List { patterns, .. } => Permutation::new().line("[", state.indent).sep_list(
                state.indent(1),
                settings,
                (",", ","),
                patterns,
                |perm, multiline| vec![perm.maybe_append("]", state.indent, multiline)],
            ),
            Pattern::Entity { patterns, .. } => {
                Permutation::new().line("{", state.indent).sep_list(
                    state.indent(1),
                    settings,
                    (",", ""),
                    patterns,
                    |perm, multiline| vec![perm.maybe_append("}", state.indent, multiline)],
                )
            }
        }
    }
}

impl<'i> Bracketed for Pattern<'i> {
    fn is_bracketed(&self) -> bool {
        matches!(self, Pattern::List { .. } | Pattern::Entity { .. })
    }
}

impl<'i> Formattable for FieldPattern<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            FieldPattern::SameName(ident) => Permutation::only(ident.name, state.indent),
            FieldPattern::Pattern { field, pattern, .. } => Permutation::body(
                Some(
                    Permutation::new()
                        .line(field.name, state.indent)
                        .append_str(": "),
                ),
                pattern,
                state,
                settings,
            ),
        }
    }
}

impl<'i> Formattable for Node<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Node::Term(term, ..) => term.permutations(state, settings),
            Node::BinExpr(expr) => Permutation::join(
                expr.left.permutations(state, settings),
                expr.right.permutations(state, settings),
                |left, right| {
                    let op = expr.op_span.as_str().trim();
                    vec![
                        left.clone()
                            .append_str(format!(" {} ", op))
                            .append_perm(right.clone()),
                        left.line(format!("{} ", op), state.indent + 1)
                            .append_perm(right),
                    ]
                },
            ),
            Node::UnExpr(expr) => {
                let op = match expr.op {
                    UnOp::Neg => "-",
                };
                Permutation::new()
                    .line(op, state.indent)
                    .join_with(expr.inner.permutations(state, settings), |a, b| {
                        Some(a.append_perm(b))
                    })
            }
            Node::Call(expr) => expr
                .caller
                .permutations(state, settings)
                .into_iter()
                .flat_map(|perm| {
                    perm.append_str("(").sep_list(
                        state.indent(1),
                        settings,
                        (",", ","),
                        &expr.args,
                        |perm, multiline| vec![perm.maybe_append(")", state.indent, multiline)],
                    )
                })
                .collect(),
            Node::Bind(expr) => expr.permutations(state, settings),
            Node::Access(expr) => {
                let root = expr.root.best_permutation(state, settings);
                let access = expr.accessor.best_permutation(state.indent(1), settings);
                let appended = root.clone().append_perm(access.clone());
                let chain_access = state.chain_access
                    || expr.root.is_access_chain(5)
                    || appended.is_line()
                        && appended.max_width() > settings.max_width
                        && expr.root.is_access_chain(3)
                    || !appended.is_line();
                vec![if chain_access {
                    expr.root
                        .best_permutation(state.chain_access(), settings)
                        .extend(
                            expr.accessor
                                .best_permutation(state.indent(1).chain_access(), settings),
                        )
                } else {
                    root.append_within(access, settings.max_width)
                }]
            }
            Node::If(expr) => {
                let condition = Permutation::new()
                    .line("if ", state.indent)
                    .join_with(
                        expr.condition.permutations(state, settings),
                        |init, condition| Some(init.append_perm(condition).append_str(" then ")),
                    )
                    .best_permutation(state, settings);
                let condition_and_if_true =
                    Permutation::body(Some(condition), &*expr.if_true, state, settings)
                        .best_permutation(state, settings);
                let else_and_if_false = Permutation::body(
                    Some(Permutation::new().line(" else ", state.indent)),
                    &*expr.if_false,
                    state,
                    settings,
                )
                .best_permutation(state, settings);
                vec![condition_and_if_true.append_within(else_and_if_false, settings.max_width)]
            }
            Node::Match(expr) => {
                let matched = Permutation::new()
                    .line("match ", state.indent)
                    .append_perm(expr.matched.best_permutation(state, settings));
                vec![expr.cases.iter().fold(matched, |prev, case| {
                    prev.extend(
                        Permutation::body(
                            case.pattern
                                .permutations(state.indent(1), settings)
                                .into_iter()
                                .map(|perm| perm.append_str(" => ")),
                            &case.body,
                            state.indent(1),
                            settings,
                        )
                        .best_permutation(state, settings),
                    )
                })]
            }
        }
    }
}

impl<'i> Bracketed for Node<'i> {
    fn is_bracketed(&self) -> bool {
        match self {
            Node::Term(Term::Expr(_) | Term::Entity { .. }, _) => true,
            Node::Call(expr) => expr.args.len() > 1,
            Node::Access(_) => true,
            _ => false,
        }
    }
}

impl<'i> Node<'i> {
    fn is_access_chain(&self, depth: usize) -> bool {
        if depth == 0 {
            return true;
        }
        match self {
            Node::Access(expr) => expr.root.is_access_chain(depth - 1),
            Node::Call(expr) => expr.caller.is_access_chain(depth),
            _ => false,
        }
    }
}

impl<'i> Formattable for Accessor<'i> {
    fn permutations(&self, state: FormatState, _settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Accessor::Key(key) => match key {
                Key::Field(name) => {
                    vec![Permutation::new().line(".", state.indent).append_str(name)]
                }
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
    fn permutations(&self, state: FormatState, _settings: &FormatSettings) -> Vec<Permutation> {
        Permutation::only(self, state.indent)
    }
}

impl Bracketed for str {
    fn is_bracketed(&self) -> bool {
        false
    }
}

impl<'i> Formattable for BindExpr<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        let left = self
            .pattern
            .permutations(state, settings)
            .into_iter()
            .map(|perm| perm.append_str(" = "));
        Permutation::body(left, &*self.body, state, settings)
    }
}

impl<'i> Formattable for FunctionDef<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        let left = Permutation::new()
            .line(self.ident.name, state.indent)
            .append_str("(")
            .sep_list(
                state.indent(1),
                settings,
                (",", ","),
                &self.params,
                |perm, multiline| vec![perm.maybe_append(") = ", state.indent, multiline)],
            );
        Permutation::body(left, &self.body, state, settings)
    }
}

impl<'i> Formattable for Item<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        match self {
            Item::Node(node) => node.permutations(state, settings),
            Item::FunctionDef(def) => def.permutations(state, settings),
        }
    }
}

impl<'i> Formattable for Items<'i> {
    fn permutations(&self, state: FormatState, settings: &FormatSettings) -> Vec<Permutation> {
        vec![self.iter().fold(Permutation::new(), |perm, item| {
            perm.extend(item.best_permutation(state, settings))
        })]
    }
}
