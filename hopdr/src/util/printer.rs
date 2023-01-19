use std::fmt::Display;

use crate::formula::*;
use crate::pdr::rtype;
use pretty::{BoxAllocator, DocAllocator, DocBuilder};

#[derive(Default)]
pub struct Config {}

impl Config {
    fn get_name_by_ident(&mut self, id: &Ident) -> String {
        format!("x_{}", id.get_id())
    }
}

pub struct PrettyDisplay<'a, A: Pretty>(&'a A, usize);

impl<'a, A: Pretty> Display for PrettyDisplay<'a, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let allocator = BoxAllocator;
        let mut config = Config::default();
        self.0
            .pretty::<_, ()>(&allocator, &mut config)
            .1
            .render_fmt(self.1, f)?;
        // because of lifetime issue, writing this way is somewhat necessary
        // FIXIME: write it beautifully
        Ok(())
    }
}

pub trait Pretty {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone;

    fn pretty_display<'a>(&'a self) -> PrettyDisplay<'a, Self>
    where
        Self: Sized,
    {
        self.pretty_display_with_width(120)
    }

    fn pretty_display_with_width<'a>(&'a self, width: usize) -> PrettyDisplay<'a, Self>
    where
        Self: Sized,
    {
        PrettyDisplay(self, width)
    }
}

impl Pretty for str {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, _config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        allocator.text(self)
    }
}

impl Pretty for Ident {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        // todo: making it more human-readable name
        allocator.text(config.get_name_by_ident(self))
    }
}

impl Pretty for PredKind {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, _config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        allocator.text(self.to_str())
    }
}

impl Pretty for OpKind {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, _config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        allocator.text(self.to_str())
    }
}

impl Pretty for QuantifierKind {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, _config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        allocator.text(self.to_str())
    }
}

fn paren<'b, D, A, O>(
    allocator: &'b D,
    config: &mut Config,
    prec: PrecedenceKind,
    children: &'b O,
) -> DocBuilder<'b, D, A>
where
    D: DocAllocator<'b, A>,
    D::Doc: Clone,
    A: Clone,
    O: Precedence + Pretty,
{
    let child_prec = children.precedence();
    if child_prec == PrecedenceKind::Atom {
        children.pretty(allocator, config)
    } else if child_prec < prec {
        children.pretty(allocator, config).parens()
    } else {
        children.pretty(allocator, config)
    }
}

fn pretty_bin_op<'b, D, A, T>(
    allocator: &'b D,
    config: &mut Config,
    prec: PrecedenceKind,
    op_str: &'b str,
    left: &'b T,
    right: &'b T,
) -> DocBuilder<'b, D, A>
where
    D: DocAllocator<'b, A>,
    D::Doc: Clone,
    A: Clone,
    T: Precedence + Pretty,
{
    let left = paren(allocator, config, prec, left);
    let right = paren(allocator, config, prec, right);
    left.append(allocator.space())
        .append(allocator.text(op_str))
        .append(allocator.space())
        .append(right)
}

fn pretty_abs<'b, D, A, T, V>(
    allocator: &'b D,
    config: &mut Config,
    abs_str: &'b str,
    variable: &'b V,
    content: &'b T,
) -> DocBuilder<'b, D, A>
where
    D: DocAllocator<'b, A>,
    D::Doc: Clone,
    A: Clone,
    T: Pretty,
    V: Pretty,
{
    let q = allocator.text(abs_str);
    let x = variable.pretty(allocator, config);
    let y = content.pretty(allocator, config);
    q.append(x)
        .append(allocator.text("."))
        .append(allocator.softline())
        .append(y)
}

impl Pretty for Op {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        use OpExpr::*;
        match self.kind() {
            Op(k, o1, o2) => {
                // handle (0 - x)
                // (1 + 2) + 3 -> 1 + 2 + 3
                match (*k, o1.kind()) {
                    (OpKind::Sub, OpExpr::Const(0)) => allocator.text("-").append(paren(
                        allocator,
                        config,
                        PrecedenceKind::Atom,
                        o2,
                    )),
                    _ => pretty_bin_op(allocator, config, k.precedence(), &k.to_str(), o1, o2),
                }
            }
            Var(i) => allocator.text(format!("{}", i)),
            Const(c) => allocator.text(format!("{}", c)),
            Ptr(_, o) => o.pretty(allocator, config),
        }
    }
}

#[test]
fn test_pretty_op() {
    let x = Ident::fresh();
    let y = Ident::fresh();
    let o = Op::mk_mul(Op::mk_add(Op::one(), Op::mk_var(x)), Op::mk_var(y));
    assert_eq!(
        format!("{}", o.pretty_display()),
        format!("(1 + {}) * {}", x, y)
    )
}

impl Pretty for Type {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self.kind() {
            TypeKind::Proposition => allocator.text("b"),
            TypeKind::Integer => allocator.text("i"),
            TypeKind::Arrow(x, y) => {
                let xs = x.pretty(allocator, config);
                let ys = y.pretty(allocator, config);
                let xs = if x.order() != 0 { xs.parens() } else { xs };
                xs.append(allocator.softline())
                    .append(allocator.text("→"))
                    .append(allocator.softline())
                    .append(ys)
            }
        }
    }
}

impl Pretty for Variable {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        let x = self.id.pretty(allocator, config);
        let t = self.ty.pretty(allocator, config);
        x.append(allocator.text(": ")).append(t)
    }
}

impl Pretty for Constraint {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        use ConstraintExpr::*;
        match self.kind() {
            True => allocator.text("true"),
            False => allocator.text("false"),
            Pred(p, ops) => {
                if ops.len() == 2 {
                    return pretty_bin_op(
                        allocator,
                        config,
                        self.precedence(),
                        &p.to_str(),
                        &ops[0],
                        &ops[1],
                    );
                }
                p.pretty(allocator, config).parens().append(
                    allocator
                        .intersperse(ops.iter().map(|o| o.pretty(allocator, config)), ",")
                        .parens(),
                )
            }
            Conj(c1, c2) => pretty_bin_op(allocator, config, self.precedence(), "∧", c1, c2),
            Disj(c1, c2) => pretty_bin_op(allocator, config, self.precedence(), "∨", c1, c2),
            Quantifier(q, x, c) => pretty_abs(allocator, config, q.to_str(), x, c),
        }
    }
}

#[test]
fn test_constraint_printer() {
    // ∀x: i. x >= 0 ∧ (x = 0 ∨ ∀z: i. z = 0)
    let x = Ident::fresh();
    let z = Ident::fresh();
    let c1 = Constraint::mk_geq(Op::mk_var(x), Op::zero());
    let c2 = Constraint::mk_eq(Op::mk_var(x), Op::zero());
    let c3 = Constraint::mk_eq(Op::mk_var(z), Op::zero());
    let c4 = Constraint::mk_quantifier_int(QuantifierKind::Universal, z, c3);
    let c5 = Constraint::mk_conj(c1, Constraint::mk_disj(c2, c4));
    let c6 = Constraint::mk_quantifier_int(QuantifierKind::Universal, x, c5);

    let s1 = c6.pretty_display().to_string();
    let s2 = format!("∀{x}: i. {x} >= 0 ∧ ({x} = 0 ∨ ∀{z}: i. {z} = 0)");
    assert_eq!(s1, s2);
}

impl<C: Pretty + Precedence, T> Pretty for hes::GoalBase<C, T> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        use hes::GoalKind::*;
        match self.kind() {
            Constr(c) => c.pretty(allocator, config),
            Op(o) => o.pretty(allocator, config),
            Var(x) => x.pretty(allocator, config),
            App(x, y) => {
                let x = paren(allocator, config, self.precedence(), x);
                let y = paren(allocator, config, self.precedence(), y);
                x.append(allocator.softline()).append(y)
            }
            Conj(x, y) => pretty_bin_op(allocator, config, self.precedence(), "∧", x, y),
            Disj(x, y) => pretty_bin_op(allocator, config, self.precedence(), "∨", x, y),
            Univ(x, y) => pretty_abs(allocator, config, "∀", x, y),
            Abs(x, y) => pretty_abs(allocator, config, "λ", x, y),
        }
    }
}

impl<C: Pretty + Precedence> Pretty for hes::Clause<C> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.body
            .pretty(allocator, config)
            .append(allocator.softline())
            .append(allocator.text("="))
            .append(allocator.softline())
            .append(self.head.pretty(allocator, config))
    }
}

impl<C: Pretty + Precedence> Pretty for hes::Problem<C> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        let toplevel = allocator
            .text("toplevel:")
            .append(allocator.softline())
            .append(self.top.pretty(allocator, config));

        let docs = self.clauses.iter().map(|c| {
            allocator
                .text("-")
                .append(allocator.softline())
                .append(c.pretty(allocator, config))
        });
        let body = allocator.intersperse(docs, allocator.hardline());
        toplevel.append(allocator.hardline()).append(body)
    }
}

fn pretty_predicate<'b, D, A, I, T>(
    allocator: &'b D,
    config: &mut Config,
    ident: &Ident,
    args: I,
) -> DocBuilder<'b, D, A>
where
    D: DocAllocator<'b, A>,
    D::Doc: Clone,
    A: Clone,
    I: IntoIterator<Item = &'b T>,
    T: Pretty + 'b,
{
    allocator.text(format!("P{}", ident.get_id())).append(
        allocator
            .intersperse(args.into_iter().map(|o| o.pretty(allocator, config)), ",")
            .parens(),
    )
}

impl Pretty for fofml::Atom {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        use fofml::AtomKind::*;
        match self.kind() {
            True => allocator.text("true"),
            Constraint(c) => c.pretty(allocator, config),
            Predicate(p, ops) => pretty_predicate(allocator, config, p, ops),
            Conj(x, y) => pretty_bin_op(allocator, config, self.precedence(), "∧", x, y),
            Disj(x, y) => pretty_bin_op(allocator, config, self.precedence(), "∨", x, y),
            Quantifier(q, x, c) => pretty_abs(allocator, config, q.to_str(), x, c),
            Not(c) => {
                let c = paren(allocator, config, self.precedence(), c);
                allocator.text("¬").append(allocator.softline()).append(c)
            }
        }
    }
}

impl Pretty for chc::Atom {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        pretty_predicate(allocator, config, &self.predicate, &self.args)
    }
}

impl<Atom: Pretty, C: Pretty> Pretty for chc::CHCHead<Atom, C> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            chc::CHCHead::Constraint(c) => c.pretty(allocator, config),
            chc::CHCHead::Predicate(a) => a.pretty(allocator, config),
        }
    }
}

impl<Atom: Pretty, C: Pretty + Top> Pretty for chc::CHCBody<Atom, C> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        let docs = if !self.constraint.is_true() {
            Some(self.constraint.pretty(allocator, config))
        } else {
            None
        }
        .into_iter()
        .chain(self.predicates.iter().map(|p| p.pretty(allocator, config)));
        allocator.intersperse(docs, "∧")
    }
}

impl<Atom: Pretty, C: Pretty + Top> Pretty for chc::CHC<Atom, C> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.body
            .pretty(allocator, config)
            .append(allocator.softline())
            .append(allocator.text("->"))
            .append(allocator.softline())
            .append(self.head.pretty(allocator, config))
    }
}

impl Pretty for chc::Model {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        let docs = self.model.iter().map(|(key, (args, assign))| {
            pretty_predicate(allocator, config, key, args)
                .append(allocator.softline())
                .append(allocator.text("=>"))
                .append(allocator.softline())
                .append(assign.pretty(allocator, config))
        });
        allocator.intersperse(docs, allocator.hardline())
    }
}

impl Pretty for pcsp::Atom {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        use pcsp::AtomKind::*;
        match self.kind() {
            True => allocator.text("true"),
            Constraint(c) => c.pretty(allocator, config),
            Predicate(p, ops) => pretty_predicate(allocator, config, p, ops),
            Conj(x, y) => pretty_bin_op(allocator, config, self.precedence(), "∧", x, y),
            Disj(x, y) => pretty_bin_op(allocator, config, self.precedence(), "∨", x, y),
            Quantifier(q, x, c) => pretty_abs(allocator, config, q.to_str(), x, c),
        }
    }
}

impl<Atom: Pretty> Pretty for pcsp::PCSP<Atom> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.body
            .pretty(allocator, config)
            .append(allocator.softline())
            .append(allocator.text("->"))
            .append(allocator.softline())
            .append(self.head.pretty(allocator, config))
    }
}

impl<C: Pretty> Pretty for rtype::Tau<C> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self.kind() {
            rtype::TauKind::Proposition(c) => allocator
                .text("bool[")
                .append(c.pretty(allocator, config))
                .append(allocator.text("]")),
            rtype::TauKind::IArrow(i, t) => i
                .pretty(allocator, config)
                .append(allocator.text(":int"))
                .append(allocator.softline())
                .append(allocator.text("->"))
                .append(allocator.softline())
                .append(t.pretty(allocator, config).nest(2)),
            rtype::TauKind::Arrow(ts, t) => {
                let docs = ts.iter().map(|t| {
                    let tdoc = t.pretty(allocator, config);
                    if t.order() == 0 {
                        tdoc
                    } else {
                        tdoc.parens()
                    }
                });
                let arg = allocator.intersperse(docs, "/\\");
                arg.append(allocator.softline())
                    .append(allocator.text("->"))
                    .append(allocator.softline())
                    .append(t.pretty(allocator, config).nest(2))
            }
        }
    }
}
impl<T: Pretty> Pretty for rtype::PolymorphicType<T> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.vars
            .iter()
            .fold(allocator.nil(), |cur, var| {
                cur.append(allocator.text("∀"))
                    .append(var.pretty(allocator, config))
                    .append(allocator.text("."))
                    .append(allocator.softline())
            })
            .append(self.ty.pretty(allocator, config))
    }
}

impl<T: Pretty> Pretty for rtype::TypeEnvironment<T> {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        let docs = self.map.iter().map(|(id, ts)| {
            let var = id.pretty(allocator, config);
            let docs = ts.iter().map(|t| t.pretty(allocator, config));
            let t = allocator.intersperse(docs, allocator.hardline().append("/\\ "));
            var.append(allocator.text(" : ")).append(t.nest(4))
        });
        allocator.intersperse(docs, allocator.hardline())
    }
}
