use std::fmt::Display;

use crate::formula::*;
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
        allocator.text(match self {
            PredKind::Eq => "=",
            PredKind::Neq => "!=",
            PredKind::Lt => "<",
            PredKind::Leq => "<=",
            PredKind::Gt => ">",
            PredKind::Geq => ">=",
        })
    }
}

impl Pretty for OpKind {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, _config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        allocator.text(match self {
            OpKind::Add => "+",
            OpKind::Sub => "-",
            OpKind::Mul => "*",
            OpKind::Div => "/",
            OpKind::Mod => "%",
        })
    }
}

impl Pretty for QuantifierKind {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, _config: &mut Config) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        allocator.text(match self {
            QuantifierKind::Universal => "∀",
            QuantifierKind::Existential => "∃",
        })
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
                    _ => {
                        let o1 = paren(allocator, config, k.precedence(), o1);
                        let o2 = paren(allocator, config, k.precedence(), o2);
                        o1.append(allocator.space())
                            .append(k.pretty(allocator, config))
                            .append(allocator.space())
                            .append(o2)
                    }
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
                xs.append(allocator.space())
                    .append(allocator.text("→"))
                    .append(allocator.space())
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
                    let o1 = ops[0].pretty(allocator, config);
                    let p = p.pretty(allocator, config);
                    let o2 = ops[1].pretty(allocator, config);
                    return o1
                        .append(allocator.space())
                        .append(p)
                        .append(allocator.space())
                        .append(o2);
                }
                p.pretty(allocator, config).parens().append(
                    allocator
                        .intersperse(ops.iter().map(|o| o.pretty(allocator, config)), ",")
                        .parens(),
                )
            }
            Conj(c1, c2) => {
                let c1 = paren(allocator, config, PrecedenceKind::Conj, c1);
                let c2 = paren(allocator, config, PrecedenceKind::Conj, c2);
                c1.append(allocator.space())
                    .append(allocator.text("∧"))
                    .append(allocator.space())
                    .append(c2)
            }
            Disj(c1, c2) => {
                let c1 = paren(allocator, config, PrecedenceKind::Disj, c1);
                let c2 = paren(allocator, config, PrecedenceKind::Disj, c2);
                c1.append(allocator.space())
                    .append(allocator.text("∨"))
                    .append(allocator.space())
                    .append(c2)
            }
            Quantifier(q, x, c) => {
                let q = q.pretty(allocator, config);
                let x = x.pretty(allocator, config);
                let c = c.pretty(allocator, config);
                q.append(x)
                    .append(allocator.text("."))
                    .append(allocator.space())
                    .append(c)
            }
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
