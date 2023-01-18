use std::fmt::Display;

use crate::formula::*;
use pretty::*;
use pretty::{BoxAllocator, DocAllocator, DocBuilder};

#[derive(Default)]
pub struct Config {}

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

impl Pretty for PredKind {
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
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
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
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
    fn pretty<'b, D, A>(&'b self, allocator: &'b D, config: &mut Config) -> DocBuilder<'b, D, A>
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

impl Op {
    fn paren<'b, D, A>(
        &'b self,
        allocator: &'b D,
        config: &mut Config,
        prec: Precedence,
        children: &'b Op,
    ) -> DocBuilder<'b, D, A>
    where
        D: DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        let child_prec = children.precedence();
        if child_prec == Precedence::Atom {
            children.pretty(allocator, config)
        } else if child_prec < prec {
            children.pretty(allocator, config).parens()
        } else {
            children.pretty(allocator, config)
        }
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
                    (OpKind::Sub, OpExpr::Const(0)) => allocator.text("-").append(self.paren(
                        allocator,
                        config,
                        Precedence::Atom,
                        o2,
                    )),
                    _ => {
                        let o1 = self.paren(allocator, config, k.precedence(), o1);
                        let o2 = self.paren(allocator, config, k.precedence(), o2);
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
