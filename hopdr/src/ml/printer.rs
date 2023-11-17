/// printing ml code
///
/// Our algorithm highly depends on `ocamlformat` to pretty-print things.
/// We only care about here whether we insert parentheses or not.
use super::syntax::{Expr, ExprKind, Function, Program};
use crate::formula::{Constraint, Ident, Op, OpKind, Precedence, PrecedenceKind, PredKind};
use crate::preprocess::Context;
use crate::solver::util;
use std::fmt;
use std::fmt::Write;
use std::time::Duration;

pub fn do_format(input: &str) -> String {
    // ocamlformat  --impl -
    let args = vec!["--impl", "-"];
    debug!("filename: {}", &args[0]);
    let out = util::exec_input_with_timeout(
        "ocamlformat",
        &args,
        input.as_bytes(),
        Duration::from_secs(1),
    );
    let s = String::from_utf8(out).unwrap();
    debug!("result: {s}");
    s
}

#[test]
fn test_do_format() {
    let s =
        "let rec fold_left f acc xs =match xs with[] -> acc  | x::xs' -> fold_left f (f acc x) xs'";
    let r = "let rec fold_left f acc xs =
  match xs with [] -> acc | x :: xs' -> fold_left f (f acc x) xs'\n";
    let r2 = do_format(s);
    assert_eq!(r, &r2);
}

trait DumpML {
    fn dump_ml<W: Write>(&self, f: &mut W, ctx: &Context) -> Result<(), fmt::Error>;
}

fn paren<W, O>(
    writer: &mut W,
    prec: PrecedenceKind,
    child: &O,
    ctx: &Context,
) -> Result<(), fmt::Error>
where
    W: Write,
    O: Precedence + DumpML,
{
    let child_prec = child.precedence();
    if child_prec == PrecedenceKind::Atom {
        child.dump_ml(writer, ctx)
    } else if child_prec < prec {
        write!(writer, "(")?;
        child.dump_ml(writer, ctx)?;
        write!(writer, ")")
    } else {
        child.dump_ml(writer, ctx)
    }
}

fn dump_bin_op<W, O>(
    writer: &mut W,
    prec: PrecedenceKind,
    op: &str,
    left: &O,
    right: &O,
    ctx: &Context,
) -> Result<(), fmt::Error>
where
    W: Write,
    O: Precedence + DumpML,
{
    paren(writer, prec, left, ctx)?;
    write!(writer, " {} ", op)?;
    paren(writer, prec, right, ctx)
}

impl PredKind {
    fn dump_ml(&self) -> &'static str {
        match self {
            PredKind::Eq => "=",
            PredKind::Neq => "<>",
            PredKind::Lt => "<",
            PredKind::Leq => "<=",
            PredKind::Gt => ">",
            PredKind::Geq => ">=",
        }
    }
}

impl DumpML for Constraint {
    fn dump_ml<W: Write>(&self, f: &mut W, ctx: &Context) -> Result<(), fmt::Error> {
        match self.kind() {
            crate::formula::ConstraintExpr::True => write!(f, "true"),
            crate::formula::ConstraintExpr::False => write!(f, "false"),
            crate::formula::ConstraintExpr::Pred(p, l) if l.len() == 2 => {
                assert_eq!(l.len(), 2);
                dump_bin_op(f, self.precedence(), p.dump_ml(), &l[0], &l[1], ctx)
            }
            crate::formula::ConstraintExpr::Conj(c1, c2) => {
                dump_bin_op(f, self.precedence(), "&&", c1, c2, ctx)
            }
            crate::formula::ConstraintExpr::Disj(c1, c2) => {
                dump_bin_op(f, self.precedence(), "&&", c1, c2, ctx)
            }
            crate::formula::ConstraintExpr::Quantifier(q, x, g) => {
                assert!(q.is_universal());
                assert!(x.ty.is_int());
                write!(f, "(let ")?;
                x.id.dump_ml(f, ctx)?;
                write!(f, " = rand_int() in ")?;
                g.dump_ml(f, ctx)?;
                write!(f, ")")
            }
            _ => panic!(),
        }
    }
}

impl OpKind {
    fn dump_ml(&self) -> String {
        match self {
            OpKind::Add => "+",
            OpKind::Sub => "-",
            OpKind::Mul => "*",
            OpKind::Div => "/",
            OpKind::Mod => "%",
        }
        .to_string()
    }
}

impl DumpML for Op {
    fn dump_ml<W: Write>(&self, f: &mut W, ctx: &Context) -> Result<(), fmt::Error> {
        match self.kind() {
            crate::formula::OpExpr::Op(o, x, y) => {
                let op = o.dump_ml();
                dump_bin_op(f, o.precedence(), &op, x, y, ctx)
            }
            crate::formula::OpExpr::Var(x) => x.dump_ml(f, ctx),
            crate::formula::OpExpr::Const(c) => write!(f, "{}", c),
            crate::formula::OpExpr::Ptr(_, g) => g.dump_ml(f, ctx),
        }
    }
}

impl DumpML for Ident {
    fn dump_ml<W: Write>(&self, writer: &mut W, ctx: &Context) -> Result<(), fmt::Error> {
        match ctx.inverse_map.get(self) {
            Some(v) => write!(writer, "id_{}", v.as_str().to_string().to_lowercase()),
            None => write!(writer, "{}", self),
        }
    }
}

impl DumpML for Expr {
    fn dump_ml<W: Write>(&self, f: &mut W, ctx: &Context) -> Result<(), fmt::Error> {
        match self.kind() {
            ExprKind::Var(x) => x.dump_ml(f, ctx),
            ExprKind::Constraint(c) => c.dump_ml(f, ctx),
            ExprKind::Or(x, y) => dump_bin_op(f, self.precedence(), "||", x, y, ctx),
            ExprKind::App(p1, p2) => {
                paren(f, self.precedence(), p1, ctx)?;
                write!(f, " ")?;
                paren(f, self.precedence(), p2, ctx)
            }
            ExprKind::IApp(x, o) => {
                paren(f, self.precedence(), x, ctx)?;
                write!(f, " ")?;
                paren(f, self.precedence(), o, ctx)
            }
            ExprKind::Fun { ident, body } => {
                write!(f, "fun ")?;
                ident.ident.dump_ml(f, ctx)?;
                write!(f, " -> ")?;
                body.dump_ml(f, ctx)
            }
            ExprKind::If { cond, then, els } => {
                write!(f, "if ")?;
                cond.dump_ml(f, ctx)?;
                write!(f, " then ")?;
                then.dump_ml(f, ctx)?;
                write!(f, " else ")?;
                els.dump_ml(f, ctx)
            }
            ExprKind::LetRand { ident, body } => {
                write!(f, "let ")?;
                ident.dump_ml(f, ctx)?;
                write!(f, " = rand_int() in ")?;
                body.dump_ml(f, ctx)
            }
            ExprKind::Assert(c) => {
                write!(f, "assert ")?;
                c.dump_ml(f, ctx)
            }
            ExprKind::Unit => write!(f, "()"),
            ExprKind::Raise => write!(f, "(raise FalseExc)"),
            ExprKind::TryWith { body, handler } => {
                write!(f, "try ")?;
                body.dump_ml(f, ctx)?;
                write!(f, " with FalseExc -> ")?;
                handler.dump_ml(f, ctx)
            }
            ExprKind::Sequential { lhs, rhs } => {
                lhs.dump_ml(f, ctx)?;
                write!(f, "; ")?;
                rhs.dump_ml(f, ctx)
            }
        }
    }
}

impl DumpML for Function {
    fn dump_ml<W: Write>(&self, f: &mut W, ctx: &Context) -> Result<(), fmt::Error> {
        write!(f, "let rec ")?;
        self.name.dump_ml(f, ctx)?;
        write!(f, " = ")?;
        self.body.dump_ml(f, ctx)?;
        writeln!(f, "")
    }
}

impl<'a> Program<'a> {
    fn dump_main_ml<W: Write>(&self, f: &mut W) -> Result<(), fmt::Error> {
        write!(
            f,
            "let () = for i = 1 to 1000 do (Printf.printf \"epoch %d...\\n\" i; "
        )?;
        self.main.dump_ml(f, &self.ctx)?;
        writeln!(f, ") done")
    }
    fn dump_library_func<W: Write>(&self, f: &mut W) -> Result<(), fmt::Error> {
        writeln!(f, "let rand_int () = Random.int 100 - 50\n")?;
        writeln!(f, "exception FalseExc\n")
    }
    pub fn dump_ml(&self) -> String {
        let mut s = String::new();

        self.dump_library_func(&mut s).unwrap();
        for f in self.functions.iter() {
            f.dump_ml(&mut s, &self.ctx).unwrap();
        }
        self.dump_main_ml(&mut s).unwrap();
        super::printer::do_format(&s)
    }
}
