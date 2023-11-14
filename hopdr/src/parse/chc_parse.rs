use crate::formula::chc::CHCHead;
use crate::formula::{chc, Logic};
use crate::formula::{Bot, Constraint, Ident, Negation, Op, OpKind, PredKind, Top};
use crate::util::Pretty;
use hoice::common::*;
use hoice::instance::Clause;
use hoice::instance::Instance;
use hoice::parse;
use hoice::term::RTerm;
type CHC = chc::CHC<chc::Atom, Constraint>;

fn translate_rterm_top(t: &RTerm) -> Constraint {
    match t {
        RTerm::CArray { .. }
        | RTerm::DTypNew { .. }
        | RTerm::DTypSlc { .. }
        | RTerm::DTypTst { .. }
        | RTerm::Var(_, _) => panic!("program error"),
        RTerm::Cst(c) => match c.get() {
            val::RVal::B(x) if *x => Constraint::mk_true(),
            val::RVal::B(_) => Constraint::mk_false(),
            val::RVal::N(_)
            | val::RVal::I(_)
            | val::RVal::R(_)
            | val::RVal::DTypNew { .. }
            | val::RVal::Array { .. } => panic!("program error"),
        },
        RTerm::App {
            depth,
            typ,
            op,
            args,
        } => match op {
            term::Op::Add
            | term::Op::Sub
            | term::Op::Mul
            | term::Op::CMul
            | term::Op::IDiv
            | term::Op::Div
            | term::Op::Rem
            | term::Op::ToInt
            | term::Op::ToReal
            | term::Op::Store
            | term::Op::Select
            | term::Op::Mod => panic!("program error"),
            term::Op::Gt | term::Op::Ge | term::Op::Le | term::Op::Lt | term::Op::Eql => {
                assert_eq!(args.len(), 2);
                let x = translate_rterm_op(&args[0]);
                let y = translate_rterm_op(&args[1]);
                let p = match op {
                    term::Op::Gt => PredKind::Gt,
                    term::Op::Ge => PredKind::Geq,
                    term::Op::Le => PredKind::Leq,
                    term::Op::Lt => PredKind::Lt,
                    term::Op::Eql => PredKind::Eq,
                    _ => unreachable!(),
                };
                Constraint::mk_bin_pred(p, x, y)
            }
            term::Op::Impl => {
                assert_eq!(args.len(), 2);
                let x = translate_rterm_top(&args[0]);
                let y = translate_rterm_top(&args[1]);
                Constraint::mk_implies(x, y)
            }
            term::Op::Not => {
                assert_eq!(args.len(), 1);
                let x = translate_rterm_top(&args[0]);
                x.negate().unwrap()
            }
            term::Op::And => {
                assert_eq!(args.len(), 2);
                let x = translate_rterm_top(&args[0]);
                let y = translate_rterm_top(&args[1]);
                Constraint::mk_conj(x, y)
            }
            term::Op::Or => {
                assert_eq!(args.len(), 2);
                let x = translate_rterm_top(&args[0]);
                let y = translate_rterm_top(&args[1]);
                Constraint::mk_disj(x, y)
            }
            term::Op::Ite => {
                assert_eq!(args.len(), 3);
                let x = translate_rterm_top(&args[0]);
                let x2 = x.negate().unwrap();
                let y = translate_rterm_top(&args[1]);
                let z = translate_rterm_top(&args[2]);

                let lhs = Constraint::mk_implies(x, y);
                let rhs = Constraint::mk_implies(x2, z);
                Constraint::mk_conj(lhs, rhs)
            }
            term::Op::Distinct => todo!(),
        },
        RTerm::Fun {
            depth,
            typ,
            name,
            args,
        } => todo!(),
    }
}

fn translate_varidx(v: &VarIdx) -> Ident {
    let x = v.get();
    Ident::from(x as u64)
}

fn translate_rterm_op(t: &RTerm) -> Op {
    match t {
        RTerm::Var(ty, y) => {
            assert!(ty.is_int());
            Op::mk_var(translate_varidx(y))
        }
        RTerm::Cst(x) => {
            let v = x.get();
            match v {
                val::RVal::I(x) => {
                    let (_, nums) = x.to_u64_digits();
                    if nums.len() > 1 {
                        panic!("constant is too large");
                    }
                    if nums.len() == 0 {
                        return Op::zero();
                    }
                    let n = nums[0];
                    if x.is_negative() {
                        Op::mk_const(-(n as i64))
                    } else {
                        Op::mk_const(n as i64)
                    }
                }
                val::RVal::R(_)
                | val::RVal::N(_)
                | val::RVal::B(_)
                | val::RVal::DTypNew { .. }
                | val::RVal::Array { .. } => todo!(),
            }
        }
        RTerm::App {
            depth: _,
            typ: _,
            op,
            args,
        } => {
            let op = match op {
                term::Op::Add => OpKind::Add,
                term::Op::Sub => OpKind::Sub,
                term::Op::Mul | term::Op::CMul => OpKind::Mul,
                term::Op::IDiv => OpKind::Div,
                term::Op::Div => todo!(),
                term::Op::Rem => OpKind::Mod,
                term::Op::Mod => todo!(),
                term::Op::Gt
                | term::Op::Ge
                | term::Op::Le
                | term::Op::Lt
                | term::Op::Impl
                | term::Op::Eql
                | term::Op::Not
                | term::Op::And
                | term::Op::Or
                | term::Op::Ite => panic!("program error"),
                term::Op::Distinct => todo!(),
                term::Op::ToInt => todo!(),
                term::Op::ToReal => todo!(),
                term::Op::Store => todo!(),
                term::Op::Select => todo!(),
            };
            assert_eq!(args.len(), 2);
            let x = translate_rterm_op(&args[0]);
            let y = translate_rterm_op(&args[1]);
            Op::mk_bin_op(op, x, y)
        }
        RTerm::DTypNew {
            depth,
            typ,
            name,
            args,
        } => todo!(),
        RTerm::DTypSlc {
            depth,
            typ,
            name,
            term,
        } => todo!(),
        RTerm::DTypTst {
            depth,
            typ,
            name,
            term,
        } => todo!(),
        RTerm::Fun {
            depth,
            typ,
            name,
            args,
        } => {
            panic!("fun?")
        }
        RTerm::CArray { depth, typ, term } => todo!(),
    }
}

fn translate_rterm(t: &RTerm, predicates: &mut Vec<chc::Atom>, c: &mut Constraint) {
    *c = Constraint::mk_conj(c.clone(), translate_rterm_top(t));
}

fn translate_clause(c: &Clause) -> CHC {
    let constraint = c.lhs_terms().iter().fold(Constraint::mk_true(), |c, t| {
        let e = t.get();
        Constraint::mk_conj(c.clone(), translate_rterm_top(t))
    });
    let predicates = c
        .lhs_preds()
        .iter()
        .fold(Vec::new(), |mut predicates, (p, args_h)| {
            args_h.iter().for_each(|a| {
                let args = a.iter().map(|x| translate_rterm_op(x)).collect();
                predicates.push(chc::Atom {
                    predicate: Ident::from(p.get() as u64),
                    args,
                });
            });
            predicates
        });
    let lhs = chc::CHCBody {
        predicates,
        constraint,
    };
    let rhs = match c.rhs() {
        Some((p, args)) => chc::CHCHead::Predicate(chc::Atom {
            predicate: Ident::from(p.get() as u64),
            args: args.iter().map(|x| translate_rterm_op(x)).collect(),
        }),
        None => chc::CHCHead::Constraint(Constraint::mk_false()),
    };
    CHC {
        head: rhs,
        body: lhs,
    }
}

fn translate(instance: &Instance) -> Vec<CHC> {
    let clauses = instance
        .clauses()
        .into_iter()
        .map(|c| translate_clause(c))
        .collect();
    clauses
}

fn parse_file(input: &str) -> Result<Vec<chc::CHC<chc::Atom, Constraint>>, &'static str> {
    println!("wow");
    let mut instance = Instance::new();
    println!("nice");
    let mut cxt = parse::ParserCxt::new();
    println!("hello");
    let res = match cxt
        .parser(input, 0, &hoice::common::Profiler::new())
        .parse(&mut instance)
    {
        Ok(res) => res,
        Err(_) => return Err("parse fail"),
    };
    assert_eq!(res, parse::Parsed::CheckSat);

    Ok(translate(&instance))
}

#[test]
fn test_parse_file() {
    let input = "(set-logic HORN)
(declare-fun mc91 ( Int Int ) Bool)
(assert (forall ((n Int)) (=> (> n 100) (mc91 n (- n 10)))))
(assert (forall ((n Int) (t Int) (r Int))
    (=>
        (and
            (<= n 100)
            (mc91 (+ n 11) t)
            (mc91 t r)
        )
        (mc91 n r)
    )
))
(assert (forall ((n Int) (r Int))
    (=>
        (and
            (<= n 101)
            (not (= r 91))
            (mc91 n r)
        )
        false
    )
))
(check-sat)
    ";
    let chc = parse_file(input).unwrap();
    chc.iter().for_each(|c| {
        println!("{}", c.pretty_display());
    })
}
