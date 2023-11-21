use crate::formula::chc::CHCHead;
use crate::formula::{chc, Logic};
use crate::formula::{Bot, Constraint, Ident, Negation, Op, OpKind, PredKind, Top};
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
        RTerm::App { op, args, .. } => match op {
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
        RTerm::Fun { .. } => todo!(),
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
                term::Op::Ite => {
                    assert_eq!(args.len(), 3);
                    let c = translate_rterm_top(&args[0]);
                    let x = translate_rterm_op(&args[1]);
                    let y = translate_rterm_op(&args[2]);
                    return Op::mk_ite(c, x, y);
                }
                term::Op::Gt
                | term::Op::Ge
                | term::Op::Le
                | term::Op::Lt
                | term::Op::Impl
                | term::Op::Eql
                | term::Op::Not
                | term::Op::And
                | term::Op::Or => unimplemented!(),
                term::Op::Distinct => todo!(),
                term::Op::ToInt => todo!(),
                term::Op::ToReal => todo!(),
                term::Op::Store => todo!(),
                term::Op::Select => todo!(),
            };
            assert!(args.len() >= 2);

            if args.len() != 2 {
                assert!(op == OpKind::Add || op == OpKind::Mul);
            }
            let x = translate_rterm_op(&args[0]);
            let y = translate_rterm_op(&args[1]);
            let mut o = Op::mk_bin_op(op, x, y);
            for z in args.iter().skip(2) {
                let z = translate_rterm_op(z);
                o = Op::mk_bin_op(op, o, z);
            }
            o
        }
        RTerm::DTypNew { .. } => todo!(),
        RTerm::DTypSlc { .. } => todo!(),
        RTerm::DTypTst { .. } => todo!(),
        RTerm::Fun { .. } => {
            panic!("fun?")
        }
        RTerm::CArray { .. } => todo!(),
    }
}

fn translate_clause(c: &Clause) -> CHC {
    let constraint = c.lhs_terms().iter().fold(Constraint::mk_true(), |c, t| {
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

fn rename_op(o: &Op, varmap: &mut HashMap<Ident, Ident>) -> Op {
    match o.kind() {
        crate::formula::OpExpr::Op(o, x, y) => {
            Op::mk_bin_op(*o, rename_op(x, varmap), rename_op(y, varmap))
        }
        crate::formula::OpExpr::Var(v) => match varmap.get(v) {
            Some(i) => Op::mk_var(i.clone()),
            None => {
                let i = Ident::fresh();
                varmap.insert(v.clone(), i.clone());
                Op::mk_var(i)
            }
        },
        crate::formula::OpExpr::Const(x) => Op::mk_const(*x),
        crate::formula::OpExpr::ITE(c, x, y) => Op::mk_ite(
            rename_constraint(c, varmap),
            rename_op(x, varmap),
            rename_op(y, varmap),
        ),
        crate::formula::OpExpr::Ptr(_, _) => panic!("program error"),
    }
}

fn rename_constraint(c: &Constraint, varmap: &mut HashMap<Ident, Ident>) -> Constraint {
    match c.kind() {
        crate::formula::ConstraintExpr::True | crate::formula::ConstraintExpr::False => c.clone(),
        crate::formula::ConstraintExpr::Pred(p, l) => {
            Constraint::mk_pred(*p, l.iter().map(|x| rename_op(x, varmap)).collect())
        }
        crate::formula::ConstraintExpr::Conj(x, y) => {
            Constraint::mk_conj(rename_constraint(x, varmap), rename_constraint(y, varmap))
        }
        crate::formula::ConstraintExpr::Disj(x, y) => {
            Constraint::mk_disj(rename_constraint(x, varmap), rename_constraint(y, varmap))
        }
        crate::formula::ConstraintExpr::Quantifier(q, x, c) => {
            Constraint::mk_quantifier(*q, x.clone(), rename_constraint(c, varmap))
        }
    }
}

fn rename_clause(c: CHC, pred_map: &mut HashMap<Ident, Ident>) -> CHC {
    let mut arg_map = HashMap::new();
    let head = match c.head {
        CHCHead::Constraint(c) => CHCHead::Constraint(rename_constraint(&c, &mut arg_map)),
        CHCHead::Predicate(p) => match pred_map.get(&p.predicate) {
            Some(i) => CHCHead::Predicate(chc::Atom {
                predicate: i.clone(),
                args: p.args.iter().map(|x| rename_op(x, &mut arg_map)).collect(),
            }),
            None => {
                let i = Ident::fresh();
                pred_map.insert(p.predicate, i.clone());
                CHCHead::Predicate(chc::Atom {
                    predicate: i,
                    args: p.args.iter().map(|x| rename_op(x, &mut arg_map)).collect(),
                })
            }
        },
    };
    let predicates = c
        .body
        .predicates
        .iter()
        .map(|p| chc::Atom {
            predicate: match pred_map.get(&p.predicate) {
                Some(i) => i.clone(),
                None => {
                    let i = Ident::fresh();
                    pred_map.insert(p.predicate, i.clone());
                    i
                }
            },
            args: p.args.iter().map(|x| rename_op(x, &mut arg_map)).collect(),
        })
        .collect();
    let constraint = rename_constraint(&c.body.constraint, &mut arg_map);
    let body = chc::CHCBody {
        predicates,
        constraint,
    };
    CHC { head, body }
}

fn translate(instance: &Instance, var_map: &mut HashMap<Ident, Ident>) -> Vec<CHC> {
    let clauses = instance
        .clauses()
        .into_iter()
        .map(|c| rename_clause(translate_clause(c), var_map))
        .collect();
    clauses
}

pub fn parse_chc(input: &str) -> Result<Vec<chc::CHC<chc::Atom, Constraint>>, &'static str> {
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
    let mut var_map = HashMap::new();
    Ok(translate(&instance, &mut var_map))
}

pub fn get_mc91() -> Vec<chc::CHC<chc::Atom, Constraint>> {
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
    parse_chc(input).unwrap()
}

#[test]
fn test_parse_file() {
    use crate::util::Pretty;
    let chc = get_mc91();
    chc.iter().for_each(|c| {
        println!("{}", c.pretty_display());
    })
}
