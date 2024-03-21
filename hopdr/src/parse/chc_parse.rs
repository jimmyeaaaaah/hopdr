use crate::formula::chc::CHCHead;
use crate::formula::{chc, Logic};
use crate::formula::{Bot, Constraint, Ident, Negation, Op, OpKind, PredKind, Top, Type, Variable};
use crate::util::info::{Variable as Info, VariableMap};
use hoice::common::*;
use hoice::instance::Clause;
use hoice::instance::Instance;
use hoice::parse;
use hoice::preproc;
use hoice::term::RTerm;

type CHC = chc::CHC<chc::Atom, Constraint>;
type ExtendedCHC = chc::ExtendedCHC<chc::Atom, Constraint>;

// during parsing, we encode boolean as integer (1 or 0).

fn handle_atomic_predicate<'a>(
    op: &term::Op,
    mut args: impl Iterator<Item = &'a RTerm> + 'a,
    vmap: &mut VariableMap,
    instance: &Instance,
) -> Constraint {
    match op {
        term::Op::Gt | term::Op::Ge | term::Op::Le | term::Op::Lt | term::Op::Eql => {
            let x = translate_rterm_op(args.next().unwrap(), vmap, instance);
            let y = translate_rterm_op(args.next().unwrap(), vmap, instance);
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
        _ => panic!("program error"),
    }
}

fn bool_variable_encoding(id: Ident) -> Constraint {
    Constraint::mk_eq(Op::mk_var(id), Op::mk_const(1))
}

fn translate_rterm_top(t: &RTerm, vmap: &mut VariableMap, instance: &Instance) -> Constraint {
    match t {
        RTerm::CArray { .. }
        | RTerm::DTypNew { .. }
        | RTerm::DTypSlc { .. }
        | RTerm::DTypTst { .. } => panic!("program error"),
        RTerm::Var(ty, x) => {
            assert!(ty.is_bool());
            bool_variable_encoding(transform_varidx(*x, vmap, instance))
        }
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
                handle_atomic_predicate(op, args.iter().map(|x| &**x), vmap, instance)
            }
            term::Op::Impl => {
                assert_eq!(args.len(), 2);
                let x = translate_rterm_top(&args[0], vmap, instance);
                let y = translate_rterm_top(&args[1], vmap, instance);
                Constraint::mk_implies(x, y)
            }
            term::Op::Not => {
                assert_eq!(args.len(), 1);
                let x = translate_rterm_top(&args[0], vmap, instance);
                x.negate().unwrap()
            }
            term::Op::And => {
                assert!(args.len() >= 2);
                let x = translate_rterm_top(&args[0], vmap, instance);
                let y = translate_rterm_top(&args[1], vmap, instance);
                let mut c = Constraint::mk_conj(x, y);
                for z in args.iter().skip(2) {
                    let z = translate_rterm_top(z, vmap, instance);
                    c = Constraint::mk_conj(c, z);
                }
                c
            }
            term::Op::Or => {
                assert!(args.len() >= 2);
                let x = translate_rterm_top(&args[0], vmap, instance);
                let y = translate_rterm_top(&args[1], vmap, instance);
                let mut c = Constraint::mk_disj(x, y);
                for z in args.iter().skip(2) {
                    let z = translate_rterm_top(z, vmap, instance);
                    c = Constraint::mk_disj(c, z);
                }
                c
            }
            term::Op::Ite => {
                assert_eq!(args.len(), 3);
                let x = translate_rterm_top(&args[0], vmap, instance);
                let x2 = x.negate().unwrap();
                let y = translate_rterm_top(&args[1], vmap, instance);
                let z = translate_rterm_top(&args[2], vmap, instance);

                let lhs = Constraint::mk_implies(x, y);
                let rhs = Constraint::mk_implies(x2, z);
                Constraint::mk_conj(lhs, rhs)
            }
            term::Op::Distinct => todo!(),
        },
        RTerm::Fun { .. } => todo!(),
    }
}

fn decode_op2constr(x: Op) -> Constraint {
    match x.kind() {
        crate::formula::OpExpr::Var(x) => bool_variable_encoding(*x),
        crate::formula::OpExpr::ITE(c, x, y)
            if x.eval_with_empty_env() == Some(1) && y.eval_with_empty_env() == Some(0) =>
        {
            c.clone()
        }
        _ => panic!("program error"),
    }
}
fn encode_constr2op(c: Constraint) -> Op {
    Op::mk_ite(c, Op::one(), Op::zero())
}
fn handle_bin_bool_op(x: Op, y: Op, f: impl Fn(Constraint, Constraint) -> Constraint) -> Op {
    let c1 = decode_op2constr(x);
    let c2 = decode_op2constr(y);
    let c = f(c1, c2);
    encode_constr2op(c)
}

fn transform_varidx(p: VarIdx, _vmap: &mut VariableMap, _instance: &Instance) -> Ident {
    let id = Ident::from(p.get() as u64);
    id
}

fn translate_rterm_op(t: &RTerm, vmap: &mut VariableMap, instance: &Instance) -> Op {
    match t {
        RTerm::Var(ty, y) => {
            if ty.is_int() || ty.is_bool() {
                Op::mk_var(transform_varidx(*y, vmap, instance))
            } else {
                panic!("program error")
            }
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
                val::RVal::B(x) if *x => Op::mk_const(1),
                val::RVal::B(_) => Op::mk_const(0),
                val::RVal::R(_)
                | val::RVal::N(_)
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
                term::Op::Mod => OpKind::Mod,
                term::Op::Ite => {
                    assert_eq!(args.len(), 3);
                    let c = translate_rterm_top(&args[0], vmap, instance);
                    let x = translate_rterm_op(&args[1], vmap, instance);
                    let y = translate_rterm_op(&args[2], vmap, instance);
                    return Op::mk_ite(c, x, y);
                }
                term::Op::Gt | term::Op::Ge | term::Op::Le | term::Op::Lt | term::Op::Eql => {
                    let c = handle_atomic_predicate(op, args.iter().map(|x| &**x), vmap, instance);
                    return encode_constr2op(c);
                }
                term::Op::And => {
                    assert!(args.len() >= 2);
                    let mut c = translate_rterm_op(&args[0], vmap, instance);
                    for z in args.iter().skip(1) {
                        let z: crate::formula::P<crate::formula::OpExpr> =
                            translate_rterm_op(z, vmap, instance);
                        c = handle_bin_bool_op(c, z, Constraint::mk_conj)
                    }
                    return c;
                }
                term::Op::Or => {
                    assert!(args.len() >= 2);
                    let mut c = translate_rterm_op(&args[0], vmap, instance);
                    for z in args.iter().skip(1) {
                        let z: crate::formula::P<crate::formula::OpExpr> =
                            translate_rterm_op(z, vmap, instance);
                        c = handle_bin_bool_op(c, z, Constraint::mk_disj)
                    }
                    return c;
                }
                term::Op::Not => {
                    assert_eq!(args.len(), 1);
                    let o = translate_rterm_op(&args[0], vmap, instance);
                    let c = decode_op2constr(o);
                    return encode_constr2op(c.negate().unwrap());
                }
                term::Op::Impl => {
                    assert_eq!(args.len(), 2);
                    let x = translate_rterm_op(&args[0], vmap, instance);
                    let y = translate_rterm_op(&args[1], vmap, instance);
                    return handle_bin_bool_op(x, y, Constraint::mk_implies);
                }
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
            let x = translate_rterm_op(&args[0], vmap, instance);
            let y = translate_rterm_op(&args[1], vmap, instance);
            let mut o = Op::mk_bin_op(op, x, y);
            for z in args.iter().skip(2) {
                let z = translate_rterm_op(z, vmap, instance);
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

fn register_and_transform_prdidx(p: PrdIdx, vmap: &mut VariableMap, instance: &Instance) -> Ident {
    let id: Ident = Ident::from(p.get() as u64);
    let info = Info::new(id, instance[p].name.clone());
    vmap.insert(id, info);
    id
}

fn translate_clause(c: &Clause, vmap: &mut VariableMap, instance: &Instance) -> ExtendedCHC {
    let constraint = c.lhs_terms().iter().fold(Constraint::mk_true(), |c, t| {
        Constraint::mk_conj(c.clone(), translate_rterm_top(t, vmap, instance))
    });

    let predicates = c
        .lhs_preds()
        .iter()
        .fold(Vec::new(), |mut predicates, (p, args_h)| {
            args_h.iter().for_each(|a| {
                let args = a
                    .iter()
                    .map(|x| translate_rterm_op(x, vmap, instance))
                    .collect();
                let id = register_and_transform_prdidx(*p, vmap, instance);
                predicates.push(chc::Atom {
                    predicate: id,
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
            predicate: register_and_transform_prdidx(p, vmap, instance),
            args: args
                .iter()
                .map(|x| translate_rterm_op(x, vmap, instance))
                .collect(),
        }),
        None => chc::CHCHead::Constraint(Constraint::mk_false()),
    };
    let chc = CHC {
        head: rhs,
        body: lhs,
    };

    let free_variables = c
        .vars()
        .iter()
        .map(|v| {
            let id = Ident::from(v.idx.get() as u64);
            let ty = if v.typ.is_int() {
                Type::mk_type_int()
            } else if v.typ.is_bool() {
                Type::mk_type_bit()
            } else {
                panic!("unknown type")
            };
            Variable::mk(id, ty)
        })
        .collect();
    ExtendedCHC {
        free_variables,
        chc,
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

fn rename_clause(
    c: ExtendedCHC,
    pred_map: &mut HashMap<Ident, Ident>,
    variable_map: &mut VariableMap,
    original_clause: &Clause,
) -> ExtendedCHC {
    let mut arg_map = HashMap::new();
    let new_variables: Vec<_> = c
        .free_variables
        .iter()
        .map(|x| Variable::mk(Ident::fresh(), x.ty.clone()))
        .collect();
    for (old, new) in c.free_variables.iter().zip(new_variables.iter()) {
        arg_map.insert(old.id, new.id);
    }
    let head = match c.chc.head {
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
        .chc
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
    let constraint = rename_constraint(&c.chc.body.constraint, &mut arg_map);
    let body = chc::CHCBody {
        predicates,
        constraint,
    };
    let chc = CHC { head, body };

    original_clause.vars().iter().for_each(|x| {
        let id = Ident::from(x.idx.get() as u64);
        match arg_map.get(&id) {
            Some(i) => {
                let name = x.name.clone();
                let info = Info::new(i.clone(), name);
                variable_map.insert(i.clone(), info);
            }
            None => {}
        }
    });

    ExtendedCHC {
        free_variables: new_variables,
        chc,
    }
}

fn translate(
    instance: &Instance,
    var_map: &mut HashMap<Ident, Ident>,
) -> (Vec<ExtendedCHC>, VariableMap) {
    let mut pmap = VariableMap::new();
    let clauses = instance
        .clauses()
        .into_iter()
        .map(|c| {
            let mut vmap = VariableMap::new();
            let c = rename_clause(
                translate_clause(c, &mut pmap, instance),
                var_map,
                &mut vmap,
                c,
            );
            pmap.extend(vmap);
            c
        })
        .collect();
    (clauses, pmap)
}

#[derive(Clone, Debug)]
pub enum CHCTranslateError {
    ParseFail,
    Unsat,
}

impl CHCTranslateError {
    pub fn is_unsat(&self) -> bool {
        matches!(self, CHCTranslateError::Unsat)
    }
}

pub fn parse_chc(input: &str) -> Result<(Vec<ExtendedCHC>, VariableMap), CHCTranslateError> {
    let mut instance = Instance::new();
    let mut cxt = parse::ParserCxt::new();
    let res = match cxt
        .parser(input, 0, &hoice::common::Profiler::new())
        .parse(&mut instance)
    {
        Ok(res) => res,
        Err(_) => return Err(CHCTranslateError::ParseFail),
    };

    // preprocess by hoice
    let profiler = Profiler::new();
    match preproc::work(&mut instance, &profiler) {
        Ok(_) => (),
        Err(r) => {
            if r.is_unsat() {
                return Err(CHCTranslateError::Unsat);
            }
        }
    }
    assert_eq!(res, parse::Parsed::CheckSat);
    let mut var_map = HashMap::new();
    let (vc, vmmap) = translate(&instance, &mut var_map);
    Ok((vc, vmmap))
}

pub fn get_mc91() -> Vec<ExtendedCHC> {
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
    parse_chc(input).unwrap().0
}

pub fn get_linear() -> Vec<ExtendedCHC> {
    let input = "(set-logic HORN)
    (declare-fun P (Int) Bool)
    (assert (forall ((x Int)) (P 0)))
    (assert (forall ((x Int) ) (=> (and (< x 10000) (P x)) (P (+ x 1)))))
    (assert (forall ((x Int) ) (=> (and (>= x 10000) (P x)) (> x 10000))))
    (check-sat)";
    parse_chc(input).unwrap().0
}

#[test]
fn test_parse_file() {
    use crate::util::Pretty;
    let chc = get_mc91();
    chc.iter().for_each(|c| {
        println!("{}", c.chc.pretty_display());
    })
}
