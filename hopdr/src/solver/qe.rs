use std::collections::HashMap;

use super::smt::{constraint_to_smt2_inner, encode_ident, z3_solver};
use super::SMTSolverType;
use crate::formula::chc::Model;
use crate::formula::{Bot, Constraint, Fv, Ident, Logic, Negation, Op, OpKind, PredKind, Top};
use lexpr::Value;
use lexpr::{self, Cons};

pub struct QESolver {}

pub fn qe_solver(ty: SMTSolverType) -> QESolver {
    match ty {
        SMTSolverType::Z3 | SMTSolverType::Auto => QESolver {},
        SMTSolverType::CVC => unimplemented!(),
    }
}

fn parse_variable(v: &str) -> Ident {
    assert!(v.starts_with('x'));
    Ident::parse_ident(&v[1..]).unwrap_or_else(|| panic!("parse fail"))
}

fn parse_opkind(v: &Value) -> OpKind {
    let x = v
        .as_symbol()
        .unwrap_or_else(|| panic!("parse error: {:?}", v));
    match x {
        "+" => OpKind::Add,
        "-" => OpKind::Sub,
        "*" => OpKind::Mul,
        _ => panic!("failed to handle operator: {}", x),
    }
}

fn parse_op(v: &Value) -> Op {
    match v {
        Value::Number(n) => Op::mk_const(n.as_i64().unwrap()),
        Value::Symbol(x) => Op::mk_var(parse_variable(x)),
        Value::Cons(cons) => {
            let car = cons.car();
            let opkind = parse_opkind(car);
            let mut args: Vec<_> = cons
                .cdr()
                .as_cons()
                .unwrap_or_else(|| panic!("parse error: {:?}", v))
                .iter()
                .map(|v| parse_op(v.car()))
                .collect();

            // handle case (- 1)
            if args.len() == 1 && opkind == OpKind::Sub {
                args = vec![Op::zero(), args[0].clone()];
            }
            // TODO: args.len() > 2
            if args.len() > 2 {
                panic!("failed to parse: {}", v)
            }
            assert_eq!(args.len(), 2);
            Op::mk_bin_op(opkind, args[0].clone(), args[1].clone())
        }
        Value::Nil
        | Value::Null
        | Value::Bool(_)
        | Value::Char(_)
        | Value::String(_)
        | Value::Keyword(_)
        | Value::Bytes(_)
        | Value::Vector(_) => panic!("parse error"),
    }
}

#[test]
fn test_parse_op() {
    use crate::formula::AlphaEquivalence;
    let s = "(+ x_x1 1)";
    let x = Ident::fresh();
    let o1 = Op::mk_add(Op::mk_var(x), Op::mk_const(1));
    let o2 = parse_op(&lexpr::from_str(s).unwrap());
    assert!(o1.alpha_equiv(&o2));

    let s = "(- x_x2 (+ x_x1 1))";
    let x1 = Ident::fresh();
    let x2 = Ident::fresh();
    let o1 = Op::mk_add(Op::mk_var(x1), Op::mk_const(1));
    let o1 = Op::mk_sub(Op::mk_var(x2), o1);
    let o2 = parse_op(&lexpr::from_str(s).unwrap());
    assert!(o1.alpha_equiv(&o2));

    let s = "(* (- 1) xx_2978)";
    let o1 = Op::mk_mul(Op::mk_sub(Op::mk_const(0), Op::mk_const(1)), Op::mk_var(x1));
    let o2 = parse_op(&lexpr::from_str(s).unwrap());
    assert!(o1.alpha_equiv(&o2));
}

fn parse_predicate(kind_str: &str) -> PredKind {
    match kind_str {
        "=" => PredKind::Eq,
        "<" => PredKind::Lt,
        "<=" => PredKind::Leq,
        ">" => PredKind::Gt,
        ">=" => PredKind::Geq,
        _ => panic!("unknown operator: {}", kind_str),
    }
}
fn parse_let_arg<'a>(v: &'a Value, env: &mut HashMap<String, Constraint>) -> (String, Constraint) {
    debug!("let arg: {:?}", v);
    let cons = v
        .as_cons()
        .unwrap_or_else(|| panic!("parse error: {:?}", v));
    debug!("body: {:?}", cons.cdr().as_cons().unwrap().car());
    let varname = cons
        .car()
        .as_symbol()
        .unwrap_or_else(|| panic!("parse error: {:?}", v));
    let expr = parse_constraint(cons.cdr().as_cons().unwrap().car(), env);
    (varname.to_string(), expr)
}
fn parse_constraint_cons(cons: &Cons, env: &mut HashMap<String, Constraint>) -> Constraint {
    let cons_str = cons
        .car()
        .as_symbol()
        .unwrap_or_else(|| panic!("parse error: {:?}", cons));

    match cons_str {
        "and" | "or" => {
            let args: Vec<_> = cons
                .cdr()
                .as_cons()
                .unwrap_or_else(|| panic!("parse error: {:?}", cons_str))
                .iter()
                .map(|v| parse_constraint(v.car(), env))
                .collect();
            // TODO: implement cases where there are more than two arguments
            assert_eq!(args.len(), 2);
            if cons_str == "and" {
                args.iter().fold(Constraint::mk_true(), |x, y| {
                    Constraint::mk_conj(x, y.clone())
                })
            } else {
                args.iter().fold(Constraint::mk_false(), |x, y| {
                    Constraint::mk_disj(x, y.clone())
                })
            }
        }
        _ => {
            let expr = cons.car();
            let kind_str = expr
                .as_symbol()
                .unwrap_or_else(|| panic!("parse error: {:?}", expr));
            match kind_str {
                "not" => {
                    let args: Vec<_> = cons
                        .cdr()
                        .as_cons()
                        .unwrap_or_else(|| panic!("parse error: {:?}", cons_str))
                        .iter()
                        .map(|v| parse_constraint(v.car(), env))
                        .collect();
                    assert_eq!(args.len(), 1);
                    args[0].negate().unwrap()
                }
                "let" => {
                    let args: Vec<_> = cons
                        .cdr()
                        .as_cons()
                        .unwrap_or_else(|| panic!("parse error: {:?}", cons_str))
                        .iter()
                        .cloned()
                        .collect();
                    assert_eq!(args.len(), 2);
                    let (varname, expr) =
                        parse_let_arg(args[0].car().as_cons().unwrap().car(), env);
                    let old = env.insert(varname.clone(), expr);
                    println!("parse_constriant: {:?}", args[1].car());
                    let c = parse_constraint(args[1].car(), env);
                    match old {
                        Some(old_expr) => {
                            env.insert(varname, old_expr);
                        }
                        None => {
                            env.remove(&varname);
                        }
                    }
                    c
                }
                _ => {
                    let pred = parse_predicate(kind_str);
                    let args: Vec<_> = cons
                        .cdr()
                        .as_cons()
                        .unwrap_or_else(|| panic!("parse error: {:?}", cons_str))
                        .iter()
                        .map(|v| parse_op(v.car()))
                        .collect();
                    // currently, we don't care about the predicates that take more than
                    // two arguments; so if there is, then it must can cause some bugs.
                    assert_eq!(args.len(), 2);
                    Constraint::mk_pred(pred, args)
                }
            }
        }
    }
}

fn parse_constraint(v: &Value, env: &mut HashMap<String, Constraint>) -> Constraint {
    match v {
        Value::Bool(t) if *t => Constraint::mk_true(),
        Value::Symbol(s) if s.as_ref() == "true" => Constraint::mk_true(),
        Value::Bool(_) => Constraint::mk_false(),
        Value::Symbol(s) if s.as_ref() == "false" => Constraint::mk_false(),
        Value::Cons(cons) => parse_constraint_cons(cons, env),
        Value::Symbol(s) if env.contains_key(s.as_ref()) => env.get(s.as_ref()).unwrap().clone(),
        Value::Nil
        | Value::Null
        | Value::Number(_)
        | Value::Char(_)
        | Value::String(_)
        | Value::Symbol(_)
        | Value::Keyword(_)
        | Value::Bytes(_)
        | Value::Vector(_) => panic!("parse error: {:?}", v),
    }
}

#[test]
fn test_parse_constraint() {
    let mut env = HashMap::new();
    let env = &mut env;
    use crate::formula::AlphaEquivalence;
    let s = "(= x_x1 0)";
    let x = lexpr::from_str(s).unwrap();
    let c = parse_constraint(&x, env);
    let x = Ident::fresh();
    let c2 = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(0));
    assert!(c.alpha_equiv(&c2));

    let x = lexpr::from_str("#t").unwrap();
    let c = parse_constraint(&x, env);
    assert!(c.alpha_equiv(&Constraint::mk_true()));

    let x = lexpr::from_str("#f").unwrap();
    let c = parse_constraint(&x, env);
    assert!(c.alpha_equiv(&Constraint::mk_false()));
}

impl QESolver {
    fn to_smt(&self, formula: &Constraint) -> String {
        let fvs = formula.fv();
        let declare_funs = fvs
            .iter()
            .map(|ident| format!("(declare-fun {} () Int)", encode_ident(ident)))
            .collect::<Vec<_>>()
            .join("\n");
        let c_str = constraint_to_smt2_inner(formula, SMTSolverType::Z3);

        format!(
            "{}\n (assert {})\n (apply (using-params qe))\n",
            declare_funs, c_str
        )
    }
    fn parse(&self, s: &str) -> Result<Constraint, lexpr::parse::Error> {
        debug!("qe parsing: {s}");
        fn filter_value(v: &&Value) -> bool {
            let symbols = [":precision", "goal", "precise", ":depth"];
            match v {
                Value::Bool(_) | Value::Nil | Value::Cons(_) => true,
                Value::Symbol(x) => !symbols.contains(&x.as_ref()),
                Value::Null
                | Value::Number(_)
                | Value::Char(_)
                | Value::String(_)
                | Value::Keyword(_)
                | Value::Bytes(_)
                | Value::Vector(_) => false,
            }
        }
        let x = lexpr::from_str(s)?;
        let data = x.as_cons().unwrap().cdr().as_cons().unwrap().car();
        let c = if let Value::Cons(x) = data {
            x.iter()
                .map(|x| x.car())
                .filter(filter_value)
                .map(|x| parse_constraint(x, &mut HashMap::new()))
                .fold(Constraint::mk_true(), Constraint::mk_conj)
        } else {
            panic!("parse error: qe smt2 formula {} ({:?})", s, x)
        };
        Ok(c)
    }
    pub fn default_solver() -> QESolver {
        qe_solver(SMTSolverType::Z3)
    }
    pub fn solve(&self, formula: &Constraint) -> Constraint {
        debug!("trying quantifier elimination: {formula}");
        let smt_string = self.to_smt(formula);
        let result = z3_solver(smt_string);
        debug!("result string: {result}");
        let r = self
            .parse(&result)
            .unwrap_or_else(|_| panic!("qe result parse failed: {}", result));
        debug!("result: {r}");
        r
    }
    pub fn model_quantifer_elimination(&self, model: &mut Model) {
        for (_, (_, c)) in model.model.iter_mut() {
            let (qs, _) = c.to_pnf_raw();
            if qs.iter().any(|(q, _)| q.is_existential()) {
                *c = self.solve(c);
            }
        }
    }
}

#[test]
fn test_z3_qe_result() {
    use crate::formula::AlphaEquivalence;
    let s = "(goals
(goal
  (= x_x1 0)
  (>= x_x2 1)
  :precision precise :depth 1)
)";
    let z3_solver = qe_solver(SMTSolverType::Z3);
    let c = z3_solver.parse(s).unwrap();

    let x1 = Ident::fresh();
    let x2 = Ident::fresh();
    let c1 = Constraint::mk_eq(Op::mk_var(x1), Op::mk_const(0));
    let c2 = Constraint::mk_geq(Op::mk_var(x2), Op::mk_const(1));
    let c3 = Constraint::mk_conj(c1, c2.clone());
    assert!(c.alpha_equiv(&c3));

    let s = "(goals
(goal
  #t 
  (>= x_x2 1)
  :precision precise :depth 1)
)";
    let c = z3_solver.parse(s).unwrap();
    let c4 = Constraint::mk_conj(Constraint::mk_true(), c2);
    assert!(c.alpha_equiv(&c4));

    let s = "(goals
    (goal
      (>= (+ xx_2980 (* (- 1) xx_2978)) 0)
      :precision precise :depth 1)
    )";
    let o = Op::mk_mul(Op::mk_sub(Op::mk_const(0), Op::mk_const(1)), Op::mk_var(x1));
    let o = Op::mk_add(Op::mk_var(x2), o);
    let c2 = Constraint::mk_geq(o, Op::mk_const(0));

    let c = z3_solver.parse(s).unwrap();
    assert!(c.alpha_equiv(&c2));

    let s = "(goals
(goal
  (>= xx_9291 1)
  (>= xx_9292 0)
  (let ((a!1 (or (not (>= xx_9292 0)) (<= (+ xx_9291 (* (- 1) xx_9292)) 0))))
    (not (and (not (<= xx_9291 0)) a!1)))
  (>= xx_9292 0)
  :precision precise :depth 1)
)    ";
    z3_solver.parse(s).unwrap();
}

#[test]
fn test_quantifier_elimination() {
    use crate::formula::{FirstOrderLogic, QuantifierKind};
    // formula: ∃z. (z ≥ 1 ∧ x = 0) ∧ y − z ≥ 0
    let x = Ident::fresh();
    let y = Ident::fresh();
    let z = Ident::fresh();
    let c1 = Constraint::mk_geq(Op::mk_var(z), Op::mk_const(1));
    let c2 = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(0));
    let c3 = Constraint::mk_geq(Op::mk_sub(Op::mk_var(y), Op::mk_var(z)), Op::mk_const(0));
    let c = Constraint::mk_conj(Constraint::mk_conj(c1, c2), c3);
    let c = Constraint::mk_quantifier_int(QuantifierKind::Existential, z, c);
    let z3_solver = qe_solver(SMTSolverType::Z3);
    let result = z3_solver.solve(&c);
    let (v, _) = result.to_pnf_raw();
    assert_eq!(v.len(), 0);
}
