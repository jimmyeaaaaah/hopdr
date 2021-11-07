use std::collections::{HashMap, HashSet};
use std::fmt;

use super::pcsp;
use super::{
    Bot, Conjunctive, Constraint, Fv, Ident, Op, OpKind, PredKind, QuantifierKind, Subst, Top,
};
use crate::solver::smt;
use crate::util::P;

#[derive(Debug)]
pub enum AtomKind {
    True, // equivalent to Constraint(True). just for optimization purpose
    Constraint(Constraint),
    Predicate(Ident, Vec<Ident>),
    Conj(Atom, Atom),
    Disj(Atom, Atom),
    Not(Atom),
    Quantifier(QuantifierKind, Ident, Atom),
}
pub type Atom = P<AtomKind>;

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            AtomKind::True => write!(f, "true"),
            AtomKind::Constraint(c) => write!(f, "{}", c),
            AtomKind::Predicate(id, ops) => {
                write!(f, "{}(", id)?;
                for op in ops.iter() {
                    write!(f, "{},", op)?;
                }
                write!(f, ")")
            }
            AtomKind::Conj(x, y) => write!(f, "({} & {})", x, y),
            AtomKind::Disj(x, y) => write!(f, "({} & {})", x, y),
            AtomKind::Not(x) => write!(f, "not({})", x),
            AtomKind::Quantifier(q, x, c) => write!(f, "{} {}. {}", q, x, c),
        }
    }
}

///
/// P(x1, x2) -> a1 x1 + a2 x2 + b >= 0
pub struct Template {
    // information of the original predicate
    id: Ident,
    nargs: usize,
    coef_linear: Vec<Ident>,
}

fn gen_linear_sum(coefs: impl IntoIterator<Item = Op>, args: &[Ident]) -> Op {
    if args.len() > 0 {
        let mut coefs = coefs.into_iter();
        let c = coefs.next().unwrap();
        let mut cur = Op::mk_bin_op(OpKind::Mul, c, Op::mk_var(args[0]));
        for (id, coef) in args[1..].iter().zip(coefs) {
            let id = Op::mk_var(*id);
            let term = Op::mk_bin_op(OpKind::Mul, coef, id);
            cur = Op::mk_bin_op(OpKind::Add, cur, term)
        }
        cur
    } else {
        Op::mk_const(0)
    }
}

impl Template {
    fn new(id: Ident, nargs: usize) -> Template {
        let mut coef_linear = Vec::new();
        for _ in 0..nargs {
            coef_linear.push(Ident::fresh());
        }
        Template {
            id,
            nargs,
            coef_linear,
        }
    }

    fn apply(&self, args: &[Ident]) -> Constraint {
        let mut c = Constraint::mk_false();

        let o = gen_linear_sum(self.coef_linear.iter().map(|x| Op::mk_var(*x)), args);
        c = Constraint::mk_pred(PredKind::Eq, vec![o, Op::mk_const(0)]);
        c
    }

    fn coef_iter<'a>(&'a self) -> impl Iterator<Item = &'a Ident> {
        self.coef_linear.iter()
    }

    fn to_constraint(self, model: &smt::Model) -> (Vec<Ident>, Constraint) {
        let args = (0..self.nargs)
            .into_iter()
            .map(|_| Ident::fresh())
            .collect::<Vec<_>>();

        let op_args = self.coef_linear.iter().map(|x| {
            let v = model.get(x).unwrap();
            Op::mk_const(v)
        });
        let o = gen_linear_sum(op_args, &args);
        let c = Constraint::mk_pred(PredKind::Eq, vec![o, Op::mk_const(0)]);
        (args, c)
    }
}

impl Atom {
    fn replace_by_template(&self, map: &HashMap<Ident, Template>) -> Constraint {
        match self.kind() {
            AtomKind::True => Constraint::mk_true(),
            AtomKind::Constraint(c) => c.clone(),
            AtomKind::Conj(x, y) => {
                Constraint::mk_conj(x.replace_by_template(map), y.replace_by_template(map))
            }
            AtomKind::Disj(x, y) => {
                Constraint::mk_disj(x.replace_by_template(map), y.replace_by_template(map))
            }
            AtomKind::Not(c) => c.replace_by_template(map).negate().unwrap(),
            AtomKind::Quantifier(q, v, x) => {
                Constraint::mk_quantifier_int(*q, *v, x.replace_by_template(map))
            }
            AtomKind::Predicate(p, l) => map.get(p).unwrap().apply(l),
        }
    }
    /// check the satisfiability of the given fofml formula
    pub fn check_satisfiability(
        &self,
        vars: &HashSet<Ident>,
        map: &HashMap<Ident, pcsp::Predicate>,
    ) -> Option<HashMap<Ident, (Vec<Ident>, Constraint)>> {
        let mut templates = HashMap::new();
        let mut fvs = HashSet::new();
        for predicate in map.values() {
            let t = Template::new(predicate.id, predicate.args.len());
            for i in t.coef_iter() {
                fvs.insert(*i);
            }
            templates.insert(predicate.id, t);
        }
        let c = self.replace_by_template(&templates);
        // check satisfiability of c and get model
        let mut solver = smt::default_solver();
        let model = match solver.solve_with_model(&c, vars, &fvs) {
            Ok(model) => model,
            Err(smt::SMTResult::Unsat) => {
                // when c is unsat, returns None
                return None;
            }
            _ => panic!("program error"),
        };
        // generate map predicate -> constraints
        let h = templates
            .into_iter()
            .map(|(p, t)| (p, t.to_constraint(&model)))
            .collect();
        Some(h)
    }
    pub fn mk_disj(x: Self, y: Self) -> Atom {
        Atom::new(AtomKind::Disj(x.clone(), y.clone()))
    }
    pub fn mk_false() -> Atom {
        Atom::mk_constraint(Constraint::mk_false())
    }
    pub fn mk_not(x: Self) -> Atom {
        Atom::new(AtomKind::Not(x))
    }
    // auxiliary function for generating constraint
    pub fn mk_constraint(c: Constraint) -> Atom {
        Atom::new(AtomKind::Constraint(c))
    }
    pub fn mk_pred(p: Ident, l: Vec<Ident>) -> Atom {
        Atom::new(AtomKind::Predicate(p, l))
    }
    fn mk_quantifier(q: QuantifierKind, x: Ident, c: Atom) -> Atom {
        Atom::new(AtomKind::Quantifier(q, x, c))
    }
    pub fn mk_univq(x: Ident, c: Atom) -> Atom {
        Atom::mk_quantifier(QuantifierKind::Universal, x, c)
    }
    pub fn mk_existq(x: Ident, c: Atom) -> Atom {
        Atom::mk_quantifier(QuantifierKind::Existential, x, c)
    }
}

impl Fv for Atom {
    type Id = Ident;
    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            AtomKind::True | AtomKind::Constraint(_) => (),
            AtomKind::Predicate(ident, _) => {
                fvs.insert(*ident);
            }
            AtomKind::Conj(x, y) | AtomKind::Disj(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            AtomKind::Not(x) => {
                x.fv_with_vec(fvs);
            }
            AtomKind::Quantifier(_, x, c) => {
                c.fv_with_vec(fvs);
                fvs.remove(x);
            }
        }
    }
}

impl From<Constraint> for Atom {
    fn from(from: Constraint) -> Atom {
        Atom::mk_constraint(from)
    }
}

impl From<pcsp::Atom> for Atom {
    fn from(from: pcsp::Atom) -> Atom {
        match from.kind() {
            pcsp::AtomKind::True => Atom::mk_true(),
            pcsp::AtomKind::Constraint(c) => Atom::mk_constraint(c.clone()),
            pcsp::AtomKind::Predicate(p, l) => Atom::mk_pred(*p, l.clone()),
            pcsp::AtomKind::Conj(x, y) => Atom::mk_conj(x.clone().into(), y.clone().into()),
            pcsp::AtomKind::Disj(x, y) => Atom::mk_disj(x.clone().into(), y.clone().into()),
            pcsp::AtomKind::Quantifier(q, x, c) if *q == QuantifierKind::Universal => {
                Atom::mk_univq(*x, c.clone().into())
            }
            pcsp::AtomKind::Quantifier(q, x, c) if *q == QuantifierKind::Existential => {
                Atom::mk_existq(*x, c.clone().into())
            }
            pcsp::AtomKind::Quantifier(_q, _x, _c) => panic!("fail"),
        }
    }
}

impl From<pcsp::PCSP<pcsp::Atom>> for Atom {
    fn from(from: pcsp::PCSP<pcsp::Atom>) -> Atom {
        Atom::mk_disj(Atom::mk_not(from.body.into()), from.head.into())
    }
}

impl Top for Atom {
    fn mk_true() -> Self {
        Atom::new(AtomKind::True)
    }
}

impl Conjunctive for Atom {
    fn mk_conj(x: Self, y: Self) -> Atom {
        use AtomKind::*;
        match (&*x, &*y) {
            (True, _) => y.clone(),
            (_, True) => x.clone(),
            _ => Atom::new(Conj(x.clone(), y.clone())),
        }
    }
}

impl Subst for Atom {
    fn subst(&self, x: &Ident, v: &super::Op) -> Self {
        let eq = vec![Op::mk_var(*x), v.clone()];
        let c = Atom::mk_constraint(Constraint::mk_pred(PredKind::Eq, eq));
        Atom::mk_conj(c, self.clone())
    }
}
