use std::collections::{HashMap, HashSet};
use std::fmt;

use super::hes;
use super::pcsp;
use super::{
    Bot, Conjunctive, Constraint, Fv, Ident, Op, OpKind, PredKind, QuantifierKind, Rename, Subst,
    Top, Type, Variable,
};
use crate::solver::smt;
use crate::util::P;

#[derive(Debug, PartialEq)]
pub enum AtomKind {
    True, // equivalent to Constraint(True). just for optimization purpose
    Constraint(Constraint),
    Predicate(Ident, Vec<Op>),
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

impl Rename for Atom {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self.kind() {
            AtomKind::True => self.clone(),
            AtomKind::Constraint(c) => Atom::mk_constraint(c.rename(x, y)),
            AtomKind::Predicate(p, l) => {
                let l2 = l.iter().map(|id| id.rename(x, y)).collect();
                Atom::mk_pred(*p, l2)
            }
            AtomKind::Conj(a1, a2) => Atom::mk_conj(a1.rename(x, y), a2.rename(x, y)),
            AtomKind::Disj(a1, a2) => Atom::mk_disj(a1.rename(x, y), a2.rename(x, y)),
            AtomKind::Not(a) => Atom::mk_not(a.rename(x, y)),
            AtomKind::Quantifier(q, x, a) => Atom::mk_quantifier(*q, *x, a.rename(x, y)),
        }
    }
}

impl From<Constraint> for Atom {
    fn from(from: Constraint) -> Atom {
        Atom::mk_constraint(from)
    }
}
impl From<Atom> for Constraint {
    fn from(from: Atom) -> Constraint {
        match from.kind() {
            AtomKind::True => Constraint::mk_true(),
            AtomKind::Constraint(c) => c.clone(),
            AtomKind::Conj(a1, a2) => {
                let c1 = a1.clone().into();
                let c2 = a2.clone().into();
                Constraint::mk_conj(c1, c2)
            }
            AtomKind::Disj(a1, a2) => {
                let c1 = a1.clone().into();
                let c2 = a2.clone().into();
                Constraint::mk_disj(c1, c2)
            }
            AtomKind::Not(a) => {
                let c: Constraint = a.clone().into();
                c.negate().unwrap()
            }
            AtomKind::Quantifier(q, x, a) => {
                let c: Constraint = a.clone().into();
                Constraint::mk_quantifier_int(*q, *x, c)
            }
            AtomKind::Predicate(_, _) => panic!("program error"),
        }
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

impl From<pcsp::PCSP<Atom>> for Atom {
    fn from(from: pcsp::PCSP<Atom>) -> Atom {
        Atom::mk_disj(Atom::mk_not(from.body), from.head)
    }
}

impl Top for Atom {
    fn mk_true() -> Self {
        Atom::new(AtomKind::True)
    }

    fn is_true(&self) -> bool {
        match self.kind() {
            AtomKind::True => true,
            _ => false,
        }
    }
}

impl Bot for Atom {
    fn mk_false() -> Self {
        Atom::new(AtomKind::Constraint(Constraint::mk_false()))
    }

    fn is_false(&self) -> bool {
        match self.kind() {
            AtomKind::Constraint(x) => x.is_false(),
            _ => false,
        }
    }
}

impl Conjunctive for Atom {
    fn mk_conj(x: Self, y: Self) -> Atom {
        use AtomKind::*;
        Atom::new(Conj(x, y))
    }
}

impl Subst for Atom {
    type Item = super::Op;
    fn subst(&self, x: &Ident, v: &super::Op) -> Self {
        match self.kind() {
            AtomKind::True => self.clone(),
            AtomKind::Constraint(c) => Atom::mk_constraint(c.subst(x, v)),
            AtomKind::Predicate(p, l) => {
                let l2 = l.iter().map(|id| id.subst(x, v)).collect();
                Atom::mk_pred(*p, l2)
            }
            AtomKind::Conj(_, _) => todo!(),
            AtomKind::Disj(_, _) => todo!(),
            AtomKind::Not(_) => todo!(),
            AtomKind::Quantifier(_, _, _) => todo!(),
        }
    }
}

impl From<Atom> for hes::Goal<Atom> {
    fn from(c: Atom) -> Self {
        hes::Goal::mk_constr(c)
    }
}

impl From<Constraint> for hes::Goal<Atom> {
    fn from(c: Constraint) -> Self {
        let a: Atom = c.into();
        a.into()
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
    ) -> Option<HashMap<Ident, (Vec<Op>, Constraint)>> {
        let mut templates = HashMap::new();
        let mut fvs = HashSet::new();
        for predicate in map.values() {
            let t = Template::new(predicate.args.len());
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
        Atom::new(AtomKind::Disj(x, y))
    }
    pub fn mk_false() -> Atom {
        Atom::mk_constraint(Constraint::mk_false())
    }
    pub fn mk_not(x: Self) -> Atom {
        Atom::new(AtomKind::Not(x))
    }
    //pub fn mk_var(x: Ident) -> Atom {
    //    Atom::new(AtomKind::)
    //}
    // auxiliary function for generating constraint
    pub fn mk_constraint(c: Constraint) -> Atom {
        Atom::new(AtomKind::Constraint(c))
    }
    pub fn mk_pred(p: Ident, l: Vec<Op>) -> Atom {
        Atom::new(AtomKind::Predicate(p, l))
    }
    pub fn mk_quantifier(q: QuantifierKind, x: Ident, c: Atom) -> Atom {
        Atom::new(AtomKind::Quantifier(q, x, c))
    }
    pub fn mk_univq(x: Ident, c: Atom) -> Atom {
        Atom::mk_quantifier(QuantifierKind::Universal, x, c)
    }
    pub fn mk_existq(x: Ident, c: Atom) -> Atom {
        Atom::mk_quantifier(QuantifierKind::Existential, x, c)
    }
    pub fn negate(self) -> Atom {
        Atom::mk_not(self)
    }
    pub fn integer_fv(&self) -> HashSet<Ident> {
        fn inner(atom: &Atom, fvs: &mut HashSet<Ident>) {
            match atom.kind() {
                AtomKind::True => (),
                AtomKind::Constraint(c) => {
                    c.fv_with_vec(fvs);
                }
                AtomKind::Predicate(_, args) => {
                    for a in args {
                        a.fv_with_vec(fvs);
                    }
                }
                AtomKind::Conj(x, y) | AtomKind::Disj(x, y) => {
                    inner(x, fvs);
                    inner(y, fvs);
                }
                AtomKind::Quantifier(_, x, c) => {
                    inner(c, fvs);
                    fvs.remove(x);
                }
                AtomKind::Not(x) => inner(x, fvs),
            }
        }
        let mut fvs = HashSet::new();
        inner(self, &mut fvs);
        fvs
    }
    pub fn to_constraint(&self) -> Option<Constraint> {
        match self.kind() {
            AtomKind::True => Some(Constraint::mk_true()),
            AtomKind::Constraint(c) => Some(c.clone()),
            AtomKind::Predicate(_, _) => None,
            AtomKind::Conj(x, y) => x
                .to_constraint()
                .map(|x| y.to_constraint().map(|y| Constraint::mk_conj(x, y)))
                .flatten(),
            AtomKind::Disj(x, y) => x
                .to_constraint()
                .map(|x| y.to_constraint().map(|y| Constraint::mk_disj(x, y)))
                .flatten(),
            AtomKind::Quantifier(q, x, c) => c
                .to_constraint()
                .map(|c| Constraint::mk_quantifier(*q, Variable::mk(*x, Type::mk_type_int()), c)),
            AtomKind::Not(x) => x.to_constraint().map(|x| x.negate()).flatten(),
        }
    }
}

trait TemplateKind {
    fn apply(&self, args: &[Op]) -> Constraint;
    fn instantiate(&self, args: &[Op], model: &smt::Model) -> Constraint;
    fn coefs<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Ident> + 'a>;
}

struct Linear {
    coefs: Vec<Ident>,
    constant: Ident,
    predicate: PredKind,
}

impl Linear {
    fn to_constraint(
        &self,
        coefs: impl Iterator<Item = Op>,
        args: &[Op],
        constant: Op,
    ) -> Constraint {
        let o = gen_linear_sum(coefs, args);
        let o = Op::mk_bin_op(OpKind::Add, o, constant);
        Constraint::mk_pred(self.predicate, vec![o, Op::mk_const(0)])
    }
}

impl Linear {
    fn new(nargs: usize, predicate: PredKind) -> Linear {
        let mut coefs = Vec::new();
        for _ in 0..nargs {
            coefs.push(Ident::fresh());
        }
        let constant = Ident::fresh();
        Linear {
            coefs,
            constant,
            predicate,
        }
    }
}

fn new_eq_template(nargs: usize) -> Linear {
    Linear::new(nargs, PredKind::Eq)
}

fn new_gt_template(nargs: usize) -> Linear {
    Linear::new(nargs, PredKind::Gt)
}

impl TemplateKind for Linear {
    fn apply(&self, args: &[Op]) -> Constraint {
        let coefs = self.coefs.iter().map(|x| Op::mk_var(*x));
        let constant = Op::mk_var(self.constant);
        self.to_constraint(coefs, args, constant)
    }

    fn instantiate(&self, args: &[Op], model: &smt::Model) -> Constraint {
        let coefs = self.coefs.iter().map(|x| {
            let v = model.get(x).unwrap();
            Op::mk_const(v)
        });
        let constant = Op::mk_const(model.get(&self.constant).unwrap());
        self.to_constraint(coefs, args, constant)
    }

    fn coefs<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Ident> + 'a> {
        Box::new(self.coefs.iter().chain(vec![&self.constant]))
    }
}

///
/// P(x1, x2) -> a1 x1 + a2 x2 + b >= 0
pub struct Template<'a> {
    // information of the original predicate
    nargs: usize,
    template_kinds: Vec<Box<dyn TemplateKind + 'a>>,
}

fn gen_linear_sum(coefs: impl IntoIterator<Item = Op>, args: &[Op]) -> Op {
    if !args.is_empty() {
        let mut coefs = coefs.into_iter();
        let c = coefs.next().unwrap();
        let mut cur = Op::mk_bin_op(OpKind::Mul, c, args[0].clone());
        for (id, coef) in args[1..].iter().zip(coefs) {
            let id = id.clone();
            let term = Op::mk_bin_op(OpKind::Mul, coef, id);
            cur = Op::mk_bin_op(OpKind::Add, cur, term)
        }
        cur
    } else {
        Op::mk_const(0)
    }
}

impl<'a> Template<'a> {
    fn new(nargs: usize) -> Template<'a> {
        let mut template_kinds: Vec<Box<dyn TemplateKind>> = Vec::new();
        // Here, the list of templates
        //// 1. ax + by + c = d
        //template_kinds.push(Box::new(new_eq_template(nargs)));
        // 1. ax + by + c > d
        template_kinds.push(Box::new(new_gt_template(nargs)));
        Template {
            nargs,
            template_kinds,
        }
    }

    fn apply(&self, args: &[Op]) -> Constraint {
        let mut c = Constraint::mk_true();
        for t in self.template_kinds.iter() {
            c = Constraint::mk_conj(t.apply(args), c);
        }
        c
    }

    fn coef_iter(&'a self) -> impl Iterator<Item = &'a Ident> {
        self.template_kinds.iter().map(|x| x.coefs()).flatten()
    }

    fn to_constraint(self, model: &smt::Model) -> (Vec<Op>, Constraint) {
        let args = (0..self.nargs)
            .into_iter()
            .map(|_| Op::mk_var(Ident::fresh()))
            .collect::<Vec<_>>();
        let mut c = Constraint::mk_true();
        for t in self.template_kinds.iter() {
            c = Constraint::mk_conj(t.instantiate(&args, model), c);
        }
        (args, c)
    }
}
