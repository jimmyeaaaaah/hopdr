use crate::formula::chc::Model;
use crate::formula::{chc, pcsp, Constraint, Logic, Negation, Subst, Top};
use crate::solver;

use either::Either;

use std::fmt;

#[derive(Clone)]
enum Atom {
    Positive(chc::Atom),
    Negative(chc::Atom),
}

type Body = chc::CHCBody<Atom, Constraint>;
type CHC = chc::CHC<Atom, Constraint>;

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Positive(c) => write!(f, "{}", c),
            Atom::Negative(c) => write!(f, "¬{}", c),
        }
    }
}

impl From<chc::Atom> for Atom {
    fn from(a: chc::Atom) -> Self {
        Self::Positive(a)
    }
}

impl Atom {
    fn replace_neg_with_model(&self, model: &Model) -> Either<chc::Atom, Constraint> {
        match self {
            Atom::Positive(c) => either::Left(c.clone()),
            Atom::Negative(c) => {
                let (args, constraint) = model.model.get(&c.predicate).unwrap();
                let constraint =
                    constraint.subst_multi(args.iter().cloned().zip(c.args.iter().cloned()));
                either::Right(constraint.negate().unwrap())
            }
        }
    }
}

impl Body {
    fn replace_neg_with_model(&self, model: &Model) -> chc::CHCBody<chc::Atom, Constraint> {
        let mut constraint = self.constraint.clone();
        let mut predicates = Vec::new();
        for predicate in self.predicates.iter() {
            match predicate.replace_neg_with_model(model) {
                Either::Left(atom) => predicates.push(atom),
                Either::Right(c) => constraint = Constraint::mk_conj(c, constraint),
            }
        }
        chc::CHCBody {
            predicates,
            constraint,
        }
    }
}

impl chc::CHCHead<Atom, Constraint> {
    fn replace_neg_with_model(&self, model: &Model) -> chc::CHCHead<chc::Atom, Constraint> {
        match self {
            chc::CHCHead::Constraint(c) => chc::CHCHead::Constraint(c.clone()),
            chc::CHCHead::Predicate(a) => match a.replace_neg_with_model(model) {
                Either::Left(atom) => chc::CHCHead::Predicate(atom),
                Either::Right(c) => chc::CHCHead::Constraint(c.clone()),
            },
        }
    }
}

impl CHC {
    fn replace_with_model(&self, model: &Model) -> chc::CHC<chc::Atom, Constraint> {
        let body = self.body.replace_neg_with_model(model);
        let head = self.head.replace_neg_with_model(model);
        chc::CHC { head, body }
    }
}

#[derive(Clone)]
pub enum Head {
    Predicates(Vec<chc::Atom>),
    Constraint(Constraint),
}

impl fmt::Display for Head {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Head::Constraint(c) => write!(f, "{}", c),
            Head::Predicates(ps) => {
                let mut first = true;
                for p in ps {
                    if first {
                        first = false;
                    } else {
                        write!(f, " \\/ ")?;
                    }
                    write!(f, "{}", p)?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Clone)]
pub struct Clause {
    head: Head,
    body: chc::CHCBody<chc::Atom, Constraint>,
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} => {}", self.body, self.head)
    }
}

// this CHC is extended with "negative occurrence" of preds in the body

pub fn generate_clauses(pairs: impl Iterator<Item = (pcsp::Atom, Head)>) -> Vec<Clause> {
    let mut chcs = Vec::new();
    for (body, head) in pairs {
        for body in chc::body_iter(body) {
            chcs.push(Clause {
                body,
                head: head.clone(),
            })
        }
    }
    chcs
}

/// Calculates the upperbound of p
///
/// Assumption: clauses are acyclic
/// Replace pred with another one only when the new one is greater than
/// the old one in the topological order of predicates.
/// temporarily we always assume that the upperbound is top.
fn calculate_upperbound(_clauses: &[Clause], _p: &chc::Atom) -> Constraint {
    return Constraint::mk_true();
    //   use rpds::Stack;
    //   /// reperesents left[0] /\ ... /\ left[m-1] /\ constraint => right[0] \/ ... \/ right[n-1]
    //   #[derive(Clone)]
    //   struct State {
    //       left: Stack<chc::Atom>,
    //       right: Stack<chc::Atom>,
    //       constraint: Constraint,
    //   }
    //   let mut left = Stack::new();
    //   let mut right = Stack::new();
    //   let mut constraint = Constraint::mk_true();
    //   let mut state = State{left, right, constraint};

    //   while left.len() != 0 || right.len() != 0{
    //       match left.pop() {
    //           Some(l, a) => {
    //
    //           }
    //       }
    //   }
    //   constraint.negate().unwrap()
}

fn translate_clauses_to_problems(clauses: &[Clause]) -> Vec<Vec<CHC>> {
    let mut problems: Vec<Vec<CHC>> = vec![Vec::new()];
    for clause in clauses {
        let mut next_problems = Vec::new();
        match &clause.head {
            Head::Predicates(preds) => {
                for i in 0..preds.len() {
                    // the sol of preds[0..i] has been calculated,
                    // preds[i] is now focused
                    // (i.e. the clause in this loop has the form of ... => preds[i])
                    // preds[i+1..] will be replaced by upperbounds by `calculate_upperbound`
                    let head = chc::CHCHead::Predicate(preds[i].clone().into());
                    let mut body_preds: Vec<Atom> = clause
                        .body
                        .predicates
                        .iter()
                        .cloned()
                        .map(|x| x.into())
                        .collect();
                    for j in 0..i {
                        body_preds.push(Atom::Negative(preds[j].clone()));
                    }
                    let mut body_constr = clause.body.constraint.clone();
                    for p in &preds[i + 1..] {
                        let c = calculate_upperbound(clauses, p).negate().unwrap();
                        body_constr = Constraint::mk_conj(body_constr, c);
                    }
                    let body = Body {
                        predicates: body_preds,
                        constraint: body_constr,
                    };
                    let c = CHC { head, body };
                    for problem in problems.iter() {
                        let mut p = problem.clone();
                        p.push(c.clone());
                        next_problems.push(p);
                    }
                }
            }
            Head::Constraint(c) => {
                let body = {
                    let predicates = clause
                        .body
                        .predicates
                        .iter()
                        .cloned()
                        .map(|x| x.into())
                        .collect();
                    let constraint = clause.body.constraint.clone();
                    Body {
                        predicates,
                        constraint,
                    }
                };
                let head = chc::CHCHead::Constraint(c.clone());
                let c = CHC { head, body };
                next_problems = problems;
                for problem in next_problems.iter_mut() {
                    problem.push(c.clone());
                }
            }
        }
        problems = next_problems;
    }
    problems
}

#[test]
fn test_translate_clauses_to_problems() {
    use crate::formula::{Ident, Op};
    // P(x) => Q(x)
    // true => Q(x) \/ R(x)

    let p = Ident::fresh();
    let q = Ident::fresh();
    let r = Ident::fresh();
    let x = Ident::fresh();
    let argx = vec![Op::mk_var(x)];
    let head = Head::Predicates(vec![chc::Atom {
        predicate: q,
        args: argx.clone(),
    }]);
    let body = chc::CHCBody {
        predicates: vec![chc::Atom {
            predicate: p,
            args: argx.clone(),
        }],
        constraint: Constraint::mk_true(),
    };
    let c1 = Clause { head, body };
    let head = Head::Predicates(vec![
        chc::Atom {
            predicate: q,
            args: argx.clone(),
        },
        chc::Atom {
            predicate: r,
            args: argx.clone(),
        },
    ]);
    let body = chc::CHCBody {
        predicates: Vec::new(),
        constraint: Constraint::mk_true(),
    };
    let c2 = Clause { head, body };
    let clauses = vec![c1, c2];
    let chcss = translate_clauses_to_problems(&clauses);
    println!("chcss.len() == {}", chcss.len());
    for (i, chcs) in chcss.iter().enumerate() {
        println!("problem {}", i);
        for chc in chcs {
            println!("- {}", chc);
        }
    }
    assert!(chcss.len() == 2);
}

fn solve_chcs(clauses: &Vec<CHC>, current_model: &chc::Model) -> Option<Model> {
    // 1. replace negative occurrence of predicates in clauses with its model in current_model
    let clauses = clauses
        .iter()
        .map(|c| c.replace_with_model(current_model))
        .collect();

    // 2. check if sat
    let m = match solver::chc::default_solver().solve(&clauses) {
        solver::chc::CHCResult::Sat(m) => m,
        solver::chc::CHCResult::Unsat => return None,
        solver::chc::CHCResult::Unknown => {
            panic!("PDR fails to infer a refinement type due to the background CHC solver's error")
        }
        solver::chc::CHCResult::Timeout => panic!(
            "PDR fails to infer a refinement type due to timeout of the background CHC solver"
        ),
    };

    // 3. interpolate it
    crate::title!("model from CHC solver");
    // TODO: Display model
    debug!("{}", m);
    let m = solver::interpolation::solve(&clauses);

    Some(m)
}

pub fn solve(clauses: &[Clause]) -> Model {
    crate::title!("clauses");
    for clause in clauses {
        debug!("- {}", clause);
    }
    // 1. generate a sequence of CHC problems;
    let problems = translate_clauses_to_problems(clauses);
    crate::title!("problems");
    for (i, problem) in problems.iter().enumerate() {
        debug!("problem {}", i);
        for c in problem {
            debug!("- {}", c);
        }
    }

    let mut current_model = Model::new();
    // 2. solve constraints sequentially
    for problem in problems {
        let model = solve_chcs(&problem, &current_model).unwrap();
        current_model.merge(model);
    }
    current_model
}
