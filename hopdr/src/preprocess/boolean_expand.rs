use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Ident, Op, TyEnv, Type};

pub struct BooleanExpandTransform {}

type Goal = hes::Goal<formula::Constraint>;

//fn handle_constr(c: &Constraint, env: &mut HashMap<Ident, bool>) -> Constraint {
//    unimplemented!()
//}

fn dfs(goal: Goal, fvbool: &[Ident], cur: usize) -> Goal {
    if cur == fvbool.len() {
        goal.simplify()
    } else {
        let v = fvbool[cur];
        let g1 = goal.isubst(&v, &Op::one());
        let g1 = dfs(g1, fvbool, cur + 1);
        let g2 = goal.isubst(&v, &Op::zero());
        let g2 = dfs(g2, fvbool, cur + 1);
        Goal::mk_conj_opt(g1, g2)
    }
}

fn handle_goal(goal: &Goal, mut fvbools: Vec<Ident>) -> Goal {
    match goal.kind() {
        GoalKind::Univ(v, g) if v.ty.is_bit() => {
            fvbools.push(v.id);
            handle_goal(g, fvbools)
        }
        GoalKind::Univ(v, g) => {
            let g = handle_goal(g, fvbools);
            Goal::mk_univ(v.clone(), g)
        }
        GoalKind::Abs(v, g) => {
            let g = handle_goal(g, fvbools);
            Goal::mk_abs(v.clone(), g)
        }
        _ => dfs(goal.clone(), &fvbools, 0),
    }
}

impl TypedPreprocessor for BooleanExpandTransform {
    fn transform_goal(&self, goal: &Goal, _t: &Type, _env: &mut TyEnv) -> Goal {
        debug!("transform_goal: {}", goal);
        let fvbools = Vec::new();
        handle_goal(goal, fvbools)
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    debug!("boolean expand transform");
    let t = BooleanExpandTransform {};
    t.transform(problem)
}

#[test]
fn test_boolean_transform() {
    // ∀x. ∀b. ∀y. ∀c. (b = 1 /\ (x > 0)) \/ (b != 0 /\ c = 1 /\ (y > 0))
    use crate::formula::*;

    let x = Ident::fresh();
    let xv = Variable::mk(x, Type::mk_type_int());
    let b = Ident::fresh();
    let bv = Variable::mk(b, Type::mk_type_bit());
    let y = Ident::fresh();
    let yv = Variable::mk(y, Type::mk_type_int());
    let c = Ident::fresh();
    let cv = Variable::mk(c, Type::mk_type_bit());
    let c1 = Constraint::mk_eq(Op::mk_var(b.clone()), Op::one());
    let c2 = Constraint::mk_gt(Op::mk_var(x.clone()), Op::zero());
    let c3 = Constraint::mk_neq(Op::mk_var(b.clone()), Op::zero());
    let c4 = Constraint::mk_eq(Op::mk_var(c.clone()), Op::one());
    let c5 = Constraint::mk_gt(Op::mk_var(y.clone()), Op::zero());
    let g1 = Goal::mk_conj(Goal::mk_constr(c1), Goal::mk_constr(c2));
    let g2 = Goal::mk_conj(
        Goal::mk_constr(c3),
        Goal::mk_conj(Goal::mk_constr(c4), Goal::mk_constr(c5)),
    );
    let g3 = Goal::mk_disj(g1, g2);
    let g = Goal::mk_univ(
        xv,
        Goal::mk_univ(bv, Goal::mk_univ(yv, Goal::mk_univ(cv, g3))),
    );
    println!("{}", g);
    let g_after = handle_goal(&g, Vec::new());
    println!("{}", g_after);
}
