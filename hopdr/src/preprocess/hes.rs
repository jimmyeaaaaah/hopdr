use std::{collections::HashMap, error::Error, fmt, mem::uninitialized, unimplemented};

use fmt::Formatter;
use lazy_static::lazy;
use rpds::HashTrieMap;

use crate::formula::{OpKind, PredKind, Type as SimpleType};
use crate::parse;
use crate::util::{global_counter, Unique, P};

type Ident = String;

#[derive(Debug)]
pub enum ExprKind {
    Var(Ident),
    Num(i64),
    True,
    False,
    Op(OpKind, Expr, Expr),
    Pred(PredKind, Expr, Expr),
    App(Expr, Expr),
    And(Expr, Expr),
    Or(Expr, Expr),
    Univ(Ident, Expr),
}
type Expr = Unique<ExprKind>;

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            ExprKind::Var(id) => write!(f, "{}", id),
            ExprKind::Op(op, e1, e2) => write!(f, "({} {} {})", e1, op, e2),
            ExprKind::Pred(pred, e1, e2) => write!(f, "({} {} {})", e1, pred, e2),
            ExprKind::App(e1, e2) => write!(f, "({} {})", e1, e2),
            ExprKind::And(e1, e2) => write!(f, "({} & {})", e1, e2),
            ExprKind::Or(e1, e2) => write!(f, "({} | {})", e1, e2),
            ExprKind::Num(x) => write!(f, "{}", x),
            ExprKind::True => write!(f, "true"),
            ExprKind::False => write!(f, "false"),
            ExprKind::Univ(id, e) => write!(f, "∀{}. {}", id, e),
        }
    }
}

impl Expr {
    pub fn mk_var(x: Ident) -> Expr {
        Expr::new(ExprKind::Var(x))
    }
    pub fn mk_num(x: i64) -> Expr {
        Expr::new(ExprKind::Num(x))
    }
    pub fn mk_true() -> Expr {
        Expr::new(ExprKind::True)
    }
    pub fn mk_false() -> Expr {
        Expr::new(ExprKind::False)
    }
    pub fn mk_op(op: OpKind, e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::Op(op, e1, e2))
    }
    pub fn mk_pred(pred: PredKind, e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::Pred(pred, e1, e2))
    }
    pub fn mk_app(e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::App(e1, e2))
    }
    pub fn mk_and(e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::And(e1, e2))
    }
    pub fn mk_or(e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::Or(e1, e2))
    }
    pub fn mk_univ(id: Ident, e: Expr) -> Expr {
        Expr::new(ExprKind::Univ(id, e))
    }
}

#[derive(Clone, Debug)]
pub struct VariableS<Ty> {
    pub id: Ident,
    pub ty: Ty,
}
impl<Ty: fmt::Display> fmt::Display for VariableS<Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id, self.ty)
    }
}

type Variable = VariableS<SimpleType>;

impl VariableS<TmpType> {
    fn new(id: Ident, ty: TmpType) -> VariableS<TmpType> {
        VariableS { id, ty }
    }
}

#[derive(Debug)]
pub struct Clause<Ty> {
    pub id: VariableS<Ty>,
    pub args: Vec<Ident>,
    pub expr: Expr,
}

impl<Ty: fmt::Display> fmt::Display for Clause<Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        for arg in self.args.iter() {
            write!(f, " {}", arg)?;
        }
        write!(f, " = {}", self.expr)
    }
}

#[derive(Debug)]
pub struct ValidityChecking {
    pub formulas: Vec<Clause<SimpleType>>,
    pub toplevel: Expr,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct TypeVariable {
    id: u64,
}

impl fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'var_{}", self.id)
    }
}

impl TypeVariable {
    fn new() -> TypeVariable {
        let id = global_counter();
        TypeVariable { id }
    }
}

#[derive(Debug)]
enum TmpTypeKind {
    Proposition,
    Integer,
    Arrow(TmpType, TmpType),
    Var(TypeVariable),
}

type TmpType = P<TmpTypeKind>;
impl fmt::Display for TmpTypeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmpTypeKind::Proposition => write!(f, "prop"),
            TmpTypeKind::Integer => write!(f, "int"),
            TmpTypeKind::Arrow(t1, t2) => write!(f, "{} -> {}", t1, t2),
            TmpTypeKind::Var(t) => write!(f, "{}", t),
        }
    }
}

impl TmpType {
    fn fresh_type_variable() -> TmpType {
        TmpType::new(TmpTypeKind::Var(TypeVariable::new()))
    }
    fn mk_arrow(arg: TmpType, ret: TmpType) -> TmpType {
        TmpType::new(TmpTypeKind::Arrow(arg, ret))
    }
    fn mk_int() -> TmpType {
        TmpType::new(TmpTypeKind::Integer)
    }
    fn mk_prop() -> TmpType {
        TmpType::new(TmpTypeKind::Proposition)
    }
    fn subst(&self, k: TypeVariable, t: TmpType) -> TmpType {
        use TmpTypeKind::*;
        match self.kind() {
            Arrow(t1, t2) => TmpType::mk_arrow(t1.subst(k.clone(), t.clone()), t2.subst(k, t)),
            Var(ty_var) if ty_var == &k => t,
            _ => self.clone(),
        }
    }
    fn occur(&self, v: &TypeVariable) -> bool {
        match self.kind() {
            TmpTypeKind::Arrow(t1, t2) => t1.occur(v) || t2.occur(v),
            TmpTypeKind::Var(x) if x == v => true,
            _ => false,
        }
    }
    fn force(&self) -> SimpleType {
        use TmpTypeKind::*;
        match self.kind() {
            Proposition => SimpleType::mk_type_prop(),
            Integer => SimpleType::mk_type_int(),
            Arrow(t1, t2) => SimpleType::mk_type_arrow(t1.force(), t2.force()),
            Var(ty_var) => {
                warn!(
                    "{} is not constrained in the process of type checking",
                    ty_var
                );
                warn!("{} is regarded as integer", ty_var);
                SimpleType::mk_type_int()
            }
        }
    }
}

#[derive(Clone, Debug)]
struct TmpTypeCache {
    int: TmpType,
    prop: TmpType,
}

impl TmpTypeCache {
    fn new() -> TmpTypeCache {
        TmpTypeCache {
            int: TmpType::mk_int(),
            prop: TmpType::mk_prop(),
        }
    }
}

impl Expr {
    pub fn from(e: parse::Expr) -> Expr {
        match e.into() {
            parse::ExprKind::Var(v) => Expr::mk_var(v),
            parse::ExprKind::Num(x) => Expr::mk_num(x),
            parse::ExprKind::True => Expr::mk_true(),
            parse::ExprKind::False => Expr::mk_false(),
            parse::ExprKind::Op(op, e1, e2) => Expr::mk_op(op, Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::Pred(p, e1, e2) => Expr::mk_pred(p, Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::App(e1, e2) => Expr::mk_app(Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::And(e1, e2) => Expr::mk_and(Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::Or(e1, e2) => Expr::mk_or(Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::Univ(x, e) => Expr::mk_univ(x, Expr::from(e)),
            _ => panic!("not implemented"),
        }
    }
}

impl Expr {
    fn append_constraints<'a>(
        &'a self,
        env: &mut Environment<'a>,
        constraints: &mut Constraints,
    ) -> TmpType {
        match self.kind() {
            ExprKind::Var(ident) => env.get(ident).expect(&format!("not found {}", ident)),
            ExprKind::Num(_) => TmpType::mk_int(),
            ExprKind::True | ExprKind::False => TmpType::mk_prop(),
            ExprKind::Op(_, e1, e2) => {
                let t1 = e1.append_constraints(env, constraints);
                let t2 = e2.append_constraints(env, constraints);
                constraints.add(t1, env.mk_int());
                constraints.add(t2, env.mk_int());
                env.mk_int()
            }
            ExprKind::Pred(_, e1, e2) => {
                let t1 = e1.append_constraints(env, constraints);
                let t2 = e2.append_constraints(env, constraints);
                constraints.add(t1, env.mk_int());
                constraints.add(t2, env.mk_int());
                env.mk_prop()
            }
            ExprKind::App(e1, e2) => {
                let t1 = e1.append_constraints(env, constraints);
                let t2 = e2.append_constraints(env, constraints);
                let ret_t = TmpType::fresh_type_variable();
                constraints.add(t1, TmpType::mk_arrow(t2, ret_t.clone()));
                ret_t
            }
            ExprKind::And(e1, e2) | ExprKind::Or(e1, e2) => {
                let t1 = e1.append_constraints(env, constraints);
                let t2 = e2.append_constraints(env, constraints);
                constraints.add(t1, env.mk_prop());
                constraints.add(t2, env.mk_prop());
                env.mk_prop()
            }
            ExprKind::Univ(_, e) => {
                let t = e.append_constraints(env, constraints);
                constraints.add(t, env.mk_prop());
                env.mk_prop()
            }
        }
    }
}

impl Clause<TmpType> {
    pub fn from(vc: parse::Clause) -> Clause<TmpType> {
        let t = TmpType::fresh_type_variable();
        let id = VariableS::new(vc.id, t);
        let expr = Expr::from(vc.expr);
        let c = Clause {
            id,
            args: vc.args,
            expr,
        };
        c
    }
    fn append_constraints<'a>(&'a self, mut env: Environment<'a>, constraints: &mut Constraints) {
        debug!("{}", &env);
        debug!("{}", self);
        let ret_ty = TmpType::fresh_type_variable();
        let mut current_ty = ret_ty.clone();
        for arg in self.args.iter() {
            let arg_ty = TmpType::fresh_type_variable();
            current_ty = TmpType::mk_arrow(arg_ty.clone(), current_ty);
            env.add(arg, arg_ty);
        }
        constraints.add(current_ty, self.id.ty.clone());
        let t = self.expr.append_constraints(&mut env, constraints);
        constraints.add(t, ret_ty)
    }
}

#[derive(Clone, Debug)]
struct Environment<'a> {
    map: HashTrieMap<&'a str, TmpType>,
    type_cache: TmpTypeCache,
}

impl fmt::Display for Environment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for (i, t) in self.map.iter() {
            write!(f, "{}: {}, ", i, t)?;
        }
        write!(f, "]")
    }
}

impl<'a> Environment<'a> {
    fn new() -> Environment<'a> {
        Environment {
            map: HashTrieMap::new(),
            type_cache: TmpTypeCache::new(),
        }
    }
    fn add(&mut self, id: &'a str, ty: TmpType) {
        self.map = self.map.insert(id, ty);
    }
    fn get(&self, id: &'a str) -> Option<TmpType> {
        self.map.get(id).cloned()
    }
    fn mk_int(&self) -> TmpType {
        self.type_cache.int.clone()
    }
    fn mk_prop(&self) -> TmpType {
        self.type_cache.prop.clone()
    }
}

fn generate_global_environment<'a>(formulas: &'a Vec<Clause<TmpType>>) -> Environment<'a> {
    let mut env = Environment::new();
    for formula in formulas.iter() {
        env.add(&formula.id.id, formula.id.ty.clone());
    }
    env
}

struct Constraint {
    left: TmpType,
    right: TmpType,
}

impl Constraint {
    fn new(left: TmpType, right: TmpType) -> Constraint {
        Constraint { left, right }
    }
    fn kind<'a>(&'a self) -> (&'a TmpTypeKind, &'a TmpTypeKind) {
        let left = self.left.kind();
        let right = self.right.kind();
        (left, right)
    }
    fn subst(&self, x: TypeVariable, t: TmpType) -> Constraint {
        Constraint::new(self.left.subst(x.clone(), t.clone()), self.right.subst(x, t))
    }
}

#[derive(Debug)]
enum TypeError {
    Error,
    OccurenceCheck,
}

struct Constraints(Vec<Constraint>);
impl Constraints {
    fn new() -> Constraints {
        Constraints(Vec::new())
    }
    fn add(&mut self, left: TmpType, right: TmpType) {
        self.0.push(Constraint::new(left, right))
    }
    fn subst(&mut self, x: TypeVariable, t: TmpType) {
        let x = &x;
        let t = &t;
        for c in self.0.iter_mut() {
            *c = c.subst(x.clone(), t.clone())
        }
    }
    fn solve(&mut self) -> Result<TySubst, TypeError> {
        let mut ty_subst = TySubst::new();
        loop {
            use TmpTypeKind::*;
            match self.0.pop() {
                None => break Ok(ty_subst),
                Some(c) => {
                    let rhs = c.right.clone();
                    debug!("unify {} = {}", c.left, c.right);
                    match c.kind() {
                        (Proposition, Proposition) | (Integer, Integer) => {}
                        (Var(x), Var(y)) if x == y => {}
                        (Var(x), _) => {
                            if rhs.occur(x) {
                                break Err(TypeError::OccurenceCheck);
                            }
                            self.subst(x.clone(), rhs.clone());
                            ty_subst.add(x.clone(), rhs);
                        }
                        (_, Var(_)) => {
                            let lhs = c.left;
                            let rhs = c.right;
                            self.add(rhs, lhs);
                        }
                        (Arrow(t1, s1), Arrow(t2, s2)) => {
                            self.add(t1.clone(), t2.clone());
                            self.add(s1.clone(), s2.clone());
                        },
                        _ => {
                            debug!("tried to unify {} = {}", c.left, c.right);
                            break Err(TypeError::Error)
                        }
                    }
                }
            }
        }
    }
}

struct TySubst(HashMap<TypeVariable, TmpType>);

impl TySubst {
    fn new() -> TySubst {
        TySubst(HashMap::new())
    }
    fn add(&mut self, k: TypeVariable, t: TmpType) {
        {
            let k = &k;
            let t = &t;
            for (_, y) in self.0.iter_mut() {
                *y = y.subst(k.clone(), t.clone());
            }
        }
        self.0.insert(k, t);
    }
    fn subst(&self, t: TmpType) -> SimpleType {
        match t.kind() {
            TmpTypeKind::Proposition => SimpleType::mk_type_prop(),
            TmpTypeKind::Integer => SimpleType::mk_type_int(),
            TmpTypeKind::Arrow(t1, t2) => {
                SimpleType::mk_type_arrow(self.subst(t1.clone()), self.subst(t2.clone()))
            }
            TmpTypeKind::Var(ty_var) => match self.0.get(ty_var) {
                Some(t) => t.force(),
                None => panic!("substitution of type variable failed"),
            },
        }
    }
}

fn typing(formulas: Vec<parse::Clause>) -> Vec<Clause<SimpleType>> {
    let formulas = formulas
        .into_iter()
        .map(|x| Clause::<TmpType>::from(x))
        .collect();
    let ty_subst = {
        let env = generate_global_environment(&formulas);
        let mut constraints = Constraints::new();
        for clause in formulas.iter() {
            clause.append_constraints(env.clone(), &mut constraints);
        }
        constraints.solve().unwrap()
    };
    formulas
        .into_iter()
        .map(|clause| {
            let ty = ty_subst.subst(clause.id.ty);
            let id = VariableS {
                id: clause.id.id,
                ty: ty,
            };
            Clause {
                id,
                expr: clause.expr,
                args: clause.args,
            }
        })
        .collect()
}

impl From<parse::Problem> for ValidityChecking {
    fn from(vc: parse::Problem) -> ValidityChecking {
        match vc {
            parse::Problem::NuHFLZValidityChecking(mut vc) => {
                // adhoc
                vc.formulas.push(parse::Clause {
                    id: "!!TOPLEVEL!!".to_string(),
                    args: Vec::new(),
                    expr: vc.toplevel,
                    fixpoint: parse::Fixpoint::Greatest,
                });
                let mut formulas = typing(vc.formulas);
                let toplevel = formulas.pop().unwrap().expr;
                ValidityChecking { formulas, toplevel }
            }
        }
    }
}
