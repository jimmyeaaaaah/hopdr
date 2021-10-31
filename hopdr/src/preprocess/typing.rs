use rpds::HashTrieMap;
use std::{collections::HashMap, fmt};

use super::hes::{Clause as ClauseS, Expr, ExprKind, ValidityChecking, VariableS};
use crate::parse;
use crate::util::{global_counter, P};
use crate::{formula::Type as SimpleType, parse::Ident};

type Clause<Ty> = ClauseS<parse::Ident, Ty>;
type ExprTmp = Expr<parse::Ident, TmpType>;
type ExprSimpleType = Expr<parse::Ident, SimpleType>;

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
            TmpTypeKind::Arrow(t1, t2) => write!(f, "({} -> {})", t1, t2),
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

impl VariableS<parse::Ident, TmpType> {
    fn from_ident(id: String) -> VariableS<parse::Ident, TmpType> {
        let t = TmpType::fresh_type_variable();
        VariableS::new(Ident::new(id), t)
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

impl ExprTmp {
    pub fn from(e: parse::Expr) -> ExprTmp {
        match e.into() {
            parse::ExprKind::Var(v) => Expr::mk_var(Ident::new(v)),
            parse::ExprKind::Num(x) => Expr::mk_num(x),
            parse::ExprKind::True => Expr::mk_true(),
            parse::ExprKind::False => Expr::mk_false(),
            parse::ExprKind::Op(op, e1, e2) => {
                Expr::mk_op(op, ExprTmp::from(e1), ExprTmp::from(e2))
            }
            parse::ExprKind::Pred(p, e1, e2) => {
                Expr::mk_pred(p, ExprTmp::from(e1), ExprTmp::from(e2))
            }
            parse::ExprKind::App(e1, e2) => Expr::mk_app(ExprTmp::from(e1), ExprTmp::from(e2)),
            parse::ExprKind::And(e1, e2) => Expr::mk_and(ExprTmp::from(e1), ExprTmp::from(e2)),
            parse::ExprKind::Or(e1, e2) => Expr::mk_or(ExprTmp::from(e1), ExprTmp::from(e2)),
            parse::ExprKind::Univ(x, e) => {
                let id = VariableS::from_ident(x);
                Expr::mk_univ(id, ExprTmp::from(e))
            }
            _ => panic!("not implemented"),
        }
    }
    fn append_constraints<'a>(
        &'a self,
        env: &mut Environment<'a>,
        constraints: &mut Constraints,
    ) -> TmpType {
        match self.kind() {
            ExprKind::Var(ident) => env
                .get(ident)
                .unwrap_or_else(|| panic!("not found {}", ident)),
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
    fn ty_subst(self, subst: &TySubst) -> ExprSimpleType {
        match self.into() {
            ExprKind::Var(i) => ExprSimpleType::mk_var(i),
            ExprKind::Num(v) => ExprSimpleType::mk_num(v),
            ExprKind::True => ExprSimpleType::mk_true(),
            ExprKind::False => ExprSimpleType::mk_false(),
            ExprKind::Op(o, x, y) => {
                let x = x.ty_subst(subst);
                let y = y.ty_subst(subst);
                ExprSimpleType::mk_op(o, x, y)
            }
            ExprKind::Pred(p, x, y) => {
                let x = x.ty_subst(subst);
                let y = y.ty_subst(subst);
                ExprSimpleType::mk_pred(p, x, y)
            }
            ExprKind::App(x, y) => {
                let x = x.ty_subst(subst);
                let y = y.ty_subst(subst);
                ExprSimpleType::mk_app(x, y)
            }
            ExprKind::And(x, y) => {
                let x = x.ty_subst(subst);
                let y = y.ty_subst(subst);
                ExprSimpleType::mk_and(x, y)
            }
            ExprKind::Or(x, y) => {
                let x = x.ty_subst(subst);
                let y = y.ty_subst(subst);
                ExprSimpleType::mk_or(x, y)
            }
            ExprKind::Univ(v, x) => {
                let x = x.ty_subst(subst);
                let ty = subst.subst(v.ty);
                let v = VariableS::new(v.id, ty);
                ExprSimpleType::mk_univ(v, x)
            }
        }
    }
}
impl Clause<TmpType> {
    pub fn from(vc: parse::Clause) -> Clause<TmpType> {
        let id = VariableS::from_ident(vc.id);
        let expr = ExprTmp::from(vc.expr);

        Clause {
            id,
            args: vc.args.into_iter().map(Ident::new).collect(),
            expr,
        }
    }
    fn append_constraints<'a>(&'a self, mut env: Environment<'a>, constraints: &mut Constraints) {
        let ret_ty = TmpType::fresh_type_variable();
        let mut current_ty = ret_ty.clone();
        for arg in self.args.iter().rev() {
            let arg_ty = TmpType::fresh_type_variable();
            current_ty = TmpType::mk_arrow(arg_ty.clone(), current_ty);
            env.add(arg, arg_ty);
        }
        constraints.add(current_ty, self.id.ty.clone());
        debug!("{}", &env);
        debug!("{}", self);
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

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} = {}", self.left, self.right)
    }
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
        Constraint::new(
            self.left.subst(x.clone(), t.clone()),
            self.right.subst(x, t),
        )
    }
}

#[derive(Debug)]
enum TypeError {
    Error,
    OccurenceCheck,
}

struct Constraints(Vec<Constraint>);

impl fmt::Display for Constraints {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "[constraints]")?;
        for c in self.0.iter() {
            writeln!(f, "{}", c)?;
        }
        writeln!(f)
    }
}

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
                        }
                        _ => {
                            debug!("tried to unify {} = {}", c.left, c.right);
                            break Err(TypeError::Error);
                        }
                    }
                }
            }
        }
    }
}

#[derive(Debug)]
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

pub fn typing(
    mut formulas: Vec<parse::Clause>,
    toplevel: parse::Expr,
) -> ValidityChecking<parse::Ident, SimpleType> {
    // adhoc
    formulas.push(parse::Clause {
        id: "!!TOPLEVEL!!".to_string(),
        args: Vec::new(),
        expr: toplevel,
        fixpoint: parse::Fixpoint::Greatest,
    });

    let formulas = formulas.into_iter().map(Clause::<TmpType>::from).collect();
    let ty_subst = {
        let env = generate_global_environment(&formulas);
        let mut constraints = Constraints::new();
        for clause in formulas.iter() {
            clause.append_constraints(env.clone(), &mut constraints);
        }
        debug!("{}", constraints);
        constraints.solve().unwrap()
    };
    let mut formulas: Vec<Clause<SimpleType>> = formulas
        .into_iter()
        .map(|clause| {
            let ty = ty_subst.subst(clause.id.ty);
            let id = VariableS {
                id: clause.id.id,
                ty,
            };
            let expr = clause.expr.ty_subst(&ty_subst);
            Clause {
                id,
                expr,
                args: clause.args,
            }
        })
        .collect();

    let toplevel = formulas.pop().unwrap().expr;
    ValidityChecking {
        clauses: formulas,
        toplevel,
    }
}
