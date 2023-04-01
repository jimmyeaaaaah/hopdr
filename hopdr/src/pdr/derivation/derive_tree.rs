use super::super::rtype::Refinement;
use super::tree::*;
use super::{Atom, Ty, G};
use crate::pdr::rtype::TauKind;
use crate::solver;
use crate::util::Pretty;
use crate::{formula::*, pdebug};

use rpds::Stack;

#[derive(Clone, Debug)]
pub(super) struct DeriveNode {
    // Γ ⊢ ψ : τ
    // Γ is omitted
    pub rule: Rule,
    pub expr: G,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub enum Rule {
    Conjoin,
    Disjoin,
    Var,
    Univ(Ident),
    IAbs(Ident),
    Abs(Vec<Ty>),
    IApp(Op),
    App,
    Subsumption,
    Atom,
}

impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Rule::Conjoin => "Conj",
            Rule::Disjoin => "Disj",
            Rule::Var => "Var",
            Rule::Univ(_) => "Univ",
            Rule::IAbs(_) => "IAbs",
            Rule::Abs(_) => "Abs",
            Rule::IApp(_) => "IApp",
            Rule::App => "App",
            Rule::Subsumption => "Sub",
            Rule::Atom => "Atom",
        };
        write!(f, "{}", s)
    }
}

impl crate::util::printer::Pretty for DeriveNode {
    fn pretty<'b, D, A>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        al.text("(")
            .append(self.rule.to_string())
            .append(") |- ")
            .append(
                self.expr
                    .pretty(al, config)
                    .append(al.line())
                    .append(":")
                    .append(al.line())
                    .append(self.ty.pretty(al, config))
                    .hang(2)
                    .group(),
            )
    }
}

fn reset_expr_for_subsumption(expr: &mut G) {
    expr.aux.level_arg = Stack::new();
    expr.aux.id = Ident::fresh();
}

impl DeriveNode {
    fn conjoin(expr: G, left: &Self, right: &Self) -> Self {
        let rule = Rule::Conjoin;
        let ty = match (left.ty.kind(), right.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Ty::mk_prop_ty(Atom::mk_conj(c1.clone(), c2.clone()))
            }
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", left.ty, right.ty),
        };
        DeriveNode { rule, expr, ty }
    }
    fn disjoin(expr: G, left: &Self, right: &Self) -> Self {
        let rule = Rule::Disjoin;
        let ty = match (left.ty.kind(), right.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Ty::mk_prop_ty(Atom::mk_disj(c1.clone(), c2.clone()))
            }
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", left.ty, right.ty),
        };
        DeriveNode { rule, expr, ty }
    }
    fn quantify(expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::Univ(*ident);
        let ty = match node.ty.kind() {
            TauKind::Proposition(c1) => Ty::mk_prop_ty(Atom::mk_quantifier_int(
                crate::formula::QuantifierKind::Universal,
                *ident,
                c1.clone(),
            )),
            TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
        };
        DeriveNode { rule, expr, ty }
    }
    fn iarrow(expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::IAbs(*ident);
        let ty = Ty::mk_iarrow(*ident, node.ty.clone());
        DeriveNode { rule, expr, ty }
    }
    fn arrow(expr: G, node: &Self, ts: Vec<Ty>) -> Self {
        let rule = Rule::Abs(ts.clone());
        let ty = Ty::mk_arrow(ts, node.ty.clone());
        DeriveNode { rule, expr, ty }
    }
    fn iapp(expr: G, node: &Self, op: &Op) -> Self {
        let rule = Rule::IApp(op.clone());
        let ty = match node.ty.kind() {
            TauKind::IArrow(x, t2) => t2.subst(x, op),
            _ => panic!("fatal"),
        };
        DeriveNode { rule, expr, ty }
    }
    fn subsumption(node: &Self, ty: Ty) -> Self {
        let rule = Rule::Subsumption;
        let mut expr = node.expr.clone();
        // reset the information
        reset_expr_for_subsumption(&mut expr);
        DeriveNode { rule, expr, ty }
    }
    fn app(expr: G, pred_node: &Self) -> Self {
        let rule = Rule::App;
        let ty = match pred_node.ty.kind() {
            TauKind::Arrow(_, rt) => rt.clone(),
            TauKind::Proposition(_) | TauKind::IArrow(_, _) => {
                panic!("app rule is used for a wrong derivation")
            }
        };
        DeriveNode { rule, expr, ty }
    }
}

#[derive(Clone)]
pub(super) struct Derivation {
    tree: Tree<DeriveNode>,
    pub coefficients: Stack<Ident>,
}

impl crate::util::printer::Pretty for Derivation {
    fn pretty<'b, D, A>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.tree.pretty(al, config)
    }
}

fn concat_stacks<'a, T: 'a + Clone, I>(stacks: I) -> Stack<T>
where
    I: Iterator<Item = &'a Stack<T>>,
{
    let mut s = Stack::new();
    for stack in stacks {
        for x in stack.iter() {
            s.push_mut(x.clone());
        }
    }
    s
}

impl Derivation {
    pub fn get_node_by_id<'a>(&'a self, node_id: ID) -> Node<'a, DeriveNode> {
        self.tree.get_node_by_id(node_id)
    }
    pub fn get_nodes_by_goal_id<'a>(
        &'a self,
        id: &'a Ident,
    ) -> impl Iterator<Item = Node<'a, DeriveNode>> + 'a {
        self.tree.filter(move |n| n.expr.aux.id == *id)
    }
    pub fn get_node_closest_to_root_by_goal_id<'a>(
        &'a self,
        id: &'a Ident,
    ) -> Option<Node<'a, DeriveNode>> {
        fn inner<'a>(
            d: &'a Derivation,
            id: &Ident,
            cur: ID,
            level: usize,
        ) -> Option<(Node<'a, DeriveNode>, usize)> {
            let node = d.tree.get_node_by_id(cur);
            if node.item.expr.aux.id == *id {
                Some((node, level))
            } else {
                let mut mx = None;
                for child in d.tree.get_children(node) {
                    match (inner(d, id, child.id, level + 1), &mx) {
                        (Some((n, level)), Some((_, cur))) if level < *cur => mx = Some((n, level)),
                        (Some((n, level)), None) => mx = Some((n, level)),
                        (_, _) => (),
                    }
                }
                mx
            }
        }
        inner(self, id, self.tree.root().id, 0).map(|(n, _)| n)
    }
    pub fn get_types_by_id<'a>(&'a self, id: &'a Ident) -> impl Iterator<Item = Ty> + 'a {
        self.tree
            .filter(move |n| n.expr.aux.id == *id)
            .map(|n| n.item.ty.clone())
    }
    fn get_node_by_level<'a>(
        &'a self,
        node_id: ID,
        level: &'a usize,
    ) -> impl Iterator<Item = Node<'a, DeriveNode>> + 'a {
        let node = self.tree.get_node_by_id(node_id);
        self.tree.filter_descendants(node, move |n| {
            n.expr.aux.level_arg.iter().any(|arg| arg == level)
        })
    }
    pub fn get_types_by_level<'a>(
        &'a self,
        node_id: ID,
        level: &'a usize,
    ) -> impl Iterator<Item = Ty> + 'a {
        self.get_node_by_level(node_id, level)
            .map(|n| n.item.ty.clone())
    }
    pub fn get_derivations_by_level<'a>(
        &'a self,
        node_id: ID,
        level: &'a usize,
    ) -> impl Iterator<Item = Self> + 'a {
        let node = self.tree.get_node_by_id(node_id);
        self.tree
            .filter_descendants(node, move |n| {
                n.expr.aux.level_arg.iter().any(|arg| arg == level)
            })
            .map(move |n| self.sub_derivation(&n.id))
    }

    pub fn rule_atom(expr: G, ty: Ty) -> Self {
        let rule = Rule::Atom;
        let node = DeriveNode { rule, expr, ty };
        Self {
            tree: Tree::singleton(node),
            coefficients: Stack::new(),
        }
    }

    pub fn rule_var(expr: G, ty: Ty, coefficients: Stack<Ident>) -> Self {
        let rule = Rule::Var;
        let node = DeriveNode { rule, expr, ty };
        Self {
            tree: Tree::singleton(node),
            coefficients,
        }
    }

    fn rule_one_arg_inner(node: DeriveNode, d: Self) -> Self {
        Self {
            tree: Tree::tree_with_child(node, d.tree),
            ..d
        }
    }

    fn rule_two_arg_inner(node: DeriveNode, d1: Self, d2: Self) -> Self {
        Self {
            tree: Tree::tree_with_two_children(node, d1.tree, d2.tree),
            coefficients: concat_stacks([d1.coefficients, d2.coefficients].iter()),
        }
    }

    fn rule_multiples<I>(node: DeriveNode, derivations: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let mut tree = Tree::singleton(node);
        let (_, coefficients) = derivations.fold((&mut tree, Stack::new()), |(t, coefs), d| {
            pdebug!("rule_multiples");
            pdebug!(d.tree);
            t.append_children(d.tree);
            let coefficients = concat_stacks([coefs, d.coefficients].iter());
            (t, coefficients)
        });
        Self { tree, coefficients }
    }
    pub fn rule_conjoin(expr: G, d1: Self, d2: Self) -> Self {
        let root = DeriveNode::conjoin(expr, d1.tree.root().item, d2.tree.root().item);
        Self::rule_two_arg_inner(root, d1, d2)
    }
    pub fn rule_disjoin(expr: G, d1: Self, d2: Self) -> Self {
        let root = DeriveNode::disjoin(expr, d1.tree.root().item, d2.tree.root().item);
        Self::rule_two_arg_inner(root, d1, d2)
    }
    pub fn rule_quantifier(expr: G, d: Self, x: &Ident) -> Self {
        let root = DeriveNode::quantify(expr, d.tree.root().item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_iarrow(expr: G, d: Self, x: &Ident) -> Self {
        let root = DeriveNode::iarrow(expr, d.tree.root().item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_arrow(expr: G, d: Self, tys: Vec<Ty>) -> Self {
        let root = DeriveNode::arrow(expr, d.tree.root().item, tys);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_iapp(expr: G, d: Self, o: &Op) -> Self {
        let root = DeriveNode::iapp(expr, d.tree.root().item, o);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_subsumption(d: Self, ty: Ty) -> Self {
        let child = d.tree.root();
        let s = child.item.ty.clone();
        let constraint = Ty::check_subtype(&Atom::mk_true(), &s, &ty);
        let root = DeriveNode::subsumption(child.item, ty);
        let mut d = Self::rule_one_arg_inner(root, d);
        d
    }
    pub fn rule_app<I>(expr: G, d1: Self, args: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let root = DeriveNode::app(expr, &d1.tree.root().item);
        Self::rule_multiples(root, std::iter::once(d1).chain(args))
    }
    pub fn update_with_model(&mut self, m: &solver::Model) {
        self.tree.iter_mut(|item| {
            let mut ty = item.ty.clone();
            for (var, val) in m.model.iter() {
                ty = ty.subst(var, &Op::mk_const(*val));
            }
            item.ty = ty;
        });
    }
    pub fn root_ty(&self) -> &Ty {
        &self.tree.root().item.ty
    }
    pub fn node_id_to_ty<'a>(&'a self, id: &'a ID) -> &'a Ty {
        &id.to_item(&self.tree).ty
    }
    /// get subderivation of `id`
    fn sub_derivation<'a>(&'a self, id: &'a ID) -> Self {
        let node = id.to_node(&self.tree);
        let tree = self.tree.subtree(node);
        // Assume constraints and coeffcients are saved in the main derivation, so
        // we omit them here.
        Derivation {
            tree,
            coefficients: Stack::new(),
        }
    }
    // Assume a derivation tree like
    //        π          ⋮
    //   ----------  ---------
    //   P x: *<c>   Q x: *<c2>
    //   ------------------------
    //     P x /\ Q x: *<c/\c2>
    // and (\y. y /\ Q x) (P x) -> P x /\ Q x
    // then, by using this function, we can create a derivation tree like
    //                   ⋮
    //   ----------  ---------
    //   y: *<c>   Q x: *<c2>
    //   ------------------------
    //     P x /\ Q x: *<c/\c2>
    // and returns [π]
    pub fn replace_derivation_at_level_with_var(
        &mut self,
        node_id: ID,
        level: &usize,
        var: Ident,
    ) -> Vec<Self> {
        let var_expr = G::mk_var(var);
        let mut tree = self.tree.clone();
        let mut derivations = vec![];
        pdebug!("tries to replace");
        pdebug!(self.tree);
        for node in self
            .tree
            .filter_descendants(self.tree.get_node_by_id(node_id), move |n| {
                n.expr.aux.level_arg.iter().any(|arg| arg == level)
            })
        {
            let d = Self::rule_var(var_expr.clone(), node.item.ty.clone(), Stack::new());
            let sub_derivation = self.sub_derivation(&node.id);
            derivations.push(sub_derivation);
            pdebug!("replace_derivation_at_level_with_var var: ", var);
            pdebug!("node: ", node.item);
            pdebug!(tree);
            tree = tree.replace_subtree(node, d.tree);
        }
        self.tree = tree;
        derivations
    }
    // traverse sub derivation from `from` and deref `id` and replace `id` with `old_id`
    pub fn traverse_and_recover_int_var(&mut self, from: ID, id: &Ident, old_id: &Ident) {
        self.tree.update_children(from, |node| {
            let ty = node.ty.clone();
            let new_ty = ty.deref_ptr(id).rename(id, old_id);
            node.ty = new_ty;
        });
    }
    pub fn rename_int_var(&mut self, from: ID, old_id: &Ident, new_id: &Ident) {
        self.tree.update_children(from, |node| {
            let ty = node.ty.clone();
            let new_ty = ty.rename(old_id, new_id);
            node.ty = new_ty;
        })
    }
    fn update_parents(
        &mut self,
        target_id: ID,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        let r = self
            .tree
            .update_parent_until(target_id, |n, children, prev| {
                debug!("updating parents... {}", n.pretty_display());
                let prev = match prev {
                    Some(prev) => prev,
                    None => return (false, n.clone()),
                };
                let ty = match &n.rule {
                    Rule::Conjoin => {
                        let cnstr = children
                            .iter()
                            .map(|child| match child.ty.kind() {
                                TauKind::Proposition(c) => c.clone(),
                                TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => {
                                    panic!("not conjoin")
                                }
                            })
                            .fold(Atom::mk_true(), Atom::mk_conj);
                        Ty::mk_prop_ty(cnstr)
                    }
                    Rule::Disjoin => {
                        let cnstr = children
                            .iter()
                            .map(|child| match child.ty.kind() {
                                TauKind::Proposition(c) => c.clone(),
                                TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => {
                                    panic!("not conjoin")
                                }
                            })
                            .fold(Atom::mk_false(), Atom::mk_disj);
                        Ty::mk_prop_ty(cnstr)
                    }
                    Rule::Univ(x) => {
                        assert_eq!(children.len(), 1);
                        let cnstr = match children[0].ty.kind() {
                            TauKind::Proposition(c) => c.clone(),
                            TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("not conjoin"),
                        };
                        Ty::mk_prop_ty(Atom::mk_univ_int(*x, cnstr))
                    }
                    Rule::IAbs(x) => {
                        assert_eq!(children.len(), 1);
                        Ty::mk_iarrow(*x, children[0].ty.clone())
                    }
                    Rule::Abs(x) => {
                        assert_eq!(children.len(), 1);
                        Ty::mk_arrow(x.clone(), children[0].ty.clone())
                    }
                    Rule::IApp(o) => {
                        assert_eq!(children.len(), 1);
                        match children[0].ty.kind() {
                            TauKind::IArrow(x, t) => t.subst(&x, &o),
                            _ => panic!("program error"),
                        }
                    }
                    Rule::App => {
                        //assert_eq!(children.len(), 2);
                        // todo?
                        assert!(children.len() >= 2);
                        let node = prev;

                        // case1: the updated child was in pred
                        if node.expr.aux.id == children[0].expr.aux.id {
                            let pred = children[0].ty.clone();
                            let body_tys =
                                children[1..].iter().map(|child| child.ty.clone()).collect();
                            let (arg_ty, ret_ty) = match pred.kind() {
                                TauKind::Arrow(arg, t) => (arg.clone(), t.clone()),
                                TauKind::Proposition(_) | TauKind::IArrow(_, _) => {
                                    panic!("program error")
                                }
                            };
                            super::Context::append_clauses_by_subst(
                                clauses,
                                &body_tys,
                                &arg_ty,
                                &pred.rty_no_exists(),
                            );
                            ret_ty.clone()
                        }
                        // case2: the updated child was in body
                        else {
                            // insert subsumption here
                            for child in children[1..].iter() {
                                if node.expr.aux.id == child.expr.aux.id {
                                    todo!();
                                    return (true, n.clone());
                                }
                            }
                            panic!("program error")
                        }
                    }
                    Rule::Subsumption => {
                        assert_eq!(children.len(), 1);
                        return (true, n.clone());
                    }
                    Rule::Var | Rule::Atom => panic!("program error"),
                };
                let n = DeriveNode {
                    ty,
                    rule: n.rule.clone(),
                    expr: n.expr.clone(),
                };
                (false, n)
            });
        let id = match r {
            Some(n) => n.id,
            None => {
                panic!("parent not found")
            }
        };
        // due to the lifetime reason...
        let n = self.tree.get_node_by_id(id);
        // append constraints here
        assert!(matches!(n.item.rule, Rule::Subsumption));

        let ty2 = n.item.ty.clone();

        let children: Vec<_> = self.tree.get_children(n).collect();
        assert_eq!(children.len(), 1);
        let ty1 = children[0].item.ty.clone();
        // ty1 <: ty2
        super::Context::append_clauses_by_subst(
            clauses,
            &vec![ty1.clone()],
            &vec![ty2],
            &Atom::mk_true(),
        );
    }
    fn update_expr_inner(&mut self, node_id: ID, expr: &G) {
        self.tree.update_node_by_id(node_id).expr = expr.clone();
        let children: Vec<_> = self
            .tree
            .get_children(node_id.to_node(&self.tree))
            .map(|child| child.id)
            .collect();
        let n = self.get_node_by_id(node_id).item;
        match n.rule {
            Rule::Conjoin => {
                let (g1, g2) = expr.conj();
                assert_eq!(children.len(), 2);
                self.update_expr_inner(children[0], g1);
                self.update_expr_inner(children[1], g2);
            }
            Rule::Disjoin => {
                let (g1, g2) = expr.disj();
                assert_eq!(children.len(), 2);
                self.update_expr_inner(children[0], g1);
                self.update_expr_inner(children[1], g2);
            }
            Rule::Var => {
                debug_assert!(expr.is_var());
            }
            Rule::Atom => (),
            Rule::Univ(x) => {
                let (y, g) = expr.univ();
                assert_eq!(x, y.id);
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g);
            }
            Rule::IAbs(x) => {
                let (y, g) = expr.abs();
                //assert_eq!(x, y.id);
                debug_assert!(y.ty.is_int());
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g);
            }
            Rule::Abs(_) => {
                let (_, g) = expr.abs();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g);
            }
            Rule::IApp(_) => {
                let (x, y) = expr.app();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], x);
                for i in 1..children.len() {
                    self.update_expr_inner(children[i], y);
                }
            }
            Rule::App => {
                let (x, y) = expr.app();
                assert!(children.len() >= 2);
                self.update_expr_inner(children[0], x);
                for i in 1..children.len() {
                    self.update_expr_inner(children[i], y);
                }
            }
            Rule::Subsumption => {
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], &expr);

                let mut expr = expr.clone();
                reset_expr_for_subsumption(&mut expr);
                self.tree.update_node_by_id(node_id).expr = expr.clone();
            }
        }
    }
    fn update_expr(&mut self, expr: &G) {
        let root_id = self.tree.root().id;
        self.update_expr_inner(root_id, expr)
    }
    fn finalize_subject_expansion(
        &mut self,
        node_id: ID,
        pred_ty: &Ty,
        reduction: &super::Reduction,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        let target_node = self
            .get_node_closest_to_root_by_goal_id(&reduction.app_expr.aux.id)
            .unwrap()
            .id;
        pdebug!("derivation before updating parents");
        pdebug!(self);

        self.update_parents(target_node, clauses);
        // finally replace the expressions in the derivation with the expr before the reduction
        pdebug!("derivation before updating exprs");
        pdebug!(self);
        self.update_expr(&reduction.before_reduction)
    }
    pub fn subject_expansion_int(
        &mut self,
        node_id: ID,
        reduction: &super::Reduction,
        pred_ty: &Ty,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        let (pred_arg_ident, pred_body_ty) = match pred_ty.kind() {
            TauKind::IArrow(x, t) => (*x, t.clone()),
            TauKind::Proposition(_) | TauKind::Arrow(_, _) => panic!("fail"),
        };

        let (t, node_id) = self.tree.insert_partial_tree(node_id, |body| {
            let body = Derivation {
                tree: body,
                coefficients: Stack::new(),
            };

            let tmp_deriv = Derivation::rule_subsumption(body, pred_body_ty);

            let tmp_deriv =
                Derivation::rule_iarrow(reduction.predicate.clone(), tmp_deriv, &pred_arg_ident);

            let op: Op = reduction.reduction_info.arg.clone().into();
            let app_deriv = Derivation::rule_iapp(reduction.app_expr.clone(), tmp_deriv, &op);
            app_deriv.tree
        });

        self.tree = t;
        self.finalize_subject_expansion(node_id, pred_ty, reduction, clauses);
    }
    pub fn subject_expansion_pred(
        &mut self,
        node_id: ID,
        arg_derivations: Vec<Self>,
        reduction: &super::Reduction,
        pred_ty: &Ty,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        let (arg_tys, pred_body_ty) = match pred_ty.kind() {
            TauKind::Arrow(tys, t) => (tys, t.clone()),
            TauKind::Proposition(_) | TauKind::IArrow(_, _) => panic!("fail"),
        };

        let (t, node_id) = self.tree.insert_partial_tree(node_id, |body| {
            let body = Derivation {
                tree: body,
                coefficients: Stack::new(),
            };

            let tmp_deriv = Derivation::rule_subsumption(body, pred_body_ty);

            let tmp_deriv =
                Derivation::rule_arrow(reduction.predicate.clone(), tmp_deriv, arg_tys.clone());
            let app_deriv = Derivation::rule_app(
                reduction.app_expr.clone(),
                tmp_deriv,
                arg_derivations.into_iter(),
            );

            app_deriv.tree
        });

        self.tree = t;
        self.finalize_subject_expansion(node_id, pred_ty, reduction, clauses);
    }

    pub fn collect_constraints<'a>(&'a self) -> impl Iterator<Item = Atom> + 'a {
        // collect all subsumptions
        self.tree
            .filter(|n| matches!(n.rule, Rule::Subsumption))
            .map(move |n| {
                let ty = n.item.ty.clone();
                let children: Vec<_> = self.tree.get_children(n).collect();
                assert_eq!(children.len(), 1);
                let child = &children[0];
                Ty::check_subtype(&Atom::mk_true(), &child.item.ty, &ty)
            })
    }
}
