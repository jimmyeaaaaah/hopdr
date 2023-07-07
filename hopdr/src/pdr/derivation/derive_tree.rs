use std::collections::{HashMap, HashSet};

use super::tree::*;
use super::{Atom, Ty, G};
use crate::pdebug;
use crate::pdr::rtype::{TBot, Tau, TauKind};
use crate::solver;
use crate::util::Pretty;
use crate::{formula::*, highlight};

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
    Univ,
    IAbs,
    Abs(Vec<Ty>),
    IApp(Op),
    App,
    Subsumption,
    Equivalence,
    Atom,
    Poly(Ident),
}

impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Rule::Conjoin => "Conj",
            Rule::Disjoin => "Disj",
            Rule::Var => "Var",
            Rule::Univ => "Univ",
            Rule::IAbs => "IAbs",
            Rule::Abs(_) => "Abs",
            Rule::IApp(_) => "IApp",
            Rule::App => "App",
            Rule::Subsumption => "Sub",
            Rule::Equivalence => "Equi",
            Rule::Atom => "Atom",
            Rule::Poly(x) => "Poly",
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
        let rule = Rule::Univ;
        let ty = match node.ty.kind() {
            TauKind::Proposition(c1) => Ty::mk_prop_ty(Atom::mk_quantifier_int(
                crate::formula::QuantifierKind::Universal,
                *ident,
                c1.clone(),
            )),
            TauKind::PTy(_, _) | TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
        };
        DeriveNode { rule, expr, ty }
    }
    fn iarrow(expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::IAbs;
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
    fn equivalence(node: &Self, ty: Ty) -> Self {
        let rule = Rule::Equivalence;
        let expr = node.expr.clone();
        DeriveNode { rule, expr, ty }
    }
    fn poly(node: &Self, x: Ident) -> Self {
        let rule = Rule::Poly(x);
        let expr = node.expr.clone();
        let ty = Ty::mk_poly_ty(x, node.ty.clone());
        DeriveNode { rule, expr, ty }
    }
    fn app(expr: G, pred_node: &Self) -> Self {
        let rule = Rule::App;
        let ty = match pred_node.ty.kind() {
            TauKind::Arrow(_, rt) => rt.clone(),
            TauKind::PTy(_, _) | TauKind::Proposition(_) | TauKind::IArrow(_, _) => {
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
    #[allow(dead_code)]
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
    #[allow(dead_code)]
    pub fn get_types_by_level<'a>(
        &'a self,
        node_id: ID,
        level: &'a usize,
    ) -> impl Iterator<Item = Ty> + 'a {
        self.get_node_by_level(node_id, level)
            .map(|n| n.item.ty.clone())
    }
    #[allow(dead_code)]
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
        let root = DeriveNode::subsumption(child.item, ty);
        let d = Self::rule_one_arg_inner(root, d);
        d
    }
    pub fn rule_equivalence(mut d: Self, ty: Ty) -> Self {
        let child_id = d.tree.root().id;
        let root = DeriveNode::equivalence(d.tree.root().item, ty);
        reset_expr_for_subsumption(&mut d.tree.update_node_by_id(child_id).expr);
        let d = Self::rule_one_arg_inner(root, d);
        d
    }
    pub fn rule_app<I>(expr: G, d1: Self, args: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let root = DeriveNode::app(expr, &d1.tree.root().item);
        Self::rule_multiples(root, std::iter::once(d1).chain(args))
    }
    pub fn rule_polymorphic_type(d: Self, x: Ident) -> Self {
        let item = d.tree.root().item;
        let root = DeriveNode::poly(item, x);
        Self::rule_one_arg_inner(root, d)
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
        for node in self
            .tree
            .filter_descendants(self.tree.get_node_by_id(node_id), move |n| {
                n.expr.aux.level_arg.iter().any(|arg| arg == level)
            })
        {
            let d = Self::rule_var(var_expr.clone(), node.item.ty.clone(), Stack::new());
            let sub_derivation = self.sub_derivation(&node.id);
            derivations.push(sub_derivation);
            tree = tree.replace_subtree(node, d.tree);
        }
        self.tree = tree;
        derivations
    }

    fn update_parents(&mut self, target_id: ID) {
        fn update_app_branchs(t: &mut Tree<DeriveNode>, target_id: ID, ident: &Ident, op: &Op) {
            t.update_node_by_id(target_id).ty =
                t.get_node_by_id(target_id).item.ty.subst(ident, op);
            for child in t
                .get_children(target_id.to_node(&t))
                .map(|n| n.id)
                .collect::<Vec<_>>()
            {
                update_app_branchs(t, child, ident, op);
            }
        }
        //pdebug!("update parents");
        //pdebug!(self.tree);
        self.tree
            .update_parent_until(target_id, |t, cur, prev| {
                let n = t.get_node_by_id(cur).item;
                //pdebug!("update_parent_until", n);
                let ty = match prev {
                    None => n.ty.clone(),
                    Some(prev) => {
                        match &n.rule {
                            Rule::Conjoin => {
                                let cnstr = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| match child.item.ty.kind() {
                                        TauKind::Proposition(c) => c.clone(),
                                        TauKind::PTy(_, _)
                                        | TauKind::IArrow(_, _)
                                        | TauKind::Arrow(_, _) => {
                                            panic!("not conjoin")
                                        }
                                    })
                                    .fold(Atom::mk_true(), Atom::mk_conj);
                                Ty::mk_prop_ty(cnstr)
                            }
                            Rule::Disjoin => {
                                let cnstr = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| match child.item.ty.kind() {
                                        TauKind::Proposition(c) => c.clone(),
                                        TauKind::PTy(_, _)
                                        | TauKind::IArrow(_, _)
                                        | TauKind::Arrow(_, _) => {
                                            panic!("not disjoin")
                                        }
                                    })
                                    .fold(Atom::mk_false(), Atom::mk_disj);
                                Ty::mk_prop_ty(cnstr)
                            }
                            Rule::Univ => {
                                let children: Vec<_> = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| child.item)
                                    .collect();
                                assert_eq!(children.len(), 1);
                                let cnstr = match children[0].ty.kind() {
                                    TauKind::Proposition(c) => c.clone(),
                                    TauKind::PTy(_, _)
                                    | TauKind::IArrow(_, _)
                                    | TauKind::Arrow(_, _) => {
                                        panic!("not conjoin")
                                    }
                                };
                                let x = n.expr.univ().0;
                                Ty::mk_prop_ty(Atom::mk_univ_int(x.id, cnstr))
                            }
                            Rule::IAbs => {
                                let children: Vec<_> = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| child.item)
                                    .collect();
                                assert_eq!(children.len(), 1);
                                let x = n.expr.abs().0;
                                Ty::mk_iarrow(x.id, children[0].ty.clone())
                            }
                            Rule::Poly(x) => {
                                let children: Vec<_> = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| child.item)
                                    .collect();
                                assert_eq!(children.len(), 1);
                                Ty::mk_poly_ty(*x, children[0].ty.clone())
                            }
                            Rule::Abs(x) => {
                                let children: Vec<_> = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| child.item)
                                    .collect();
                                assert_eq!(children.len(), 1);
                                Ty::mk_arrow(x.clone(), children[0].ty.clone())
                            }
                            Rule::IApp(o) => {
                                let children: Vec<_> = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| child.item)
                                    .collect();
                                assert_eq!(children.len(), 1);
                                match children[0].ty.kind() {
                                    TauKind::IArrow(x, t) => t.subst(&x, &o),
                                    _ => panic!("program error"),
                                }
                            }
                            Rule::App => {
                                let children: Vec<_> = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| child)
                                    .collect();
                                //assert_eq!(children.len(), 2);
                                // todo?
                                assert!(children.len() >= 1);
                                let node = t.get_node_by_id(prev).item;

                                // case1: the updated child was in pred
                                if node.expr.aux.id == children[0].item.expr.aux.id {
                                    // first we update other children
                                    // match &int_substitution {
                                    //     Some((x, o)) => {
                                    //         for child_id in children[1..]
                                    //             .into_iter()
                                    //             .map(|child| child.id)
                                    //             .collect::<Vec<_>>()
                                    //         {
                                    //             update_app_branchs(t, child_id, &x, &o);
                                    //         }
                                    //     }
                                    //     None => (),
                                    // }

                                    // then we retrieve the updated children
                                    let children: Vec<_> = t
                                        .get_children(t.get_node_by_id(cur))
                                        .map(|child| child)
                                        .collect();
                                    let pred = children[0].item.ty.clone();
                                    let body_tys: Vec<_> = children[1..]
                                        .iter()
                                        .map(|child| child.item.ty.clone())
                                        .collect();
                                    let (arg_ty, ret_ty) = match pred.kind() {
                                        TauKind::Arrow(arg, t) => (arg.clone(), t.clone()),
                                        TauKind::PTy(_, _)
                                        | TauKind::Proposition(_)
                                        | TauKind::IArrow(_, _) => {
                                            panic!("program error")
                                        }
                                    };
                                    // subsumption
                                    //t.update_node_by_id(children[0].id).ty =
                                    //    Ty::mk_arrow(body_tys, ret_ty.clone());
                                    // for (body_ty, arg_ty) in body_tys
                                    //     .iter()
                                    //     .filter(|x| !x.is_bot())
                                    //     .zip(arg_ty.iter().filter(|x| !x.is_bot())) {
                                    //
                                    //     }

                                    if !body_tys
                                        .iter()
                                        .filter(|x| !x.is_bot())
                                        .zip(arg_ty.iter().filter(|x| !x.is_bot()))
                                        .all(|(t1, t2)| t1 == t2)
                                    {
                                        debug!("subsumption");
                                        for body_ty in body_tys.iter() {
                                            crate::pdebug!(body_ty);
                                        }
                                        debug!("<:");
                                        for body_ty in arg_ty.iter() {
                                            crate::pdebug!(body_ty);
                                        }
                                        panic!("subsumption invalid")
                                    }
                                    ret_ty.clone()
                                }
                                // case2: the updated child was in body
                                else {
                                    // insert subsumption here
                                    for child in children[1..].iter() {
                                        if node.expr.aux.id == child.item.expr.aux.id {
                                            todo!();
                                            return (true, n.clone());
                                        }
                                    }
                                    panic!("program error")
                                }
                            }
                            Rule::Equivalence | Rule::Subsumption => {
                                let children: Vec<_> = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| child.item)
                                    .collect();
                                assert_eq!(children.len(), 1);
                                return (true, n.clone());
                            }
                            Rule::Var | Rule::Atom => panic!("program error"),
                        }
                    }
                };
                let n = t.get_node_by_id(cur).item;
                let n = DeriveNode {
                    ty,
                    rule: n.rule.clone(),
                    expr: n.expr.clone(),
                };
                (false, n)
            })
            .unwrap();
    }
    fn update_expr_inner(&mut self, node_id: ID, expr: &G) {
        self.tree.update_node_by_id(node_id).expr = expr.clone();
        let children: Vec<_> = self
            .tree
            .get_children(node_id.to_node(&self.tree))
            .map(|child| child.id)
            .collect();
        let n = self.get_node_by_id(node_id).item;
        //crate::title!("update_expr_inner");
        //crate::pdebug!(n);
        //crate::pdebug!(expr);
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
            Rule::Univ => {
                let (y, g) = expr.univ();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g);
            }
            Rule::IAbs => {
                let (y, g) = expr.abs();
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
            }
            Rule::App => {
                let (x, y) = expr.app();
                assert!(children.len() >= 1);
                self.update_expr_inner(children[0], x);
                for i in 1..children.len() {
                    self.update_expr_inner(children[i], y);
                }
            }
            Rule::Subsumption | Rule::Poly(_) => {
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], &expr);

                let mut expr = expr.clone();
                reset_expr_for_subsumption(&mut expr);
                self.tree.update_node_by_id(node_id).expr = expr.clone();
            }
            Rule::Equivalence => {
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], &expr);

                let mut expr = expr.clone();
                reset_expr_for_subsumption(&mut expr);

                // Unlike the case for subsumption, we replace the original one
                // so that we can refer to the more general type afterwards.
                self.tree.update_node_by_id(children[0]).expr = expr.clone();
            }
        };
    }
    fn update_expr(&mut self, expr: &G) {
        //pdebug!("update_expr");
        //pdebug!(self.tree);
        let root_id = self.tree.root().id;
        self.update_expr_inner(root_id, expr);
    }

    fn finalize_subject_expansion(&mut self, reduction: &super::Reduction, target_node: ID) {
        // finally replace the expressions in the derivation with the expr before the reduction
        self.update_expr(&reduction.before_reduction);
        self.update_parents(target_node);
    }
    pub fn subject_expansion_int(&mut self, node_id: ID, reduction: &super::Reduction) {
        let ri = &reduction.reduction_info;
        let abs_cnt = match &ri.reduction_type {
            super::ReductionType::Int(i) => i.abs_introduced,
            super::ReductionType::Pred(_) => panic!("program error: int reduction is assumed"),
        };

        // constructing body derivation
        let arg_derivations =
            self.replace_derivation_at_level_with_var(node_id, &ri.level, ri.arg_var.id);
        assert_eq!(arg_derivations.len(), 0);

        // all Ptr(id) in the constraints in ty should be dereferenced
        //self.traverse_and_recover_int_var(node_id, &ri.arg_var.id, &ri.old_id);

        //            D                      D
        //          ------                ------
        //  x ≠ e    ψ: t                 ψ: t
        // ---------------         ---------------------  (IAbs)
        //   x ≠ e \/ ψ:       --->     λx.ψ: x: int -> t
        // ---------------          --------------------  (IApp)
        //  ∀ x. x ≠ e ∨ ψ           (λx.ψ) e: [e/x]t
        // ----------------         ------------------
        //        ⋮                      ⋮
        // but, actually, we have to omit all the expressions introduced for eta expansion
        let op: Op = reduction.reduction_info.arg.clone().into();

        // node (obtained from node_id) is λf. λg. λh. ∀ x. x ≠ e ∨ ψ f g h
        // we remove the redundant abstractions introduced by eta expansion
        let mut node = node_id.to_node(&self.tree);
        pdebug!("subject expansion int");
        pdebug!(node.item);
        let mut remaining_abs_count = 0;
        while !matches!(node.item.rule, Rule::Univ) {
            node = self.tree.get_one_child(node);
            remaining_abs_count += 1;
        }

        debug!("abs_count: {abs_cnt}, remaining_abs_count: {remaining_abs_count}");

        // node: ∀ x. x ≠ e ∨ ψ f g h
        // child: x ≠ e ∨ ψ f g h
        let child = self.tree.get_one_child(node);
        debug_assert!(matches!(child.item.rule, Rule::Disjoin));

        // remove apps for eta expansion
        // body is the subformula that starts from  ∀ x. x ≠ e ∨ ψ f g h, and obtain ψ
        let mut body = self.tree.get_two_children(child).1;

        // skip for the redundant ones
        for _ in 0..remaining_abs_count {
            match body.item.rule {
                Rule::App | Rule::IApp(_) => (),
                _ => {
                    pdebug!("not app");
                    debug!("abs count: {abs_cnt}");
                    pdebug!(body.item);
                    panic!("program error")
                }
            }
            body = self.tree.get_children(body).next().unwrap();
        }
        let mut outer_app_derivations = Vec::new();
        for _ in remaining_abs_count..abs_cnt {
            match body.item.rule {
                Rule::App | Rule::IApp(_) => (),
                _ => {
                    pdebug!("not app");
                    debug!("abs count: {abs_cnt}");
                    pdebug!(body.item);
                    panic!("program error")
                }
            }
            let item = body.item.clone();
            let mut children = self.tree.get_children(body);
            let pred = children.next().unwrap();
            let arg = children.next().map(|arg| self.tree.subtree(arg));
            body = pred;
            outer_app_derivations.push((arg, item));
        }
        let ret_ty = body.item.ty.clone();
        let subtree = self.tree.subtree(body);

        debug!("before generated subtree:");
        pdebug!(subtree);

        // now the node's expr must be (λx. Ψ) op
        // and the child's expr must be λx. Ψ,
        // dummy is expected to be replaced later in `update_expr`
        let dummy = G::mk_true();
        let node = DeriveNode {
            rule: Rule::IAbs,
            expr: dummy.clone(),
            ty: Ty::mk_iarrow(ri.old_id, ret_ty.clone()),
        };
        let subtree = Tree::tree_with_child(node, subtree);
        let node = DeriveNode {
            rule: Rule::IApp(op.clone()),
            expr: dummy,
            ty: ret_ty.subst(&ri.old_id, &op),
        };
        let mut subtree = Tree::tree_with_child(node, subtree);

        for (deriv, n) in outer_app_derivations.into_iter().rev() {
            subtree = match deriv {
                // Some: case where the app's arg is pred
                Some(mut deriv) => {
                    // replace all the types by (&ri.old_id, &op) ?
                    deriv.iter_mut(|d| d.ty = d.ty.subst(&ri.old_id, &op));
                    Tree::tree_with_two_children(n, subtree, deriv)
                }
                // None: it's iapp
                None => Tree::tree_with_child(n, subtree),
            };
        }
        debug!("generated subtree:");
        pdebug!(subtree);

        // replace_subtree is buggy, so currently, some hacking here....
        // remove (λx. Ψ) x's children first.
        let children: Vec<_> = self
            .tree
            .get_children(node_id.to_node(&self.tree))
            .into_iter()
            .collect();
        let mut t = self.tree.clone();
        for child in children {
            t = t.drop_subtree(child);
        }

        // insert Ψ's derivation to (λx. Ψ)'s children.
        *t.update_node_by_id(node_id) = subtree.root().item.clone();
        for (i, child) in subtree.get_children(subtree.root()).enumerate() {
            t.insert_children_at(node_id, i, subtree.subtree(child));
        }

        self.tree = t;

        self.finalize_subject_expansion(reduction, node_id);
    }

    pub fn subject_expansion_pred(&mut self, node_id: ID, reduction: &super::Reduction) {
        let ri = &reduction.reduction_info;
        let arg_derivations =
            self.replace_derivation_at_level_with_var(node_id, &ri.level, ri.arg_var.id);
        let mut arg_derivations_new: Vec<Derivation> = Vec::new();
        for arg_d in arg_derivations {
            let mut should_append = true;
            for d2 in arg_derivations_new.iter() {
                if arg_d.root_ty() == d2.root_ty() {
                    // already exists
                    highlight!("arg derivations already exists");
                    pdebug!(arg_d, " vs ", d2);
                    should_append = false;
                    break;
                }
            }
            if should_append {
                arg_derivations_new.push(arg_d);
            }
        }
        let arg_derivations = arg_derivations_new;

        let arg_derivations: Vec<_> = arg_derivations
            .into_iter()
            .map(|d| {
                let mut d = d;
                let ty = d.root_ty().clone();
                let fvs = ty.fv();
                for id in fvs.difference(&reduction.fvints) {
                    d = Self::rule_polymorphic_type(d, *id);
                }
                d
            })
            .collect();

        let (arg_tys, arg_derivations) = if arg_derivations.is_empty() {
            (vec![], vec![])
        } else {
            // if a shared_ty is attached with the predicate we are focusing on, we have to use it
            (
                arg_derivations
                    .iter()
                    .map(|d| d.root_ty().clone())
                    .collect(),
                arg_derivations,
            )
        };

        let (t, _node_id) = self.tree.insert_partial_tree(node_id, |body| {
            let body = Derivation {
                tree: body,
                coefficients: Stack::new(),
            };

            let tmp_deriv =
                Derivation::rule_arrow(reduction.predicate.clone(), body, arg_tys.clone());
            let app_deriv = Derivation::rule_app(
                reduction.app_expr.clone(),
                tmp_deriv,
                arg_derivations.into_iter(),
            );

            app_deriv.tree
        });

        self.tree = t;
        let target_node = self
            .get_node_closest_to_root_by_goal_id(&reduction.app_expr.aux.id)
            .unwrap()
            .id;

        self.finalize_subject_expansion(reduction, target_node);
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
                Ty::check_subtype_result(&child.item.ty, &ty).unwrap_or_else(|| {
                    let mut coefficients = Stack::new();
                    let c =
                        Ty::check_subtype(&Atom::mk_true(), &child.item.ty, &ty, &mut coefficients);
                    if coefficients.iter().next().is_some() {
                        panic!("failed to check subtype: {} <: {}", child.item.ty, ty)
                    }
                    c
                })
            })
    }
    pub fn collect_chcs<'a>(
        &'a self,
    ) -> impl Iterator<Item = chc::CHC<chc::Atom, Constraint>> + 'a {
        self.collect_constraints()
            .map(|c| match c.to_chcs_or_pcsps() {
                either::Either::Left(c) => c.into_iter(),
                either::Either::Right(_) => panic!("failed to transform to chcs: {}", c),
            })
            .flatten()
    }

    fn clone_with_template_inner(
        &self,
        node_id: ID,
        env: &mut HashMap<Ident, Stack<(Ty, Ty)>>,
        // when mode_shared is enabled, we prepare only one template type for
        // each lambda abstraction's argument even the type was τ₁ ∧ ⋯ ∧ τₙ
        // otherwise, we prepare the template for each type
        mode_shared: bool,
        ints: Stack<Ident>,
    ) -> Self {
        let n = self.get_node_by_id(node_id);
        let expr = n.item.expr.clone();
        let t = match n.item.rule {
            Rule::Conjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.clone_with_template_inner(child1.id, env, mode_shared, ints.clone());
                let d2 = self.clone_with_template_inner(child2.id, env, mode_shared, ints.clone());
                Self::rule_conjoin(expr, d1, d2)
            }
            Rule::Disjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.clone_with_template_inner(child1.id, env, mode_shared, ints.clone());
                let d2 = self.clone_with_template_inner(child2.id, env, mode_shared, ints.clone());
                Self::rule_disjoin(expr, d1, d2)
            }
            Rule::Var => {
                let v = expr.var();
                let ty = env
                    .get(v)
                    .map(|ty_map| {
                        // if its bot type, we don't have to care about it
                        if n.item.ty.is_bot() {
                            &ty_map.iter().next().unwrap().1
                        } else {
                            ty_map
                                .iter()
                                .find_map(|(t1, t2)| if &n.item.ty == t1 { Some(t2) } else { None })
                                .expect(&format!("failed to find {v}: {}", n.item.pretty_display()))
                        }
                    })
                    .cloned()
                    .unwrap_or_else(|| n.item.ty.clone());
                self.tree.get_no_child(n);
                Self::rule_var(expr, ty, Stack::new())
            }
            Rule::Univ => {
                let x = expr.univ().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints.push(x));
                Self::rule_quantifier(expr, d, &x)
            }
            Rule::IAbs => {
                let x = expr.abs().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints.push(x));
                Self::rule_iarrow(expr, d, &x)
            }
            Rule::Abs(_) => {
                let x = expr.abs().0;
                let (arg_ty, _) = n.item.ty.arrow();

                let mut arg_template_tys = Vec::new();
                let fvs = ints.iter().cloned().collect();
                let mut ty_map = Stack::new();
                if mode_shared {
                    let arg_temp_ty = Ty::from_sty(&x.ty, &fvs);
                    arg_template_tys.push(arg_temp_ty.clone());
                    for t in arg_ty.iter() {
                        // TODO! fix body_ty!
                        ty_map.push_mut((t.body_ty(), arg_temp_ty.clone()));
                    }
                } else {
                    for t in arg_ty.iter() {
                        let arg_temp_ty = Ty::from_sty(&x.ty, &fvs);
                        arg_template_tys.push(arg_temp_ty.clone());
                        ty_map.push_mut((t.clone(), arg_temp_ty.clone()));
                    }
                };
                let old = env.insert(x.id, ty_map);
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints.clone());
                if let Some(ty) = old {
                    env.insert(x.id, ty);
                }

                Self::rule_arrow(expr, d, arg_template_tys)
            }
            Rule::IApp(_) => {
                let (_, e) = expr.app();
                let o: Op = e.clone().into();
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints);
                Self::rule_iapp(expr, d, &o)
            }
            Rule::Poly(_) => {
                // skip poly
                let child = self.tree.get_one_child(n);
                self.clone_with_template_inner(child.id, env, mode_shared, ints)
            }
            Rule::App if mode_shared => {
                let mut c = self.tree.get_children(n);
                let c1 = c.next().unwrap();
                let d1 = self.clone_with_template_inner(c1.id, env, mode_shared, ints.clone());
                let ty1 = d1.root_ty().clone();
                let (d2, is_bot) = match c.next() {
                    Some(c2) => {
                        let d2 =
                            self.clone_with_template_inner(c2.id, env, mode_shared, ints.clone());
                        (d2, false)
                    }
                    None => (
                        Derivation::rule_atom(
                            expr.app().1.clone(),
                            Ty::mk_bot(&ty1.arrow().0[0].to_sty()),
                        ),
                        true,
                    ),
                };
                let ty2 = d2.root_ty().clone();

                let (_, ret_ty) = ty1.arrow();
                let ret_tmp_ty = ret_ty.clone_with_template(&mut ints.iter().cloned().collect());
                let ty3 = Ty::mk_arrow(vec![ty2], ret_tmp_ty);

                let d3 = Self::rule_subsumption(d1, ty3);

                if is_bot {
                    Self::rule_app(expr, d3, std::iter::empty())
                } else {
                    Self::rule_app(expr, d3, std::iter::once(d2))
                }
            }
            Rule::App => {
                unimplemented!()
            }
            // skip subsumption and equivalence
            Rule::Equivalence | Rule::Subsumption => {
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints);
                d
            }
            Rule::Atom => Self::rule_atom(expr, n.item.ty.clone()),
        };
        Derivation {
            tree: t.tree,
            coefficients: t.coefficients,
        }
    }
    pub fn clone_with_template(&self, mode_shared: bool) -> Self {
        highlight!("clone_with_template");
        pdebug!(self);
        let root = self.tree.root().id;
        let mut env = HashMap::new();
        let ints = Stack::new();
        let d = self.clone_with_template_inner(root, &mut env, mode_shared, ints);
        let n = self.get_node_by_id(root);
        match n.item.rule {
            Rule::Subsumption => (),
            _ => panic!("program error"),
        }
        let ty = n.item.ty.clone();
        Self::rule_subsumption(d, ty)
    }
    #[allow(dead_code)]
    /// This function is used to check that the derivation is well-formed
    /// if strict flag is enabled, then check_sanity checks if the given derivation tree
    /// is well-formed in the sense that all free variables of each type are bound.
    pub fn check_sanity(&self, strict: bool) -> bool {
        // now only check if app is sane since others are probably fine
        fn go(d: &Derivation, node_id: ID, ints: &Stack<Ident>, strict: bool) -> bool {
            let n = d.get_node_by_id(node_id);
            let fvs = n.item.ty.fv();
            if strict
                && !fvs
                    .difference(&ints.iter().cloned().collect())
                    .next()
                    .is_none()
            {
                pdebug!("fail: ", n.item);
                panic!("derivation is not well-formed");
            };
            match n.item.rule {
                Rule::Var | Rule::Atom => {
                    d.tree.get_no_child(n);
                    true
                }
                Rule::Conjoin | Rule::Disjoin => {
                    let (child1, child2) = d.tree.get_two_children(n);
                    go(d, child1.id, ints, strict) && go(d, child2.id, ints, strict)
                }
                Rule::IAbs => {
                    let x = n.item.expr.abs().0;
                    assert!(x.ty.is_int());
                    let ints = ints.push(x.id);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict)
                }
                Rule::Univ => {
                    let x = n.item.expr.univ().0;
                    assert!(x.ty.is_int());
                    let ints = ints.push(x.id);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict)
                }
                Rule::Poly(x) => {
                    let ints = ints.push(x);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict)
                }
                Rule::IApp(_) | Rule::Abs(_) | Rule::Subsumption | Rule::Equivalence => {
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, ints, strict)
                }
                Rule::App => {
                    let children: Vec<_> = d.tree.get_children(n).collect();
                    let pred_ty = children[0].item.ty.clone();
                    let arg_tys: Vec<_> = children[1..]
                        .iter()
                        .map(|child| child.item.ty.clone())
                        .collect();
                    let body_tys = pred_ty.arrow().0;
                    // subsumption
                    if !body_tys
                        .iter()
                        .filter(|x| !x.is_bot())
                        .zip(arg_tys.iter().filter(|x| !x.is_bot()))
                        .all(|(t1, t2)| t1 == t2)
                    {
                        debug!("subsumption");
                        for body_ty in body_tys.iter() {
                            crate::pdebug!(body_ty);
                        }
                        debug!("<:");
                        for body_ty in arg_tys.iter() {
                            crate::pdebug!(body_ty);
                        }
                        debug!("is wrong");
                        panic!();
                    }

                    children.iter().all(|c| go(d, c.id, ints, strict))
                }
            }
        }
        go(self, self.tree.root().id, &Stack::new(), strict)
    }
}
