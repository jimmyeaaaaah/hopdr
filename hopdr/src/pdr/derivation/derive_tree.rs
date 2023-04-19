use std::collections::HashMap;

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
            TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
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
    // traverse sub derivation from `from` and deref `id` and replace `id` with `old_id`
    pub fn traverse_and_recover_int_var(&mut self, from: ID, id: &Ident, old_id: &Ident) {
        self.tree.update_children(from, |node| {
            let ty = node.ty.clone();
            let new_ty = ty.deref_ptr(id).rename(id, old_id);
            node.ty = new_ty;
        });
    }

    fn update_parents(&mut self, target_id: ID, int_substitution: Option<(Ident, Op)>) {
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
        debug!("updating parents");
        crate::pdebug!(self);
        self.tree
            .update_parent_until(target_id, |t, cur, prev| {
                let n = t.get_node_by_id(cur).item;
                debug!("update_parent: {}", n.pretty_display());
                let ty = match prev {
                    None => n.ty.clone(),
                    Some(prev) => {
                        match &n.rule {
                            Rule::Conjoin => {
                                let cnstr = t
                                    .get_children(t.get_node_by_id(cur))
                                    .map(|child| match child.item.ty.kind() {
                                        TauKind::Proposition(c) => c.clone(),
                                        TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => {
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
                                        TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => {
                                            panic!("not conjoin")
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
                                    TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => {
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
                                assert!(children.len() >= 2);
                                let node = t.get_node_by_id(prev).item;

                                // case1: the updated child was in pred
                                if node.expr.aux.id == children[0].item.expr.aux.id {
                                    // first we update other children
                                    match &int_substitution {
                                        Some((x, o)) => {
                                            for child_id in children[1..]
                                                .into_iter()
                                                .map(|child| child.id)
                                                .collect::<Vec<_>>()
                                            {
                                                update_app_branchs(t, child_id, &x, &o);
                                            }
                                        }
                                        None => (),
                                    }

                                    // then we retrieve the updated children
                                    let children: Vec<_> = t
                                        .get_children(t.get_node_by_id(cur))
                                        .map(|child| child.item)
                                        .collect();
                                    let pred = children[0].ty.clone();
                                    let body_tys: Vec<_> = children[1..]
                                        .iter()
                                        .map(|child| child.ty.clone())
                                        .collect();
                                    let (arg_ty, ret_ty) = match pred.kind() {
                                        TauKind::Arrow(arg, t) => (arg.clone(), t.clone()),
                                        TauKind::Proposition(_) | TauKind::IArrow(_, _) => {
                                            panic!("program error")
                                        }
                                    };
                                    // subsumption
                                    debug!("subsumption");
                                    for body_ty in body_tys.iter() {
                                        crate::pdebug!(body_ty);
                                    }
                                    debug!("<:");
                                    for body_ty in arg_ty.iter() {
                                        crate::pdebug!(body_ty);
                                    }
                                    assert!(body_tys
                                        .iter()
                                        .filter(|x| !x.is_bot())
                                        .zip(arg_ty.iter().filter(|x| !x.is_bot()))
                                        .all(|(t1, t2)| t1 == t2));
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
                debug!("subst {ty} with {int_substitution:?}");
                let ty = int_substitution
                    .as_ref()
                    .map(|(id, op)| ty.subst(id, op))
                    .unwrap_or(ty);
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
        // crate::title!("update_expr_inner");
        // crate::pdebug!(n);
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
            Rule::Equivalence => {
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], &expr);

                let mut expr = expr.clone();
                reset_expr_for_subsumption(&mut expr);

                // Unlike the case for subsumption, we replace the original one
                // so that we can refer to the more general type afterwards.
                self.tree.update_node_by_id(children[0]).expr = expr.clone();
            }
        }
    }
    fn update_expr(&mut self, expr: &G) {
        let root_id = self.tree.root().id;
        self.update_expr_inner(root_id, expr)
    }
    fn finalize_subject_expansion(
        &mut self,
        reduction: &super::Reduction,
        int_substitution: Option<(Ident, Op)>,
    ) {
        let target_node = self
            .get_node_closest_to_root_by_goal_id(&reduction.app_expr.aux.id)
            .unwrap()
            .id;

        self.update_parents(target_node, int_substitution);
        // finally replace the expressions in the derivation with the expr before the reduction
        self.update_expr(&reduction.before_reduction)
    }
    pub fn subject_expansion_int(&mut self, node_id: ID, reduction: &super::Reduction) {
        let ri = &reduction.reduction_info;
        let ret_ty = self.node_id_to_ty(&node_id).clone();

        // constructing body derivation
        let arg_derivations =
            self.replace_derivation_at_level_with_var(node_id, &ri.level, ri.arg_var.id);
        assert_eq!(arg_derivations.len(), 0);

        // all Ptr(id) in the constraints in ty should be dereferenced
        // derivation.traverse_and_recover_int_var(node_id, &ri.arg_var.id, &ri.old_id);

        // TODO: update body's type derivation
        // first insert abs derivation
        let (t, _node_id) = self.tree.insert_partial_tree(node_id, |body| {
            let body = Derivation {
                tree: body,
                coefficients: Stack::new(),
            };
            let mut tmp_deriv =
                Derivation::rule_iarrow(reduction.predicate.clone(), body, &ri.old_id);

            let op: Op = reduction.reduction_info.arg.clone().into();
            let eq_constr =
                Atom::mk_constraint(Constraint::mk_eq(Op::mk_var(ri.old_id.clone()), op.clone()));
            let pred_ty = Tau::mk_iarrow(ri.old_id, ret_ty.clone());
            let pred_ty = pred_ty.conjoin_constraint_to_rty(&eq_constr);

            tmp_deriv
                .tree
                .update_node_by_id(tmp_deriv.tree.root().id)
                .ty = pred_ty;

            let app_deriv = Derivation::rule_iapp(reduction.app_expr.clone(), tmp_deriv, &op);
            let app_deriv = Derivation::rule_equivalence(app_deriv, ret_ty.subst(&ri.old_id, &op));
            app_deriv.tree
        });

        let x = reduction.predicate.abs().0.id;
        let op = reduction.reduction_info.arg.clone().into();

        self.tree = t;
        self.finalize_subject_expansion(reduction, Some((x, op)));
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
            highlight!("expand node");
            pdebug!(arg_d, should_append);
            if should_append {
                arg_derivations_new.push(arg_d);
            }
        }
        let arg_derivations = arg_derivations_new;

        let (arg_tys, arg_derivations) = if arg_derivations.is_empty() {
            (
                vec![Ty::mk_bot(&ri.arg_var.ty)],
                vec![Derivation::rule_atom(
                    ri.arg.clone(),
                    Ty::mk_bot(&ri.arg_var.ty),
                )],
            )
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
        self.finalize_subject_expansion(reduction, None);
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
                Ty::check_subtype_result(&child.item.ty, &ty)
                    .unwrap_or_else(|| Ty::check_subtype(&Atom::mk_true(), &child.item.ty, &ty))
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
        env: &mut HashMap<Ident, Ty>,
        ints: Stack<Ident>,
    ) -> Self {
        let n = self.get_node_by_id(node_id);
        crate::pdebug!(n.item);
        let expr = n.item.expr.clone();
        let t = match n.item.rule {
            Rule::Conjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.clone_with_template_inner(child1.id, env, ints.clone());
                let d2 = self.clone_with_template_inner(child2.id, env, ints.clone());
                Self::rule_conjoin(expr, d1, d2)
            }
            Rule::Disjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.clone_with_template_inner(child1.id, env, ints.clone());
                let d2 = self.clone_with_template_inner(child2.id, env, ints.clone());
                Self::rule_disjoin(expr, d1, d2)
            }
            Rule::Var => {
                let v = expr.var();
                let ty = env.get(v).cloned().unwrap_or_else(|| n.item.ty.clone());
                self.tree.get_no_child(n);
                Self::rule_var(expr, ty, Stack::new())
            }
            Rule::Univ => {
                let x = expr.univ().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, ints.push(x));
                Self::rule_quantifier(expr, d, &x)
            }
            Rule::IAbs => {
                let x = expr.abs().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, ints.push(x));
                Self::rule_iarrow(expr, d, &x)
            }
            Rule::Abs(_) => {
                let x = expr.abs().0;
                let ty = Ty::from_sty(&x.ty, &ints.iter().cloned().collect());
                let old = env.insert(x.id, ty.clone());
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, ints.clone());
                if let Some(ty) = old {
                    env.insert(x.id, ty);
                }
                Self::rule_arrow(expr, d, vec![ty.clone()])
            }
            Rule::IApp(_) => {
                let (_, e) = expr.app();
                let o: Op = e.clone().into();
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, ints);
                Self::rule_iapp(expr, d, &o)
            }
            Rule::App => {
                let mut c = self.tree.get_children(n);
                let c1 = c.next().unwrap();
                let c2 = c.next().unwrap();
                let d1 = self.clone_with_template_inner(c1.id, env, ints.clone());
                let d2 = self.clone_with_template_inner(c2.id, env, ints.clone());
                let ty1 = d1.root_ty().clone();
                let ty2 = d2.root_ty().clone();

                let (_, ret_ty) = ty1.arrow();
                let ret_tmp_ty = ret_ty.clone_with_template(&mut ints.iter().cloned().collect());
                let ty3 = Ty::mk_arrow(vec![ty2], ret_tmp_ty);

                let d3 = Self::rule_subsumption(d1, ty3);
                Self::rule_app(expr, d3, std::iter::once(d2))
            }
            // skip subsumption and equivalence
            Rule::Equivalence | Rule::Subsumption => {
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, ints);
                d
            }
            Rule::Atom => Self::rule_atom(expr, n.item.ty.clone()),
        };
        Derivation {
            tree: t.tree,
            coefficients: t.coefficients,
        }
    }
    pub fn clone_with_template(&self) -> Self {
        let root = self.tree.root().id;
        let mut env = HashMap::new();
        let ints = Stack::new();
        let d = self.clone_with_template_inner(root, &mut env, ints);
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
