use std::collections::{HashMap, HashSet};

use super::tree::*;
use super::{Atom, Ty, G};
use crate::pdebug;
use crate::pdr::rtype::{Instantiation, TBot, Tau, TauKind};
use crate::solver;
use crate::util::Pretty;
use crate::{formula::*, highlight};

use rpds::{HashTrieMap, Stack};

const PRINT_ASSUMPTION: bool = true;

#[derive(Clone, Debug)]
pub(super) struct DeriveNode {
    // Γ; C ⊢ ψ : τ
    // Γ is omitted
    pub context: Stack<Atom>, // C equals the conjoin of them
    pub rule: Rule,
    pub expr: G,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub enum Rule {
    Conjoin,
    Disjoin,
    // Ty: original ty
    // Stack<Instantiation>: seq of instantiations
    // the ty in the derivation is expected to be the instantiated type
    // of ty with the instantiations
    Var(Stack<Instantiation>, Ty),
    Univ,
    IAbs,
    Abs(Vec<Ty>),
    IApp(Op),
    App,
    Subsumption, // Atom: rty
    Equivalence,
    Atom,
    Poly(Ident),
}

impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Rule::Conjoin => "Conj",
            Rule::Disjoin => "Disj",
            Rule::Var(_, _) => "Var",
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
        let body = match &self.rule {
            Rule::Var(_, original_ty) => self
                .expr
                .pretty(al, config)
                .append(al.line())
                .append(":")
                .append(al.line())
                .append(self.ty.pretty(al, config))
                .append(al.line())
                .append("{{")
                .append(original_ty.pretty(al, config))
                .append("}}")
                .hang(2)
                .group(),
            _ => self
                .expr
                .pretty(al, config)
                .append(al.line())
                .append(":")
                .append(al.line())
                .append(self.ty.pretty(al, config))
                .hang(2)
                .group(),
        };
        let doc = al.text("(").append(self.rule.to_string()).append(")");
        if PRINT_ASSUMPTION {
            doc.append(al.line())
                .append(al.intersperse(self.context.iter().map(|x| x.pretty(al, config)), " ∧ "))
        } else {
            doc
        }
        .append(al.line())
        .append("|-")
        .append(al.line())
        .append(body)
        .group()
    }
}

fn reset_expr_for_subsumption(expr: &mut G) {
    expr.aux.level_arg = Stack::new();
    expr.aux.id = Ident::fresh();
}

impl DeriveNode {
    fn conjoin(context: Stack<Atom>, expr: G, left: &Self, right: &Self) -> Self {
        let rule = Rule::Conjoin;
        let ty = match (left.ty.kind(), right.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Ty::mk_prop_ty(Atom::mk_conj(c1.clone(), c2.clone()))
            }
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", left.ty, right.ty),
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn disjoin(context: Stack<Atom>, expr: G, left: &Self, right: &Self) -> Self {
        let rule = Rule::Disjoin;
        let ty = match (left.ty.kind(), right.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Ty::mk_prop_ty(Atom::mk_disj(c1.clone(), c2.clone()))
            }
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", left.ty, right.ty),
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn quantify(context: Stack<Atom>, expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::Univ;
        let ty = match node.ty.kind() {
            TauKind::Proposition(c1) => Ty::mk_prop_ty(Atom::mk_quantifier_int(
                crate::formula::QuantifierKind::Universal,
                *ident,
                c1.clone(),
            )),
            TauKind::PTy(_, _) | TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn iarrow(context: Stack<Atom>, expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::IAbs;
        let ty = Ty::mk_iarrow(*ident, node.ty.clone());
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn arrow(context: Stack<Atom>, expr: G, node: &Self, ts: Vec<Ty>) -> Self {
        let rule = Rule::Abs(ts.clone());
        let ty = Ty::mk_arrow(ts, node.ty.clone());
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn iapp(context: Stack<Atom>, expr: G, node: &Self, op: &Op) -> Self {
        let rule = Rule::IApp(op.clone());
        let ty = match node.ty.kind() {
            TauKind::IArrow(x, t2) => t2.subst(x, op),
            _ => panic!("fatal"),
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn subsumption(context: Stack<Atom>, node: &Self, ty: Ty) -> Self {
        let rule = Rule::Subsumption;
        let mut expr = node.expr.clone();
        // reset the information
        reset_expr_for_subsumption(&mut expr);
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn equivalence(context: Stack<Atom>, node: &Self, ty: Ty) -> Self {
        let rule = Rule::Equivalence;
        let expr = node.expr.clone();
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn poly(context: Stack<Atom>, node: &Self, x: Ident) -> Self {
        let rule = Rule::Poly(x);
        let expr = node.expr.clone();
        let ty = Ty::mk_poly_ty(x, node.ty.clone());
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn app(context: Stack<Atom>, expr: G, pred_node: &Self) -> Self {
        let rule = Rule::App;
        let ty = match pred_node.ty.kind() {
            TauKind::Arrow(_, rt) => rt.clone(),
            TauKind::PTy(_, _) | TauKind::Proposition(_) | TauKind::IArrow(_, _) => {
                panic!("app rule is used for a wrong derivation")
            }
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    pub fn constraint(&self) -> Atom {
        self.context
            .iter()
            .fold(Atom::mk_true(), |acc, c| Atom::mk_conj(acc, c.clone()))
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
    pub fn get_types_by_goal_id<'a>(&'a self, id: &'a Ident) -> impl Iterator<Item = Ty> + 'a {
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

    pub fn single_node(n: DeriveNode) -> Self {
        Self {
            tree: Tree::singleton(n),
            coefficients: Stack::new(),
        }
    }

    pub fn rule_atom(context: Stack<Atom>, expr: G, ty: Ty) -> Self {
        let rule = Rule::Atom;
        let node = DeriveNode {
            context,
            rule,
            expr,
            ty,
        };
        Self {
            tree: Tree::singleton(node),
            coefficients: Stack::new(),
        }
    }

    pub fn rule_var(
        context: Stack<Atom>,
        expr: G,
        ty: Ty,
        original_ty: Ty,
        coefficients: Stack<Ident>,
        instantiations: Stack<Instantiation>,
    ) -> Self {
        let rule = Rule::Var(instantiations, original_ty);
        let node = DeriveNode {
            context,
            rule,
            expr,
            ty,
        };
        Self {
            tree: Tree::singleton(node),
            coefficients,
        }
    }

    pub fn rule_instantiate(expr: G, ty: Ty, instantiations: Stack<Instantiation>) -> Self {
        unimplemented!()
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
    pub fn rule_conjoin(context: Stack<Atom>, expr: G, d1: Self, d2: Self) -> Self {
        let root = DeriveNode::conjoin(context, expr, d1.tree.root().item, d2.tree.root().item);
        Self::rule_two_arg_inner(root, d1, d2)
    }
    pub fn rule_disjoin(context: Stack<Atom>, expr: G, d1: Self, d2: Self) -> Self {
        let root = DeriveNode::disjoin(context, expr, d1.tree.root().item, d2.tree.root().item);
        Self::rule_two_arg_inner(root, d1, d2)
    }
    pub fn rule_quantifier(context: Stack<Atom>, expr: G, d: Self, x: &Ident) -> Self {
        let root = DeriveNode::quantify(context, expr, d.tree.root().item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_iarrow(context: Stack<Atom>, expr: G, d: Self, x: &Ident) -> Self {
        let root = DeriveNode::iarrow(context, expr, d.tree.root().item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_arrow(context: Stack<Atom>, expr: G, d: Self, tys: Vec<Ty>) -> Self {
        let root = DeriveNode::arrow(context, expr, d.tree.root().item, tys);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_iapp(context: Stack<Atom>, expr: G, d: Self, o: &Op) -> Self {
        let root = DeriveNode::iapp(context, expr, d.tree.root().item, o);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_subsumption(context: Stack<Atom>, d: Self, ty: Ty) -> Self {
        let child = d.tree.root();
        let root = DeriveNode::subsumption(context, child.item, ty);
        let d = Self::rule_one_arg_inner(root, d);
        d
    }
    pub fn rule_equivalence(context: Stack<Atom>, mut d: Self, ty: Ty) -> Self {
        let child_id = d.tree.root().id;
        let root = DeriveNode::equivalence(context, d.tree.root().item, ty);
        reset_expr_for_subsumption(&mut d.tree.update_node_by_id(child_id).expr);
        let d = Self::rule_one_arg_inner(root, d);
        d
    }
    pub fn rule_app<I>(context: Stack<Atom>, expr: G, d1: Self, args: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let root = DeriveNode::app(context, expr, &d1.tree.root().item);
        Self::rule_multiples(root, std::iter::once(d1).chain(args))
    }
    pub fn rule_polymorphic_type(context: Stack<Atom>, d: Self, x: Ident) -> Self {
        let item = d.tree.root().item;
        let root = DeriveNode::poly(context, item, x);
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
        fvints: &HashSet<Ident>,
    ) -> Vec<Self> {
        let var_expr = G::mk_var(var);
        let mut tree = self.tree.clone();
        let mut derivations = vec![];
        let contexts = self.get_node_by_id(node_id).item.context.clone();
        for node in self
            .tree
            .filter_descendants(self.tree.get_node_by_id(node_id), move |n| {
                n.expr.aux.level_arg.iter().any(|arg| arg == level)
            })
        {
            let mut sub_derivation = self.sub_derivation(&node.id);
            let context = sub_derivation.tree.root().item.context.clone();

            let instantiated_ty = node.item.ty.clone();
            let fvs = instantiated_ty.fv();
            let mut instantiations = Stack::new();

            // introduce the difference of the context to the result type
            let context_original = sub_derivation.tree.root().item.context.clone();

            let mut constraint = Atom::mk_true();
            for cnstr in context_original.iter() {
                if !context.iter().any(|c| c == cnstr) {
                    constraint = Atom::mk_conj(constraint, cnstr.clone());
                }
            }
            let new_ty = instantiated_ty.conjoin_constraint_to_rty(&constraint);
            sub_derivation =
                Self::rule_equivalence(context.clone(), sub_derivation, new_ty.clone());

            for id in fvs.difference(fvints) {
                sub_derivation = Self::rule_polymorphic_type(context.clone(), sub_derivation, *id);
                instantiations.push_mut(Instantiation {
                    ident: *id,
                    op: Op::mk_var(*id),
                });
            }

            let d = Self::rule_var(
                context,
                var_expr.clone(),
                instantiated_ty,
                sub_derivation.root_ty().clone(),
                Stack::new(),
                instantiations,
            );

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
        pdebug!("update parents");
        pdebug!(self.tree);
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
                            Rule::Var(_, _) | Rule::Atom => panic!("program error"),
                        }
                    }
                };
                let n = t.get_node_by_id(cur).item;
                let n = DeriveNode {
                    context: n.context.clone(),
                    ty,
                    rule: n.rule.clone(),
                    expr: n.expr.clone(),
                };
                (false, n)
            })
            .unwrap();
    }
    fn update_expr_inner(
        &mut self,
        node_id: ID,
        expr: &G,
        mut alpha_renaming_map: Stack<(Ident, Ident)>,
    ) {
        fn retrieve_ty_alpha_renaming(t: &Ty, map: Stack<(Ident, Ident)>) -> Ty {
            let mut ty = t.clone();
            for (x, y) in map.iter() {
                ty = ty.rename(x, y);
            }
            ty
        }
        let old_expr = self.tree.get_node_by_id(node_id).item.expr.clone();
        let old_ty = self.tree.get_node_by_id(node_id).item.ty.clone();

        let node = self.tree.update_node_by_id(node_id);
        node.expr = expr.clone();
        node.ty = retrieve_ty_alpha_renaming(&old_ty, alpha_renaming_map.clone());

        // update context
        let mut context = node.context.clone();
        for (x, y) in alpha_renaming_map.iter() {
            context = context.iter().map(|a| a.rename(x, y)).collect();
        }
        node.context = context;

        let children: Vec<_> = self
            .tree
            .get_children(node_id.to_node(&self.tree))
            .map(|child| child.id)
            .collect();
        let n = self.get_node_by_id(node_id).item;
        //crate::title!("update_expr_inner");
        //crate::pdebug!(n);
        //crate::pdebug!(expr);
        self.tree.update_node_by_id(node_id).rule = match &n.rule {
            Rule::Conjoin => {
                let (g1, g2) = expr.conj();
                assert_eq!(children.len(), 2);
                self.update_expr_inner(children[0], g1, alpha_renaming_map.clone());
                self.update_expr_inner(children[1], g2, alpha_renaming_map.clone());
                Rule::Conjoin
            }
            Rule::Disjoin => {
                let (g1, g2) = expr.disj();
                assert_eq!(children.len(), 2);
                self.update_expr_inner(children[0], g1, alpha_renaming_map.clone());
                self.update_expr_inner(children[1], g2, alpha_renaming_map.clone());
                Rule::Disjoin
            }
            Rule::Var(i, ty) => {
                debug_assert!(expr.is_var());
                let ty = retrieve_ty_alpha_renaming(&ty, alpha_renaming_map.clone());
                Rule::Var(i.clone(), ty)
            }
            Rule::Atom => Rule::Atom,
            Rule::Univ => {
                let (v, _) = old_expr.univ();
                let (w, g) = expr.univ();
                if v.ty.is_int() && v.id != w.id {
                    alpha_renaming_map.push_mut((v.id, w.id));
                }

                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g, alpha_renaming_map.clone());
                Rule::Univ
            }
            Rule::IAbs => {
                let (w, g) = expr.abs();
                debug_assert!(w.ty.is_int());

                // After the subject expansion, some of the expr are placed as "true"
                // as a placeholder, which can be ignored here.
                match old_expr.kind() {
                    hes::GoalKind::Abs(_, _) => {
                        let (v, _) = old_expr.abs();
                        if v.ty.is_int() && v.id != w.id {
                            alpha_renaming_map.push_mut((v.id, w.id));
                            let (x, t) = old_ty.iarrow();
                            let ty = Ty::mk_iarrow(v.id, t.rename(x, &v.id));
                            self.tree.update_node_by_id(node_id).ty =
                                retrieve_ty_alpha_renaming(&ty, alpha_renaming_map.clone());
                        }
                    }
                    _ => (),
                }
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g, alpha_renaming_map.clone());
                Rule::IAbs
            }
            Rule::Abs(tys) => {
                let (_, g) = expr.abs();
                let tys = tys
                    .into_iter()
                    .map(|t| retrieve_ty_alpha_renaming(&t, alpha_renaming_map.clone()))
                    .collect();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g, alpha_renaming_map.clone());
                Rule::Abs(tys)
            }
            Rule::IApp(op) => {
                let (x, y) = expr.app();
                let mut op = op.clone();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], x, alpha_renaming_map.clone());

                for (x, y) in alpha_renaming_map.iter() {
                    op = op.rename(x, y)
                }
                Rule::IApp(op)
            }
            Rule::App => {
                let (x, y) = expr.app();
                assert!(children.len() >= 1);
                self.update_expr_inner(children[0], x, alpha_renaming_map.clone());
                for i in 1..children.len() {
                    self.update_expr_inner(children[i], y, alpha_renaming_map.clone());
                }
                Rule::App
            }
            Rule::Subsumption | Rule::Poly(_) => {
                let rule = n.rule.clone();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], &expr, alpha_renaming_map.clone());

                let mut expr = expr.clone();
                reset_expr_for_subsumption(&mut expr);
                self.tree.update_node_by_id(node_id).expr = expr.clone();
                rule
            }
            Rule::Equivalence => {
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], &expr, alpha_renaming_map.clone());

                let mut expr = expr.clone();
                reset_expr_for_subsumption(&mut expr);

                // Unlike the case for subsumption, we replace the original one
                // so that we can refer to the more general type afterwards.
                self.tree.update_node_by_id(children[0]).expr = expr.clone();
                Rule::Equivalence
            }
        };
    }
    fn update_expr(&mut self, expr: &G) {
        //pdebug!("update_expr");
        //pdebug!(self.tree);
        let root_id = self.tree.root().id;
        self.update_expr_inner(root_id, expr, Stack::new());
    }

    fn finalize_subject_expansion(&mut self, reduction: &super::Reduction, target_node: ID) {
        self.update_parents(target_node);
        // finally replace the expressions in the derivation with the expr before the reduction
        self.update_expr(&reduction.before_reduction);
    }

    pub fn subject_expansion_pred(
        &mut self,
        node_id: ID,
        reduction: &super::Reduction,
        reduction_idx: usize,
    ) -> Vec<Derivation> {
        //let ri = &reduction.reduction_info;
        let ri = &reduction.reduction_infos[reduction_idx];
        let arg_derivations = self.replace_derivation_at_level_with_var(
            node_id,
            &ri.level,
            ri.arg_var.id,
            &reduction.fvints,
        );
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
        arg_derivations_new
    }

    fn extract_body_derivation(&self, target_node: ID, int_arg_count: usize) -> Tree<DeriveNode> {
        let mut cur = target_node.to_node(&self.tree);
        for _ in 0..int_arg_count {
            debug_assert!(matches!(cur.item.rule, Rule::Univ));
            let n = self.tree.get_one_child(cur);
            debug_assert!(matches!(n.item.rule, Rule::Disjoin));
            cur = self.tree.get_two_children(n).1;
        }
        self.tree.subtree(cur)
    }

    fn append_int_abs(
        &self,
        tree: Tree<DeriveNode>,
        ri: &super::ReductionInfo,
    ) -> Tree<DeriveNode> {
        let dummy = G::mk_true();
        let n = DeriveNode {
            context: tree.root().item.context.clone(),
            rule: Rule::IAbs,
            expr: dummy.clone(),
            ty: Tau::mk_iarrow(ri.old_id, tree.root().item.ty.clone()),
        };
        Tree::tree_with_child(n, tree)
    }

    fn append_int_app(
        &self,
        tree: Tree<DeriveNode>,
        ri: &super::ReductionInfo,
    ) -> Tree<DeriveNode> {
        let dummy = G::mk_true();
        let op: Op = ri.arg.clone().into();
        let (x, ty) = tree.root().item.ty.iarrow();
        let n = DeriveNode {
            context: tree.root().item.context.clone(),
            rule: Rule::IApp(op.clone()),
            expr: dummy.clone(),
            ty: ty.subst(x, &op),
        };
        Tree::tree_with_child(n, tree)
    }

    fn append_pred_abs(
        &self,
        tree: Tree<DeriveNode>,
        arg_derivations: &Vec<Derivation>,
    ) -> Tree<DeriveNode> {
        let arg_tys: Vec<_> = arg_derivations
            .iter()
            .map(|d| d.root_ty().clone())
            .collect();
        let dummy = G::mk_true();
        let n = DeriveNode {
            context: tree.root().item.context.clone(),
            rule: Rule::Abs(arg_tys.clone()),
            expr: dummy.clone(),
            ty: Tau::mk_arrow(arg_tys.clone(), tree.root().item.ty.clone()),
        };
        Tree::tree_with_child(n, tree)
    }

    fn append_pred_app(
        &self,
        tree: Tree<DeriveNode>,
        arg_derivations: Vec<Derivation>,
    ) -> Tree<DeriveNode> {
        debug!("append_pred_app");
        pdebug!(tree);
        let context = tree.root().item.context.clone();
        let pred_derivation = Derivation {
            coefficients: Stack::new(),
            tree: tree,
        };
        let dummy = G::mk_true();
        Derivation::rule_app(context, dummy, pred_derivation, arg_derivations.into_iter()).tree
    }

    pub fn append_abs(
        &self,
        t: Tree<DeriveNode>,
        reduction: &super::Reduction,
        derivation_map: &HashMap<usize, Vec<Derivation>>,
    ) -> Tree<DeriveNode> {
        let mut subtree = t;
        for (idx, ri) in reduction.reduction_infos.iter().enumerate().rev() {
            match ri.reduction_type {
                super::ReductionType::Int(_) => {
                    subtree = self.append_int_abs(subtree, ri);
                }
                super::ReductionType::Pred(_) => {
                    let derivations = derivation_map.get(&idx).unwrap();
                    subtree = self.append_pred_abs(subtree, derivations);
                }
            }
        }
        subtree
    }
    pub fn append_app(
        &self,
        t: Tree<DeriveNode>,
        reduction: &super::Reduction,
        mut derivation_map: HashMap<usize, Vec<Derivation>>,
    ) -> Tree<DeriveNode> {
        let mut subtree = t;
        for (idx, ri) in reduction.reduction_infos.iter().enumerate() {
            match ri.reduction_type {
                super::ReductionType::Int(_) => {
                    subtree = self.append_int_app(subtree, ri);
                }
                super::ReductionType::Pred(_) => {
                    let derivations = derivation_map.remove(&idx).unwrap();
                    subtree = self.append_pred_app(subtree, derivations);
                }
            }
        }
        subtree
    }

    pub fn expand_node(&mut self, target_node: ID, reduction: &super::Reduction) {
        let mut derivation_map = HashMap::new();
        let mut int_arg_count = 0;
        for (idx, ri) in reduction.reduction_infos.iter().enumerate() {
            match ri.reduction_type {
                super::ReductionType::Int(_) => {
                    //self.subject_expansion_int(target_node, reduction, idx);
                    int_arg_count += 1;
                }
                super::ReductionType::Pred(_) => {
                    let arg_derivation = self.subject_expansion_pred(target_node, reduction, idx);
                    derivation_map.insert(idx, arg_derivation);
                }
            }
        }
        let subtree = self.extract_body_derivation(target_node, int_arg_count);
        let subtree = self.append_abs(subtree, reduction, &derivation_map);
        let subtree = self.append_app(subtree, reduction, derivation_map);
        // top_id must be a fresh id assigned by the dummy expr
        let top_id = subtree.root().item.expr.aux.id;
        self.tree = self.tree.insert_partial_tree(target_node, |_| subtree).0;

        let target_node = self
            .get_node_closest_to_root_by_goal_id(&top_id)
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
                let constraints = n
                    .item
                    .context
                    .iter()
                    .fold(Atom::mk_true(), |acc, c| Atom::mk_conj(acc, c.clone()));
                let children: Vec<_> = self.tree.get_children(n).collect();
                assert_eq!(children.len(), 1);
                let child = &children[0];
                // conjoin constraint of the rule
                Ty::check_subtype_result(&child.item.ty, &ty).unwrap_or_else(|| {
                    let mut coefficients = Stack::new();
                    let c = Ty::check_subtype(&constraints, &child.item.ty, &ty, &mut coefficients);
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
        let context = n.item.context.clone();
        let t = match &n.item.rule {
            Rule::Conjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.clone_with_template_inner(child1.id, env, mode_shared, ints.clone());
                let d2 = self.clone_with_template_inner(child2.id, env, mode_shared, ints.clone());
                Self::rule_conjoin(context, expr, d1, d2)
            }
            Rule::Disjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.clone_with_template_inner(child1.id, env, mode_shared, ints.clone());
                let d2 = self.clone_with_template_inner(child2.id, env, mode_shared, ints.clone());
                Self::rule_disjoin(context, expr, d1, d2)
            }
            Rule::Var(instantiations, original_ty) => {
                let v = expr.var();
                let (ty, instantiations, original_ty) = env
                    .get(v)
                    .map(|ty_map| {
                        // if its bot type, we don't have to care about it
                        if n.item.ty.is_bot() {
                            &ty_map.iter().next().unwrap().1
                        } else {
                            ty_map
                                .iter()
                                .find_map(
                                    |(t1, t2)| if original_ty == t1 { Some(t2) } else { None },
                                )
                                .expect(&format!("failed to find {v}: {}", n.item.pretty_display()))
                        }
                    })
                    .cloned()
                    .map(|x| (x.clone(), Stack::new(), x.clone()))
                    .unwrap_or_else(|| {
                        (
                            n.item.ty.clone(),
                            instantiations.clone(),
                            original_ty.clone(),
                        )
                    });
                self.tree.get_no_child(n);
                Self::rule_var(context, expr, ty, original_ty, Stack::new(), instantiations)
            }
            Rule::Univ => {
                let x = expr.univ().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints.push(x));
                Self::rule_quantifier(context, expr, d, &x)
            }
            Rule::IAbs => {
                let x = expr.abs().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints.push(x));
                Self::rule_iarrow(context, expr, d, &x)
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
                        ty_map.push_mut((t.clone(), arg_temp_ty.clone()));
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

                Self::rule_arrow(context, expr, d, arg_template_tys)
            }
            Rule::IApp(_) => {
                let (_, e) = expr.app();
                let o: Op = e.clone().into();
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints);
                Self::rule_iapp(context, expr, d, &o)
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
                            context.clone(),
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

                let d3 = Self::rule_subsumption(context.clone(), d1, ty3);

                if is_bot {
                    Self::rule_app(context, expr, d3, std::iter::empty())
                } else {
                    Self::rule_app(context, expr, d3, std::iter::once(d2))
                }
            }
            Rule::App => {
                unimplemented!()
            }
            // skip subsumption and equivalence
            Rule::Equivalence => {
                let ty = n.item.ty.clone();
                let child = self.tree.get_one_child(n);
                let before_ty = child.item.ty.clone();
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints);
                if d.root_ty() != &before_ty {
                    Self::rule_subsumption(context, d, ty)
                } else {
                    Self::rule_equivalence(context, d, ty)
                }
            }
            Rule::Subsumption => {
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(child.id, env, mode_shared, ints);
                d
            }
            Rule::Atom => Self::rule_atom(context, expr, n.item.ty.clone()),
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
        Self::rule_subsumption(Stack::new(), d, ty)
    }
    #[allow(dead_code)]
    /// This function is used to check that the derivation is well-formed
    /// if strict flag is enabled, then check_sanity checks if the given derivation tree
    /// is well-formed in the sense that all free variables of each type are bound.
    pub fn check_sanity(&self, strict: bool) -> bool {
        // now only check if app is sane since others are probably fine
        fn go(
            d: &Derivation,
            node_id: ID,
            ints: &Stack<Ident>,
            strict: bool,
            env: &HashTrieMap<Ident, Vec<Ty>>,
        ) -> bool {
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
            match &n.item.rule {
                Rule::Var(_, ty) => {
                    let x = n.item.expr.var();
                    d.tree.get_no_child(n);
                    //if !ints.iter().any(|y| x == y) {
                    //    let ty2 = env.get(&x).unwrap();
                    //    assert!(ty2.iter().any(|t| t == ty));
                    //}
                    true
                }
                Rule::Atom => {
                    let expr: Constraint = n.item.expr.clone().into();
                    let expr2 = n.item.ty.prop().clone().into();
                    assert_eq!(expr, expr2);
                    true
                }
                Rule::Conjoin | Rule::Disjoin => {
                    let (child1, child2) = d.tree.get_two_children(n);
                    go(d, child1.id, ints, strict, env) && go(d, child2.id, ints, strict, env)
                }
                Rule::IAbs => {
                    let x = n.item.expr.abs().0;
                    assert!(x.ty.is_int());
                    let ints = ints.push(x.id);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict, env)
                }
                Rule::Univ => {
                    let x = n.item.expr.univ().0;
                    assert!(x.ty.is_int());
                    let ints = ints.push(x.id);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict, env)
                }
                Rule::Poly(x) => {
                    let ints = ints.push(*x);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict, env)
                }
                Rule::IApp(_) | Rule::Subsumption | Rule::Equivalence => {
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, ints, strict, env)
                }
                Rule::Abs(_) => {
                    let (arg_ty, _) = n.item.ty.arrow();
                    let (x, _) = n.item.expr.abs();
                    let child = d.tree.get_one_child(n);
                    let env = env.insert(x.id, arg_ty.clone());
                    go(d, child.id, ints, strict, &env)
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

                    children.iter().all(|c| go(d, c.id, ints, strict, env))
                }
            }
        }
        go(
            self,
            self.tree.root().id,
            &Stack::new(),
            strict,
            &HashTrieMap::new(),
        )
    }
}
