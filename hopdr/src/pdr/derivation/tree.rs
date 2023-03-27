use std::collections::{HashMap, VecDeque};

use crate::util::global_counter;

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, PartialOrd, Ord)]
pub struct ID(u64);

fn gen_id() -> ID {
    ID(global_counter())
}

impl ID {
    pub fn to_item<'a, T>(&'a self, tree: &'a Tree<T>) -> &'a T {
        tree.items.get(self).unwrap()
    }
    pub fn to_node<'a, T>(&'a self, tree: &'a Tree<T>) -> Node<T> {
        tree.get_node_by_id(*self)
    }
}

// using petgraph's Graph as the core graph library is not a good choice since
// it seems not to support merging two graphs in an efficient way
// (c.f. https://github.com/petgraph/petgraph/issues/276)
// In hopdr's usecase, merging two nodes happens everywhere.
// I guess it does not cause any bottleneck immediately, since basically the slowest
// part of hopdr is SMT solving.
// However, we should be aware that this part will be a bottleneck.
//
// I think it is not so much hard to implement myself this tree library
// without depending on any other external crate since we don't use almost nothing
// other than add_node and connect two nodes.
// So, if I have a time to do so, I'll do so...

#[derive(Clone)]
struct IDTree {
    //nodes: Vec<ID>,
    edges: HashMap<ID, Vec<ID>>,
    parent: HashMap<ID, ID>,
}

impl IDTree {
    fn new() -> Self {
        IDTree {
            edges: HashMap::new(),
            parent: HashMap::new(),
        }
    }
    fn add_node(&mut self, node: ID) {
        self.edges.insert(node, Vec::new());
    }
    fn add_edge(&mut self, from: ID, to: ID) {
        debug_assert!(self.edges.contains_key(&from) && self.edges.contains_key(&to));
        self.edges.get_mut(&from).unwrap().push(to);
        let r = self.parent.insert(to, from);
        debug_assert!(r.is_none())
    }
    fn add_edge_at(&mut self, from: ID, to: ID, child_idx: usize) {
        debug_assert!(self.edges.contains_key(&from) && self.edges.contains_key(&to));
        let v = self.edges.get_mut(&from).unwrap();
        v.insert(child_idx, to);
        let r = self.parent.insert(to, from);
        debug_assert!(r.is_none())
    }
    fn nodes<'a>(&'a self) -> impl Iterator<Item = ID> + 'a {
        self.edges.keys().copied()
    }
    fn all_edges<'a>(&'a self) -> impl Iterator<Item = (ID, ID)> + 'a {
        self.edges
            .iter()
            .map(|(x, v)| v.iter().map(move |y| (*x, *y)))
            .flatten()
    }
    fn get_parent(&self, node: ID) -> Option<ID> {
        self.parent.get(&node).copied()
    }
    fn edges<'a>(&'a self, node: ID) -> impl Iterator<Item = (ID, ID)> + 'a {
        self.edges
            .get(&node)
            .unwrap()
            .iter()
            .map(move |y| (node, *y))
    }
    fn children<'a>(&'a self, node: ID) -> impl Iterator<Item = ID> + 'a {
        self.edges.get(&node).unwrap().iter().copied()
    }
    fn subtree<'a>(&'a self, node: ID) -> Self {
        fn traverse(
            t: &IDTree,
            cur: ID,
            edges: &mut HashMap<ID, Vec<ID>>,
            parent: &mut HashMap<ID, ID>,
        ) {
            for child in t.children(cur) {
                traverse(t, child, edges, parent)
            }
            edges.insert(cur, t.edges.get(&cur).unwrap().clone());
            parent.insert(cur, t.parent.get(&cur).unwrap().clone());
        }
        let mut edges = HashMap::new();
        let mut parent = HashMap::new();
        traverse(self, node, &mut edges, &mut parent);
        Self { edges, parent }
    }
    fn drop_subtree<'a>(&'a self, node: ID) -> Self {
        fn traverse(
            t: &IDTree,
            cur: ID,
            edges: &mut HashMap<ID, Vec<ID>>,
            parent: &mut HashMap<ID, ID>,
        ) {
            for child in t.children(cur) {
                traverse(t, child, edges, parent)
            }
            edges.remove(&cur);
            parent.remove(&cur);
        }
        let mut edges = self.edges.clone();
        let mut parent = self.parent.clone();
        let ptr = edges.get_mut(parent.get(&node).unwrap()).unwrap();
        ptr.retain(|elem| elem != &node);
        traverse(self, node, &mut edges, &mut parent);
        Self { edges, parent }
    }
    pub fn replace_subtree<'a>(&'a self, node: ID, graph: Self, root: ID) -> Self {
        fn traverse(
            t: &IDTree,
            cur: ID,
            edges: &mut HashMap<ID, Vec<ID>>,
            parent: &mut HashMap<ID, ID>,
        ) {
            for child in t.children(cur) {
                traverse(t, child, edges, parent)
            }
            edges.remove(&cur);
            parent.remove(&cur);
        }
        let mut edges = self.edges.clone();
        let mut parent = self.parent.clone();
        let ptr = edges.get_mut(parent.get(&node).unwrap()).unwrap();
        // replace the edge to the new tree
        for item in ptr.iter_mut() {
            if *item == node {
                *item = root;
                break;
            }
        }
        for (id, e) in graph.edges {
            edges.insert(id, e);
        }
        for (id, p) in graph.parent {
            parent.insert(id, p);
        }
        // finally remove all the old graph related objects
        traverse(self, node, &mut edges, &mut parent);
        Self { edges, parent }
    }
}

#[derive(Clone)]
pub struct Tree<T> {
    graph: IDTree,
    items: HashMap<ID, T>,
    root: ID,
}

#[derive(Copy, Clone)]
pub struct Node<'a, T> {
    pub item: &'a T,
    pub id: ID,
}

pub struct TreeIterator<'a, T> {
    tree: &'a Tree<T>,
    queue: VecDeque<ID>,
}

impl<'a, T> TreeIterator<'a, T> {
    fn new(tree: &'a Tree<T>, from: ID) -> Self {
        let mut queue = VecDeque::new();
        queue.push_back(from);
        Self { tree, queue }
    }
}

impl<'a, T> Iterator for TreeIterator<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let r = self.queue.pop_front()?;
        for child in self.tree.graph.children(r) {
            self.queue.push_back(child);
        }
        Some(self.tree.get_node_by_id(r))
    }
}

impl<T> Tree<T> {
    pub fn get_node_by_id<'a>(&'a self, id: ID) -> Node<'a, T> {
        let item = self.items.get(&id).unwrap();
        Node { item, id }
    }
    pub fn singleton(item: T) -> Tree<T> {
        let root = gen_id();
        let mut graph = IDTree::new();
        graph.add_node(root);
        let mut items = HashMap::new();
        items.insert(root, item);
        Tree { graph, items, root }
    }
    fn append_children_inner(&mut self, child: &Tree<T>) {
        for node in child.graph.nodes() {
            self.graph.add_node(node);
        }
        for (a, b) in child.graph.all_edges() {
            self.graph.add_edge(a, b);
        }
    }
    pub fn append_children(&mut self, child: Tree<T>) {
        self.append_children_inner(&child);
        self.graph.add_edge(self.root, child.root);
        self.items.extend(child.items)
    }
    pub fn insert_children_at(&mut self, parent_node: ID, index: usize, child: Tree<T>) {
        self.append_children_inner(&child);
        self.graph.add_edge_at(parent_node, child.root, index);
        self.items.extend(child.items)
    }
    pub fn tree_from_children<I>(item: T, children: I) -> Tree<T>
    where
        I: Iterator<Item = Tree<T>>,
    {
        let mut tree = Self::singleton(item);
        for child in children {
            tree.append_children(child)
        }
        tree
    }
    pub fn tree_with_child(item: T, child: Tree<T>) -> Tree<T> {
        Self::tree_from_children(item, std::iter::once(child))
    }
    pub fn tree_with_two_children(item: T, child1: Tree<T>, child2: Tree<T>) -> Tree<T> {
        Self::tree_from_children(item, std::iter::once(child1).chain(std::iter::once(child2)))
    }
    pub fn root(&self) -> Node<T> {
        self.get_node_by_id(self.root)
    }
    pub fn get_children<'a>(&'a self, node: Node<'a, T>) -> impl Iterator<Item = Node<'a, T>> {
        let id = node.id;
        self.graph
            .edges(id)
            .map(move |(_, id)| self.get_node_by_id(id))
    }
    pub fn nth_child<'a>(&'a self, node: Node<'a, T>, n: usize) -> Option<Node<'a, T>> {
        self.get_children(node).nth(n)
    }
    pub fn search<'a, F>(&'a self, check: F) -> Option<Node<'a, T>>
    where
        F: Fn(&T) -> bool,
    {
        self.graph.nodes().find_map(|id| {
            let node = self.get_node_by_id(id);
            if check(node.item) {
                Some(node)
            } else {
                None
            }
        })
    }
    pub fn iter_descendants<'a>(&'a self, node: Node<'a, T>) -> impl Iterator<Item = Node<'a, T>> {
        TreeIterator::new(self, node.id)
    }
    pub fn filter_descendants<'a, P>(
        &'a self,
        node: Node<'a, T>,
        predicate: P,
    ) -> impl Iterator<Item = Node<'a, T>>
    where
        P: 'a + Fn(&T) -> bool,
    {
        self.iter_descendants(node)
            .filter(move |x| predicate(&x.item))
    }
    pub fn filter<'a, P>(&'a self, predicate: P) -> impl Iterator<Item = Node<'a, T>>
    where
        P: 'a + Fn(&T) -> bool,
    {
        self.graph.nodes().filter_map(move |id| {
            let node = self.get_node_by_id(id);
            if predicate(node.item) {
                Some(node)
            } else {
                None
            }
        })
    }
    pub fn iter_mut<'a, P>(&'a mut self, f: P)
    where
        P: Fn(&mut T),
    {
        self.items.iter_mut().for_each(|(_, item)| f(item))
    }
    fn parent(&self, node: ID) -> Option<ID> {
        self.graph.get_parent(node)
    }
    pub fn traverse_parent_until<'a, P>(
        &'a self,
        base: Node<'a, T>,
        predicate: P,
    ) -> Option<Node<'a, T>>
    where
        P: Fn(&T) -> bool,
    {
        let mut cur = base;
        loop {
            if predicate(cur.item) {
                break Some(cur);
            }
            if let Some(parent_id) = self.parent(cur.id) {
                cur = self.get_node_by_id(parent_id)
            } else {
                break None;
            }
        }
    }
    /// Searches up the tree from the given `base` node, passing a reference to the
    /// item associated with each node and its children to the `predicate` closure. The `predicate`
    /// closure returns a tuple containing a boolean indicating whether the target node has been
    /// found, and an updated version of the target item. If the target node is found, the function
    /// returns `Some(node)` containing a reference to that node. If the top of the tree is reached
    /// without finding the target node, the function returns `None`.
    pub fn update_parent_until<'a, P>(
        &'a mut self,
        base: ID,
        mut predicate: P,
    ) -> Option<Node<'a, T>>
    where
        P: FnMut(&T, Vec<&T>, Option<&T>) -> (bool, T),
    {
        let mut cur = base;
        let mut prev = None;
        loop {
            let target = self.items.get(&cur).unwrap();
            let children = self
                .get_children(self.get_node_by_id(cur))
                .map(|n| n.item)
                .collect();
            let (cont, t) = predicate(
                target,
                children,
                prev.map(|id| self.items.get(&id).unwrap()),
            );
            *self.items.get_mut(&cur).unwrap() = t;
            if cont {
                break Some(self.get_node_by_id(cur));
            }
            if let Some(parent_id) = self.parent(cur) {
                prev = Some(cur);
                cur = parent_id
            } else {
                break None;
            }
        }
    }
    fn update_children_inner<'a, P>(&'a mut self, node_id: ID, f: &P)
    where
        P: 'a + Fn(&mut T),
    {
        let item = self.items.get_mut(&node_id).unwrap();
        f(item);

        let children: Vec<_> = self.graph.children(node_id).collect();
        for child_id in children {
            self.update_children_inner(child_id, f)
        }
    }
    pub fn update_children<'a, P>(&'a mut self, node_id: ID, f: P)
    where
        P: 'a + Fn(&mut T),
    {
        self.update_children_inner(node_id, &f)
    }
}
impl<T: Clone> Tree<T> {
    fn projection(&self, graph: IDTree, root: ID) -> Self {
        let items: HashMap<_, _> = self
            .items
            .iter()
            .filter_map(|(id, item)| {
                if graph.edges.contains_key(id) {
                    Some((*id, item.clone()))
                } else {
                    None
                }
            })
            .collect();
        Self { items, graph, root }
    }
    pub fn subtree<'a>(&'a self, node: Node<'a, T>) -> Self {
        let graph = self.graph.subtree(node.id);
        self.projection(graph, node.id)
    }
    pub fn drop_subtree<'a>(&'a self, node: Node<'a, T>) -> Self {
        // you cannot drop the whole tree (there is no empty tree)
        assert_ne!(node.id, self.root);
        let graph = self.graph.drop_subtree(node.id);
        self.projection(graph, self.root)
    }
    pub fn replace_subtree<'a>(&'a self, node: Node<'a, T>, tree: Self) -> Self {
        // you cannot drop the whole tree (there is no empty tree)
        assert_ne!(node.id, self.root);
        let graph = self.graph.replace_subtree(node.id, tree.graph, tree.root);
        let mut result = self.projection(graph, self.root);
        // append items in tree
        for (id, item) in tree.items.into_iter() {
            result.items.insert(id, item);
        }
        result
    }
    //             2  3
    // insert here→ \/
    //               1
    //   ↓
    //  2       ...
    //   \     /
    //    5   6
    //     \ /
    //      4  3
    //      | /
    //      1
    // node_id: 2
    //
    pub fn insert_partial_tree<P>(&self, node_id: ID, f: P) -> Self
    where
        P: FnOnce(Self) -> Self,
    {
        let parent_node = self
            .parent(node_id)
            .expect("the node you specified is the root node");
        let sub_tree = self.subtree(node_id.to_node(self));
        let child_tree = f(sub_tree);

        let target_idx = self
            .get_children(parent_node.to_node(self))
            .enumerate()
            .find_map(
                |(idx, child)| {
                    if child.id == node_id {
                        Some(idx)
                    } else {
                        None
                    }
                },
            )
            .unwrap();

        // 1. first remove all the nodes and edges in sub_tree
        let mut parent_tree = self.drop_subtree(node_id.to_node(self));
        parent_tree.insert_children_at(parent_node, target_idx, child_tree);
        parent_tree
    }
    pub fn update_node_by_id<'a>(&'a mut self, node_id: ID) -> &'a mut T {
        self.items.get_mut(&node_id).unwrap()
    }
}

#[test]
fn tree_basics() {
    // 1-2
    // |-2-3
    let t1 = Tree::singleton(3);
    let t3 = Tree::tree_with_child(2, t1);
    let t2 = Tree::singleton(2);
    let t = Tree::tree_with_two_children(1, t3, t2);
    let root = t.root();
    assert_eq!(*root.item, 1);
    for child in t.get_children(root) {
        assert_eq!(*child.item, 2);
        for child2 in t.get_children(child) {
            assert_eq!(*child2.item, 3);

            // parent
            let parent = t.parent(child2.id).unwrap();
            assert_eq!(parent, child.id);

            assert!(t.traverse_parent_until(child2, |v| *v == 1).is_some())
        }
    }

    assert!(t.search(|x| *x == 4).is_none());
    assert!(t.search(|x| *x == 3).is_some());

    assert_eq!(t.filter(|x| *x == 2).count(), 2);

    assert_eq!(
        t.iter_descendants(t.root())
            .map(|n| *n.item)
            .collect::<Vec<_>>(),
        vec![1, 2, 2, 3]
    );
    let child = t.get_children(root).nth(0).unwrap();
    assert_eq!(
        t.filter_descendants(child, |x| *x == 3)
            .map(|n| *n.item)
            .collect::<Vec<_>>(),
        vec![3]
    );

    let t2 = t.drop_subtree(child);
    assert_eq!(
        t2.iter_descendants(t2.root())
            .map(|n| *n.item)
            .collect::<Vec<_>>(),
        vec![1, 2]
    );
    let t5 = t.subtree(child);
    assert_eq!(
        t5.iter_descendants(t5.root())
            .map(|n| *n.item)
            .collect::<Vec<_>>(),
        vec![2, 3]
    );

    let t7 = Tree::tree_with_child(4, Tree::singleton(5));
    let t6 = t.replace_subtree(child, t7);
    assert_eq!(
        t6.iter_descendants(t6.root())
            .map(|n| *n.item)
            .collect::<Vec<_>>(),
        vec![1, 4, 2, 5]
    );

    // update children
    let mut t8 = t.clone();
    t8.update_children(t8.root, |x| *x = 10);
    assert_eq!(
        t8.iter_descendants(t8.root())
            .map(|n| *n.item)
            .collect::<Vec<_>>(),
        vec![10, 10, 10, 10]
    );
    //           3
    //            \
    //             2  2
    // insert here→ \/
    //               1
    //   ↓
    // 3
    //  \
    //   2
    //    \
    //     5   6
    //      \ /
    //       4  2
    //       | /
    //       1
    //  node_id: 2
    //
    let mut t9 = t.insert_partial_tree(child.id, |t| {
        let six = Tree::singleton(6);
        let five = Tree::tree_with_child(5, t);
        let four = Tree::tree_with_two_children(4, five, six);
        four
    });
    assert_eq!(*t9.root().item, 1);
    let v: Vec<_> = t9.get_children(t9.root()).collect();
    assert_eq!(v.len(), 2);
    let four_node = v[0];
    let two_node = v[1];
    let v: Vec<_> = t9.get_children(four_node).collect();
    assert_eq!(v.len(), 2);
    assert_eq!(*v[0].item, 5);
    assert_eq!(*v[1].item, 6);
    let v: Vec<_> = t9.get_children(v[0]).collect();
    assert_eq!(*v[0].item, 2);

    let v: Vec<_> = t9.get_children(v[0]).collect();
    assert_eq!(v.len(), 1);
    assert_eq!(*v[0].item, 3);

    let v: Vec<_> = t9.get_children(two_node).collect();
    assert_eq!(v.len(), 0);

    // update 2's parents up to 1 is updated to 7
    // 3
    //  \
    //   2  ← start here
    //    \
    //     5   6
    //      \ /
    //       4  2
    //       | /
    //       1
    //
    // 3
    //  \
    //   7
    //    \
    //     7   6
    //      \ /
    //       7  2
    //       | /
    //       1
    let node = t9.search(|x| *x == 2).unwrap();
    let n = t9
        .update_parent_until(node.id, |v, children, prev| {
            if *v != 1 {
                println!("manipulating... {v}");
                if let Some(prev) = prev {
                    println!("prev_node: {prev}");
                }
                println!("children:");
                for child in children {
                    println!("- {child}");
                }
                (false, 7)
            } else {
                (true, *v)
            }
        })
        .unwrap();
    assert_eq!(*n.item, 1);

    assert_eq!(*t9.root().item, 1);
    let v: Vec<_> = t9.get_children(t9.root()).collect();
    assert_eq!(v.len(), 2);
    let seven_node = v[0];
    let two_node = v[1];
    assert_eq!(*seven_node.item, 7);
    let v: Vec<_> = t9.get_children(seven_node).collect();
    assert_eq!(v.len(), 2);
    assert_eq!(*v[0].item, 7);
    assert_eq!(*v[1].item, 6);
    let v: Vec<_> = t9.get_children(v[0]).collect();
    assert_eq!(*v[0].item, 7);

    let v: Vec<_> = t9.get_children(v[0]).collect();
    assert_eq!(v.len(), 1);
    assert_eq!(*v[0].item, 3);

    let v: Vec<_> = t9.get_children(two_node).collect();
    assert_eq!(v.len(), 0);
}
