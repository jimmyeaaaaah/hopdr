use rpds::{HashTrieSet, List, HashTrieMap};
use std::{collections::HashMap, rc::Weak, cell::RefCell, rc::Rc};
use std::ops::Deref;
use crate::util::P;


#[derive(Clone)]
pub struct TreeNode<T: ?Sized> {
    parent: Weak<TreeNode<T>>,
    children: Vec<Tree<T>>,
    pub item: T,
}

#[derive(Clone)]
pub struct Tree<T: ?Sized> {
    ptr: Rc<TreeNode<T>>,
}
impl <T>Tree<T> {
    fn new(item: TreeNode<T>) -> Tree<T> {
        Tree { ptr: Rc::new(item)}
    }
}


impl<T: Clone> Tree<T> {
    pub fn singleton(item: T) -> Tree<T> {
        let parent = RefCell::new(Weak::new());
        let children = RefCell::new(Vec::new());
        Tree::new(TreeNode { children, parent, item})
    }
    pub fn append_children(&mut self, child: Tree<T>) {
        *child.ptr.parent.borrow_mut() = Rc::downgrade(&self.ptr);
        self.ptr.children.borrow_mut().push(child);
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
    pub fn search<'a, F>(&'a self, check: F) -> Option<Tree<T>>
    where
        F: Fn(&T) -> bool,
    {
        self.
        self.graph.nodes().find_map(|id| {
            let node = self.get_node_by_id(id);
            if check(node.item) {
                Some(node)
            } else {
                None
            }
        })
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
        self.items.iter_mut().for_each(|(key, item)| f(item))
    }
    fn parent(&self, node: ID) -> Option<ID> {
        let v: Vec<_> = self
            .graph
            .neighbors_directed(node, petgraph::Incoming)
            .collect();
        assert!(v.len() <= 1);
        if v.len() == 0 {
            None
        } else {
            Some(v[0])
        }
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
    /// given an iterator whose items are indices of each child to some nodes
    /// if there is no node specified, this function returns None.
    ///
    /// For example, if you want to get c, you have to pass path [0, 0, 0].
    /// For b2, [0, 1]
    /// `-- a
    ///     |-- b
    ///     |   |-- c
    ///     |   `-- c2
    ///     `-- b2
    // pub fn at<'a, I>(&self, path: I) -> Option<Node<'a, T>>
    // where
    //     I: Iterator<Item = usize>,
    // {
    //     let mut cur = self.root();
    //     while let Some(child) = {

    //     }
    // }
}

#[test]
fn tree_basics() {
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

    assert_eq!(t.filter(|x| *x == 2).count(), 2)
}
