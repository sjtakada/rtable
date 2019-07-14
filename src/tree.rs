//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//

use std::cell::RefCell;
use std::cell::RefMut;
use std::rc::Rc;
use std::iter::Iterator;
use std::iter::IntoIterator;

use super::prefix::*;

///
/// Tree struct.
///
pub struct Tree<P: Prefixable, D> {
    /// Top Node.
    top: Option<Rc<Node<P, D>>>,

    /// Number of node in this tree.
    count: usize,
}

/// Utility function to check prefix match this node.
fn node_match_prefix<P: Prefixable, D>(curr: Option<Rc<Node<P, D>>>, prefix: &P) -> bool {
    match curr {
        None => false,
        Some(node) => {
            node.prefix.len() <= prefix.len() && node.prefix().contains(prefix)
        }
    }
}

///
/// Tree impl.
///
impl<P: Prefixable, D> Tree<P, D> {
    /// Constructor.
    pub fn new() -> Tree<P, D> {
        Tree {
            top: None,
            count: 0usize,
        }
    }

    /// Return top node.
    pub fn top(&self) -> Option<Rc<Node<P, D>>> {
        self.top.clone()
    }

    /// Get node with given prefix, create one if it doesn't exist.
    pub fn get_node(&mut self, prefix: &P) -> NodeIterator<P, D> {
        let mut matched: Option<Rc<Node<P, D>>> = None;
        let mut curr: Option<Rc<Node<P, D>>> = self.top.clone();
        let mut new_node: Rc<Node<P, D>>;
        
        while node_match_prefix(curr.clone(), prefix) {
            let node = curr.clone().unwrap();
            if node.prefix().len() == prefix.len() {
                return NodeIterator::from_node(node)
            }

            matched = Some(node.clone());
            curr = node.child_with(prefix.bit_at(node.prefix().len()));
        }

        match curr.clone() {
            None => {
                new_node = Rc::new(Node::new(prefix));
                match matched {
                    Some(node) => {
                        Node::<P, D>::set_child(node, new_node.clone());
                    },
                    None => {
                        self.top.replace(new_node.clone());
                    }
                }

            },
            Some(node) => {
                new_node = Rc::new(Node::from_common(node.prefix(), prefix));
                Node::<P, D>::set_child(new_node.clone(), node);

                match matched {
                    Some(node) => {
                        Node::<P, D>::set_child(node, new_node.clone());
                    },
                    None => {
                        self.top.replace(new_node.clone());
                    }
                }

                if new_node.prefix().len() != prefix.len() {
                    matched = Some(new_node.clone());
                    new_node = Rc::new(Node::new(prefix));
                    Node::<P, D>::set_child(matched.unwrap().clone(), new_node.clone());
                }
            }
        }

        NodeIterator::from_node(new_node)
    }

    /// Perform exact match lookup
    pub fn lookup_exact(&self, prefix: &P) -> NodeIterator<P, D> {
        let mut curr = self.top.clone();

        while node_match_prefix(curr.clone(), prefix) {
            let node = curr.clone().unwrap();
            if node.prefix().len() == prefix.len() {
                if node.has_data() {
                    return NodeIterator::from_node(node)
                }
                else {
                    break;
                }
            }

            curr = node.child_with(prefix.bit_at(node.prefix().len()));
        }

        NodeIterator { node: None }
    }

    /// Perform longest match lookup
    pub fn lookup(&self, prefix: &P) -> NodeIterator<P, D> {
        let mut curr = self.top.clone();
        let mut matched: Option<Rc<Node<P, D>>> = None;

        while node_match_prefix(curr.clone(), prefix) {
            let node = curr.clone().unwrap();
            if node.has_data() {
                matched = Some(node.clone());
            }

            if node.prefix().len() == prefix.len() {
                break;
            }

            curr = node.child_with(prefix.bit_at(node.prefix().len()));
        }

        if matched.is_some() {
            NodeIterator::from_node(matched.unwrap())
        }
        else {
            NodeIterator { node: None }
        }
    }

/*
    /// Erase a node from tree, and return iterator for next node.
    pub fn erase(&mut self, mut it: NodeIterator<P, D>) -> NodeIterator<P, D> {
        let next = it.next();

        if let Some(node) = it.node() {
            let has_left = node.child(Child::Left).is_some();
            let has_right = node.child(Child::Right).is_some();

            // if the node has both children, we cannot erase, this is error situation.
            if has_left && has_right {
                return NodeIterator { node: None }
            }

            let mut child = if has_left {
                node.children[Child::Left as usize].replace(None)
            } else if has_right {
                node.children[Child::Right as usize].replace(None)
            } else {
                None
            };

            let parent = node.parent.clone();
            if child.is_some() {
                match parent {
                    Some(parent) => child.set_parent(parent.clone()),
                    None => child.sert_parent(None)
                }
            }

            match parent {
                Some(node) => {
                    if parent.child(Child::Left) == node {
                        parent.set_child(child, Child::Left);
                    } else {
                        parent.set_child(child, Child::Right);
                    }
                },
                None => {
                    self.top = Some(parent.clone());
                }
            }

            if parent.is_some() && !parent.is_locked() {
                self.erase(parent);
            }
        }

        return NodeIterator { node: next }
    }
*/
}

///
/// Tree IntoIterator.
///
impl<P: Prefixable, D> IntoIterator for Tree<P, D> {
    type Item = Rc<Node<P, D>>;
    type IntoIter = NodeIterator<P, D>;

    fn into_iter(self) -> Self::IntoIter {
        let top = self.top.clone();

        NodeIterator::<P, D> {
            node: top,
        }
    }
}

/// NodeIterator.
pub struct NodeIterator<P: Prefixable, D> {
    node: Option<Rc<Node<P, D>>>,
}

/// Impl NodeIterator.
impl<P: Prefixable, D> NodeIterator<P, D> {
    pub fn from_node(node: Rc<Node<P, D>>) -> NodeIterator<P, D> {
        NodeIterator::<P, D> {
            node: Some(node.clone())
        }
    }

    pub fn node(&mut self) -> &Option<Rc<Node<P, D>>> {
        &self.node
    }

    pub fn set_data(&mut self, data: D) {
        let node = self.node.clone();
        match node {
            Some(node) => node.set_data(data),
            None => { }
        }
    }
}

/// Impl Iterator for NodeIterator.
impl<P: Prefixable, D> Iterator for NodeIterator<P, D> {
    type Item = Rc<Node<P, D>>;
    fn next(&mut self) -> Option<Rc<Node<P, D>>> {
        let node = self.node.clone();
        match node {
            Some(node) => {
                self.node = node.next().clone();
                Some(node)
            },
            None => None
        }
    }
}

///
/// Enum Child.
///
pub enum Child {
    Left = 0,
    Right = 1,
}

///
/// Node struct.
///
pub struct Node<P: Prefixable, D> {
    /// Parent Node.
    parent: RefCell<Option<Rc<Node<P, D>>>>,

    /// Child Nodes.
    children: [RefCell<Option<Rc<Node<P, D>>>>; 2],

    /// Prefix associated with this node.
    prefix: P,

    /// Data.
    data: RefCell<Option<D>>,
}

///
/// Node impl.
///
impl<P: Prefixable, D> Node<P, D> {
    /// Return new node.
    pub fn new(prefix: &P) -> Node<P, D> {
        Node {
            parent: RefCell::new(None),
            children: [RefCell::new(None), RefCell::new(None)],
            prefix: P::from_prefix(prefix),
            data: RefCell::new(None),
        }
    }

    /// Return new node with common prefix.
    pub fn from_common(prefix1: &P, prefix2: &P) -> Node<P, D> {
        let pcommon = P::from_common(prefix1, prefix2);
        Self::new(&pcommon)
    }

    /// Return reference to prefix.
    pub fn prefix(&self) -> &P {
        &self.prefix
    }

    /// Return one of child node - left(0) or right(1)
    pub fn child(&self, bit: Child) -> Option<Rc<Node<P, D>>> {
        self.children[bit as usize].borrow_mut().clone()
    }

    /// Return one of child node - left(0) or right(1)
    pub fn child_with(&self, bit: u8) -> Option<Rc<Node<P, D>>> {
        self.children[bit as usize].borrow_mut().clone()
    }

    /// Return parent node.
    pub fn parent(&self) -> Option<Rc<Node<P, D>>> {
        self.parent.borrow_mut().clone()
    }

    /// Set given node as a child at left or right
    fn set_child(parent: Rc<Node<P, D>>, child: Rc<Node<P, D>>) {
        let bit = child.prefix().bit_at(parent.prefix().len());
        //Rc::get_mut(&mut parent).unwrap().set_child_at(child.clone(), bit);
        //Rc::get_mut(&mut child).unwrap().set_parent(parent.clone());
        parent.set_child_at(child.clone(), bit);
        child.set_parent(parent.clone());
    }

    /// Set child at left or right.
    fn set_child_at(&self, child: Rc<Node<P, D>>, bit: u8) {
        self.children[bit as usize].borrow_mut().replace(child.clone());
    }

    /// Set parent.
    pub fn set_parent(&self, parent: Rc<Node<P, D>>) {
        self.parent.borrow_mut().replace(parent.clone());
    }

    /// Set data.
    pub fn set_data(&self, data: D) {
        self.data.replace(Some(data));
    }

    /// Unset data.
    pub fn unset_data(&self) -> Option<D> {
        self.data.replace(None)
    }

    /// Return reference to data.
    pub fn data(&self) -> RefMut<Option<D>> {
        self.data.borrow_mut()
    }

    /// Return true if node has data.
    pub fn has_data(&self) -> bool {
        self.data.borrow_mut().is_some()
    }

    /// Return true if node has child or data.
    pub fn is_locked(&self) -> bool {
        if self.children[Child::Left as usize].borrow_mut().is_some() {
            true
        } else if self.children[Child::Right as usize].borrow_mut().is_some() {
            true
        } else if self.has_data() {
            true
        } else {
            false
        }
    }

    /// Return next Node.  TODO: refactoring
    pub fn next(&self) -> Option<Rc<Node<P, D>>> {
        if let Some(node) = self.child(Child::Left) {
            return Some(node.clone())
        }
        else if let Some(node) = self.child(Child::Right) {
            return Some(node.clone())
        }
        else {
            if let Some(parent) = self.parent() {
                if let Some(l_child) = parent.child(Child::Left) {
                    if l_child.as_ref() as *const _ == self as *const _ {
                        if let Some(r_child) = parent.child(Child::Right) {
                            return Some(r_child.clone())
                        }
                    }
                }

                let mut curr = parent;
                while let Some(parent) = curr.parent() {
                    if let Some(l_child) = parent.child(Child::Left) {
                        if l_child.as_ref() as *const _ == curr.as_ref() as *const _ {
                            if let Some(r_child) = parent.child(Child::Right) {
                                return Some(r_child.clone())
                            }
                        }
                    }
                    curr = parent;
                }
            }
        }

        None
    }
}

///
/// Unit tests for Tree and Node.
///
#[cfg(test)]
mod tests {
    use super::*;
    use std::net::Ipv4Addr;

    pub struct Data {
        pub v: u32
    }

    #[test]
    pub fn test_tree_ipv4() {
        let mut tree = Tree::<Prefix<Ipv4Addr>, Data>::new();
        let p1 = Prefix::<Ipv4Addr>::from_str("10.10.10.0/24").unwrap();
        let p2 = Prefix::<Ipv4Addr>::from_str("10.10.0.0/16").unwrap();
        let d1 = Data { v: 100 };
        let d2 = Data { v: 200 };

        let mut it = tree.get_node(&p1);
        it.set_data(d1);

        let mut it = tree.get_node(&p2);
        it.set_data(d2);

        let mut it = tree.lookup_exact(&p1);
        match it.node().as_ref() {
            Some(node) => {
                match node.data().as_ref() {
                    Some(data) => assert_eq!(data.v, 100),
                    None => assert!(false),
                }
            },
            None => assert!(false),
        }

        let mut it = tree.lookup_exact(&p2);
        match it.node().as_ref() {
            Some(node) => {
                match node.data().as_ref() {
                    Some(data) => assert_eq!(data.v, 200),
                    None => assert!(false),
                }
            },
            None => assert!(false),
        }

        let p3 = Prefix::<Ipv4Addr>::from_str("10.10.0.0/20").unwrap();
        let mut it = tree.lookup_exact(&p3);
        match it.node().as_ref() {
            None => { },
            Some(data) => assert!(false)
        }

        let mut it = tree.lookup(&p3);
        match it.node().as_ref() {
            Some(node) => {
                match node.data().as_ref() {
                    Some(data) => {
                        assert_eq!(node.prefix().len(), 16);
                        assert_eq!(data.v, 200);
                    },
                    None => assert!(false),
                }
            },
            None => assert!(false)
        }

        let d0 = Data { v: 0 };
        let pd = Prefix::<Ipv4Addr>::from_str("0.0.0.0/0").unwrap();
        let mut it = tree.get_node(&pd);
        match it.node().as_ref() {
            Some(node) => node.set_data(d0),
            None => assert!(false),
        }

        let p4 = Prefix::<Ipv4Addr>::from_str("10.0.0.0/8").unwrap();
        let mut it = tree.lookup(&p4);
        match it.node().as_ref() {
            Some(node) => assert_eq!(node.prefix().len(), 0),
            None => assert!(false),
        }

/*
        for n in tree {
            println!("{}", n.prefix().to_string());
        }

        assert!(false);
*/
    }
}
