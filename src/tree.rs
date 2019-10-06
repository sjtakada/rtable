//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//

use std::cell::RefCell;
use std::cell::RefMut;
use std::iter::IntoIterator;
use std::iter::Iterator;
use std::rc::Rc;

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
        Some(node) => node.prefix.len() <= prefix.len() && node.prefix().contains(prefix),
    }
}

fn same_object<T>(a: *const T, b: *const T) -> bool {
    a == b
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

    /// Return count with data.
    pub fn count(&self) -> usize {
        self.count
    }

    /// Get node with given prefix, create one if it doesn't exist.
    pub fn get_node(&mut self, prefix: &P) -> NodeIterator<P, D> {
        let mut matched: Option<Rc<Node<P, D>>> = None;
        let mut curr: Option<Rc<Node<P, D>>> = self.top.clone();
        let mut new_node: Rc<Node<P, D>>;

        while node_match_prefix(curr.clone(), prefix) {
            let node = curr.clone().unwrap();
            if node.prefix().len() == prefix.len() {
                return NodeIterator::from_node(node);
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
                    }
                    None => {
                        self.top.replace(new_node.clone());
                    }
                }
            }
            Some(node) => {
                new_node = Rc::new(Node::from_common(node.prefix(), prefix));
                Node::<P, D>::set_child(new_node.clone(), node);

                match matched {
                    Some(node) => {
                        Node::<P, D>::set_child(node, new_node.clone());
                    }
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

    /// Insert data with given prefix, and return:
    /// - false if data already exist with the prefix.
    /// - true if successfully inserted the data.
    pub fn insert(&mut self, prefix: &P, data: D) -> bool {
        let it = self.lookup_exact(prefix);
        match it.node() {
            Some(node) => {
                if node.has_data() {
                    false
                } else {
                    node.set_data(data);
                    self.count += 1;
                    true
                }
            }
            None => {
                let mut it = self.get_node(prefix);
                it.set_data(data);
                self.count += 1;
                true
            }
        }
    }

    /// Update data with given prefix, and return:
    /// - old data if data exists and successfully replace.
    /// - None if data does not exist, and replace does not occur.
    pub fn update(&mut self, prefix: &P, data: D) -> Option<D> {
        let it = self.lookup_exact(prefix);
        match it.node() {
            Some(node) => {
                if node.has_data() {
                    node.set_data(data)
                } else {
                    None
                }
            }
            None => None,
        }
    }

    /// Insert if data does not exist, or Update, and return:
    /// - old data if data exists and successfully replace.
    /// - None if data does not exist.
    pub fn upsert(&mut self, prefix: &P, data: D) -> Option<D> {
        let it = self.lookup_exact(prefix);
        match it.node() {
            Some(node) => {
                if !node.has_data() {
                    self.count += 1;
                }
                node.set_data(data)
            }
            None => {
                self.get_node(prefix).set_data(data);
                self.count += 1;
                None
            }
        }
    }

    /// Delete data with the prefix if data exist, and return:
    /// - old data if data exists and successfully delete.
    /// - None if data does not exist.
    pub fn delete(&mut self, prefix: &P) -> Option<D> {
        let it = self.lookup_exact(prefix);
        let old_data = match it.node() {
            Some(node) => {
                if node.has_data() {
                    self.count -= 1;
                }
                node.unset_data()
            }
            None => None,
        };
        self.erase(it);
        old_data
    }

    /// Perform exact match lookup.
    pub fn lookup_exact(&self, prefix: &P) -> NodeIterator<P, D> {
        let mut curr = self.top.clone();

        while node_match_prefix(curr.clone(), prefix) {
            let node = curr.clone().unwrap();
            if node.prefix().len() == prefix.len() {
                if node.has_data() {
                    return NodeIterator::from_node(node);
                } else {
                    break;
                }
            }

            curr = node.child_with(prefix.bit_at(node.prefix().len()));
        }

        NodeIterator { node: None }
    }

    /// Perform longest match lookup.
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
        } else {
            NodeIterator { node: None }
        }
    }

    /// Erase a node from tree, and return iterator for next node.
    pub fn erase(&mut self, it: NodeIterator<P, D>) -> NodeIterator<P, D> {
        let curr = it.node();
        let next = match curr {
            Some(node) => node.next(),
            None => None,
        };

        if let Some(target) = curr {
            let has_left = target.child(Child::Left).is_some();
            let has_right = target.child(Child::Right).is_some();

            // if the node has both children, we cannot erase, this is error situation.
            if has_left && has_right {
                return NodeIterator { node: None };
            }

            let child = if has_left {
                target.children[Child::Left as usize].replace(None)
            } else {
                target.children[Child::Right as usize].replace(None)
            };

            let parent = target.parent().clone();
            if child.is_some() {
                match parent {
                    Some(parent) => child.clone().unwrap().set_parent(parent.clone()),
                    None => child.clone().unwrap().unset_parent(),
                }
            }

            let parent = target.parent().clone();
            match parent {
                Some(node) => {
                    // TODO: refactoring.
                    let bit = if node.has_child_with(Child::Left as u8)
                        && same_object(node.child(Child::Left).unwrap().as_ref(), target.as_ref())
                    {
                        Child::Left
                    } else {
                        Child::Right
                    };

                    match child {
                        None => node.unset_child_at(bit as u8),
                        Some(child) => node.set_child_at(child, bit as u8),
                    }
                }
                None => {
                    self.top = child.clone();
                }
            }

            let parent = target.parent().clone();
            if parent.is_some() {
                let node = parent.clone().unwrap();
                if !node.is_locked() {
                    self.erase(NodeIterator { node: parent });
                }
            }
        }

        return NodeIterator { node: next };
    }

    /// Return node iterator.
    pub fn node_iter(&self) -> NodeIterator<P, D> {
        NodeIterator::<P, D> {
            node: self.top.clone(),
        }
    }
}

///
/// Tree IntoIterator.
///
impl<P: Prefixable, D> IntoIterator for &Tree<P, D> {
    type Item = Rc<Node<P, D>>;
    type IntoIter = DataIterator<P, D>;

    fn into_iter(self) -> Self::IntoIter {
        let top = self.top.clone();

        DataIterator::<P, D> { node: top }
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
            node: Some(node.clone()),
        }
    }

    pub fn node(&self) -> &Option<Rc<Node<P, D>>> {
        &self.node
    }

    pub fn set_data(&mut self, data: D) {
        let node = self.node.clone();
        match node {
            Some(node) => node.set_data(data),
            None => None,
        };
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
            }
            None => None,
        }
    }
}

/// DataIterator, only iterate node with data.
pub struct DataIterator<P: Prefixable, D> {
    node: Option<Rc<Node<P, D>>>,
}

/// Impl DataIterator.
impl<P: Prefixable, D> DataIterator<P, D> {
    pub fn node(&self) -> &Option<Rc<Node<P, D>>> {
        &self.node
    }
}

/// Impl Iterator for DataIterator.
impl<P: Prefixable, D> Iterator for DataIterator<P, D> {
    type Item = Rc<Node<P, D>>;
    fn next(&mut self) -> Option<Rc<Node<P, D>>> {
        let node = self.node.clone();
        match node {
            Some(node) => {
                if !node.has_data() {
                    let node = node.next_with_data().clone();
                    match node {
                        Some(node) => {
                            self.node = node.next_with_data().clone();
                            Some(node)
                        }
                        None => return None,
                    }
                } else {
                    self.node = node.next_with_data().clone();
                    Some(node)
                }
            }
            None => None,
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

    /// Return true if child at left or right.
    pub fn has_child_with(&self, bit: u8) -> bool {
        if let Some(ref _node) = *self.children[bit as usize].borrow_mut() {
            true
        } else {
            false
        }
    }

    /// Return parent node.
    pub fn parent(&self) -> Option<Rc<Node<P, D>>> {
        self.parent.borrow_mut().clone()
    }

    /// Set given node as a child at left or right
    fn set_child(parent: Rc<Node<P, D>>, child: Rc<Node<P, D>>) {
        let bit = child.prefix().bit_at(parent.prefix().len());
        parent.set_child_at(child.clone(), bit);
        child.set_parent(parent.clone());
    }

    /// Set child at left or right.
    fn set_child_at(&self, child: Rc<Node<P, D>>, bit: u8) {
        self.children[bit as usize]
            .borrow_mut()
            .replace(child.clone());
    }

    /// Unset child at left or fight.
    fn unset_child_at(&self, bit: u8) {
        self.children[bit as usize].replace(None);
    }

    /// Set parent.
    pub fn set_parent(&self, parent: Rc<Node<P, D>>) {
        self.parent.replace(Some(parent.clone()));
    }

    /// Unset parent.
    pub fn unset_parent(&self) {
        self.parent.replace(None);
    }

    /// Set data.
    pub fn set_data(&self, data: D) -> Option<D> {
        self.data.replace(Some(data))
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
            return Some(node.clone());
        } else if let Some(node) = self.child(Child::Right) {
            return Some(node.clone());
        } else {
            if let Some(parent) = self.parent() {
                if let Some(l_child) = parent.child(Child::Left) {
                    if l_child.as_ref() as *const _ == self as *const _ {
                        if let Some(r_child) = parent.child(Child::Right) {
                            return Some(r_child.clone());
                        }
                    }
                }

                let mut curr = parent;
                while let Some(parent) = curr.parent() {
                    if let Some(l_child) = parent.child(Child::Left) {
                        if l_child.as_ref() as *const _ == curr.as_ref() as *const _ {
                            if let Some(r_child) = parent.child(Child::Right) {
                                return Some(r_child.clone());
                            }
                        }
                    }
                    curr = parent;
                }
            }
        }

        None
    }

    /// Return next Node with data.
    pub fn next_with_data(&self) -> Option<Rc<Node<P, D>>> {
        let mut next = self.next();

        while let Some(node) = next {
            if node.has_data() {
                return Some(node);
            }
            next = node.next();
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
    use std::net::Ipv6Addr;

    pub struct Data {
        pub v: u32,
    }

    impl Data {
        fn new(v: u32) -> Rc<Data> {
            Rc::new(Data { v: v })
        }
    }

    type RouteTableIpv4 = Tree<Prefix<Ipv4Addr>, Rc<Data>>;
    type RouteTableIpv6 = Tree<Prefix<Ipv6Addr>, Rc<Data>>;

    fn route_ipv4_add(
        tree: &mut RouteTableIpv4,
        prefix_str: &str,
        d: Rc<Data>,
    ) -> Result<(), PrefixParseError> {
        let p = Prefix::<Ipv4Addr>::from_str(prefix_str)?;
        tree.insert(&p, d);

        Ok(())
    }

    fn route_ipv4_delete(
        tree: &mut RouteTableIpv4,
        prefix_str: &str,
    ) -> Result<(), PrefixParseError> {
        let p = Prefix::<Ipv4Addr>::from_str(prefix_str)?;
        tree.delete(&p);

        Ok(())
    }

    fn route_ipv4_lookup(
        tree: &RouteTableIpv4,
        prefix_str: &str,
    ) -> Result<Option<(Rc<Data>, Prefix<Ipv4Addr>)>, PrefixParseError> {
        let p = Prefix::<Ipv4Addr>::from_str(prefix_str)?;
        let it = tree.lookup(&p);

        match it.node().as_ref() {
            Some(node) => {
                let data = node.data().clone();
                match data {
                    Some(data) => Ok(Some((data.clone(), node.prefix().clone()))),
                    None => Ok(None),
                }
            }
            None => Ok(None),
        }
    }

    fn route_ipv4_lookup_exact<'a>(
        tree: &RouteTableIpv4,
        prefix_str: &str,
    ) -> Result<Option<Rc<Data>>, PrefixParseError> {
        let p = Prefix::<Ipv4Addr>::from_str(prefix_str)?;
        let it = tree.lookup_exact(&p);

        match it.node().as_ref() {
            Some(node) => Ok(node.data().clone()),
            None => Ok(None),
        }
    }

    fn route_ipv6_add(
        tree: &mut RouteTableIpv6,
        prefix_str: &str,
        d: Rc<Data>,
    ) -> Result<(), PrefixParseError> {
        let p = Prefix::<Ipv6Addr>::from_str(prefix_str)?;
        tree.insert(&p, d);

        Ok(())
    }

    fn route_ipv6_delete(
        tree: &mut RouteTableIpv6,
        prefix_str: &str,
    ) -> Result<(), PrefixParseError> {
        let p = Prefix::<Ipv6Addr>::from_str(prefix_str)?;
        tree.delete(&p);

        Ok(())
    }

    fn route_ipv6_lookup(
        tree: &RouteTableIpv6,
        prefix_str: &str,
    ) -> Result<Option<(Rc<Data>, Prefix<Ipv6Addr>)>, PrefixParseError> {
        let p = Prefix::<Ipv6Addr>::from_str(prefix_str)?;
        let it = tree.lookup(&p);

        match it.node().as_ref() {
            Some(node) => {
                let data = node.data().clone();
                match data {
                    Some(data) => Ok(Some((data.clone(), node.prefix().clone()))),
                    None => Ok(None),
                }
            }
            None => Ok(None),
        }
    }

    fn route_ipv6_lookup_exact<'a>(
        tree: &RouteTableIpv6,
        prefix_str: &str,
    ) -> Result<Option<Rc<Data>>, PrefixParseError> {
        let p = Prefix::<Ipv6Addr>::from_str(prefix_str)?;
        let it = tree.lookup_exact(&p);

        match it.node().as_ref() {
            Some(node) => Ok(node.data().clone()),
            None => Ok(None),
        }
    }

    #[test]
    pub fn test_tree_ipv4() {
        let mut tree = RouteTableIpv4::new();

        route_ipv4_add(&mut tree, "10.10.10.0/24", Data::new(100)).expect("Route add error");
        route_ipv4_add(&mut tree, "10.10.0.0/16", Data::new(200)).expect("Route add error");

        match route_ipv4_lookup(&tree, "10.10.10.0/24").expect("Route lookup error") {
            Some((data, _)) => assert_eq!(data.v, 100),
            None => assert!(false),
        }

        match route_ipv4_lookup_exact(&tree, "10.10.0.0/16").expect("Route lookup error") {
            Some(data) => assert_eq!(data.v, 200),
            None => assert!(false),
        }

        match route_ipv4_lookup_exact(&tree, "10.10.0.0/20").expect("Route lookup error") {
            Some(_data) => assert!(false),
            None => {}
        }

        match route_ipv4_lookup(&tree, "10.10.0.0/20").expect("Route lookup error") {
            Some((data, p)) => {
                assert_eq!(p.len(), 16);
                assert_eq!(data.v, 200);
            }
            None => assert!(false),
        }

        route_ipv4_add(&mut tree, "0.0.0.0/0", Data::new(0)).expect("Route add error");

        match route_ipv4_lookup(&tree, "10.0.0.0/8").expect("Route lookup error") {
            Some((_data, p)) => {
                assert_eq!(p.len(), 0);
            }
            None => assert!(false),
        }

        assert_eq!(tree.count(), 3);

        // TODO: Actually it does not delete the route.
        route_ipv4_delete(&mut tree, "10.10.0.0/20").expect("Route delete error");
        assert_eq!(tree.count(), 3);

        route_ipv4_add(&mut tree, "1.1.1.1/32", Data::new(0)).expect("Route add error");
        route_ipv4_add(&mut tree, "192.168.1.0/24", Data::new(0)).expect("Route add error");

        route_ipv4_add(&mut tree, "127.0.0.0/8", Data::new(0)).expect("Route add error");
        route_ipv4_add(&mut tree, "20.20.0.0/20", Data::new(0)).expect("Route add error");
        route_ipv4_add(&mut tree, "64.64.64.128/25", Data::new(0)).expect("Route add error");

        let v: Vec<_> = tree.into_iter().map(|n| n.prefix().to_string()).collect();
        assert_eq!(
            v,
            &[
                "0.0.0.0/0",
                "1.1.1.1/32",
                "10.10.0.0/16",
                "10.10.10.0/24",
                "20.20.0.0/20",
                "64.64.64.128/25",
                "127.0.0.0/8",
                "192.168.1.0/24"
            ]
        );

        let v: Vec<_> = tree.node_iter().map(|n| n.prefix().to_string()).collect();
        assert_eq!(
            v,
            &[
                "0.0.0.0/0",
                "0.0.0.0/1",
                "0.0.0.0/3",
                "0.0.0.0/4",
                "1.1.1.1/32",
                "10.10.0.0/16",
                "10.10.10.0/24",
                "20.20.0.0/20",
                "64.0.0.0/2",
                "64.64.64.128/25",
                "127.0.0.0/8",
                "192.168.1.0/24"
            ]
        );

        assert_eq!(tree.count(), 8);

        route_ipv4_delete(&mut tree, "10.10.10.0/24").expect("Route add error");
        route_ipv4_delete(&mut tree, "10.10.0.0/16").expect("Route add error");
        route_ipv4_delete(&mut tree, "0.0.0.0/0").expect("Route add error");
        route_ipv4_delete(&mut tree, "1.1.1.1/32").expect("Route add error");
        route_ipv4_delete(&mut tree, "192.168.1.0/24").expect("Route add error");
        route_ipv4_delete(&mut tree, "127.0.0.0/8").expect("Route add error");
        route_ipv4_delete(&mut tree, "20.20.0.0/20").expect("Route add error");
        route_ipv4_delete(&mut tree, "64.64.64.128/25").expect("Route add error");

        assert_eq!(tree.count(), 0);

        let x: Vec<&str> = [].to_vec();

        let v: Vec<_> = tree.into_iter().map(|n| n.prefix().to_string()).collect();
        assert_eq!(v, x);

        let v: Vec<_> = tree.node_iter().map(|n| n.prefix().to_string()).collect();
        assert_eq!(v, x);
    }

    #[test]
    pub fn test_tree_ipv6() {
        let mut tree = RouteTableIpv6::new();

        route_ipv6_add(&mut tree, "2001::/64", Data::new(100)).expect("Route add error");
        route_ipv6_add(&mut tree, "2001::/48", Data::new(200)).expect("Route add error");

        match route_ipv6_lookup(&tree, "2001::/64").expect("Route lookup error") {
            Some((data, _)) => assert_eq!(data.v, 100),
            None => assert!(false),
        }

        match route_ipv6_lookup_exact(&tree, "2001::/48").expect("Route lookup error") {
            Some(data) => assert_eq!(data.v, 200),
            None => assert!(false),
        }

        match route_ipv6_lookup_exact(&tree, "2001::/56").expect("Route lookup error") {
            Some(_data) => assert!(false),
            None => {}
        }

        match route_ipv6_lookup(&tree, "2001::/56").expect("Route lookup error") {
            Some((data, p)) => {
                assert_eq!(p.len(), 48);
                assert_eq!(data.v, 200);
            }
            None => assert!(false),
        }

        route_ipv6_add(&mut tree, "::/0", Data::new(0)).expect("Route add error");

        match route_ipv6_lookup(&tree, "2001::/32").expect("Route lookup error") {
            Some((_data, p)) => {
                assert_eq!(p.len(), 0);
            }
            None => assert!(false),
        }

        assert_eq!(tree.count(), 3);

        // Likewise, it does not delete the route.
        route_ipv6_delete(&mut tree, "2001::/56").expect("Route delete error");
        assert_eq!(tree.count(), 3);

        route_ipv6_add(&mut tree, "2001:db8::1/128", Data::new(0)).expect("Route add error");
        route_ipv6_add(&mut tree, "3001:a:b::c/64", Data::new(0)).expect("Route add error");
        route_ipv6_add(&mut tree, "7001:1:1::/64", Data::new(0)).expect("Route add error");
        route_ipv6_add(&mut tree, "ff80::/10", Data::new(0)).expect("Route add error");
        route_ipv6_add(&mut tree, "ff00::/8", Data::new(0)).expect("Route add error");

        let v: Vec<_> = tree.into_iter().map(|n| n.prefix().to_string()).collect();
        assert_eq!(
            v,
            &[
                "::/0",
                "2001::/48",
                "2001::/64",
                "2001:db8::1/128",
                "3001:a:b::c/64",
                "7001:1:1::/64",
                "ff00::/8",
                "ff80::/10"
            ]
        );
        let v: Vec<_> = tree.node_iter().map(|n| n.prefix().to_string()).collect();
        assert_eq!(
            v,
            &[
                "::/0",
                "::/1",
                "2000::/3",
                "2001::/20",
                "2001::/48",
                "2001::/64",
                "2001:db8::1/128",
                "3001:a:b::c/64",
                "7001:1:1::/64",
                "ff00::/8",
                "ff80::/10"
            ]
        );

        route_ipv6_delete(&mut tree, "2001::/64").expect("Route add error");
        route_ipv6_delete(&mut tree, "2001::/48").expect("Route add error");
        route_ipv6_delete(&mut tree, "::/0").expect("Route add error");
        route_ipv6_delete(&mut tree, "2001:db8::1/128").expect("Route add error");
        route_ipv6_delete(&mut tree, "3001:a:b::c/64").expect("Route add error");
        route_ipv6_delete(&mut tree, "7001:1:1::/64").expect("Route add error");
        route_ipv6_delete(&mut tree, "ff80::/10").expect("Route add error");
        route_ipv6_delete(&mut tree, "ff00::/8").expect("Route add error");

        assert_eq!(tree.count(), 0);

        let x: Vec<&str> = [].to_vec();

        let v: Vec<_> = tree.into_iter().map(|n| n.prefix().to_string()).collect();
        assert_eq!(v, x);

        let v: Vec<_> = tree.node_iter().map(|n| n.prefix().to_string()).collect();
        assert_eq!(v, x);
    }
}
