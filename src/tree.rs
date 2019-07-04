//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//

use std::rc::Rc;
use std::cell::RefCell;

///
/// Tree struct.
///
pub struct Tree<P, D> {
    /// Top Node.
    top: Rc<Node<P, D>>,

    /// Number of node in this tree.
    count: usize,
}

///
/// Tree impl.
///
impl<P, D> Tree<P, D> {

}

///
/// Enum Child.
///
enum Child {
    Left = 0,
    Right = 1,
}

///
/// Node struct.
///
pub struct Node<P, D> {
    /// Parent Node.
    parent: RefCell<Option<Rc<Node<P, D>>>>,

    /// Child Nodes.
    children: [RefCell<Option<Rc<Node<P, D>>>>; 2],

    /// Prefix associated with this node.
    prefix: P,

    /// Data.
    data: Option<Rc<D>>,
}

///
/// Node impl.
///
impl<P, D> Node<P, D> {
    /// Return new node.
    fn new(prefix: P) -> Node<P, D> {
        Node {
            parent: RefCell::new(None),
            children: [RefCell::new(None), RefCell::new(None)],
            prefix: prefix,
            data: None,
        }
    }

    /// Return reference to prefix.
    fn prefix(&self) -> &P {
        &self.prefix
    }

    /// Return one of child node - left(0) or right(1)
    fn child(&self, bit: Child) -> Option<Rc<Node<P, D>>> {
        self.children[bit as usize].borrow().clone()
    }

    /// Return parent node.
    fn parent(&self) -> Option<Rc<Node<P, D>>> {
        self.parent.borrow().clone()
    }

    /// Set child at left or right.
    fn set_child_at(&self, child: Rc<Node<P, D>>, bit: Child) {
        self.children[bit as usize].replace(Some(child.clone()));
    }
}

