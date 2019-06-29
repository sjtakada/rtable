//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//

use std::rc::Rc;

struct Tree<P, D> {
    top: Rc<Node<P, D>>,

    prefix: P,
}

struct Node<P, D> {
    parent: Rc<Node<P, D>>,

//    children: [Rc<Node<P, D>>; 2],
    children: (Rc<Node<P, D>>, Rc<Node<P, D>>),

    prefix: P,

    data: Rc<D>,
}
