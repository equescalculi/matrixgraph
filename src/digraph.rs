// Copyright 2015 Marius Ritter
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// A digraph represented by a dense adjacency matrix of fixed size

use traits::BasicGraphMethods;

/// A digraph represented by a dense adjacency matrix of fixed size
///
/// The cells of the adjacency matrix are assigned values of type Option<f64>
/// where a None value represents the absence of an edge.
#[derive(PartialEq, Clone, Debug)]
pub struct Digraph {
    size: usize,
    weights: Vec<Option<f64>>,
}

impl Digraph {
    /// Creates a new digraph object with a fixed size.
    pub fn new(size: usize) -> Digraph {
        let weights: Vec<Option<f64>> = vec![None; size * size];
        Digraph {
            size: size,
            weights: weights
        }
    }

    /// Creates a new digraph object with a fixed size from a vector that is
    /// the row-wise representation of an adjacency matrix.
    pub fn from_vec(weights: &Vec<Option<f64>>) -> Digraph {
        let size: usize
            = (weights.len() as f64).powf(0.5f64).floor() as usize;
        assert!(weights.len() == size * size,
                "The weights vector is not of square dimension.");

        Digraph {
            size: size,
            weights: weights.clone()
        }
    }

    /// Returns the vector that is the row-wise representation of the
    /// adjacency matrix of the digraph.
    pub fn to_vec(&self) -> Vec<Option<f64>> {
        self.weights.clone()
    }
}

impl BasicGraphMethods for Digraph {
    fn size(&self) -> usize {
        self.size
    }

    fn get_edge(&self, edge: (usize, usize)) -> Option<f64> {
        let (node1, node2): (usize, usize) = edge;
        let size: usize = self.size();
        assert!(node1 < size, "The first node index is out of range.");
        assert!(node2 < size, "The second node index is out of range.");

        self.weights[size * node1 + node2]
    }

    fn set_edge(&mut self, edge: (usize, usize), value: Option<f64>) {
        let (node1, node2): (usize, usize) = edge;
        let size: usize = self.size();
        assert!(node1 < size, "The first node index is out of range.");
        assert!(node2 < size, "The second node index is out of range.");

        self.weights[size * node1 + node2] = value;
    }
}

// TESTS

#[cfg(test)]
mod test {
    use traits::BasicGraphMethods;

    #[test]
    fn test_graph_construction_1() {
        let w1 = vec![
            None, Some(-1.0f64),
            Some(4.0f64), None
        ];
        let mut g = super::Digraph::from_vec(&w1);
        let edges1 = vec![
           g.get_edge((0, 0)), g.get_edge((0, 1)),
           g.get_edge((1, 0)), g.get_edge((1, 1))
        ];
        assert_eq!(edges1, w1);
        assert_eq!(g.size(), 2);

        let w2 = vec![
            Some(1.0f64), Some(2.0f64),
            Some(3.0f64), Some(4.0f64),
        ];
        g.set_edge((0, 0), w2[0]);
        g.set_edge((0, 1), w2[1]);
        g.set_edge((1, 0), w2[2]);
        g.set_edge((1, 1), w2[3]);
        let edges2 = vec![
           g.get_edge((0, 0)), g.get_edge((0, 1)),
           g.get_edge((1, 0)), g.get_edge((1, 1))
        ];
        assert_eq!(edges2, w2);
        assert_eq!(g.size(), 2);
    }

    #[test]
    #[should_panic]
    fn test_graph_construction_2() {
        let w: Vec<Option<f64>> = vec![None, Some(1.0f64)];
        super::Digraph::from_vec(&w);
    }

    #[test]
    fn test_graph_construction_3() {
        let g = super::Digraph::new(0);
        let w: Vec<Option<f64>> = vec![];
        assert_eq!(g.size(), 0);
        assert_eq!(g.to_vec(), w);
    }

    #[test]
    #[should_panic]
    fn test_graph_construction_4() {
        let g = super::Digraph::new(0);
        g.get_edge((0, 0));
    }
}
