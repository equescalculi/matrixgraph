// Copyright 2015 Marius Ritter
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// A simple graph represented by the upper right triangle of an adjacency
/// matrix of fixed size

use std::cmp;
use traits::{BasicGraphMethods, GraphProperties, GraphErrors,
             GraphAlgorithms, UndirectedGraphAlgorithms};

/// A simple graph represented by the upper right triangle of an adjacency
/// matrix of fixed size
///
/// The cells of the adjacency matrix are assigned values of type Option<f64>
/// where a None value represents the absence of an edge.
#[derive(PartialEq, Clone, Debug)]
pub struct SimpleGraph {
    size: usize,
    weights: Vec<Option<f64>>,
}

impl SimpleGraph {
    /// Creates a new simple graph object with a fixed size.
    pub fn new(size: usize) -> SimpleGraph {
        let weights: Vec<Option<f64>> = match size {
            0 => vec![],
            _ => vec![None; size * (size - 1) / 2]
        };
        SimpleGraph {
            size: size,
            weights: weights
        }
    }

    /// Creates a new simple graph object with a fixed size from a vector
    /// that is the row-wise representation of the upper right triangle of an
    /// adjacency matrix.
    ///
    /// Note: A zero-sized vector creates a graph with a single vertex.
    pub fn from_vec(weights: &Vec<Option<f64>>) -> SimpleGraph {
        let size: usize
            = (((1.0f64 + 8.0f64 * (weights.len() as f64)).powf(0.5f64)
                + 1.0f64) / 2.0f64)
              .ceil() as usize;
        assert!(weights.len() == size * (size - 1) / 2,
                "The weights vector does not fit the size of the upper \
                 right triangle of a matrix.");

        SimpleGraph {
            size: size,
            weights: weights.clone()
        }
    }

    /// Returns the vector that is the row-wise representation of the upper
    /// right triangle of the adjacency matrix of the simple graph.
    pub fn to_vec(&self) -> Vec<Option<f64>> {
        self.weights.clone()
    }

    /// Returns the vector that is the row-wise representation of the full
    /// adjacency matrix of the simple graph.
    pub fn to_digraph_vec(&self) -> Vec<Option<f64>> {
        let mut matrix = self.weights.clone();
        let size = self.size();
        for i in 0..size {
            for j in 0..i {
                let value = matrix[j * size + i];
                matrix.insert(i * size + j, value);
            }
            matrix.insert(i * (size + 1), None);
        }
        matrix
    }
}

impl BasicGraphMethods for SimpleGraph {
    fn size(&self) -> usize {
        self.size
    }

    fn get_edge(&self, edge: (usize, usize)) -> Option<f64> {
        let size: usize = self.size();
        assert!(edge.0 < size, "The first node index is out of range.");
        assert!(edge.1 < size, "The second node index is out of range.");

        let (node1, node2): (usize, usize)
            = (cmp::min(edge.0, edge.1), cmp::max(edge.0, edge.1));
        if node1 == node2 {
            return None;
        };
        self.weights[size * node1 + node2 - (node1 + 2) * (node1 + 1) / 2]
    }

    fn set_edge(&mut self, edge: (usize, usize), value: Option<f64>) {
        let size: usize = self.size();
        assert!(edge.0 < size, "The first node index is out of range.");
        assert!(edge.1 < size, "The second node index is out of range.");
        assert!(edge.0 != edge.1, "A SimpleGraph object cannot have loops.");

        let (node1, node2): (usize, usize)
            = (cmp::min(edge.0, edge.1), cmp::max(edge.0, edge.1));
        self.weights[size * node1 + node2 - (node1 + 2) * (node1 + 1) / 2]
            = value;
    }
}

impl GraphProperties for SimpleGraph {
    fn is_loopfree(&self) -> bool {
        true
    }

    fn is_symmetric(&self) -> bool {
        true
    }
}

impl GraphAlgorithms<SimpleGraph> for SimpleGraph {
    // As negative edges in undirected graphs always lead to negative cycles
    // when calculating the shortest paths, the Johnson's algorithm is
    // identical to Dijkstra's algorithm.
    fn johnson_graph(&self) -> Result<(SimpleGraph, Vec<f64>), GraphErrors> {
        if !self.is_nonnegative() {
            return Err(GraphErrors::ContainsNegativeCycle);
        }
        let size = self.size();
        let nweights: Vec<Option<f64>> = self.to_vec();
        let heights: Vec<f64> = vec![0.0f64; size];
        Ok((SimpleGraph::from_vec(&nweights), heights))
    }

    fn johnson(&self, source: usize)
            -> Result<(Vec<Option<f64>>, Vec<Option<usize>>), GraphErrors> {
        assert!(source < self.size(), "The node index is out of range.");

        match self.dijkstra(source) {
            Err(GraphErrors::ContainsNegativeEdge)
                => Err(GraphErrors::ContainsNegativeCycle),
            Err(f) => Err(f),
            Ok(m) => Ok(m)
        }
    }

    fn johnson_all(&self)
            -> Vec<Result<(Vec<Option<f64>>, Vec<Option<usize>>),
                          GraphErrors>> {
        (0..self.size()).map(|i| self.johnson(i)).collect()
    }
}

impl UndirectedGraphAlgorithms for SimpleGraph {
}

// TESTS

#[cfg(test)]
mod test {
    use traits::{BasicGraphMethods, GraphProperties, GraphErrors,
                 GraphAlgorithms, UndirectedGraphAlgorithms};

    #[test]
    fn test_graph_construction_1() {
        let u1 = vec![
            Some(4.0f64), None, Some(-1.0f64),
            Some(2.5f64), Some(-3.0f64),
            None
        ];
        let w1 = vec![
            None, Some(4.0f64), None, Some(-1.0f64),
            Some(4.0f64), None, Some(2.5f64), Some(-3.0f64),
            None, Some(2.5f64), None, None,
            Some(-1.0f64), Some(-3.0f64), None, None
        ];
        let mut g = super::SimpleGraph::from_vec(&u1);
        let edges1 = vec![
           g.get_edge((0, 0)), g.get_edge((0, 1)),
           g.get_edge((0, 2)), g.get_edge((0, 3)),
           g.get_edge((1, 0)), g.get_edge((1, 1)),
           g.get_edge((1, 2)), g.get_edge((1, 3)),
           g.get_edge((2, 0)), g.get_edge((2, 1)),
           g.get_edge((2, 2)), g.get_edge((2, 3)),
           g.get_edge((3, 0)), g.get_edge((3, 1)),
           g.get_edge((3, 2)), g.get_edge((3, 3)),
        ];
        let nbh_0: Vec<usize> = vec![1, 3].into_iter().collect();
        let nbh_1: Vec<usize> = vec![0, 2, 3].into_iter().collect();
        let nbh_2: Vec<usize> = vec![1].into_iter().collect();
        let nbh_3: Vec<usize> = vec![0, 1].into_iter().collect();
        assert_eq!(edges1, w1);
        assert_eq!(g.to_digraph_vec(), w1);
        assert_eq!(g.size(), 4);
        assert_eq!(g.is_loopfree(), true);
        assert_eq!(g.is_nonnegative(), false);
        assert_eq!(g.is_complete(), false);
        assert_eq!(g.is_symmetric(), true);
        assert_eq!(g.predecessors(0), nbh_0);
        assert_eq!(g.successors(0), nbh_0);
        assert_eq!(g.predecessors(1), nbh_1);
        assert_eq!(g.successors(1), nbh_1);
        assert_eq!(g.predecessors(2), nbh_2);
        assert_eq!(g.successors(2), nbh_2);
        assert_eq!(g.predecessors(3), nbh_3);
        assert_eq!(g.successors(3), nbh_3);

        g.set_edge((0, 2), Some(1.0f64));
        g.set_edge((3, 2), Some(3.0f64));
        let e03: f64 = g.get_edge((3, 0)).unwrap();
        g.set_edge((0, 3), Some(-e03));
        let e13: f64 = g.get_edge((3, 1)).unwrap();
        g.set_edge((1, 3), Some(0.0f64 * e13));
        let w2 = vec![
            None, Some(4.0f64), Some(1.0f64), Some(1.0f64),
            Some(4.0f64), None, Some(2.5f64), Some(-0.0f64),
            Some(1.0f64), Some(2.5f64), None, Some(3.0f64),
            Some(1.0f64), Some(-0.0f64), Some(3.0f64), None
        ];
        let edges2 = vec![
           g.get_edge((0, 0)), g.get_edge((0, 1)),
           g.get_edge((0, 2)), g.get_edge((0, 3)),
           g.get_edge((1, 0)), g.get_edge((1, 1)),
           g.get_edge((1, 2)), g.get_edge((1, 3)),
           g.get_edge((2, 0)), g.get_edge((2, 1)),
           g.get_edge((2, 2)), g.get_edge((2, 3)),
           g.get_edge((3, 0)), g.get_edge((3, 1)),
           g.get_edge((3, 2)), g.get_edge((3, 3)),
        ];
        let nbh_0_new: Vec<usize> = vec![1, 2, 3].into_iter().collect();
        let nbh_1_new: Vec<usize> = vec![0, 2, 3].into_iter().collect();
        let nbh_2_new: Vec<usize> = vec![0, 1, 3].into_iter().collect();
        let nbh_3_new: Vec<usize> = vec![0, 1, 2].into_iter().collect();
        assert_eq!(edges2, w2);
        assert_eq!(g.to_digraph_vec(), w2);
        assert_eq!(g.size(), 4);
        assert_eq!(g.is_loopfree(), true);
        assert_eq!(g.is_nonnegative(), true);
        assert_eq!(g.is_complete(), true);
        assert_eq!(g.is_symmetric(), true);
        assert_eq!(g.predecessors(0), nbh_0_new);
        assert_eq!(g.successors(0), nbh_0_new);
        assert_eq!(g.predecessors(1), nbh_1_new);
        assert_eq!(g.successors(1), nbh_1_new);
        assert_eq!(g.predecessors(2), nbh_2_new);
        assert_eq!(g.successors(2), nbh_2_new);
        assert_eq!(g.predecessors(3), nbh_3_new);
        assert_eq!(g.successors(3), nbh_3_new);
    }

    #[test]
    #[should_panic]
    fn test_graph_construction_2() {
        let w: Vec<Option<f64>> = vec![None, Some(1.0f64)];
        super::SimpleGraph::from_vec(&w);
    }

    #[test]
    fn test_graph_construction_3() {
        let g = super::SimpleGraph::new(0);
        let w: Vec<Option<f64>> = vec![];
        assert_eq!(g.size(), 0);
        assert_eq!(g.to_vec(), w);
    }

    #[test]
    #[should_panic]
    fn test_graph_construction_4() {
        let g = super::SimpleGraph::new(0);
        g.get_edge((0, 0));
    }

    #[test]
    fn test_graph_construction_5() {
        let g = super::SimpleGraph::new(1);
        let w: Vec<Option<f64>> = vec![];
        assert_eq!(g.size(), 1);
        assert_eq!(g.to_vec(), w);
        assert_eq!(g.get_edge((0, 0)), None);
    }

    #[test]
    fn test_graph_construction_6() {
        let w: Vec<Option<f64>> = vec![];
        let g = super::SimpleGraph::from_vec(&w);
        assert_eq!(g.size(), 1);
        assert_eq!(g.to_vec(), w);
        assert_eq!(g.get_edge((0, 0)), None);
    }

    #[test]
    #[should_panic]
    fn test_graph_construction_7() {
        let mut g = super::SimpleGraph::new(2);
        g.set_edge((1, 1), Some((1.0f64)));
    }

    #[test]
    fn test_shortest_paths_1() {
        let g = super::SimpleGraph::from_vec(&vec![
            Some(2.0f64), None,
            Some(-1.0f64)
        ]);
        assert_eq!(g.dijkstra(0), Err(GraphErrors::ContainsNegativeEdge));
        assert_eq!(g.johnson(0), Err(GraphErrors::ContainsNegativeCycle));
    }

    #[test]
    fn test_shortest_paths_2() {
        let g = super::SimpleGraph::from_vec(&vec![
            Some(2.0f64), Some(4.5f64), None,
            Some(3.0f64), Some(0.0f64),
            Some(2.0f64)
        ]);
        let d: Result<(Vec<Option<f64>>, Vec<Option<usize>>), GraphErrors>
            = Ok((vec![Some(0.0f64), Some(2.0f64), Some(4.0f64),
                       Some(2.0f64)],
                  vec![None, Some(0), Some(3), Some(1)]));
        assert_eq!(g.dijkstra(0), d);
        assert_eq!(g.johnson(0), d);
    }

    #[test]
    fn test_components_1() {
        let g = super::SimpleGraph::from_vec(&vec![
            None, None, None, None, Some(1.0f64),
            None, None, None, None,
            None, None, Some(1.0f64),
            Some(1.0f64), None,
            None
        ]);
        let c = vec![vec![0, 2, 5], vec![1], vec![3, 4]];
        assert_eq!(g.components(), c);
    }

    #[test]
    fn test_prim_1() {
        let g = super::SimpleGraph::from_vec(&vec![
            Some(2.0f64), Some(3.0f64), None, None,
            Some(1.0f64), Some(4.0f64), Some(-1.0f64),
            Some(1.0f64), Some(2.0f64),
            Some(5.0f64)
        ]);
        let mst: Vec<(usize, usize)> = vec![
            (0, 1), (1, 4), (1, 2), (2, 3)
        ];
        assert_eq!(g.prim(), mst);
    }

    #[test]
    fn test_prim_2() {
        let g = super::SimpleGraph::from_vec(&vec![
            Some(1.0f64), None, None,
            None, None,
            Some(2.0f64)
        ]);
        let mst: Vec<(usize, usize)> = vec![
            (0, 1), (2, 3)
        ];
        assert_eq!(g.prim(), mst);
    }
}
