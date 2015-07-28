// Copyright 2015 Marius Ritter
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// A digraph represented by a dense adjacency matrix of fixed size

use traits::{BasicGraphMethods, GraphProperties, GraphErrors,
             GraphAlgorithms, DirectedGraphAlgorithms};

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

impl GraphProperties for Digraph {
}

impl GraphAlgorithms<Digraph> for Digraph {
    fn johnson_graph(&self) -> Result<(Digraph, Vec<f64>), GraphErrors> {
        let size = self.size();
        let mut eweights: Vec<Option<f64>> = self.weights.clone();
        for i in 0..size {
            eweights.insert(size * (i + 1) + i, None);
        }
        eweights.extend(vec![Some(0.0f64); size + 1].into_iter());
        let egraph = Digraph::from_vec(&eweights);
        let heights: Vec<f64> = match egraph.bellman_ford(size) {
            Ok(m) => { m.0.iter().map(|&x| x.unwrap()).collect() }
            Err(f) => { return Err(f); }
        };
        let nweights = self.weights.iter().enumerate().map(|(i, &x)| match x {
                Some(f) => Some(f + heights[i / size] - heights[i % size]),
                None => None,
            }).collect();
        Ok((Digraph::from_vec(&nweights), heights))
    }
}

impl DirectedGraphAlgorithms for Digraph {
}

// TESTS

#[cfg(test)]
mod test {
    use traits::{BasicGraphMethods, GraphProperties, GraphErrors,
                 GraphAlgorithms, DirectedGraphAlgorithms};

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
        let set_0: Vec<usize> = vec![0];
        let set_1: Vec<usize> = vec![1];
        assert_eq!(edges1, w1);
        assert_eq!(g.size(), 2);
        assert_eq!(g.is_loopfree(), true);
        assert_eq!(g.is_nonnegative(), false);
        assert_eq!(g.is_complete(), true);
        assert_eq!(g.is_symmetric(), false);
        assert_eq!(g.predecessors(0), set_1);
        assert_eq!(g.predecessors(1), set_0);
        assert_eq!(g.successors(0), set_1);
        assert_eq!(g.successors(1), set_0);

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
        let set_01: Vec<usize> = vec![0, 1];
        assert_eq!(edges2, w2);
        assert_eq!(g.size(), 2);
        assert_eq!(g.is_loopfree(), false);
        assert_eq!(g.is_nonnegative(), true);
        assert_eq!(g.is_complete(), true);
        assert_eq!(g.is_symmetric(), false);
        assert_eq!(g.predecessors(0), set_01);
        assert_eq!(g.predecessors(1), set_01);
        assert_eq!(g.successors(0), set_01);
        assert_eq!(g.successors(1), set_01);

        g.set_edge((0, 1), w2[2]);
        assert_eq!(g.is_symmetric(), true);
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

    // From Wikipedia:
    // https://en.wikipedia.org/w/index.php?
    // title=Floyd%E2%80%93Warshall_algorithm&oldid=667601616
    #[test]
    fn test_shortest_paths_1() {
        let g = super::Digraph::from_vec(&vec![
            None, None, Some(-2.0f64), None,
            Some(4.0f64), None, Some(3.0f64), None,
            None, None, None, Some(2.0f64),
            None, Some(-1.0f64), None, None
        ]);
        let d: Result<(Vec<Option<f64>>, Vec<Option<usize>>), GraphErrors>
            = Ok((vec![Some(0.0f64), Some(-1.0f64), Some(-2.0f64),
                       Some(0.0f64)],
                  vec![None, Some(3), Some(0), Some(2)]));
        assert_eq!(g.dijkstra(0), Err(GraphErrors::ContainsNegativeEdge));
        assert_eq!(g.johnson(0), d);
    }

    #[test]
    fn test_shortest_paths_2() {
        let g = super::Digraph::from_vec(&vec![
            None, Some(2.0f64), Some(3.0f64), Some(1.0f64), None, None,
            None, None, None, None, Some(4.0f64), None,
            None, None, None, None, None, Some(7.0f64),
            None, None, Some(8.0f64), None, Some(6.0f64), Some(5.0f64),
            None, None, None, None, None, Some(5.0f64),
            Some(3.0f64), None, None, None, None, None
        ]);
        let d: Vec<Result<(Vec<Option<f64>>, Vec<Option<usize>>),
                   GraphErrors>> = vec![
            Ok((vec![Some(0.0f64), Some(2.0f64), Some(3.0f64),
                     Some(1.0f64), Some(6.0f64), Some(6.0f64)],
                vec![None, Some(0), Some(0), Some(0), Some(1), Some(3)])),
            Ok((vec![Some(12.0f64), Some(0.0f64), Some(15.0f64),
                     Some(13.0f64), Some(4.0f64), Some(9.0f64)],
                vec![Some(5), None, Some(0), Some(0), Some(1), Some(4)])),
            Ok((vec![Some(10.0f64), Some(12.0f64), Some(0.0f64),
                     Some(11.0f64), Some(16.0f64), Some(7.0f64)],
                vec![Some(5), Some(0), None, Some(0), Some(1), Some(2)])),
            Ok((vec![Some(8.0f64), Some(10.0f64), Some(8.0f64),
                     Some(0.0f64), Some(6.0f64), Some(5.0f64)],
                vec![Some(5), Some(0), Some(3), None, Some(3), Some(3)])),
            Ok((vec![Some(8.0f64), Some(10.0f64), Some(11.0f64),
                     Some(9.0f64), Some(0.0f64), Some(5.0f64)],
                vec![Some(5), Some(0), Some(0), Some(0), None, Some(4)])),
            Ok((vec![Some(3.0f64), Some(5.0f64), Some(6.0f64),
                     Some(4.0f64), Some(9.0f64), Some(0.0f64)],
                vec![Some(5), Some(0), Some(0), Some(0), Some(1), None]))
        ];
        assert_eq!(g.dijkstra_all(), d);
        assert_eq!(g.johnson_all(), d);
    }

    // From Wikipedia:
    // https://en.wikipedia.org/w/index.php?
    // title=Floyd%E2%80%93Warshall_algorithm&oldid=667601616
    #[test]
    fn test_shortest_paths_3() {
        let g = super::Digraph::from_vec(&vec![
            None, None, Some(-2.0f64), None,
            Some(4.0f64), None, Some(3.0f64), None,
            None, None, None, Some(2.0f64),
            None, Some(-1.0f64), None, None
        ]);
        let d: Vec<Result<(Vec<Option<f64>>, Vec<Option<usize>>),
                   GraphErrors>> = vec![
            Ok((vec![Some(0.0f64), Some(-1.0f64), Some(-2.0f64),
                     Some(0.0f64)],
                vec![None, Some(3), Some(0), Some(2)])),
            Ok((vec![Some(4.0f64), Some(0.0f64), Some(2.0f64), Some(4.0f64)],
                vec![Some(1), None, Some(0), Some(2)])),
            Ok((vec![Some(5.0f64), Some(1.0f64), Some(0.0f64), Some(2.0f64)],
                vec![Some(1), Some(3), None, Some(2)])),
            Ok((vec![Some(3.0f64), Some(-1.0f64), Some(1.0f64), Some(0.0f64)],
                vec![Some(1), Some(3), Some(0), None]))
        ];
        assert_eq!(g.bellman_ford_all(), d);
        assert_eq!(g.johnson_all(), d);
    }

    // From Wikipedia:
    // https://en.wikipedia.org/w/index.php?
    // title=Floyd%E2%80%93Warshall_algorithm&oldid=667601616
    #[test]
    fn test_shortest_paths_4() {
        let g = super::Digraph::from_vec(&vec![
            None, None, Some(-2.0f64), None,
            Some(4.0f64), None, Some(3.0f64), None,
            None, None, None, Some(2.0f64),
            None, Some(-1.0f64), None, None
        ]);
        let d = vec![
            vec![Some(0.0f64), Some(-1.0f64), Some(-2.0f64), Some(0.0f64)],
            vec![Some(4.0f64), Some(0.0f64), Some(2.0f64), Some(4.0f64)],
            vec![Some(5.0f64), Some(1.0f64), Some(0.0f64), Some(2.0f64)],
            vec![Some(3.0f64), Some(-1.0f64), Some(1.0f64), Some(0.0f64)]
        ];
        let p = vec![
            vec![None, Some(3), Some(0), Some(2)],
            vec![Some(1), None, Some(0), Some(2)],
            vec![Some(1), Some(3), None, Some(2)],
            vec![Some(1), Some(3), Some(0), None]
        ];
        assert_eq!(g.floyd_warshall(), (d, p));
    }

    // negative cycle
    #[test]
    fn test_shortest_paths_5() {
        let g = super::Digraph::from_vec(&vec![
            None, Some(1.0f64), None,
            None, None, Some(2.0f64),
            Some(-4.0f64), None, None
        ]);
        assert_eq!(g.bellman_ford(0),
                   Err(GraphErrors::ContainsNegativeCycle));
        assert_eq!(g.johnson(0), Err(GraphErrors::ContainsNegativeCycle));
    }

    #[test]
    fn test_components_1() {
        let g = super::Digraph::from_vec(&vec![
            None, Some(1.0f64), None, None, None, None, Some(1.0f64),
            None, None, Some(1.0f64), None, None, None, None,
            Some(1.0f64), None, None, None, None, None, None,
            None, None, Some(1.0f64), None, Some(1.0f64), None, None,
            None, None, None, None, None, Some(1.0f64), None,
            Some(1.0f64), None, None, Some(1.0f64), Some(1.0f64), None, None,
            None, None, None, None, None, None, Some(1.0f64)
        ]);
        let c0: Vec<usize> = vec![0, 1, 2];
        let c1: Vec<usize> = vec![3, 4, 5];
        let c2: Vec<usize> = vec![6];
        assert_eq!(g.sc_components(), vec![c0, c1, c2]);
    }
}
