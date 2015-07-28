// Copyright 2015 Marius Ritter
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::{HashMap, HashSet};
use distance_queue::DistanceQueue;

/// Provides basic graph methods.
pub trait BasicGraphMethods {
    /// Returns the size of the graph, i.e. its number of vertices.
    fn size(&self) -> usize;

    /// Returns the value of an edge of the graph.
    fn get_edge(&self, edge: (usize, usize)) -> Option<f64>;

    /// Sets the value of an edge of the graph.
    fn set_edge(&mut self, edge: (usize, usize), value: Option<f64>);
}

/// Provides methods to check the graph for several properties.
pub trait GraphProperties : BasicGraphMethods {
    /// Returns `true` if the graph is loop-free.
    fn is_loopfree(&self) -> bool {
        for i in 0..self.size() {
            if self.get_edge((i, i)).is_some() {
                return false;
            }
        }
        true
    }

    /// Returns `true` if the graph has no edges with negative weight.
    fn is_nonnegative(&self) -> bool {
        for i in 0..self.size() {
            for j in 0..self.size() {
                let edge = self.get_edge((i, j));
                if let Some(w) = edge {
                    if w.is_sign_negative() && w < 0.0f64 {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Returns `true` if the graph is complete.
    fn is_complete(&self) -> bool {
        for i in 0..self.size() {
            for j in 0..self.size() {
                if i != j && self.get_edge((i, j)).is_none() {
                    return false;
                }
            }
        }
        true
    }

    /// Returns `true` if the graph is symmetric.
    fn is_symmetric(&self) -> bool {
        for i in 0..self.size() {
            for j in 0..i {
                if self.get_edge((i, j)) != self.get_edge((j, i)) {
                    return false;
                }
            }
        }
        true
    }

    /// Returns the direct predecessors of a given vertex as a vector.
    fn predecessors(&self, node: usize) -> Vec<usize> {
        assert!(node < self.size(), "The target index is out of range.");

        (0..self.size()).filter(|&i| self.get_edge((i, node)).is_some())
            .collect()
    }

    /// Returns the direct successors of a given vertex as a vector.
    fn successors(&self, node: usize) -> Vec<usize> {
        assert!(node < self.size(), "The source index is out of range.");

        (0..self.size()).filter(|&i| self.get_edge((node, i)).is_some())
            .collect()
    }
}

/// Error types that are returned by the graph algorithms.
#[derive(Eq, PartialEq, Clone, Debug)]
pub enum GraphErrors {
    /// Is returned by `dijkstra` and `dijkstra_all` if the graph contains
    /// edges with negative weights.
    ContainsNegativeEdge,

    /// Is returned by `bellman_ford`, `bellman_ford_all`, `johnson` and
    /// `johnson_all` if the graph contains negative cycles.
    ContainsNegativeCycle,
}

/// Provides several graph algorithms that are applicable for both undirected
/// and directed graphs.
pub trait GraphAlgorithms<T> : GraphProperties where T: GraphAlgorithms<T> {
    /// Performs Dijkstra's algorithm starting from a given vertex and
    /// returns a Result object. The result is an error in the case of a
    /// negative edge weight. Otherwise the result is an tuple containing a
    /// vector of the sums of weights of the shortest paths and a vector of
    /// the predecessors of each vertex on its shortest path.
    fn dijkstra(&self, source: usize)
            -> Result<(Vec<Option<f64>>, Vec<Option<usize>>), GraphErrors> {
        let size = self.size();
        assert!(source < size, "The node index is out of range.");

        if !self.is_nonnegative() {
            return Err(GraphErrors::ContainsNegativeEdge);
        }

        let mut dists: Vec<Option<f64>> = (0..size)
            .map(|i| match i == source {
                true => Some(0.0f64),
                false => None,
            }).collect();

        let mut predecessors: Vec<Option<usize>> = vec![None; size];

        let mut queue: DistanceQueue = DistanceQueue::new();
        for i in 0..size {
            if i == source {
                queue.push((i, Some(0.0f64)));
            } else {
                queue.push((i, None));
            }
        }

        let mut unprocessed: HashSet<usize> = (0..size).collect();
        while let Some(item) = queue.pop() {
            let (node, val) = item;
            unprocessed.remove(&node);
            if let Some(ndist) = val {
                for &i in unprocessed.iter() {
                    if let Some(edge) = self.get_edge((node, i)) {
                        let altdist = ndist + edge;
                        if dists[i].is_none() || altdist < dists[i].unwrap() {
                            predecessors[i] = Some(node);
                            dists[i] = Some(altdist);
                            queue.decrease(i, Some(altdist));
                        }
                    }
                }
            }
        }

        Ok((dists, predecessors))
    }

    /// Performs Dijkstra's algorithm for all vertices and returns a vector
    /// containing the result for each vertex as described for `dijkstra`.
    fn dijkstra_all(&self)
            -> Vec<Result<(Vec<Option<f64>>, Vec<Option<usize>>),
                          GraphErrors>> {
        (0..self.size()).map(|i| self.dijkstra(i)).collect()
    }

    /// Performs the Bellman-Ford algorithm starting from a given vertex and
    /// returns a Result object. The result is an error in the case of a
    /// negative cycle. Otherwise the result unwraps to tuple containing a
    /// vector of the sums of weights of the shortest paths and a vector of
    /// the predecessors of each vertex on its shortest path.
    fn bellman_ford(&self, source: usize)
            -> Result<(Vec<Option<f64>>, Vec<Option<usize>>), GraphErrors> {
        let size = self.size();
        assert!(source < size, "The node index is out of range.");

        let mut dists: Vec<Option<f64>> = (0..size)
            .map(|i| match i == source {
                true => Some(0.0f64),
                false => None,
            }).collect();

        let mut predecessors: Vec<Option<usize>> = vec![None; size];

        for _ in 1..size { // repeat size-1 times
            for i in 0..size {
                let currdist: f64 = match dists[i] {
                    Some(f) => f,
                    None => continue,
                };
                for j in 0..size {
                    let edge: f64 = match self.get_edge((i, j)) {
                        Some(f) => f,
                        None => continue,
                    };
                    if dists[j].is_none()
                            || dists[j].unwrap() > currdist + edge {
                        predecessors[j] = Some(i);
                        dists[j] = Some(currdist + edge);
                    }
                }
            }
        }

        for i in 0..size {
            let currdist: f64 = match dists[i] {
                Some(f) => f,
                None => continue,
            };
            for j in 0..size {
                let edge: f64 = match self.get_edge((i, j)) {
                    Some(f) => f,
                    None => continue,
                };
                if dists[j].is_none()
                        || dists[j].unwrap() > currdist + edge {
                    return Err(GraphErrors::ContainsNegativeCycle);
                }
            }
        }

        Ok((dists, predecessors))
    }

    /// Performs the Bellman-Ford algorithm for all vertices and returns a
    /// vector containing the result for each vertex as described for
    /// `bellman_ford`.
    fn bellman_ford_all(&self)
            -> Vec<Result<(Vec<Option<f64>>, Vec<Option<usize>>),
                          GraphErrors>> {
        (0..self.size()).map(|i| self.bellman_ford(i)).collect()
    }

    /// Returns the reweighted graph and the corresponding heights of the
    /// graph for Johnson's algorithm.
    fn johnson_graph(&self) -> Result<(T, Vec<f64>), GraphErrors>
        where T: GraphAlgorithms<T>;

    /// Performs Johnson's algorithm starting from a given vertex and returns
    /// a Result object. The result is an error in the case of a negative
    /// cycle. Otherwise the result unwraps to a tuple containing a vector of
    /// the sums of weights of the shortest paths and a vector of the
    /// predecessors of each vertex on its shortest path.
    fn johnson(&self, source: usize)
            -> Result<(Vec<Option<f64>>, Vec<Option<usize>>), GraphErrors> {
        assert!(source < self.size(), "The node index is out of range.");

        match self.johnson_graph() {
            Ok((graph, heights)) => {
                match graph.dijkstra(source) {
                    Ok((dists, predecessors)) => {
                        Ok((dists.iter().enumerate().map(|(i, &x)| match x {
                            Some(f)  => {
                                Some(f - heights[source] + heights[i])
                            }
                            None => { None }
                        }).collect(), predecessors))
                    }
                    Err(f) => { Err(f) }
                }
            }
            Err(f) => { Err(f) }
        }
    }

    /// Performs Johnson's algorithm for all vertices and returns a vector
    /// containing the result for each vertex as described for `johnson`.
    fn johnson_all(&self)
            -> Vec<Result<(Vec<Option<f64>>, Vec<Option<usize>>),
                          GraphErrors>> {
        match self.johnson_graph() {
            Ok((graph, heights)) => {
                (0..self.size()).map(|source| match graph.dijkstra(source) {
                    Ok((dists, predecessors)) => {
                        Ok((dists.iter().enumerate().map(|(i, &x)| match x {
                            Some(f)  => {
                                Some(f - heights[source] + heights[i])
                            }
                            None => { None }
                        }).collect(), predecessors))
                    }
                    Err(f) => { Err(f) }
                }).collect()
            }
            Err(f) => { vec![Err(f); self.size()] }
        }
    }

    /// Performs the Floyd-Warshall algorithm. The result is a tuple of a
    /// vector containing for each starting vertex the vertex of the sums of
    /// weights for each path and a vector containing for each starting vertex
    /// the vector of predecessor vertices on its paths.
    fn floyd_warshall(&self)
            -> (Vec<Vec<Option<f64>>>, Vec<Vec<Option<usize>>>) {
        let size = self.size();
        let mut dists: Vec<Vec<Option<f64>>>
            = vec![vec![None; size]; size];
        for i in 0..size {
            for j in 0..size {
                dists[i][j] = match i == j {
                    true => Some(0.0f64),
                    false => self.get_edge((i, j)),
                };
            }
        }

        let mut predecessors: Vec<Vec<Option<usize>>>
            = (0..size).map(|i| (0..size).map(|j| match i == j {
                  true => { None }
                  false => {
                      match self.get_edge((i, j)).is_some() {
                          true => Some(i),
                          false => None,
                      }
                  }
              }).collect()).collect();

        for k in 0..size {
            for i in 0..size {
                let edge1: f64 = match dists[i][k] {
                    Some(f) => f,
                    None => continue,
                };
                for j in 0..size {
                    let edge2: f64 = match dists[k][j] {
                        Some(f) => f,
                        None => continue,
                    };
                    if dists[i][j].is_none()
                            || dists[i][j].unwrap() > edge1 + edge2 {
                        predecessors[i][j] = predecessors[k][j];
                        dists[i][j] = Some(edge1 + edge2);
                    }
                }
            }
        }
        (dists, predecessors)
    }
}

/// Provides several algorithms for undirected graphs.
pub trait UndirectedGraphAlgorithms : GraphProperties {
    /// Performs a breadth-first search to find the connected components of
    /// the graph and returns a vector of vectors of vertices representing the
    /// connected components of the undirected graph.
    fn components(&self) -> Vec<Vec<usize>> {
        let size = self.size();
        let mut components: Vec<Vec<usize>> = vec![];
        if size == 0 {
            return components;
        }
        let mut unvisited: HashSet<usize> = (0..size).collect();

        while unvisited.len() > 0 {
            let start = (&unvisited).iter().min().unwrap().clone();
            unvisited.remove(&start);
            let mut queue: Vec<usize> = vec![start];
            let mut component: Vec<usize> = vec![];
            while queue.len() > 0 {
                let node = queue.remove(0);
                unvisited.remove(&node);
                component.push(node);
                let nbh = self.successors(node);
                for s in nbh {
                    if unvisited.contains(&s) {
                        queue.push(s);
                    }
                }
            }
            component.sort_by(|a, b| a.cmp(b));
            components.push(component);
        }

        components
    }

    /// Performs Prim's algorithm and returns a vector containing the edges on
    /// the minimal spanning tree represented by tuples.
    fn prim(&self) -> Vec<(usize, usize)> {
        let size = self.size();
        let mut queue = DistanceQueue::new();
        for i in 0..size {
            queue.push((i, None));
        }
        let mut nearest: Vec<Option<usize>> = vec![None; size];
        let mut edges: Vec<(usize, usize)> = vec![];

        while let Some(item) = queue.pop() {
            let (node, _): (usize, Option<f64>) = item;
            if let Some(predecessor) = nearest[node] {
                edges.push((predecessor, node));
            }
            for succ in self.successors(node) {
                if let Some(value) = queue.get(succ) {
                    let weight: f64 = self.get_edge((node, succ)).unwrap();
                    if value.is_none() || value.unwrap() > weight {
                        queue.decrease(succ, Some(weight));
                        nearest[succ] = Some(node);
                    }
                }
            }
        }

        edges
    }
}

/// Provides several algorithms for directed graphs.
pub trait DirectedGraphAlgorithms : GraphProperties {
    /// Returns a vector of vectors of vertices representing the strongly
    /// connected components of the directed graph.
    ///
    /// Reference:
    /// - Harold N. Gabow,
    ///   Path-based depth-first search for strong and biconnected components,
    ///   Information Processing Letters 74 (2000) 107–114
    fn sc_components(&self) -> Vec<Vec<usize>> {
        let size = self.size();
        if size == 0 {
            return vec![];
        }

        let mut stack_s: Vec<usize> = vec![];
        let mut stack_b: Vec<usize> = vec![];
        let mut index: Vec<usize> = vec![0; size];
        let mut no_scc: usize = 0;
        let successors: Vec<Vec<usize>>
            = (0..size).map(|i| self.successors(i)).collect();

        fn scc_dfs(node: usize, successors: &Vec<Vec<usize>>,
                   stack_s: &mut Vec<usize>, stack_b: &mut Vec<usize>,
                   index: &mut Vec<usize>, no_scc: &mut usize) {
            stack_s.push(node);
            let nindex = stack_s.len();
            index[node] = nindex;
            stack_b.push(index[node]);

            let ref succs: Vec<usize> = successors[node];
            for succ in succs {
                let sindex = index[*succ];
                if sindex == 0 {
                    scc_dfs(*succ, successors, stack_s, stack_b, index,
                            no_scc);
                } else {
                    while sindex < *stack_b.last().unwrap_or(&(0 as usize)) {
                        stack_b.pop();
                    }
                }
            }

            if nindex == *stack_b.last().unwrap_or(&(nindex + 1)) {
                stack_b.pop();
                *no_scc = *no_scc + 1;
                while nindex <= stack_s.len() {
                    let topnode = stack_s.pop().unwrap();
                    index[topnode] = *no_scc;
                }
            }
        }

        for i in 0..size {
            if index[i] == 0 {
                scc_dfs(i, &successors, &mut stack_s, &mut stack_b,
                        &mut index, &mut no_scc);
            }
        }

        // sort components by the smallest vertex index
        let mut components: Vec<Vec<usize>> = vec![Vec::new(); no_scc];
        let mut cindex: HashMap<usize, usize> = HashMap::new();
        let mut current: usize = 0;
        for node in 0..size {
            let nindex = index[node] - 1;
            let pos: usize;
            if cindex.contains_key(&nindex) {
                pos = *cindex.get(&nindex).unwrap();
            } else {
                pos = current;
                cindex.insert(nindex, pos);
                current = current + 1;
            }
            components[pos].push(node);
        }

        components
    }
}
