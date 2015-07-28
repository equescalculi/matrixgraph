// Copyright 2015 Marius Ritter
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// Provides basic graph methods.
pub trait BasicGraphMethods {
    /// Returns the size of the graph, i.e. its number of vertices.
    fn size(&self) -> usize;

    /// Returns the value of an edge of the graph.
    fn get_edge(&self, edge: (usize, usize)) -> Option<f64>;

    /// Sets the value of an edge of the graph.
    fn set_edge(&mut self, edge: (usize, usize), value: Option<f64>);
}
