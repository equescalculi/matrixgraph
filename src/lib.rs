// Copyright 2015 Marius Ritter
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A graph implementation based on dense adjacency matrices
//!
//! **WARNING!** Please expect odd bugs and backward incompatible changes at
//! this early stage!
//!
//! # Features
//!
//! Supported structs:
//!
//!  * `SimpleGraph`: a simple graph represented by the upper right triangle
//!    of an adjacency matrix of fixed size
//!  * `Digraph`: a digraph represented by a dense adjacency matrix of fixed
//!    size
//!
//! # Usage
//!
//! Add this library as a crate to your project:
//!
//! ```rust
//! extern crate matrixgraph;
//! ```
//! Define a graph:
//!
//! ```rust
//! use matrixgraph::{Digraph, BasicGraphMethods};
//!
//! let mut digraph = Digraph::new(3);
//! digraph.set_edge((0, 1), Some(1.0f64));
//! digraph.set_edge((0, 2), Some(4.0f64));
//! digraph.set_edge((1, 2), Some(2.0f64));
//! ```

#![crate_type = "lib"]
#![crate_type = "dylib"]
#![crate_name = "matrixgraph"]

#![deny(non_camel_case_types)]
#![deny(non_upper_case_globals)]
#![warn(missing_docs)]
#![deny(unused_parens)]
#![deny(unused_qualifications)]

pub use simple_graph::SimpleGraph;
pub use digraph::Digraph;
pub use traits::BasicGraphMethods;

/// An enum of structs representing graphs
pub enum Graph {
    /// A simple graph represented by the upper right triangle of an adjacency
    /// matrix of fixed size
    SimpleGraph,
    /// A digraph represented by a dense adjacency matrix of fixed size
    Digraph,
}

mod simple_graph;
mod digraph;
mod traits;
