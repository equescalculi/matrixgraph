# Crate matrixgraph

A graph implementation based on dense adjacency matrices

**WARNING!** Please expect odd bugs and backward incompatible changes at
this early stage!

## Features

Supported structs:

 * `SimpleGraph`: a simple graph represented by the upper right triangle
   of an adjacency matrix of fixed size
 * `Digraph`: a digraph represented by a dense adjacency matrix of fixed
   size

## Usage

Add this library as a crate to your project:

```rust
extern crate matrixgraph;
```
Define a graph:

```rust
use matrixgraph::{Digraph, BasicGraphMethods};

let mut digraph = Digraph::new(3);
digraph.set_edge((0, 1), Some(1.0f64));
digraph.set_edge((0, 2), Some(4.0f64));
digraph.set_edge((1, 2), Some(2.0f64));
```
