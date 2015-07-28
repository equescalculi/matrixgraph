// Copyright 2015 Marius Ritter
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A queue implementation using binary heaps for (key, value) tuples

use std::collections::HashMap;

/// A queue implementation using binary heaps for (key, value) tuples
#[derive(Clone, Debug)]
pub struct DistanceQueue {
    heap: Vec<(usize, Option<f64>)>,
    hashmap: HashMap<usize, usize>,
}

// Compares the values `a` and `b` of two queue items and returns `true` if
// `a` is less than `b`.
fn qlt(a: Option<f64>, b: Option<f64>) -> bool {
    if let Some(au) = a {
        if let Some(bu) = b {
            return !au.is_nan() && (bu.is_nan() || au < bu);
        } else {
            return true;
        }
    }
    false
}

impl DistanceQueue {
    /// Creates a new queue.
    pub fn new() -> DistanceQueue {
        DistanceQueue {
            heap: vec![],
            hashmap: HashMap::new(),
        }
    }

    /// Returns the size of the heap.
    pub fn size(&self) -> usize {
        self.heap.len()
    }

    /// Returns the vector representing the heap.
    pub fn heapvec(&self) -> Vec<(usize, Option<f64>)> {
        self.heap.clone()
    }

    /// Returns the index of the heap.
    pub fn indexhashmap(&self) -> HashMap<usize, usize> {
        self.hashmap.clone()
    }

    // Returns the index of the parent of the given heap node as an Option or
    // `None` if the node is the root.
    fn parent(&self, i: usize) -> Option<usize> {
        if i == 0 {
            return None;
        }
        Some((i - 1) / 2)
    }

    // Returns the index of the left child of the given heap node as an
    // Option or `None` if the node does not have a left child.
    fn left(&self, i: usize) -> Option<usize> {
        let index = 2 * i + 1;
        if index >= self.size() {
            return None;
        }
        Some(index)
    }

    // Returns the index of the right child of the given heap node as an
    // Option or `None` if the node does not have a right child.
    fn right(&self, i: usize) -> Option<usize> {
        let index = 2 * i + 2;
        if index >= self.size() {
            return None;
        }
        Some(index)
    }

    // Restores the heap structure starting from the given heap node towards
    // the root.
    fn restore_towards_root(&mut self, i: usize) {
        if i > 0 {
            let mut j = i;
            let (mut key, mut val): (usize, Option<f64>) = self.heap[j];
            let mut p: usize = self.parent(j).unwrap();  // j = i > 0
            let (mut pkey, mut pval): (usize, Option<f64>) = self.heap[p];
            while j > 0 && qlt(val, pval) {
                self.hashmap.insert(key, p);
                self.hashmap.insert(pkey, j);
                self.heap.swap(j, p);
                j = p;
                key = self.heap[j].0;
                val = self.heap[j].1;
                p = match self.parent(j) {
                    Some(f) => f,
                    None => break
                };
                pkey = self.heap[p].0;
                pval = self.heap[p].1;
            }
        }
    }

    // Restores the heap structure starting from the given heap node towards
    // the leaves.
    fn restore_towards_leaves(&mut self, i: usize) {
        let mut j = i;
        loop {
            let mut s = j;
            if let Some(l) = self.left(j) {
                if qlt(self.heap[l].1, self.heap[j].1) {
                    s = l;
                }
            }
            if let Some(r) = self.right(j) {
                if qlt(self.heap[r].1, self.heap[s].1) {
                    s = r;
                }
            }
            if s != j {
                self.hashmap.insert(self.heap[j].0, s);
                self.hashmap.insert(self.heap[s].0, j);
                self.heap.swap(s, j);
                j = s;
            } else {
                break;
            }
        }
    }

    /// Returns `true` if the given key is in the queue.
    pub fn contains_key(&self, key: usize) -> bool {
        self.hashmap.contains_key(&key)
    }

    /// Returns the value of the given key as an Option. If the key is absent
    /// from the queue, `None` is returned.
    pub fn get(&self, key: usize) -> Option<Option<f64>> {
        let pos = self.hashmap.get(&key);
        match pos {
            Some(m) => Some(self.heap[*m].1),
            None => None
        }
    }

    /// Adds an item to the queue.
    ///
    /// Panics if the key of the item is already present in the queue.
    pub fn push(&mut self, item: (usize, Option<f64>)) {
        let key = item.0;
        assert!(!self.hashmap.contains_key(&key),
                "The key already exists in the DistanceHeap instance.");

        let i = self.size();
        self.heap.push(item);
        self.hashmap.insert(key, i);
        self.restore_towards_root(i);
    }

    /// Removes the minimal item from the queue and returns it as an Option.
    /// `None` is returned if the queue is empty.
    pub fn pop(&mut self) -> Option<(usize, Option<f64>)> {
        if self.size() == 0 {
            return None;
        }
        let item = self.heap[0];
        let lastindex = self.size() - 1;
        let lastkey = self.heap[lastindex].0;
        self.heap.swap(0, lastindex);
        self.heap.remove(lastindex);
        self.hashmap.remove(&item.0);
        self.hashmap.insert(lastkey, 0);
        self.restore_towards_leaves(0);
        Some(item)
    }

    /// Decreases the value of an item in the queue.
    ///
    /// Panics if key the of the item is absent from the queue or if the
    /// new value is not less than the current value.
    pub fn decrease(&mut self, key: usize, new_value: Option<f64>) {
        assert!(self.hashmap.contains_key(&key),
                "The key does not exist in the DistanceHeap instance.");
        let index: usize = *self.hashmap.get(&key).unwrap();
        assert!(qlt(new_value, self.heap[index].1),
                "The new value is not less than the current value.");

        self.heap[index] = (key, new_value);
        self.restore_towards_root(index);
    }
}

// TESTS

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use std::f64;

    #[test]
    fn test_qlt_1() {
        assert_eq!(super::qlt(None, None), false);
        assert_eq!(super::qlt(Some(f64::NAN), None), true);
        assert_eq!(super::qlt(None, Some(f64::NAN)), false);
        assert_eq!(super::qlt(None, Some(-1.1f64)), false);
        assert_eq!(super::qlt(Some(-1.1f64), None), true);
        assert_eq!(super::qlt(Some(f64::INFINITY), Some(f64::NAN)), true);
        assert_eq!(super::qlt(Some(f64::NAN), Some(f64::INFINITY)), false);
        assert_eq!(super::qlt(Some(-1.1f64), Some(-1.1f64)), false);
    }

    #[test]
    fn test_distance_queue_1() {
        let mut queue = super::DistanceQueue::new();

        // insertion tests

        queue.push((0, None));
        assert_eq!(queue.heapvec(), vec![(0, None)]);
        let mut hm0: HashMap<usize, usize> = HashMap::new();
        hm0.insert(0, 0);
        assert_eq!(queue.indexhashmap(), hm0);

        queue.push((1, Some(f64::INFINITY)));
        assert_eq!(queue.heapvec(),
                   vec![(1, Some(f64::INFINITY)), (0, None)]);
        let mut hm1: HashMap<usize, usize> = HashMap::new();
        hm1.insert(1, 0);
        hm1.insert(0, 1);
        assert_eq!(queue.indexhashmap(), hm1);

        queue.push((2, Some(1.1f64)));
        assert_eq!(queue.heapvec(),
                   vec![(2, Some(1.1f64)), (0, None),
                        (1, Some(f64::INFINITY))]);
        let mut hm2: HashMap<usize, usize> = HashMap::new();
        hm2.insert(2, 0);
        hm2.insert(0, 1);
        hm2.insert(1, 2);
        assert_eq!(queue.indexhashmap(), hm2);

        queue.push((4, Some(-1.1f64)));
        assert_eq!(queue.heapvec(),
                   vec![(4, Some(-1.1f64)), (2, Some(1.1f64)),
                        (1, Some(f64::INFINITY)), (0, None)]);
        let mut hm3: HashMap<usize, usize> = HashMap::new();
        hm3.insert(4, 0);
        hm3.insert(2, 1);
        hm3.insert(1, 2);
        hm3.insert(0, 3);
        assert_eq!(queue.indexhashmap(), hm3);

        queue.push((8, Some(0.0f64)));
        assert_eq!(queue.heapvec(),
                   vec![(4, Some(-1.1f64)), (8, Some(0.0f64)),
                        (1, Some(f64::INFINITY)), (0, None),
                        (2, Some(1.1f64))]);
        let mut hm4: HashMap<usize, usize> = HashMap::new();
        hm4.insert(4, 0);
        hm4.insert(8, 1);
        hm4.insert(1, 2);
        hm4.insert(0, 3);
        hm4.insert(2, 4);
        assert_eq!(queue.indexhashmap(), hm4);

        queue.push((16, Some(f64::NEG_INFINITY)));
        assert_eq!(queue.heapvec(),
                   vec![(16, Some(f64::NEG_INFINITY)), (8, Some(0.0f64)),
                        (4, Some(-1.1f64)), (0, None), (2, Some(1.1f64)),
                        (1, Some(f64::INFINITY))]);
        let mut hm5: HashMap<usize, usize> = HashMap::new();
        hm5.insert(16, 0);
        hm5.insert(8, 1);
        hm5.insert(4, 2);
        hm5.insert(0, 3);
        hm5.insert(2, 4);
        hm5.insert(1, 5);
        assert_eq!(queue.indexhashmap(), hm5);

        // removal test

        let min: Option<(usize, Option<f64>)> = queue.pop();
        assert_eq!(min, Some((16, Some(f64::NEG_INFINITY))));
        assert_eq!(queue.heapvec(),
                   vec![(4, Some(-1.1f64)),(8, Some(0.0f64)),
                        (1, Some(f64::INFINITY)), (0, None),
                        (2, Some(1.1f64))]);
        let mut hm6: HashMap<usize, usize> = HashMap::new();
        hm6.insert(4, 0);
        hm6.insert(8, 1);
        hm6.insert(1, 2);
        hm6.insert(0, 3);
        hm6.insert(2, 4);
        assert_eq!(queue.indexhashmap(), hm6);

        // priority change test

        queue.decrease(0, Some(-2.0f64));
        assert_eq!(queue.heapvec(),
                   vec![(0, Some(-2.0f64)), (4, Some(-1.1f64)),
                        (1, Some(f64::INFINITY)), (8, Some(0.0f64)),
                        (2, Some(1.1f64))]);
        let mut hm7: HashMap<usize, usize> = HashMap::new();
        hm7.insert(0, 0);
        hm7.insert(4, 1);
        hm7.insert(1, 2);
        hm7.insert(8, 3);
        hm7.insert(2, 4);
        assert_eq!(queue.indexhashmap(), hm7);
    }

    #[test]
    fn test_distance_queue_2() {
        let mut queue = super::DistanceQueue::new();
        queue.push((0, None));
        queue.push((1, Some(f64::INFINITY)));
        queue.push((2, Some(5.0f64)));
        let item: Option<(usize, Option<f64>)> = queue.pop();
        assert_eq!(item, Some((2, Some(5.0f64))));
        assert_eq!(queue.contains_key(0), true);
        assert_eq!(queue.get(0), Some(None));
        assert_eq!(queue.contains_key(1), true);
        assert_eq!(queue.get(1), Some(Some(f64::INFINITY)));
        assert_eq!(queue.contains_key(2), false);
        assert_eq!(queue.get(2), None);
    }

    #[test]
    #[should_panic]
    fn test_distance_queue_3() {
        let mut queue = super::DistanceQueue::new();
        queue.push((0, Some(1.0f64)));
        queue.push((0, Some(2.0f64)));
    }

    #[test]
    #[should_panic]
    fn test_distance_queue_4() {
        let mut queue = super::DistanceQueue::new();
        queue.push((0, Some(1.0f64)));
        queue.decrease(0, Some(2.0f64));
    }

    #[test]
    #[should_panic]
    fn test_distance_queue_5() {
        let mut queue = super::DistanceQueue::new();
        queue.decrease(0, Some(2.0f64));
    }
}
