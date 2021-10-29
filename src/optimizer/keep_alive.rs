use std::collections::{HashMap, HashSet};

use crate::util::{ArrayMap};
use super::{Dataflow, Node, Out, CFT};

//-----------------------------------------------------------------------------

/** A first-in-first-out queue. */
#[derive(Debug)]
pub struct Fifo<T: Clone> {
    items: Vec<T>,
    done: usize,
}

impl<T: Clone> Fifo<T> {
    fn new() -> Self {
        Fifo {
            items: Vec::new(),
            done: 0,
        }
    }

    fn enqueue(&mut self, item: T) {
        self.items.push(item);
    }

    fn dequeue(&mut self) -> Option<T> {
        if self.done >= self.items.len() {
            None
        } else {
            let item = self.items[self.done].clone();
            self.done += 1;
            Some(item)
        }
    }

    /** Returns all items that have ever been in the queue. */
    fn finish(self) -> Vec<T> {
        self.items
    }
}

//-----------------------------------------------------------------------------

/** The hot and cold branches from a [`Op::Guard`]. */
struct Switch<'a> {
    guard: Node,
    hot: &'a CFT,
    colds: Vec<&'a CFT>,
}

impl<'a> Switch<'a> {
    /** Separates the hot and cold paths of a [`CFT::Switch`]. */
    fn new(guard: Node, hot_index: usize, cases: &'a [CFT], default_: &'a CFT) -> Self {
        let mut hot = default_;
        let mut colds = Vec::new();
        for (i, case) in cases.iter().enumerate() {
            if i == hot_index {
                hot = case;
            } else {
                colds.push(case);
            }
        }
        if hot_index != usize::MAX {
            colds.push(default_);
        }
        Switch {guard, hot, colds}
    }
}

//-----------------------------------------------------------------------------

struct KeepAlive<'a> {
    dataflow: &'a Dataflow,
    mark: ArrayMap<Node, usize>,
    keep_alives: HashMap<Node, Box<[Out]>>,
}

impl<'a> KeepAlive<'a> {
    fn new(dataflow: &'a Dataflow) -> Self {
        let mut mark = dataflow.node_map();
        mark[dataflow.entry_node()] = 1;
        let keep_alives = HashMap::new();
        KeepAlive {dataflow, mark, keep_alives}
    }

    /**
     * Follows the hot path through `cft`.
     * Returns the [`Switch`]es and the exit [`Node`].
     */
    fn hot_path(mut cft: &'a CFT) -> (Vec<Switch>, Node) {
        let mut switches = Vec::new();
        loop {
            match cft {
                &CFT::Merge {exit, ..} => {
                    return (switches, exit);
                },
                &CFT::Switch {guard, hot_index, ref cases, ref default_} => {
                    let switch = Switch::new(guard, hot_index, cases, default_);
                    cft = switch.hot;
                    switches.push(switch);
                },
            }
        }
    }

    /**
     * Finds the live inputs and live nodes of the unmarked portion of
     * `dataflow` on which `exit` depends. Marks all the live nodes with
     * `temperature`. Adds the live inputs to `inputs`.
     */
    fn flood(&mut self, exit: Node, temperature: usize, inputs: &mut HashSet<Out>)
    -> Vec<Node> {
        let mut fifo = Fifo::new();
        // Enqueue `exit`.
        assert_eq!(self.mark[exit], 0);
        self.mark[exit] = temperature;
        fifo.enqueue(exit);
        // Breadth-first flood fill.
        while let Some(node) = fifo.dequeue() {
            for &node in self.dataflow.deps(node) {
                if self.mark[node] == 0 {
                    self.mark[node] = temperature;
                    fifo.enqueue(node);
                }
            }
            for &out in self.dataflow.ins(node) {
                let (node, _) = self.dataflow.out(out);
                if self.mark[node] == 0 {
                    self.mark[node] = temperature;
                    fifo.enqueue(node);
                } else if self.mark[node] < temperature {
                    inputs.insert(out);
                } else {
                    assert_eq!(self.mark[node], temperature);
                }
            }
        }
        fifo.finish()
    }

    /**
     * Add to `self.keep_alives` the keep-alive set for every [`Op::Guard`] in
     * `cft`. Add to `inputs` the live inputs of `cft`.
     *
     * On entry and on exit, `mark[node]` must be in `1..temperature` if `node`
     * is on the hotter path from which `cft` diverges, and `0` otherwise.
     * `mark[entry_node]` must be `1`.
     *
     * - temperature - the number of cold branches needed to reach `cft` + 2.
     *   (`0` is used for unmarked nodes, and `1` for the entry node).
     */
    fn walk(&mut self, cft: &'a CFT, inputs: &mut HashSet<Out>, temperature: usize) {
        let (switches, exit) = Self::hot_path(cft);
        // Mark everything that `exit` depends on.
        let nodes = self.flood(exit, temperature, inputs);
        // For each guard we passed...
        for switch in switches {
            // Recurse to find all the inputs of any cold path.
            let mut keep_alives = HashSet::new();
            for cold in switch.colds {
                self.walk(cold, &mut keep_alives, temperature + 1);
            }
            let keep_alives: Box<[_]> = keep_alives.into_iter().collect();
            // Add them to our own inputs if necessary.
            for &out in &*keep_alives {
                let (node, _) = self.dataflow.out(out);
                assert_ne!(self.mark[node], 0);
                if self.mark[node] < temperature {
                    // Hotter than us.
                    inputs.insert(out);
                }
            }
            // Record them in `self.keep_alives`.
            self.keep_alives.insert(switch.guard, keep_alives);
        }
        // Unark everything that we marked.
        for node in nodes {
            assert_eq!(self.mark[node], temperature);
            self.mark[node] = 0;
        }
    }
}

/**
 * For each [`Op::Guard`] in `cft`, finds the set of [`Out`]s that
 * are computed on the hot path but which must outlive the `Guard` because they
 * are also needed on at least one cold path.
 */
pub fn keep_alive_sets(dataflow: &Dataflow, cft: &CFT) -> HashMap<Node, Box<[Out]>> {
    let mut ka = KeepAlive::new(dataflow);
    ka.walk(cft, &mut HashSet::new(), 2);
    ka.keep_alives
}
