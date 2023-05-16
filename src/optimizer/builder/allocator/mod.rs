use std::collections::{HashMap};
use std::fmt::{self, Debug, Formatter};

use super::{NUM_REGISTERS, all_registers, Resources, Dataflow, Node, Exit, Frontier};
use super::cost::{BUDGET, SPILL_COST, SLOT_COST};
use super::code::{Register, Variable};
use crate::util::{ArrayMap, map_filter_max, Usage};

mod pool;
use pool::{RegisterPool};

mod placer;
use placer::{Time, LEAST as EARLY, Placer};

//-----------------------------------------------------------------------------

/// Either a `Node` or a `Spill` instruction inserted by the allocator.
#[derive(Copy, Clone, PartialEq)]
pub enum Instruction {
    Spill(Node, Node),
    Node(Node),
}

use Instruction::*;

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match *self {
            Spill(out_x, out_y) => write!(f, "({:?}, {:?})", out_x, out_y),
            Node(node) => node.fmt(f),
        }
    }
}

//-----------------------------------------------------------------------------

/// Describes how a [`Node`] depends on one of its input operands.
///
/// This is often just an input value or side-effect dependency, but can also
/// be e.g. a value needed by `node`'s cold paths.
#[derive(Debug, Copy, Clone)]
pub struct Input {
    /// Whether the `Node` needs a value computed by `node`. This affects
    /// register allocation.
    is_value: bool,
    /// Whether `node` is a dependency on a cold path. This affects instruction
    /// scheduling.
    is_cold: bool,
}

//-----------------------------------------------------------------------------

/// The state of the code generation algorithm. The state is mutated as
/// [`Instruction`]s are added.
#[derive(Debug)]
struct Allocator<'a> {
    /// The dataflow graph.
    dataflow: &'a Dataflow,
    /// The concatenation of the `input` lists of all [`Node`]s remaining
    /// to be processed. Each call to `add_node()` pops some `Node`s from this.
    usage: Usage<Node, Input>,
    /// The [`Instruction`]s processed so far.
    placer: Placer<Instruction>,
    /// The `Register` allocated for each `Node`'s result, if any.
    allocation: HashMap<Node, Register>,
    /// The `Time` at which each `Node`'s result was last accessed.
    access_times: HashMap<Node, Time>,
    /// The `Time` at which each `Node` was executed.
    node_times: HashMap<Node, Time>,
    /// The contents of each [`Register`] at the current time.
    regs: ArrayMap<Register, Option<Node>>,
    /// The `Register` allocator state.
    pool: RegisterPool,
}

impl<'a> Allocator<'a> {
    /// Create a new `Allocator`.
    ///
    /// - effects - [`Node`]s representing side-effects that have already
    ///   occurred.
    /// - variables - A mapping from the live [`Node`]s to [`Variable`]s.
    /// - dataflow - The data flow graph.
    /// - usage - The concatenation of the `input` lists of all [`Node`]s that
    ///   will be processed.
    pub fn new(
        variables: &HashMap<Node, Variable>,
        dataflow: &'a Dataflow,
        usage: Usage<Node, Input>,
    ) -> Self {
        // Initialize the data structures with the live registers of `variables`.
        let mut dirty = ArrayMap::new(NUM_REGISTERS);
        let mut allocation: HashMap<Node, Register> = HashMap::new();
        let mut regs: ArrayMap<Register, Option<Node>> = ArrayMap::new(NUM_REGISTERS);
        for (&node, &value) in variables.iter() {
            if usage.topmost(&node).is_some() {
                // `node` is alive on entry.
                if let Variable::Register(reg) = value {
                    dirty[reg] = true;
                    regs[reg] = Some(node);
                    allocation.insert(node, reg);
                }
            }
        }
        // Construct and return.
        let placer = Placer::new();
        let access_times: HashMap<Node, Time> = HashMap::new();
        let node_times: HashMap<Node, Time> = HashMap::new();
        let pool = RegisterPool::new(dirty);
        Allocator {dataflow, usage, placer, allocation, access_times, node_times, regs, pool}
    }

    /// Returns the [`Register`] containing `node`, if any.
    fn current_reg(&self, node: Node) -> Option<Register> {
        self.allocation.get(&node).copied().filter(
            |&reg| self.regs[reg] == Some(node)
        )
    }

    /// Pop one item from `self.usage`.
    /// Frees its [`Register`], if any, if the `Node` has no remaining uses.
    fn pop_use(&mut self) -> (Node, Input) {
        let (node, input) = self.usage.pop().expect("Incorrect usage information");
        if self.usage.topmost(&node).is_none() {
            if let Some(reg) = self.current_reg(node) {
                self.pool.free(reg);
            }
        }
        (node, input)
    }

    /// Record that we accessed `node` at `time` (either reading or writing).
    fn access(&mut self, node: Node, time: Time) {
        self.access_times.entry(node).or_insert(EARLY).max_with(time);
    }

    /// Select a `Register` to spill and free it.
    fn free_a_register(&mut self) -> Register {
        let i = map_filter_max(all_registers(), |reg| {
            self.regs[reg]
                .filter(|_| !self.pool.is_clean(reg))
                .map(|node| std::cmp::Reverse(
                    self.usage.topmost(&node).expect("Dirty register is unused")
                ))
        }).expect("No register is dirty");
        let reg = Register::new(i as u8).unwrap();
        self.pool.free(reg);
        reg
    }

    /// Computes the [`Time`] at which `node`'s result appears.
    fn node_time(&self, node: Node, add_latency: bool) -> Time {
        if let Some(&time) = self.node_times.get(&node) {
            if add_latency { 
                time + (self.dataflow.cost(node).latency as usize)
            } else {
                time
            }
        } else {
            EARLY
        }
    }

    /// Spills values until at least `num_required` registers are free.
    fn spill_until(&mut self, num_required: usize) {
        while self.pool.num_clean() < num_required {
            let reg_x = self.free_a_register();
            let reg_y = self.free_a_register();
            // Spill the `Register`.
            let node_x = self.regs[reg_x].unwrap();
            let node_y = self.regs[reg_y].unwrap();
            let mut time = self.node_time(node_x, true);
            time.max_with(self.node_time(node_y, true));
            self.placer.add_item(Spill(node_x, node_y), SPILL_COST, &mut time);
            self.access(node_x, time);
            self.access(node_y, time);
        }
    }

    /// Called for each [`Node`] in forwards order.
    /// - `num_inputs` - The number of items to pop from `self.usage`.
    ///   These are often just the inputs of `node`, but can also include e.g.
    ///   values needed by `node`'s cold paths.
    pub fn add_node(&mut self, node: Node, num_inputs: usize) {
        let df: &'a Dataflow = self.dataflow;
        let mut time = EARLY; // Earliest time (in cycles) when we can place `node`.
        // Read inputs.
        // Check for spilled inputs.
        // Free every input `Register` that won't be used again.
        // Bump `time` until the inputs are available.
        let mut inputs = Vec::<(Node, Input)>::new();
        let mut has_spilled_input = false;
        for _ in 0..num_inputs {
            let (in_, input) = self.pop_use();
            inputs.push((in_, input));
            if !input.is_cold {
                has_spilled_input |= input.is_value & self.current_reg(in_).is_none();
                time.max_with(self.node_time(in_, input.is_value));
            } else {
                println!("Input is not needed on the hot path");
            }
        }
        // Bump `time` until a destination register is available.
        if df.has_out(node) {
            self.spill_until(1);
            let reg = self.pool.allocate();
            self.allocation.insert(node, reg);
            if let Some(prev) = self.regs[reg].replace(node) {
                // `reg` was previously used to hold `prev`.
                if let Some(&read_time) = self.access_times.get(&prev) {
                    // `prev` was last accessed at `read_time`.
                    time.max_with(read_time);
                }
            }
            if self.usage.topmost(&node).is_none() {
                // `node` will never be used again. Free `reg` immediately.
                self.pool.free(reg);
            }
        }
        // Bump `time` until the execution resources are available.
        let mut resources = df.cost(node).resources;
        if has_spilled_input {
            // We can't be sure it's not still in a `Register`; this is a guess.
            resources += SLOT_COST;
        }
        // FIXME: A long series of zero-cost nodes will crash the placer.
        self.placer.add_item(Node(node), resources, &mut time);
        // Record the node's placement.
        self.node_times.insert(node, time);
        // Record when the input registers are accessed.
        for &(node, input) in &inputs {
            if input.is_value {
                self.access(node, time);
            }
        }
        // Record when the output register is accessed.
        if df.has_out(node) {
            self.access(node, time);
        }
    }

    /// Read the [`Node`]s that are live on exit, and the sequence `Node`.
    fn finish(mut self, num_outputs: usize) -> (Vec<Instruction>, HashMap<Node, Register>) {
        for _ in 0..num_outputs { let _ = self.pop_use(); }
        let _ = self.pop_use();
        assert_eq!(self.usage.len(), 0);
        assert!(all_registers().all(|reg| self.pool.is_clean(reg)));
        (self.placer.iter().cloned().collect(), self.allocation)
    }
}

/// Accumulates memory accesses and `Send`s that wait for them.
#[derive(Debug, Default)]
struct Address {
    mems: Vec<Node>,
    sends: Vec<Node>,
}

/// Used to sort `Node`s into a reverse execution order.
#[derive(Debug, Default)]
struct Queue {
    counts: HashMap<Node, usize>,
    queue: Vec<Node>,
}

impl Queue {
    pub fn new(nodes: &[Node]) -> Self {
        Self {
            counts: nodes.iter().map(|&node| (node, 0)).collect(),
            queue: Vec::new(),
        }
    }

    /// Increments `counts[node]`.
    pub fn increment(&mut self, node: Node) {
        if let Some(count) = self.counts.get_mut(&node) { *count += 1; }
    }

    /// Decrements `counts[node]` and if zero adds `node` to `queue`.
    pub fn decrement(&mut self, node: Node) {
        if let Some(count) = self.counts.get_mut(&node) {
            *count -= 1;
            println!("counts[{:?}] is now {:?}", node, count);
            if *count == 0 {
                println!("Enqueueing!");
                self.queue.push(node);
            }
        }
    }

    /// Removes and returns something from `queue`.
    pub fn pop(&mut self) -> Option<Node> {
        self.queue.pop()
    }
}

/// Choose the execution order and allocate [`Register`]s.
///
/// - effects - [`Node`]s representing side-effects that have already occurred.
/// - variables - the [`Variable`]s passed on entry to the hot path.
/// - dataflow - the dataflow graph.
/// - nodes - the [`Node`]s that need to be executed on the hot path.
/// - get_frontier - for [`Guard`] `Node`s, returns the dependencies of the
///   cold paths.
/// - exit - the [`Node`]s that are live on exit, and the sequence `Node`.
///
/// Returns:
/// - instructions - the execution order.
/// - allocation - which `Register` holds each `Node`'s result.
///
/// [`Guard`]: super::Op::Guard
// FIXME: Place `Send(x, y)` and `Store(y)` after all `Load(y)`s.
pub fn allocate<'a>(
    variables: &HashMap<Node, Variable>,
    dataflow: &Dataflow,
    nodes: &[Node],
    get_frontier: impl Fn(Node) -> Option<&'a Frontier>,
    exit: &Exit,
) -> (
    Vec<Instruction>,
    HashMap<Node, Register>
) {
    println!("allocate()");
    println!("variables = {:#?}", variables);
    println!("dataflow = {:#?}", dataflow);
    println!("nodes = {:#?}", nodes);
    println!("exit = {:#?}", exit);
    // Count how many things depend on each `Node`.
    // Simultaneously index all `Send`s and memory access `Node`s.
    let mut queue = Queue::new(nodes);
    let mut addresses = HashMap::<Node, Address>::new();
    for &node in nodes {
        dataflow.each_input(node, |in_, dep| {
            if !dep.is_cold() {
                // Ordering dependency.
                println!("Ordering dependency {:?}", in_);
                queue.increment(in_);
            }
            if dep.is_address() {
                println!("Memory instruction {:?}", node);
                addresses.entry(in_).or_default().mems.push(node);
            }
            if dep.is_send() {
                println!("Send instruction {:?}", node);
                addresses.entry(in_).or_default().sends.push(node);
            }
        });
    }
    println!("addresses = {:#?}", addresses);
    // Count extra dependencies due to `Send`s.
    for address in addresses.values() {
        for &mem in &address.mems {
            for &send in &address.sends {
                if mem != send {
                    // `Send` dependency.
                    println!("Send dependency {:?}", mem);
                    queue.increment(mem);
                }
            }
        }
    }
    // Count extra dependencies due to `exit`.
    println!("Sequence dependency {:?}", exit.sequence);
    queue.increment(exit.sequence);
    for &in_ in &*exit.outputs {
        println!("Output dependency {:?}", in_);
        queue.increment(in_);
    }
    println!("Before: queue = {:#?}", queue);

    // Prioritize `nodes` into a possible reverse execution order.
    // Simultaneously compute their inputs.
    let mut usage = Usage::default();
    let mut nodes_rev = Vec::new();
    println!("Sequence dependency {:?}", exit.sequence);
    queue.decrement(exit.sequence);
    usage.push(exit.sequence, Input {is_value: false, is_cold: false});
    for &in_ in &*exit.outputs {
        println!("Output dependency {:?}", in_);
        queue.decrement(in_);
        usage.push(in_, Input {is_value: true, is_cold: false});
    }
    while let Some(node) = queue.pop() {
        println!("Popping {:?} from queue", node);
        let start = usage.len();
        dataflow.each_input(node, |in_, dep| {
            if !dep.is_cold() {
                // Ordering dependency.
                println!("Ordering dependency {:?}", in_);
                queue.decrement(in_);
                usage.push(in_, Input {is_value: dep.is_value(), is_cold: false});
            }
            if dep.is_send() {
                for &mem in &addresses[&in_].mems {
                    if mem != node {
                        // `Send` dependency.
                        println!("Send dependency {:?}", mem);
                        queue.decrement(mem);
                        usage.push(mem, Input {is_value: false, is_cold: false});
                    }
                }
            }
        });
        if let Some(f) = get_frontier(node) {
            for (&in_, &v) in &f.0 {
                // Cold path dependency.
                println!("Cold path dependency{:?}", in_);
                usage.push(in_, Input {is_value: v.is_value(), is_cold: true});
            }
        }
        let end = usage.len();
        nodes_rev.push((node, end - start));
    }
    println!("After: queue = {:#?}", queue);
    assert_eq!(nodes_rev.len(), nodes.len());

    // Schedule and allocate registers for every `Node`.
    let mut a = Allocator::new(variables, dataflow, usage);
    while let Some((node, num_inputs)) = nodes_rev.pop() {
        a.add_node(node, num_inputs);
    }
    a.finish(exit.outputs.len())
}
