use crate::util::{ArrayMap};
use super::{Op, Dataflow, Node, Out, DUMMY_NODE, DUMMY_OUT, map_from_register_to_index, RegIndex, Resources};
use super::code::{Register, Slot, Value, Action};
use super::{NUM_REGISTERS, ALLOCATABLE_REGISTERS};

/** The maximum number of [`Out`]s to spill per cycle. */
const MAX_SPILLS: usize = 1;

/** The maximum number of [`Node`]s to execute per cycle. */
const MAX_NODES: usize = 6;

/**
 * The CPU resources available per cycle. The different resources are as
 * follows (modelled on Skylake):
 *  - The number of instructions that can be decoded.
 *  - The number of flag-using macro instructions (this is a hack).
 *  - The number of address generation units.
 *  - The number of load units.
 *  - The number of store units.
 *  - The number of arithmetic / logic units.
 *  - The number of multiplication units.
 * These correspond to the hexadecimal digits of the [`Resources`] from least
 * to most significant.
 */
pub const BUDGET: Resources = Resources::new(0x1412316);

/** The resources needed to move a value from one register to another. */
pub const MOVE_COST: Resources = Resources::new(0x0000001);

/** The resources needed to spill an Out. */
pub const SPILL_COST: Resources = Resources::new(0x0010101);

/**
 * The additional resources needed per operand that is a Slot.
 */
pub const SLOT_COST: Resources = Resources::new(0x0001100);

/**
 * Represents a list of instructions that can be decoded in the same cycle and
 * executed in the same cycle.
 */
#[derive(Debug)]
struct Cycle {
    /** The CPU resources unused in this `Cycle`. */
    remaining: Resources,
    /** The number of [`Out`]s in `spills`. */
    num_spills: u8,
    /** The number of [`Node`]s in `nodes`. */
    num_nodes: u8,
    /** The [`Out`]s to spill in this `Cycle`. */
    spills: [Out; MAX_SPILLS],
    /** The [`Node`]s to execute in this `Cycle`. */
    nodes: [Node; MAX_NODES],
}

impl Cycle {
    /** Constructs an empty Cycle with `BUDGET` remaining. */
    pub fn new() -> Self {
        Cycle {
            remaining: BUDGET,
            num_spills: 0,
            num_nodes: 0,
            spills: [DUMMY_OUT; MAX_SPILLS],
            nodes: [DUMMY_NODE; MAX_NODES],
        }
    }
}

/**
 * Represents an allocation of instructions to clock cycles.
 *
 * This data structure is agnostic as to whether time runs forwards or
 * backwards; you can use it to generate code in either direction. Therefore,
 * we use the terminology "larger" and "smaller", not "earlier" or "later".
 */
#[derive(Debug)]
pub struct Placer {
    /** The Cycles in which we're placing things. */
    cycles: Vec<Cycle>,
}

impl Placer {
    pub fn new() -> Self {
        Placer {
            cycles: Vec::new(),
        }
    }

    /** Find a cycle that can afford `cost`, and subtract `cost` from it. */
    fn choose_cycle(&mut self, cost: Resources, cycle: &mut usize) {
        while *cycle < self.cycles.len() && !(cost <= self.cycles[*cycle].remaining) {
            *cycle += 1;
        }
        while self.cycles.len() <= *cycle {
            self.cycles.push(Cycle::new());
        }
        self.cycles[*cycle].remaining -= cost;
    }

    /**
     * Decide when to execute `spill`. On entry, `*cycle` is the least time
     * that is acceptable. `*cycle` is increased as necessary to find a cycle
     * that can afford `cost`.
     */
    pub fn add_spill(&mut self, spill: Out, cycle: &mut usize) {
        self.choose_cycle(SPILL_COST, cycle);
        let c = &mut self.cycles[*cycle];
        assert!((c.num_spills as usize) < MAX_SPILLS);
        c.spills[c.num_spills as usize] = spill;
        c.num_spills += 1;
    }

    /**
     * Decide when to execute `node`. On entry, `*cycle` is the least time
     * that is acceptable. `*cycle` is increased as necessary to find a cycle
     * that can afford `cost`.
     */
    pub fn add_node(&mut self, node: Node, cost: Resources, cycle: &mut usize) {
        self.choose_cycle(cost, cycle);
        let c = &mut self.cycles[*cycle];
        assert!((c.num_nodes as usize) < MAX_NODES);
        c.nodes[c.num_nodes as usize ] = node;
        c.num_nodes += 1;
    }

    /**
     * Allocate spill slots, resolve operands, convert all instructions to
     * [`Action`]s, and return them in the order they should be executed in.
     *
     *  - dataflow - For looking up information about [`Node`]s.
     *  - dest_regs - The register in which each [`Out`] should initially be
     *    placed.
     *  - num_slots - The number of [`Slot`]s in use. This is incremented to
     *    allocate spill slots.
     */
    pub fn finish(
        self,
        dataflow: &Dataflow,
        dest_regs: &ArrayMap<Out, RegIndex>,
        num_slots: &mut usize,
    ) -> Vec<Action> {
        // Initialise bindings.
        let register_to_index = map_from_register_to_index();
        let mut spills: ArrayMap<Out, Option<Slot>> = dataflow.out_map();
        let mut regs: ArrayMap<RegIndex, Out> = ArrayMap::new_with(NUM_REGISTERS, || DUMMY_OUT);
        for (out, &value) in dataflow.outs(dataflow.entry_node()).zip(dataflow.inputs()) {
            match value {
                Value::Register(r) => {
                    let ri = *register_to_index.get(&r).expect("Not an allocatable register");
                    regs[ri] = out;
                },
                Value::Slot(s) => {
                    assert!(s.0 < *num_slots);
                    spills[out] = Some(s);
                },
            }
        }
        // Build the list of instructions.        
        let mut ret = Vec::with_capacity(self.cycles.len() * MAX_NODES);
        for c in self.cycles {
            for &s in &c.spills[0..c.num_spills as usize] {
                assert!(spills[s].is_none()); // Not yet spilled.
                let ri = dest_regs[s];
                assert!(regs[ri] == s); // Not yet overwritten.
                let slot = Slot(*num_slots);
                *num_slots += 1;
                spills[s] = Some(slot);
                ret.push(Action::Move(slot.into(), ALLOCATABLE_REGISTERS[ri.0].into()));
            }
            for &n in &c.nodes[0..c.num_nodes as usize] {
                let outs: Vec<Register> = dataflow.outs(n)
                    .map(|dest| ALLOCATABLE_REGISTERS[dest_regs[dest].0])
                    .collect();
                let ins: Vec<Value> = dataflow.ins(n).iter().map(|&src| {
                    let ri = dest_regs[src];
                    if regs[ri] == src {
                        ALLOCATABLE_REGISTERS[ri.0].into()
                    } else {
                        spills[src].expect("Value was overwritten but not spilled").into()
                    }
                }).collect();
                ret.push(Op::to_action(dataflow.node(n), &outs, &ins).unwrap());
            }
        }
        ret.shrink_to_fit();
        ret
    }
}
