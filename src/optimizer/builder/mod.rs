use std::collections::{HashSet, HashMap};

use super::{code, target, cost, cft, Dataflow, Node, Out, Cold, CFT, Op, Resources, LookupLeaf};
use code::{Slot, Variable, Convention, Ending, EBB};
use crate::util::{ArrayMap};

mod flood;
use flood::{flood};

mod keep_alive;
pub use keep_alive::{keep_alive_sets, HotPathTree};

mod allocator;
pub use allocator::{Instruction, allocate};

mod moves;
pub use moves::{moves};

mod codegen;
pub use codegen::{CodeGen};

//-----------------------------------------------------------------------------

use code::{Register};

const NUM_REGISTERS: usize = target::x86_64::ALLOCATABLE_REGISTERS.len();

fn all_registers() -> impl Iterator<Item=Register> {
    (0..NUM_REGISTERS).map(|i| Register::new(i as u8).unwrap())
}

//-----------------------------------------------------------------------------

struct Builder<'a> {
    dataflow: &'a Dataflow,
    marks: ArrayMap<Node, usize>,
}

impl<'a> Builder<'a> {
    fn new(dataflow: &'a Dataflow) -> Self {
        let mut marks = dataflow.node_map();
        marks[dataflow.entry_node()] = 1;
        Builder {dataflow, marks}
    }

    /** Tests whether `node` is a [`Op::Guard`]. */
    fn is_guard(&self, node: Node) -> bool {
        matches!(self.dataflow.op(node), Op::Guard)
    }

    /**
     * Converts `tree` into an [`EBB`]. Optimises the hot path in isolation,
     * and recurses on the cold paths, passing information about [`Variable`]
     * allocation and instruction scheduling.
     *
     * On entry and on exit, `marks[node]` must be in `1..coldness` if
     * `node` is before the guard from which `tree` diverges, and `0`
     * otherwise. `marks[entry_node]` must be `1`.
     *
     * - tree - the subtree to convert.
     * - coldness - 2 + the number of cold branches needed to reach `tree`.
     *   (`0` is used for unmarked nodes, and `1` for the entry node).
     * - slots_used - the number of [`Slot`]s on entry to `tree`.
     * - input - called once for each input to `tree`. It informs the caller
     *   of `walk()` that the input is live, and returns the [`Variable`] that
     *   holds it.
     */
    pub fn walk<L: Clone>(
        &mut self,
        tree: &HotPathTree<L>,
        coldness: usize,
        slots_used: usize,
        input: &mut dyn FnMut(Out) -> Variable,
        lookup_leaf: &impl LookupLeaf<L>,
    ) -> EBB<L> {
        let mut inputs = HashSet::new();
        let nodes = flood(self.dataflow, &mut self.marks, coldness, &mut inputs, tree.exit);
        let input_variables: Box<[_]> = inputs.iter().copied().map(input).collect();
        let mut variables: HashMap<Out, Variable> = inputs.iter().zip(&*input_variables).map(
            |(&out, &variable)| (out, variable)
        ).collect();
        let before: Convention = Convention {slots_used, live_values: input_variables};
        let (instructions, allocation) = allocate(&before, self.dataflow, &*nodes);
        // Allocate spill slots on the hot path.
        // Also, find the final location of each `Out`.
        let mut slots_used = before.slots_used;
        for &instruction in &instructions {
            match instruction {
                Instruction::Spill(out1, out2) => {
                    variables.insert(out1, Slot(slots_used).into());
                    slots_used += 1;
                    variables.insert(out2, Slot(slots_used).into());
                    slots_used += 1;
                },
                Instruction::Node(node) => {
                    for out in self.dataflow.outs(node) {
                        let r = allocation[out].expect("Missing destination register");
                        variables.insert(out, r.into());
                    }
                },
            }
        }

        let mut cg = CodeGen::new(
            self.dataflow,
            allocation,
            slots_used,
            variables,
            tree.exit,
            lookup_leaf.after(&tree.leaf),
        );

        // Depth-first walk from the exits back to the entry.
        let mut ending = Ending::Leaf(tree.leaf.clone());
        let mut rev_iter = instructions.iter().rev();
        let last_instruction = rev_iter.next().expect("Missing exit node");
        assert_eq!(last_instruction, &Instruction::Node(tree.exit));
        self.marks[tree.exit] = 0;
        for &instruction in rev_iter {
            match instruction {
                Instruction::Spill(out1, out2) => {
                    cg.add_spill(out1, out2);
                },
                Instruction::Node(node) => {
                    if self.is_guard(node) {
                        let hot = cg.ebb(ending);
                        let gf = tree.children.get(&node).expect("Missing GuardFailure");
                        let cold = gf.cold.map(|child| self.walk(
                            child,
                            coldness + 1,
                            cg.slots_used(),
                            &mut |out| cg.read(out),
                            lookup_leaf,
                        ));
                        let cft_switch: cft::Switch<EBB<_>> = cold.insert_hot(hot);
                        ending = Ending::Switch(code::Switch::Index {
                            discriminant: {
                                let outs = self.dataflow.ins(cft_switch.guard);
                                assert_eq!(outs.len(), 1);
                                cg.read(outs[0])
                            },
                            cases: cft_switch.cases,
                            default_: cft_switch.default_,
                        });
                    } else {
                        cg.add_node(node);
                    }
                    self.marks[node] = 0;
                },
            }
        }
        cg.ebb(ending)
    }
}

pub fn build<L: Clone>(
    before: &Convention,
    dataflow: &Dataflow,
    cft: &CFT<L>,
    lookup_leaf: &impl LookupLeaf<L>,
) -> EBB<L> {
    // Work out what is where.
    let entry = dataflow.entry_node();
    let input_map: HashMap<Out, Variable> =
        dataflow.ins(entry).iter()
        .zip(&*before.live_values)
        .map(|(&out, &variable)| (out, variable))
        .collect();
    // Compute the keep-alive sets.
    let tree = keep_alive_sets(dataflow, cft);
    // Build the new `EBB`.
    let mut builder = Builder::new(dataflow);
    builder.marks[entry] = 1;
    builder.walk(
        &tree,
        2,
        before.slots_used,
        &mut |out| *input_map.get(&out).unwrap(),
        lookup_leaf,
    )
}
