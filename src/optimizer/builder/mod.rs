use std::collections::{HashMap};
use std::fmt::{Debug};

use super::{code, target, cost, Dataflow, Node, Out, Op, Resources, LookupLeaf, Cold, CFT};
use code::{Register, Variable, Convention, EBB};

mod fill;
use fill::{Frontier, Fill, with_fill};

mod allocator;
pub use allocator::{Instruction, allocate};

mod moves;
pub use moves::{moves};

mod codegen;
pub use codegen::{CodeGen};

//-----------------------------------------------------------------------------

const NUM_REGISTERS: usize = target::x86_64::ALLOCATABLE_REGISTERS.len();

fn all_registers() -> impl Iterator<Item=Register> {
    (0..NUM_REGISTERS).map(|i| Register::new(i as u8).unwrap())
}

//-----------------------------------------------------------------------------

/// Information stored about each guard node, summarising the requirements
/// for the cases where the guard fails.
struct GuardFailure<'a, L: Clone> {
    cold: Cold<&'a CFT<L>>,
    fontier: Frontier,
}

impl<'a, L: Debug + Clone> Debug for GuardFailure<'a, L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let switch = self.cold.debug();
        f.debug_struct("GuardFailure")
            .field("cases", &switch.cases)
            .field("default_", &switch.default_)
            .field("effects", &self.fontier.effects)
            .field("inputs", &self.fontier.inputs)
            .finish()
    }
}

//-----------------------------------------------------------------------------

struct Builder<'a, L: LookupLeaf> {
    lookup_leaf: &'a L,
}

impl<'a, L: LookupLeaf> Builder<'a, L> {
    fn new(lookup_leaf: &'a L) -> Self {
        Builder {lookup_leaf}
    }

    /// Converts a [`CFT`] into an [`EBB`]. Optimises the hot path in
    /// isolation, and recurses on the cold paths, passing information about
    /// [`Variable`] allocation and instruction scheduling.
    ///
    /// - `fill` - a fresh [`Fill`] whose boundary consists of the nodes
    ///   executed before the guard from which the `HotPathTree` diverges. On
    ///   entry and exit all [`Node`]s must be unmarked.
    /// - `cft` - the code to optimise.
    /// - slots_used - the number of [`Slot`]s on entry to the code.
    /// - lookup_input - called once for each input to the code. It
    ///   returns the [`Variable`] that holds it.
    ///
    /// [`Slot`]: code::Slot
    pub fn walk<'w, 'f>(
        &'w mut self,
        fill: &'w mut Fill<'f>,
        cft: &'a CFT<L::Leaf>,
        slots_used: usize,
        lookup_input: &'w dyn Fn(Out) -> Variable,
        lookup_guard: &'w dyn Fn(Node) -> &'w GuardFailure<'a, L::Leaf>,
    ) -> EBB<L::Leaf> {
        let df = fill.dataflow();
        let is_guard = |node| matches!(df.op(node), Op::Guard);

        // Find nodes on the hot path.
        let (colds, exit, leaf) = cft.hot_path();
        fill.visit(exit);

        // Record info about each new `Op::Guard` `Node`.
        let guard_failures = colds.into_iter().map(|(guard, cold)| {
            let mut fill2 = fill.nested();
            cold.map(|&child| child.exits().for_each(|node| { fill2.visit(node); }));
            (guard, GuardFailure {cold, fontier: fill2.drain().1})
        }).collect::<HashMap<Node, GuardFailure<_>>>();
        let lookup_guard = |guard| guard_failures.get(&guard)
            .unwrap_or_else(|| lookup_guard(guard));

        // Find additional dependencies that the hot exit does not depend on.
        let guards = fill.nodes().filter(|&n| is_guard(n)).collect::<Vec<Node>>();
        for node in guards { fill.resume(&lookup_guard(node).fontier); }

        // Build an instruction schedule and allocate registers.
        let (nodes, Frontier {effects, inputs}) = fill.drain();
        let variables = inputs.into_iter().map(
            |out| (out, lookup_input(out))
        ).collect::<HashMap<Out, Variable>>();
        let (instructions, allocation) = allocate(
            &effects,
            &variables,
            df,
            &*nodes,
            |node| if is_guard(node) { Some(&lookup_guard(node).fontier.inputs) } else { None },
        );

        // Build the EBB.
        let mut cg = CodeGen::new(
            df,
            self.lookup_leaf,
            allocation,
            slots_used,
            variables,
        );
        for &instruction in &instructions {
            match instruction {
                Instruction::Spill(x, y) => {
                    cg.add_spill(x, y);
                },
                Instruction::Node(node) => {
                    fill.mark(node);
                    if is_guard(node) {
                        // Recurse on cold paths.
                        let mut fill2 = fill.nested();
                        let cold = lookup_guard(node).cold.map(|&child| self.walk(
                            &mut fill2,
                            child,
                            cg.slots_used(),
                            &|out| cg.read(out),
                            &|guard| lookup_guard(guard),
                        ));
                        cg.add_guard(node, cold);
                    } else {
                        cg.add_node(node);
                    }
                },
            }
        }
        fill.drain(); // Restore `fill` to its original state.
        cg.finish(exit, leaf)
    }
}

pub fn build<L: LookupLeaf>(
    before: &Convention,
    dataflow: &Dataflow,
    cft: &CFT<L::Leaf>,
    lookup_leaf: &L,
) -> EBB<L::Leaf> {
    // Work out what is where.
    let input_map: HashMap<Out, Variable> =
        dataflow.outs(dataflow.entry_node())
        .zip(&*before.live_values)
        .map(|(out, &variable)| (out, variable))
        .collect();
    // Build the new `EBB`.
    let mut builder = Builder::new(lookup_leaf);
    with_fill(dataflow, |mut fill| builder.walk(
        &mut fill,
        cft,
        before.slots_used,
        &|out| *input_map.get(&out).unwrap(),
        &|guard| panic!("Unknown guard {:?}", guard),
    ))
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use code::{Register, REGISTERS, Global, Precision, BinaryOp, builder};
    use BinaryOp::*;
    use Precision::*;
    use crate::util::{ArrayMap, AsUsize};

    #[test]
    fn reorder_guards() {
        // Each leaf will return a single `Register`.
        // Weight = register number.
        let afters: ArrayMap<Register, _> = REGISTERS.iter().map(
            |&r| Convention {live_values: Box::new([r.into()]), slots_used: 0}
        ).collect();
        impl LookupLeaf for ArrayMap<Register, Convention> {
            type Leaf = Register;
            fn after(&self, leaf: &Register) -> &Convention {
                &self[*leaf]
            }
            fn weight(&self, leaf: &Register) -> usize {
                leaf.as_usize()
            }
        }
        // Make a `before` Convention.
        let before = Convention {
            live_values: Box::new([
                REGISTERS[0].into(),
                REGISTERS[1].into(),
                REGISTERS[2].into(),
                REGISTERS[3].into(),
            ]),
            slots_used: 0,
        };
        // Make a dataflow graph.
        // x_1, x_2, x_3, x_4 are computed in that order,
        // but tested in reverse order.
        let mut df = Dataflow::new(4);
        let entry = df.entry_node();
        let inputs: Vec<Out> = df.outs(entry).collect();
        let x_0 = inputs[0];
        let m_1 = df.add_node(Op::Binary(P64, Mul), &[], &[x_0, x_0], 1);
        let x_1 = df.outs(m_1).next().unwrap();
        let m_2 = df.add_node(Op::Binary(P64,  Mul), &[], &[x_1, x_1], 1);
        let x_2 = df.outs(m_2).next().unwrap();
        let m_3 = df.add_node(Op::Binary(P64, Mul), &[], &[x_2, x_2], 1);
        let x_3 = df.outs(m_3).next().unwrap();
        let m_4 = df.add_node(Op::Binary(P64, Mul), &[], &[x_3, x_3], 1);
        let x_4 = df.outs(m_4).next().unwrap();
        let g_1 = df.add_node(Op::Guard, &[entry], &[x_4], 0);
        let e_1 = df.add_node(Op::Convention, &[g_1], &[inputs[1]], 0);
        let g_2 = df.add_node(Op::Guard, &[entry], &[x_3], 0);
        let e_2 = df.add_node(Op::Convention, &[g_1, g_2], &[inputs[2]], 0);
        let g_3 = df.add_node(Op::Guard, &[entry], &[x_2], 0);
        let e_3 = df.add_node(Op::Convention, &[g_1, g_2, g_3], &[inputs[3]], 0);
        let e_x = df.add_node(Op::Convention, &[g_1, g_2, g_3], &[x_1], 0);
        // Make a CFT.
        let mut cft = CFT::Merge {exit: e_x, leaf: REGISTERS[11]};
        cft = CFT::switch(g_3, [cft], CFT::Merge {exit: e_3, leaf: REGISTERS[3]}, 0);
        cft = CFT::switch(g_2, [cft], CFT::Merge {exit: e_2, leaf: REGISTERS[2]}, 0);
        cft = CFT::switch(g_1, [cft], CFT::Merge {exit: e_1, leaf: REGISTERS[1]}, 0);
        // Call `build()`.
        let _observed = build(&before, &df, &cft, &afters);
        // TODO: Expected output.
    }

    /// Regression test from Bee.
    #[test]
    fn bee_1() {
        let convention = Convention {slots_used: 0, live_values: Box::new([Variable::Global(Global(0))])};
        // Make an `EBB`.
        let ebb = builder::build(&mut |b| {
            b.index(
                Global(0),
                Box::new([
                    builder::build(&mut |mut b| {
                        b.guard(Global(0), false, builder::build(&mut |b| {
                            b.jump(5)
                        }));
                        b.jump(4)
                    }),
                    builder::build(&mut |mut b| {
                        b.guard(Global(0), true, builder::build(&mut |b| {
                            b.jump(3)
                        }));
                        b.jump(2)
                    }),
                ]),
                builder::build(&mut |b| { b.jump(1) }),
            )
        });
        // Optimize it.
        // inline let _observed = super::super::optimize(&convention, &ebb, &convention);
        let (dataflow, cft) = super::super::simulate(&convention, &ebb, &convention);
        let _observed = build(&convention, &dataflow, &cft, &convention);
        // TODO: Expected output.
    }

    /// Regression test from Bee.
    #[test]
    fn bee_2() {
        let convention = Convention {
            slots_used: 0,
            live_values: Box::new([
                Variable::Global(Global(0)),
                Variable::Register(REGISTERS[3]),
            ]),
        };
        // Make an `EBB`.
        let ebb = builder::build(&mut |mut b| {
            b.binary64(Or, REGISTERS[3], Global(0), Global(0));
            b.guard(Global(0), false, builder::build(&mut |b| { b.jump(2) }));
            b.guard(Global(0), false, builder::build(&mut |b| { b.jump(3) }));
            b.binary64(And, REGISTERS[3], Global(0), Global(0));
            b.jump(1)
        });
        // Optimize it.
        // inline let _observed = super::super::optimize(&convention, &ebb, &convention);
        let (dataflow, cft) = super::super::simulate(&convention, &ebb, &convention);
        let _observed = build(&convention, &dataflow, &cft, &convention);
        // TODO: Expected output.
    }
}
