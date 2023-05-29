use std::collections::{HashMap, HashSet};
use std::fmt::{Debug};

use super::{
    code, graph,
    allocate, Instruction,
    Fill, Frontier,
    CodeGen,
    LookupLeaf,
};
use code::{Variable, EBB};
use graph::{Dataflow, Node, Op, Cold, CFT};

//-----------------------------------------------------------------------------

/// Information stored about each guard node, summarising the requirements
/// for the cases where the guard fails.
struct GuardFailure<'a, L: Clone> {
    cold: Cold<&'a CFT<L>>,
    frontier: Frontier,
}

impl<'a, L: Debug + Clone> Debug for GuardFailure<'a, L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let switch = self.cold.debug();
        f.debug_struct("GuardFailure")
            .field("cases", &switch.cases)
            .field("default_", &switch.default_)
            .field("frontier", &self.frontier.0)
            .finish()
    }
}

//-----------------------------------------------------------------------------

struct Walker<'a, L: LookupLeaf> {
    lookup_leaf: &'a L,
}

impl<'a, L: LookupLeaf> Walker<'a, L> {
    fn new(lookup_leaf: &'a L) -> Self {
        Walker {lookup_leaf}
    }

    /// Converts a [`CFT`] into an [`EBB`]. Optimises the hot path in
    /// isolation, and recurses on the cold paths, passing information about
    /// [`Variable`] allocation and instruction scheduling.
    ///
    /// - `fill` - a fresh [`Fill`] whose boundary consists of the nodes
    ///   executed before the guard from which the `HotPathTree` diverges. On
    ///   entry and exit all [`Node`]s must be unmarked.
    /// - `cft` - the code to optimise.
    /// - `slots_used` - the number of [`Slot`]s on entry to the code.
    /// - `lookup_input` - Returns a [`Variable`] that is live on entry.
    /// - `lookup_guard` - returns the `GuardFailure` for an [`Op::Guard`]
    ///
    /// [`Slot`]: code::Slot
    pub fn walk<'w, 'f>(
        &'w mut self,
        fill: &'w mut Fill<'f>,
        cft: &'a CFT<L::Leaf>,
        slots_used: usize,
        lookup_input: &'w dyn Fn(Node) -> Variable,
        lookup_guard: &'w dyn Fn(Node) -> &'w GuardFailure<'a, L::Leaf>,
    ) -> EBB<L::Leaf> {
        let df = fill.dataflow();
        let is_guard = |node| matches!(df.op(node), Op::Guard);

        // Find nodes on the hot path.
        let (colds, exit, leaf) = cft.hot_path();
        fill.exit(exit);

        // Record info about each new `Op::Guard` `Node`.
        let guard_failures = colds.into_iter().map(|(guard, cold)| {
            let mut fill2 = fill.nested();
            cold.map(|&child| child.exits().for_each(|e| fill2.exit(e)));
            (guard, GuardFailure {cold, frontier: fill2.drain().1})
        }).collect::<HashMap<Node, GuardFailure<_>>>();
        let lookup_guard = |guard| guard_failures.get(&guard)
            .unwrap_or_else(|| lookup_guard(guard));

        // Find additional dependencies that the hot exit does not depend on.
        let guards = fill.nodes().filter(|&n| is_guard(n)).collect::<Vec<Node>>();
        for node in guards { fill.resume(&lookup_guard(node).frontier); }

        // Build an instruction schedule and allocate registers.
        let (nodes, frontier) = fill.drain();
        let variables = frontier.0.iter()
            .filter(|(_, dep)| dep.is_value())
            .map(|(&node, _)| (node, lookup_input(node)))
            .collect::<HashMap<Node, Variable>>();
        let distinct_variables: HashSet<Variable> = variables.values().copied().collect();
        assert_eq!(variables.len(), distinct_variables.len());
        let (instructions, allocation) = allocate(
            &variables,
            df,
            &nodes,
            |node| if is_guard(node) { Some(&lookup_guard(node).frontier) } else { None },
            &exit,
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
                            &|node| cg.read(node),
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

/// Convert `cft` into an [`EBB`].
///
/// - `dataflow` - the [`Dataflow`] dependencies of `cft`.
/// - `input_slots_used` - the number of [`Slot`]s that exist on entry.
/// - `input_nodes` - the live [`Node`]s on entry, and the [`Variable`]s that
///   hold them.
/// - `cft` - the control-flow tree to convert.
/// - `lookup_leaf` - looks up properties of the leaves of `cft`.
pub fn cft_to_ebb<L: LookupLeaf>(
    dataflow: &Dataflow,
    input_slots_used: usize,
    input_nodes: &HashMap<Node, Variable>,
    cft: &CFT<L::Leaf>,
    lookup_leaf: &L,
) -> EBB<L::Leaf> {
    // Make a `Fill` and make all the `Op::Input`s boundary `Node`s.
    let mut marks = HashMap::new();
    let mut fill = Fill::new(dataflow, &mut marks);
    fill.mark(dataflow.undefined());
    for &node in input_nodes.keys() { fill.mark(node); }
    // Build the new `EBB`.
    let mut walker = Walker::new(lookup_leaf);
    walker.walk(
        &mut fill.nested(),
        cft,
        input_slots_used,
        &|node| input_nodes[&node],
        &|guard| panic!("Unknown guard {:?}", guard),
    )
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use code::{Register, REGISTERS, Slot, Precision, BinaryOp, Width, build};
    use BinaryOp::*;
    use Precision::*;
    use Width::*;
    use graph::{Convention, Exit};
    use crate::util::{ArrayMap, AsUsize, reverse_map};

    const R0: Register = REGISTERS[0];
    const R1: Register = REGISTERS[1];
    const R2: Register = REGISTERS[2];
    const R3: Register = REGISTERS[3];

    /// The optimizer doesn't reorder guards at the moment. Maybe it will?
    #[test]
    fn reorder_guards() {
        // Each leaf will return a single `Register`.
        // Weight = register number.
        let afters: ArrayMap<Register, _> = REGISTERS.iter().map(
            |&r| Convention {lives: Box::new([r.into()]), slots_used: 0}
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
        // Make a dataflow graph.
        // x_1, x_2, x_3, x_4 are computed in that order,
        // but tested in reverse order.
        let mut df = Dataflow::new(4);
        let input_map: HashMap<Node, Variable> = (0..4).map(|i| {
            (df.inputs()[i], REGISTERS[i].into())
        }).collect();
        let x_0 = df.inputs()[0];
        let m_1 = df.add_node(Op::Binary(P64, Mul), &[x_0, x_0]);
        let m_2 = df.add_node(Op::Binary(P64, Mul), &[m_1, m_1]);
        let m_3 = df.add_node(Op::Binary(P64, Mul), &[m_2, m_2]);
        let m_4 = df.add_node(Op::Binary(P64, Mul), &[m_3, m_3]);
        let g_1 = df.add_node(Op::Guard, &[df.undefined(), m_4]);
        let e_1 = Exit {sequence: g_1, outputs: Box::new([df.inputs()[1]])};
        let g_2 = df.add_node(Op::Guard, &[g_1, m_3]);
        let e_2 = Exit {sequence: g_2, outputs: Box::new([df.inputs()[2]])};
        let g_3 = df.add_node(Op::Guard, &[g_2, m_2]);
        let e_3 = Exit {sequence: g_3, outputs: Box::new([df.inputs()[3]])};
        let e_x = Exit {sequence: g_3, outputs: Box::new([m_1])};
        // Make a CFT.
        let mut cft = CFT::Merge {exit: e_x, leaf: REGISTERS[11]};
        cft = CFT::switch(g_3, [cft], CFT::Merge {exit: e_3, leaf: R3}, 0);
        cft = CFT::switch(g_2, [cft], CFT::Merge {exit: e_2, leaf: R2}, 0);
        cft = CFT::switch(g_1, [cft], CFT::Merge {exit: e_1, leaf: R1}, 0);
        // Call `build()`.
        let _observed = cft_to_ebb(&df, 0, &input_map, &cft, &afters);
        // TODO: Expected output.
    }

    /// Regression test from Bee.
    #[test]
    fn bee_1() {
        let convention = Convention {slots_used: 0, lives: Box::new([R0.into()])};
        // Make an `EBB`.
        let ebb = build(|b| {
            b.index(
                R0,
                Box::new([
                    build(|mut b| {
                        b.guard(R0, false, build(|b| b.jump(5)));
                        b.jump(4)
                    }),
                    build(|mut b| {
                        b.guard(R0, true, build(|b| b.jump(3)));
                        b.jump(2)
                    }),
                ]),
                build(|b| b.jump(1)),
            )
        });
        // Optimize it.
        let mut dataflow = Dataflow::new(convention.lives.len());
        let input_map = HashMap::from([
            (dataflow.inputs()[0], R0.into()),
        ]);
        let cft = super::super::simulate(&mut dataflow, 0, reverse_map(&input_map), &ebb, &convention);
        let _observed = cft_to_ebb(&dataflow, 0, &input_map, &cft, &convention);
        // TODO: Expected output.
    }

    /// Regression test from Bee.
    #[test]
    fn bee_2() {
        let convention = Convention {
            slots_used: 0,
            lives: Box::new([R0.into(), R3.into()]),
        };
        // Make an `EBB`.
        let ebb = build(|mut b| {
            b.binary64(Or, R3, R0, R0);
            b.guard(R0, false, build(|b| b.jump(2)));
            b.guard(R0, false, build(|b| b.jump(3)));
            b.binary64(And, R3, R0, R0);
            b.jump(1)
        });
        // Optimize it.
        let mut dataflow = Dataflow::new(convention.lives.len());
        let input_map = HashMap::from([
            (dataflow.inputs()[0], R0.into()),
            (dataflow.inputs()[1], R3.into()),
        ]);
        let cft = super::super::simulate(&mut dataflow, 0, reverse_map(&input_map), &ebb, &convention);
        let _observed = cft_to_ebb(&dataflow, 0, &input_map, &cft, &convention);
        // TODO: Expected output.
    }

    /// Test `Send`.
    #[test]
    fn load_to_store() {
        let convention = Convention {
            slots_used: 2,
            lives: Box::new([Slot(0).into(), Slot(1).into()]),
        };
        // Make an `EBB`.
        let input = build(|mut b| {
            b.binary64(Mul, R0, Slot(0), Slot(0));
            b.binary64(Add, R0, Slot(1), R0);
            b.load(R0, (R0, 0, Eight));
            b.load(R1, (R0, 8, Eight));
            for _ in 0..4 {
                b.load(R2, (R0, 16, Eight));
                b.binary64(Mul, R1, R1, R2);
            }
            b.move_(Slot(0), R1);
            b.send(Slot(1), R0);
            b.const_(R1, 42);
            b.store(R1, (Slot(1), 0, Eight));
            b.jump(0)
        });
        // Optimize it.
        println!("input = {:#?}", input);
        let mut dataflow = Dataflow::new(convention.lives.len());
        let input_map = HashMap::from([
            (dataflow.inputs()[0], Slot(0).into()),
            (dataflow.inputs()[1], Slot(1).into()),
        ]);
        let cft = super::super::simulate(&mut dataflow, 2, reverse_map(&input_map), &input, &convention);
        let output = cft_to_ebb(&dataflow, 2, &input_map, &cft, &convention);
        // TODO: Expected output.
        println!("output = {:#?}", output);
    }
}
