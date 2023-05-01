use std::collections::{HashMap};

use super::{
    code, NUM_REGISTERS,
    Dataflow, Node, Op, Resources, LookupLeaf, Cold, Exit,
    moves, all_registers,
};
use code::{Register, Slot, Variable, Action, EBB, Ending};
use crate::util::{ArrayMap};

/// The element type of [`CodeGen::blocks`].
#[derive(Debug)]
struct Block<L> {
    /// The [`Action`]s to execute.
    actions: Box<[Action]>,
    /// The [`Variable`] to check.
    discriminant: Variable,
    /// What to do if `discriminant` does not have its expected value.
    cold: Cold<EBB<L>>,
}

/// The state of an algorithm that builds an [`EBB`] given `EBB`s for the cold
/// paths.
#[derive(Debug)]
pub struct CodeGen<'a, L: LookupLeaf> {
    /// The [`Dataflow`] graph of the code.
    dataflow: &'a Dataflow,
    /// Lookup information about merge points.
    lookup_leaf: &'a L,
    /// For each `Node`, the [`Register`] it should be computed into.
    allocation: HashMap<Node, Register>,
    /// The current number of stack [`Slot`]s.
    slots_used: usize,
    /// For each `Register`, what is in that `Register`.
    registers: ArrayMap<Register, Option<Node>>,
    /// For each [`Node`], the [`Variable`] it is currently held in.
    variables: HashMap<Node, Variable>,
    /// The list of [`Action`]s since the last [`Op::Guard`].
    actions: Vec<Action>,
    /// The list of basic blocks, each ending with an [`Op::Guard`].
    blocks: Vec<Block<L::Leaf>>,
}

impl<'a, L: LookupLeaf> CodeGen<'a, L> {
    pub fn new(
        dataflow: &'a Dataflow,
        lookup_leaf: &'a L,
        allocation: HashMap<Node, Register>,
        slots_used: usize,
        variables: HashMap<Node, Variable>,
    ) -> Self {
        let mut registers = ArrayMap::new(NUM_REGISTERS);
        for (&node, &v) in variables.iter() {
            if let Variable::Register(r) = v {
                registers[r] = Some(node);
            }
        }
        Self {
            dataflow,
            lookup_leaf,
            allocation,
            slots_used,
            registers,
            variables,
            actions: Vec::new(),
            blocks: Vec::new(),
        }
    }

    fn set_variable(&mut self, node: Node, new_v: impl Into<Variable>, old_v: Option<Variable>) {
        let v = self.variables.insert(node, new_v.into());
        assert_eq!(v, old_v);
    }

    /// Returns the number of [`Slot`]s in use.
    pub fn slots_used(&self) -> usize {
        self.slots_used
    }

    /// Return `node`'s [`Register`].
    fn write(&mut self, node: Node) -> Register {
        let r = self.allocation[&node];
        self.set_variable(node, r, None);
        self.registers[r] = Some(node);
        r
    }

    /// Spill `node`, returning its [`Register`].
    fn spill(&mut self, node: Node) -> Register {
        let r = self.allocation[&node];
        assert_eq!(self.registers[r], Some(node));
        let slot = Slot(self.slots_used);
        self.slots_used += 1;
        self.set_variable(node, slot, Some(r.into()));
        r
    }

    /// Returns `node`'s [`Variable`].
    pub fn read(&self, node: Node) -> Variable {
        if let Some(&r) = self.allocation.get(&node) {
            if self.registers[r] == Some(node) {
               // `node` is still in the `Register` it was computed into.
               return r.into();
           }
        }
        let v = self.variables[&node];
        if let Variable::Register(_) = v {
            // We already know `node`'s `Register` holds something else.
            panic!("Value is in a register that has been clobbered");
        }
        v
    }

    /// Generate an [`Action`] to spill `out1` and `out2`.
    pub fn add_spill(&mut self, node1: Node, node2: Node) {
        let r1 = self.spill(node1);
        let r2 = self.spill(node2);
        self.actions.push(Action::Push(Some(r1.into()), Some(r2.into())));
    }

    /// Generate an [`Action`] to execute `n`.
    pub fn add_node(&mut self, n: Node) {
        let df = self.dataflow;
        if df.cost(n).resources == Resources::new(0) { return; }
        let ins: Vec<Variable> = df.ins(n).iter().map(|&in_| self.read(in_)).collect();
        let out = if df.has_out(n) { Some(self.write(n)) } else { None };
        self.actions.push(Op::to_action(df.op(n), out, &ins));
    }

    /// Generate an `Ending::Switch` to execute `guard`.
    ///
    /// - cold - What happens if `guard` fails.
    pub fn add_guard(&mut self, guard: Node, cold: Cold<EBB<L::Leaf>>) {
        let df = self.dataflow;
        assert_eq!(df.op(guard), Op::Guard);
        assert_eq!(df.ins(guard).len(), 1);
        let discriminant = self.read(df.ins(guard)[0]);
        let mut actions = Vec::new();
        std::mem::swap(&mut actions, &mut self.actions);
        self.blocks.push(Block {actions: actions.into(), discriminant, cold});
    }

    /// Generate an `Ending::Leaf` to fulfil `exit` and merge with `leaf`.
    /// Returns the finished [`EBB`].
    pub fn finish(mut self, exit: &Exit, leaf: L::Leaf) -> EBB<L::Leaf> {
        // Work out which live values need to be moved where.
        let after = self.lookup_leaf.after(&leaf);
        let mut dest_to_src: HashMap<Variable, Variable> =
            exit.outputs.iter().zip(&*after.live_values)
                .map(|(&node, &dest)| (dest, self.read(node)))
                .collect();

        // Create spill slots if necessary to match `after`.
        while self.slots_used < after.slots_used {
            let src1 = dest_to_src.remove(&Slot(self.slots_used + 1).into());
            let src2 = dest_to_src.remove(&Slot(self.slots_used).into());
            self.actions.push(Action::Push(src1, src2));
            self.slots_used += 2;
        }

        // We need a temporary `Register`: the least used in `dest_to_src`.
        // `uses[r] & 1` indicates that `r` is used as a destination.
        // `uses[r] >> 1` counts uses of `r` as a source.
        let mut uses: ArrayMap<Register, usize> = ArrayMap::new(NUM_REGISTERS);
        for (&dest, &src) in &dest_to_src {
            if let Variable::Register(r) = dest { uses[r] |= 1; }
            if let Variable::Register(r) = src { uses[r] += 2; }
        }
        let temp = all_registers().min_by_key(|&r| uses[r]).unwrap();
        let mut temp_replacement = Variable::from(Slot(self.slots_used));

        // If `temp` is used, spill it and replace all mentions of it.
        if uses[temp] == 1 {
            // `temp` is a destination only.
            self.actions.push(Action::Push(None, None));
            self.slots_used += 2;
        } else if uses[temp] >= 2 {
            // `temp` is used as a source.
            self.actions.push(Action::Push(None, Some(temp.into())));
            self.slots_used += 2;
        } else {
            temp_replacement = Variable::from(temp);
        }

        // Move all live values into the expected `Variable`s.
        // TODO: Find a way to schedule these `Move`s properly or to eliminate them.
        self.actions.extend(moves(dest_to_src, &temp.into()).map(
            |(mut dest, mut src)| {
                if src == temp.into() { src = temp_replacement; }
                if dest == temp.into() { dest = temp_replacement; }
                Action::Move(dest, src)
            }
        ));

        if uses[temp] & 1 != 0 {
            // `temp` is a destination.
            self.actions.push(Action::Move(temp.into(), temp_replacement));
        }

        // Drop now-unused slots.
        let num_drops = self.slots_used.checked_sub(after.slots_used).unwrap();
        if num_drops > 0 {
            assert_eq!(num_drops & 1, 0);
            self.actions.push(Action::Drop(num_drops >> 1));
        }

        // Unwind the stack of `colds` and construct the final `EBB`.
        let mut ebb = EBB {actions: self.actions.into(), ending: Ending::Leaf(leaf)};
        for Block {actions, discriminant, cold} in self.blocks.into_iter().rev() {
            ebb = EBB {actions, ending: Ending::Switch(discriminant, cold.finish(ebb))};
        };
        ebb
    }
}
