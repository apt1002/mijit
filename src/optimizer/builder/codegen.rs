use std::collections::{HashMap};

use super::{
    code, NUM_REGISTERS,
    Dataflow, Node, Out, Op, Resources, LookupLeaf, Cold, Exit,
    moves, all_registers,
};
use code::{Register, Slot, Variable, Action, EBB, Ending};
use crate::util::{ArrayMap};

/// The state of an algorithm that builds a list of [`Action`].
#[derive(Debug)]
pub struct CodeGen<'a, L: LookupLeaf> {
    /// The [`Dataflow`] graph of the code.
    dataflow: &'a Dataflow,
    /// Lookup information about merge points.
    lookup_leaf: &'a L,
    /// For each `out`, the [`Register`] it should be computed into.
    allocation: HashMap<Out, Register>,
    /// The current number of stack [`Slot`]s.
    slots_used: usize,
    /// For each `Register`, what is in that `Register`.
    registers: ArrayMap<Register, Option<Out>>,
    /// For each [`Out`], the [`Variable`] it is currently held in.
    variables: HashMap<Out, Variable>,
    /// The list of [`Action`]s since the last [`Op::Guard`].
    actions: Vec<Action>,
    /// The list of basic blocks, each ending with an [`Op::Guard`].
    blocks: Vec<(Vec<Action>, Variable, Cold<EBB<L::Leaf>>)>,
}

impl<'a, L: LookupLeaf> CodeGen<'a, L> {
    pub fn new(
        dataflow: &'a Dataflow,
        lookup_leaf: &'a L,
        allocation: HashMap<Out, Register>,
        slots_used: usize,
        variables: HashMap<Out, Variable>,
    ) -> Self {
        let mut registers = ArrayMap::new(NUM_REGISTERS);
        for (&out, &v) in variables.iter() {
            if let Variable::Register(r) = v {
                registers[r] = Some(out);
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

    fn set_variable(&mut self, out: Out, new_v: impl Into<Variable>, old_v: Option<Variable>) {
        let v = self.variables.insert(out, new_v.into());
        assert_eq!(v, old_v);
    }

    /// Returns the number of [`Slot`]s in use.
    pub fn slots_used(&self) -> usize {
        self.slots_used
    }

    /// Return `out`'s [`Register`].
    fn write(&mut self, out: Out) -> Register {
        let r = self.allocation[&out];
        self.set_variable(out, r, None);
        self.registers[r] = Some(out);
        r
    }

    /// Spill `out`, returning its [`Register`].
    fn spill(&mut self, out: Out) -> Register {
        let r = self.allocation[&out];
        assert_eq!(self.registers[r], Some(out));
        let slot = Slot(self.slots_used);
        self.slots_used += 1;
        self.set_variable(out, slot, Some(r.into()));
        r
    }

    /// Returns `out`'s [`Variable`].
    pub fn read(&self, out: Out) -> Variable {
        if let Some(&r) = self.allocation.get(&out) {
            if self.registers[r] == Some(out) {
               // `out` is still in the `Register` it was computed into.
               return r.into();
           }
        }
        let v = self.variables[&out];
        if let Variable::Register(_) = v {
            // We already know `out`'s `Register` holds something else.
            panic!("Value is in a register that has been clobbered");
        }
        v
    }

    /// Generate an [`Action`] to spill `out1` and `out2`.
    pub fn add_spill(&mut self, out1: Out, out2: Out) {
        let r1 = self.spill(out1);
        let r2 = self.spill(out2);
        self.actions.push(Action::Push(Some(r1.into()), Some(r2.into())));
    }

    /// Generate an [`Action`] to execute `n`.
    pub fn add_node(&mut self, n: Node) {
        let df = self.dataflow;
        if df.cost(n).resources == Resources::new(0) { return; }
        let ins: Vec<Variable> = df.ins(n).iter().map(|&in_| self.read(in_)).collect();
        let outs: Vec<Register> = df.outs(n).map(|out| self.write(out)).collect();
        self.actions.push(Op::to_action(df.op(n), &outs, &ins));
    }

    pub fn add_guard(&mut self, guard: Node, cold: Cold<EBB<L::Leaf>>) {
        let df = self.dataflow;
        assert_eq!(df.op(guard), Op::Guard);
        assert_eq!(df.num_outs(guard), 0);
        assert_eq!(df.ins(guard).len(), 1);
        let discriminant = self.read(df.ins(guard)[0]);
        let mut actions = Vec::new();
        std::mem::swap(&mut actions, &mut self.actions);
        self.blocks.push((actions, discriminant, cold));
    }

    pub fn finish(mut self, exit: &Exit, leaf: L::Leaf) -> EBB<L::Leaf> {
        // Work out which live values need to be moved where.
        let after = self.lookup_leaf.after(&leaf);
        let mut dest_to_src: HashMap<Variable, Variable> =
            exit.outputs.iter().zip(&*after.live_values)
                .map(|(&out, &dest)| (dest, self.read(out)))
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
        let mut ebb = EBB {actions: self.actions, ending: Ending::Leaf(leaf)};
        for (actions, discriminant, cold) in self.blocks.into_iter().rev() {
            ebb = EBB {actions, ending: Ending::Switch(discriminant, cold.finish(ebb))};
        };
        ebb
    }
}
