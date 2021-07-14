use std::collections::{HashMap};

use super::{NUM_REGISTERS, all_registers, Op, moves};
use super::dataflow::{Dataflow, Node, Out};
use super::code::{Register, Slot, Variable, Convention, Action};
use crate::util::{ArrayMap};

/** The state of an algorithm that builds a list of [`Action`]s. */
pub struct CodeGen<'a> {
    /** The [`Dataflow`] graph of the code. */
    dataflow: &'a Dataflow,
    /** For each `out`, the [`Register`] it should be computed into. */
    allocation: ArrayMap<Out, Option<Register>>,
    /** The current number of stack [`Slot`]s. */
    slots_used: usize,
    /** For each [`Out`], the [`Variable`] it is currently held in. */
    spills: ArrayMap<Out, Option<Variable>>,
    /** For each [`Register`], the [`Out`] it currently holds. */
    regs: ArrayMap<Register, Option<Out>>,
    /** The list of [`Action`]s so far. */
    actions: Vec<Action>,
}

impl<'a> CodeGen<'a> {
    pub fn new(num_globals: usize, before: &Convention, dataflow: &'a Dataflow, allocation: ArrayMap<Out, Option<Register>>) -> Self {
        let mut spills = dataflow.out_map();
        let mut regs = ArrayMap::new(NUM_REGISTERS);
        for (out, &value) in dataflow.outs(dataflow.entry_node()).zip(&before.live_values) {
            match value {
                Variable::Register(r) => regs[r] = Some(out),
                Variable::Global(g) => assert!(g.0 < num_globals),
                Variable::Slot(s) => assert!(s.0 < before.slots_used),
            }
            spills[out] = Some(value);
        }
        Self {
            dataflow: dataflow,
            allocation: allocation,
            slots_used: before.slots_used,
            spills: spills,
            regs: regs,
            actions: Vec::new(),
        }
    }

    /** Puts `out` in its allocated [`Register`], and return it. */
    fn write(&mut self, out: Out) -> Register {
        let r = self.allocation[out].expect("Wrote a non-register");
        self.regs[r] = Some(out);
        r
    }

    /** Spill `out` to (unused) `slot`. Returns `out`'s [`Register`]. */
    fn spill(&mut self, out: Out, slot: Slot) -> Register {
        let old = self.spills[out].replace(slot.into());
        assert!(old.is_none()); // Not previously spilled.
        let r = self.allocation[out].expect("Spilled a non-register");
        assert_eq!(self.regs[r], Some(out)); // Not yet overwritten.
        r
    }

    /** Returns the [`Variable`] currently holding the value of [`Out`]. */
    fn read(&self, out: Out) -> Variable {
        if let Some(r) = self.allocation[out] {
            if self.regs[r] == Some(out) {
                return r.into()
            }
        }
        self.spills[out].expect("Variable was overwritten but not spilled")
    }

    /** Generate an [`Action`] to spill `out_x` and `out_y`. */
    pub fn add_spill(&mut self, out1: Out, out2: Out) {
        let r1 = self.spill(out1, Slot(self.slots_used + 1));
        let r2 = self.spill(out2, Slot(self.slots_used));
        self.actions.push(Action::Push(Some(r1.into()), Some(r2.into())));
        self.slots_used += 2;
    }

    /** Generate an [`Action`] to execute `n`. */
    pub fn add_node(&mut self, n: Node) {
        let df = self.dataflow;
        let ins: Vec<Variable> = df.ins(n).iter().map(|&in_| self.read(in_)).collect();
        let outs: Vec<Register> = df.outs(n).map(|out| self.write(out)).collect();
        self.actions.push(Op::to_action(df.op(n), &outs, &ins));
    }

    /**
     * Generate [`Action`]s as necessary to match `exit_node` to `after`, and
     * return the final list of Actions.
     */
    pub fn finish(mut self, after: &Convention, exit_node: Node) -> Box<[Action]> {
        // Work out which live values need to be moved where.
        let mut dest_to_src: HashMap<Variable, Variable> =
            self.dataflow.ins(exit_node).iter().zip(&after.live_values)
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
        let mut uses: ArrayMap<Register, usize> = ArrayMap::new(NUM_REGISTERS);
        for (&dest, &src) in &dest_to_src {
            if let Variable::Register(r) = dest { uses[r] |= 1; }
            if let Variable::Register(r) = src { uses[r] += 2; }
        }
        let temp = all_registers().min_by_key(|&r| uses[r]).unwrap();
        // If `temp` is used, spill it and replace all mentions of it.
        let temp_replacement = Variable::from(Slot(self.slots_used));
        if uses[temp] == 1 {
            // `temp` is a destination only.
            self.actions.push(Action::Push(None, None));
            self.slots_used += 2;
        } else if uses[temp] >= 2 {
            // `temp` is used as a source.
            self.actions.push(Action::Push(None, Some(temp.into())));
            self.slots_used += 2;
        }
        // Move all live values into the expected `Variable`s.
        // TODO: Find a way to schedule these `Move`s properly or to eliminate them.
        self.actions.extend(moves(dest_to_src, &temp.into()).map(|(mut dest, mut src)| {
            if src == temp.into() { src = temp_replacement; }
            if dest == temp.into() { dest = temp_replacement; }
            Action::Move(dest, src)
        }));
        if uses[temp] & 1 != 0 {
            // `temp` is a destination.
            self.actions.push(Action::Move(temp.into(), temp_replacement));
        }
        // Drop now-unused slots.
        let num_drops = self.slots_used.checked_sub(after.slots_used).unwrap();
        if num_drops > 0 {
            assert_eq!(num_drops & 1, 0);
            self.actions.push(Action::DropMany(num_drops >> 1));
        }
        // Return.
        self.actions.into()
    }
}
