use std::collections::{HashSet, HashMap};

use super::{NUM_REGISTERS, all_registers, EBB, Ending, Op, Dataflow, Node, Out, moves};
use super::code::{Register, Slot, Variable, Convention, Action};
use crate::util::{ArrayMap};

/** The state of an algorithm that builds a list of [`Action`]s in reverse. */
#[derive(Debug)]
pub struct CodeGen<'a> {
    /** The [`Dataflow`] graph of the code. */
    dataflow: &'a Dataflow,
    /** For each `out`, the [`Register`] it should be computed into. */
    allocation: ArrayMap<Out, Option<Register>>,
    /** The current number of stack [`Slot`]s. */
    slots_used: usize,
    /** For each [`Out`], the [`Variable`] it is currently held in. */
    variables: HashMap<Out, Variable>,
    /** The live [`Out`]s. */
    live_outs: HashSet<Out>,
    /** The list of [`Action`]s so far. Stored in reverse order. */
    actions_rev: Vec<Action>,
}

impl<'a> CodeGen<'a> {
    pub fn new(
        dataflow: &'a Dataflow,
        allocation: ArrayMap<Out, Option<Register>>,
        slots_used: usize,
        variables: HashMap<Out, Variable>,
        exit_node: Node,
        after: &Convention,
    ) -> Self {
        Self {
            dataflow,
            allocation,
            slots_used,
            variables,
            live_outs: HashSet::new(),
            actions_rev: Vec::new(),
        }.init(exit_node, after)
    }

    fn init(mut self, exit_node: Node, after: &Convention) -> Self {
        // Work out which live values need to be moved where.
        let mut dest_to_src: HashMap<Variable, Variable> =
            self.dataflow.ins(exit_node).iter().zip(&*after.live_values)
                .map(|(&out, &dest)| (dest, self.read(out)))
                .collect();

        let mut stored_actions = Vec::new();
        let mut slots_used = self.slots_used;

        // Create spill slots if necessary to match `after`.
        while slots_used < after.slots_used {
            let src1 = dest_to_src.remove(&Slot(slots_used + 1).into());
            let src2 = dest_to_src.remove(&Slot(slots_used).into());
            stored_actions.push(Action::Push(src1, src2));
            slots_used += 2;
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
        let temp_replacement = Variable::from(Slot(slots_used));

        // If `temp` is used, spill it and replace all mentions of it.
        if uses[temp] == 1 {
            // `temp` is a destination only.
            stored_actions.push(Action::Push(None, None));
            slots_used += 2;
        } else if uses[temp] >= 2 {
            // `temp` is used as a source.
            stored_actions.push(Action::Push(None, Some(temp.into())));
            slots_used += 2;
        }

        assert_eq!(stored_actions.len() * 2, slots_used.wrapping_sub(self.slots_used));

        // Move all live values into the expected `Variable`s.
        // TODO: Find a way to schedule these `Move`s properly or to eliminate them.
        stored_actions.extend(moves(dest_to_src, &temp.into()).map(
            |(mut dest, mut src)| {
                if src == temp.into() { src = temp_replacement; }
                if dest == temp.into() { dest = temp_replacement; }
                Action::Move(dest, src)
            }
        ));

        if uses[temp] & 1 != 0 {
            // `temp` is a destination.
            stored_actions.push(Action::Move(temp.into(), temp_replacement));
        }

        // Drop now-unused slots.
        let num_drops = slots_used.checked_sub(after.slots_used).unwrap();
        if num_drops > 0 {
            assert_eq!(num_drops & 1, 0);
            stored_actions.push(Action::DropMany(num_drops >> 1));
        }

        // Output the stored actions.
        self.actions_rev.extend(stored_actions.into_iter().rev());

        self
    }

    /** Returns the number of [`Slot`]s in use. */
    pub fn slots_used(&self) -> usize {
        self.slots_used
    }

    /** Remove `out` from `live_outs` and return its [`Register`]. */
    fn write(&mut self, out: Out) -> Register {
        let r = self.allocation[out].expect("Wrote a non-register");
        let v = self.variables.remove(&out);
        assert_eq!(v, Some(Variable::from(r)));
        self.live_outs.remove(&out);
        r
    }

    /** Remove `out` from `variables`. Returns `out`'s [`Register`] if live. */
    fn spill(&mut self, out: Out) -> Option<Register> {
        let r = self.allocation[out].expect("Spilled a non-register");
        let old_value = self.variables.insert(out, r.into());
        assert_eq!(old_value, Some(Variable::from(Slot(self.slots_used))));
        if self.live_outs.contains(&out) {
            Some(r)
        } else {
            None
        }
    }

    /** Adds `out` to `live_outs`, and returns its [`Variable`]. */
    pub fn read(&mut self, out: Out) -> Variable {
        self.live_outs.insert(out);
        self.variables[&out]
    }

    /** Generate an [`Action`] to spill `out_x` and `out_y`. */
    pub fn add_spill(&mut self, out1: Out, out2: Out) {
        self.slots_used -= 1;
        let r2 = self.spill(out2).map(|r| r.into());
        self.slots_used -= 1;
        let r1 = self.spill(out1).map(|r| r.into());
        self.actions_rev.push(Action::Push(r1.into(), r2.into()));
    }

    /** Generate an [`Action`] to execute `n`. */
    pub fn add_node(&mut self, n: Node) {
        let df = self.dataflow;
        let outs: Vec<Register> = df.outs(n).map(|out| self.write(out)).collect();
        let ins: Vec<Variable> = df.ins(n).iter().map(|&in_| self.read(in_)).collect();
        self.actions_rev.push(Op::to_action(df.op(n), &outs, &ins));
    }

    /**
     * Constructs an [`EBB`] from the [`Action`]s generated so far and from
     * `switch`. The list of `Action`s is cleared.
     */
    pub fn ebb<'b>(&mut self, ending: Ending<'b>) -> EBB<'b> {
        let before = Convention {
            live_values: self.live_outs.iter().map(|&out| self.variables[&out]).collect(),
            slots_used: self.slots_used,
        };
        let actions = self.actions_rev.drain(..).rev().collect();
        EBB {before, actions, ending}
    }
}
