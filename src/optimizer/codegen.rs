use std::collections::{HashMap};

use super::{Convention, NUM_REGISTERS, all_registers, Op, moves};
use super::dataflow::{Dataflow, Node, Out};
use super::code::{Register, REGISTERS, Slot, Value, Action};
use crate::util::{ArrayMap};

/** The state of an algorithm that builds a list of [`Action`]s. */
pub struct CodeGen<'a> {
    /** The [`Dataflow`] graph of the code. */
    dataflow: &'a Dataflow,
    /** For each `out`, the [`Register`] it should be computed into. */
    allocation: ArrayMap<Out, Option<Register>>,
    /** The current number of stack [`Slot`]s. */
    slots_used: usize,
    /** For each [`Out`], the [`Value`] it is currently held in. */
    spills: ArrayMap<Out, Option<Value>>,
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
                Value::Register(r) => regs[r] = Some(out),
                Value::Global(g) => assert!(g.0 < num_globals),
                Value::Slot(s) => assert!(s.0 < before.slots_used),
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

    /** Returns the [`Value`] currently holding the value of [`Out`]. */
    fn read(&self, out: Out) -> Value {
        if let Some(r) = self.allocation[out] {
            if self.regs[r] == Some(out) {
                return r.into()
            }
        }
        self.spills[out].expect("Value was overwritten but not spilled")
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
        let ins: Vec<Value> = df.ins(n).iter().map(|&in_| self.read(in_)).collect();
        let outs: Vec<Register> = df.outs(n).map(|out| self.write(out)).collect();
        self.actions.push(Op::to_action(df.op(n), &outs, &ins));
    }

    /**
     * Generate [`Action`]s as necessary to match `exit_node` to `after`, and
     * return the final list of Actions.
     */
    pub fn finish(mut self, after: &Convention, exit_node: Node) -> Box<[Action]> {
        println!("dataflow = {:#?}", self.dataflow);
        println!("allocation = {:#?}", self.allocation);
        println!("spills = {:#?}", self.spills);
        println!("regs = {:#?}", self.regs);
        println!("actions = {:#?}", self.actions);
        // Work out which live values need to be moved where.
        let mut is_used = ArrayMap::new(NUM_REGISTERS);
        let mut dest_to_src: HashMap<Value, Value> =
            self.dataflow.ins(exit_node).iter().zip(&after.live_values).map(|(&out, &dest)| {
                let src = self.read(out);
                if let Value::Register(r) = dest { is_used[r] = true; }
                if let Value::Register(r) = src { is_used[r] = true; }
                (dest, src)
            }).collect();
        // Create spill slots if necessary to match `after`.
        while self.slots_used < after.slots_used {
            let src1 = dest_to_src.remove(&Slot(self.slots_used + 1).into());
            let src2 = dest_to_src.remove(&Slot(self.slots_used).into());
            self.actions.push(Action::Push(src1, src2));
            self.slots_used += 2;
        }
        // Move all live values into the expected `Value`s.
        // TODO: Find a way to schedule these `Move`s properly or to eliminate them.
        // We need a temporary `Register` that is not live.
        // If one is available, use it.
        // Otherwise, spill an arbitrary `Register` and use it.
        let spill_reg = REGISTERS[0]; // TODO: Pick more carefully.
        #[allow(clippy::option_if_let_else)]
        let (temp_value, temp_replacement) =
            if let Some(r) = all_registers().find(|&r| !is_used[r]) {
                // We found an unused `Register`.
                (r.into(), r.into())
            } else {
                // Spill `spill_reg` and use it.
                let spill_slot = Slot(self.slots_used);
                self.actions.push(Action::Push(None, Some(spill_reg.into())));
                self.slots_used += 2;
                (spill_reg.into(), spill_slot.into())
            };
        let is_temp_a_dest = dest_to_src.contains_key(&temp_value);
        self.actions.extend(moves(dest_to_src, &temp_value).map(|(mut dest, mut src)| {
            if src == temp_value { src = temp_replacement; }
            if dest == temp_value { dest = temp_replacement; }
            Action::Move(dest, src)
        }));
        if is_temp_a_dest {
            self.actions.push(Action::Pop(None, Some(spill_reg)));
            self.slots_used -= 2;
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
