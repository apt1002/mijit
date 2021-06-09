use std::num::{Wrapping};
use memoffset::{offset_of};

use super::target::{Target};
use super::{jit};
use super::code::{
    self, TestOp, Precision, UnaryOp, BinaryOp, Width,
    Global, Register, Value, IntoValue, REGISTERS, FAST_VALUES, Action, Case,
};
use Precision::*;
use UnaryOp::*;
use BinaryOp::*;
use Width::*;
use Action::*;

/** Beetle's registers that are live in `State::Root`. */
#[repr(C)]
#[derive(Default)]
pub struct Registers {
    ep: u32,
    a: u32,
    sp: u32,
    rp: u32,
    s0: u32,
    r0: u32,
    throw: u32,
    bad: u32,
    not_address: u32,
}

/** Beetle's registers, including those live in all `State`s. */
#[repr(C)]
#[derive(Default)]
struct AllRegisters {
    public: Registers,
    memory: u64,
    opcode: u32,
    stack0: u32,
    stack1: u32,
    loop_flag: u32,
    loop_step: u32,
    loop_new: u32,
    loop_old: u32,
}

/** Computes the number of bytes in `n` cells. */
pub const fn cell_bytes(n: i64) -> i64 { Wrapping(4 * n).0 }

/** The number of bits in a word. */
pub const CELL_BITS: i64 = cell_bytes(8);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {
    Root,
    Dispatch,
    Next,
    Pick,
    Roll,
    Qdup,
    Lshift,
    Rshift,
    Branch,
    Branchi,
    Qbranch,
    Qbranchi,
    Loop,
    Loopi,
    Ploopp,
    Ploopm,
    Ploop,
    Ploopip,
    Ploopim,
    Ploopi,
    Halt,
}

//-----------------------------------------------------------------------------

/** The suggested size of the Beetle memory, in cells. */
pub const MEMORY_CELLS: usize = 1 << 20;
/** The suggested size of the Beetle data stack, in cells. */
pub const DATA_CELLS: usize = 1 << 18;
/** The suggested size of the Beetle return stack, in cells. */
pub const RETURN_CELLS: usize = 1 << 18;

pub struct VM<T: Target> {
    /** The compiled code, registers, and other compiler state. */
    jit: jit::Jit<Machine, T>,
    /** The Beetle state (other than the memory). */
    state: AllRegisters,
    /** The Beetle memory. */
    memory: Vec<u32>,
    /** The amount of unallocated memory, in cells. */
    free_cells: u32,
    /** The address of a HALT instruction. */
    halt_addr: u32,
}

impl<T: Target> VM<T> {
    /**
     * Constructs a Beetle virtual machine with the specified parameters.
     *
     * The memory is `memory_cells` cells. The data stack occupies the last
     * `data_cells` cells of the memory, and the return stack occupies
     * the last `return_cells` cells before that. The cells before that
     * are free for the program's use.
     */
    pub fn new(
        target: T,
        memory_cells: usize,
        data_cells: usize,
        return_cells: usize,
    ) -> Self {
        assert!(memory_cells <= u32::MAX as usize);
        assert!(data_cells <= u32::MAX as usize);
        assert!(return_cells <= u32::MAX as usize);
        let mut vm = VM {
            jit: jit::Jit::new(Machine, target, 1 << 20), // FIXME: Auto-grow code.
            state: AllRegisters::default(),
            memory: (0..memory_cells).map(|_| 0).collect(),
            free_cells: memory_cells as u32,
            halt_addr: 0,
        };
        // Allocate the data stack.
        let s_base = vm.allocate(data_cells as u32);
        let sp = s_base + cell_bytes(data_cells as i64) as u32;
        vm.registers_mut().s0 = sp;
        vm.registers_mut().sp = sp;
        // Allocate the return stack.
        let r_base = vm.allocate(return_cells as u32);
        let rp = r_base + cell_bytes(return_cells as i64) as u32;
        vm.registers_mut().r0 = rp;
        vm.registers_mut().rp = rp;
        // Allocate a word to hold a HALT instruction.
        vm.halt_addr = vm.allocate(1);
        vm.store(vm.halt_addr, 0x5F);
        vm
    }

    /** Read the public registers. */
    pub fn registers(&self) -> &Registers { &self.state.public }

    /** Read or write the public registers. */
    pub fn registers_mut(&mut self) -> &mut Registers { &mut self.state.public }

    /**
     * Allocate `cells` cells and return a Beetle pointer to them.
     * Allocation starts at the top of memory and is permanent.
     */
    pub fn allocate(&mut self, cells: u32) -> u32 {
        assert!(cells <= self.free_cells);
        self.free_cells -= cells;
        cell_bytes(i64::from(self.free_cells)) as u32
    }

    /**
     * Load `object` at address zero, i.e. in the unallocated memory.
     */
    pub fn load_object(&mut self, object: &[u32]) {
        assert!(object.len() <= self.free_cells as usize);
        for (i, &cell) in object.iter().enumerate() {
            self.memory[i] = cell;
        }
    }

    /** Return the value of the word at address `addr`. */
    pub fn load(&self, addr: u32) -> u32 {
        assert_eq!(addr & 0x3, 0);
        self.memory[(addr >> 2) as usize]
    }

    /** Set the word at address `addr` to `value`. */
    pub fn store(&mut self, addr: u32, value: u32) {
        assert_eq!(addr & 0x3, 0);
        self.memory[(addr >> 2) as usize] = value;
    }

    /** Push `item` onto the data stack. */
    pub fn push(&mut self, item: u32) {
        self.registers_mut().sp -= cell_bytes(1) as u32;
        self.store(self.registers().sp, item);
    }

    /** Pop an item from the data stack. */
    pub fn pop(&mut self) -> u32 {
        let item = self.load(self.registers().sp);
        self.registers_mut().sp += cell_bytes(1) as u32;
        item
    }

    /** Push `item` onto the return stack. */
    pub fn rpush(&mut self, item: u32) {
        self.registers_mut().rp -= cell_bytes(1) as u32;
        self.store(self.registers().rp, item);
    }

    /** Pop an item from the return stack. */
    pub fn rpop(&mut self) -> u32 {
        let item = self.load(self.registers().rp);
        self.registers_mut().rp += cell_bytes(1) as u32;
        item
    }

    /**
     * Run the code at address `ep`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`].
     */
    pub unsafe fn run(mut self, ep: u32) -> Self {
        assert!(Self::is_aligned(ep));
        self.registers_mut().ep = ep;
        self.state.memory = self.memory.as_mut_ptr() as u64;
        *self.jit.global(code::Global(0)) = &mut self.state as *mut AllRegisters as u64;
        let (jit, state) = self.jit.execute(&State::Root).expect("Execute failed");
        assert_eq!(state, State::Halt);
        self.jit = jit;
        self
    }

    /** Indicate whether an address is cell-aligned. */
    pub fn is_aligned(addr: u32) -> bool {
        addr & 0x3 == 0
    }
}

//-----------------------------------------------------------------------------

/* Register allocation. */

const TEMP: Register = REGISTERS[0];
const R1: Register = REGISTERS[1];
const R2: Register = REGISTERS[2];
const R3: Register = REGISTERS[3];
const R4: Register = REGISTERS[4];
const R5: Register = REGISTERS[5];

const BEP: Value = FAST_VALUES[6];
const BA: Value = FAST_VALUES[7];
const BSP: Value = FAST_VALUES[8];
const BRP: Value = FAST_VALUES[9];
const MEMORY: Value = FAST_VALUES[10];
const OPCODE: Value = FAST_VALUES[11];
const STACK0: Value = FAST_VALUES[12];
const STACK1: Value = FAST_VALUES[13];
const LOOP_FLAG: Value = FAST_VALUES[14];
const LOOP_STEP: Value = FAST_VALUES[15];
const LOOP_NEW: Value = FAST_VALUES[16];
const LOOP_OLD: Value = FAST_VALUES[17];

//-----------------------------------------------------------------------------

/** Beetle's address space is unified, so we always use the same `AliasMask`. */
const AM_MEMORY: code::AliasMask = code::AliasMask(0x1);

/** Beetle's registers are not in Beetle's memory, so we use a different `AliasMask`. */
const AM_REGISTER: code::AliasMask = code::AliasMask(0x2);

fn opcode(c: u8) -> TestOp { TestOp::Bits(OPCODE.into(), 0xFF, i32::from(c)) }
fn lt(v: impl IntoValue, c: i32) -> TestOp { TestOp::Lt(v.into(), c) }
fn ge(v: impl IntoValue, c: i32) -> TestOp { TestOp::Ge(v.into(), c) }
fn ult(v: impl IntoValue, c: i32) -> TestOp { TestOp::Ult(v.into(), c) }
fn uge(v: impl IntoValue, c: i32) -> TestOp { TestOp::Uge(v.into(), c) }
fn eq(v: impl IntoValue, c: i32) -> TestOp { TestOp::Eq(v.into(), c) }
fn ne(v: impl IntoValue, c: i32) -> TestOp { TestOp::Ne(v.into(), c) }

/** Build a case, in the form that `Beetle::get_code()` returns. */
fn build(
    test_op: TestOp,
    callback: impl FnOnce(&mut Builder),
    state: State,
) -> Case<State> {
    let mut b = Builder::new();
    callback(&mut b);
    Case {condition: (test_op, P32), actions: b.0, new_state: state}
}

/**
 * A utility for generating action routines.
 *
 * The methods correspond roughly to the cases of type Action. They fill in
 * Beetle-specific default parameters. `load()` and `store()` add code to map
 * Beetle addresses to native addresses. `push()` and `pop()` access Beetle
 * stacks (the native stack is not used).
 */
struct Builder(Vec<Action>);

impl Builder {
    fn new() -> Self {
        Builder(Vec::new())
    }

    fn move_(&mut self, dest: impl IntoValue, src: impl IntoValue) {
        if dest.into() != src.into() {
            self.0.push(Move(dest.into(), src.into()));
        }
    }

    fn const_(&mut self, dest: impl IntoValue, constant: i64) {
        self.0.push(Constant(P32, TEMP, constant));
        self.move_(dest, TEMP);
    }

    fn const64(&mut self, dest: impl IntoValue, constant: i64) {
        self.0.push(Constant(P64, TEMP, constant));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn unary(&mut self, op: UnaryOp, dest: impl IntoValue, src: impl IntoValue) {
        self.0.push(Unary(op, P32, TEMP, src.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src1` and `src2`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn binary(&mut self, op: BinaryOp, dest: impl IntoValue, src1: impl IntoValue, src2: impl IntoValue) {
        self.0.push(Binary(op, P32, TEMP, src1.into(), src2.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 64-bit `op` to `src1` and `src2`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn binary64(&mut self, op: BinaryOp, dest: impl IntoValue, src1: impl IntoValue, src2: impl IntoValue) {
        self.0.push(Binary(op, P64, TEMP, src1.into(), src2.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn const_binary(&mut self, op: BinaryOp, dest: impl IntoValue, src: impl IntoValue, constant: i64) {
        assert_ne!(src.into(), TEMP.into());
        self.const_(TEMP, constant);
        self.binary(op, dest, src, TEMP);
    }

    /**
     * Apply 64-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn const_binary64(&mut self, op: BinaryOp, dest: impl IntoValue, src: impl IntoValue, constant: i64) {
        assert_ne!(src.into(), TEMP.into());
        self.const64(TEMP, constant);
        self.binary64(op, dest, src, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`.
     * `TEMP` is corrupted.
     */
    fn native_address(&mut self, dest: impl IntoValue, addr: impl IntoValue) {
        self.binary64(Add, dest, MEMORY, addr);
    }

    /**
     * Compute the native address corresponding to `addr`, and load 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn load(&mut self, dest: impl IntoValue, addr: impl IntoValue) {
        self.native_address(TEMP, addr);
        self.0.push(Load(TEMP, (TEMP.into(), Four), AM_MEMORY));
        self.move_(dest, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`, and store 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn store(&mut self, src: impl IntoValue, addr: impl IntoValue) {
        assert_ne!(src.into(), TEMP.into());
        self.native_address(TEMP, addr);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_MEMORY));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn load_byte(&mut self, dest: impl IntoValue, addr: impl IntoValue) {
        self.native_address(TEMP, addr);
        self.0.push(Load(TEMP, (TEMP.into(), One), AM_MEMORY));
        self.move_(dest, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`, and store 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn store_byte(&mut self, src: impl IntoValue, addr: impl IntoValue) {
        assert_ne!(src.into(), TEMP.into());
        self.native_address(TEMP, addr);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), One), AM_MEMORY));
    }

    /**
     * Load 32 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn load_register(&mut self, dest: impl IntoValue, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as i64);
        self.0.push(Load(TEMP, (TEMP.into(), Four), AM_REGISTER));
        self.move_(dest, TEMP);
    }

    /**
     * Load 64 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn load_register64(&mut self, dest: impl IntoValue, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as i64);
        self.0.push(Load(TEMP, (TEMP.into(), Eight), AM_REGISTER));
        self.move_(dest, TEMP);
    }

    /**
     * Store 32 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn store_register(&mut self, src: impl IntoValue, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as i64);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_REGISTER));
    }

    /**
     * Store 64 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn store_register64(&mut self, src: impl IntoValue, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as i64);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Eight), AM_REGISTER));
    }

    /**
     * `load()` `dest` from `addr`, then increment `addr`.
     * `TEMP` is corrupted.
     */
    fn pop(&mut self, dest: impl IntoValue, addr: impl IntoValue) {
        assert_ne!(dest.into(), addr.into());
        assert_ne!(dest.into(), TEMP.into());
        self.load(dest, addr);
        self.const_binary(Add, TEMP, addr, cell_bytes(1));
        self.move_(addr, TEMP);
    }

    /**
     * Decrement `addr` by `cell_bytes(1)`, then `store()` `src` at `addr`.
     * `TEMP` is corrupted.
     */
    fn push(&mut self, src: impl IntoValue, addr: impl IntoValue) {
        assert_ne!(src.into(), TEMP.into());
        assert_ne!(src.into(), addr.into());
        self.const_binary(Sub, TEMP, addr, cell_bytes(1));
        self.move_(addr, TEMP);
        self.store(src, TEMP);
    }

    #[allow(dead_code)]
    fn debug(&mut self, x: impl IntoValue) {
        self.0.push(Debug(x.into()));
    }
}

//-----------------------------------------------------------------------------

/** Returns an [`Action`] that computes the address of `field`. */
macro_rules! private_register {
    ($field: ident) => {
        offset_of!(AllRegisters, $field)
    }
}

/** Returns an [`Action`] that computes the address of `field`. */
macro_rules! public_register {
    ($field: ident) => {
        offset_of!(AllRegisters, public) + offset_of!(Registers, $field)
    }
}

#[derive(Debug)]
pub struct Machine;

impl code::Machine for Machine {
    type State = State;

    fn num_globals(&self) -> usize { 1 }

    fn num_slots(&self) -> usize { 6 }

    fn liveness_mask(&self, state: Self::State) -> u64 {
        let ep = 1 << 6;
        let a = 1 << 7;
        let sp = 1 << 8;
        let rp = 1 << 9;
        let memory = 1 << 10;
        let opcode = 1 << 11;
        let stack0 = 1 << 12;
        let stack1 = 1 << 13;
        let loop_flag = 1 << 14;
        let loop_step = 1 << 15;
        let loop_new = 1 << 16;
        let loop_old = 1 << 17;
        #[allow(clippy::match_same_arms)]
        let ret = (ep | sp | rp | memory) | match state {
            State::Root => a,
            State::Next => 0,
            State::Pick => a | stack0,
            State::Roll => a | stack0,
            State::Qdup => a | stack0,
            State::Lshift => a | stack0 | stack1,
            State::Rshift => a | stack0 | stack1,
            State::Branch => 0,
            State::Branchi => a,
            State::Qbranch => a | stack0,
            State::Qbranchi => a | stack0,
            State::Loop => a | loop_flag,
            State::Loopi => a | loop_flag,
            State::Ploopp => a | loop_flag,
            State::Ploopm => a | loop_flag,
            State::Ploop => a | loop_step | loop_new | loop_old,
            State::Ploopip => a | loop_flag,
            State::Ploopim => a | loop_flag,
            State::Ploopi => a | loop_step | loop_new | loop_old,
            State::Halt => a,
            State::Dispatch => a | opcode,
        };
        ret
    }

    fn prologue(&self) -> Vec<Action> {
        let mut b = Builder::new();
        b.load_register(BEP, public_register!(ep));
        b.load_register(BA, public_register!(a));
        b.load_register(BSP, public_register!(sp));
        b.load_register(BRP, public_register!(rp));
        b.load_register64(MEMORY, private_register!(memory));
        b.load_register(OPCODE, private_register!(opcode));
        b.load_register(STACK0, private_register!(stack0));
        b.load_register(STACK1, private_register!(stack1));
        b.load_register(LOOP_FLAG, private_register!(loop_flag));
        b.load_register(LOOP_STEP, private_register!(loop_step));
        b.load_register(LOOP_NEW, private_register!(loop_new));
        b.load_register(LOOP_OLD, private_register!(loop_old));
        b.0
    }

    fn epilogue(&self) -> Vec<Action> {
        let mut b = Builder::new();
        b.store_register(BEP, public_register!(ep));
        b.store_register(BA, public_register!(a));
        b.store_register(BSP, public_register!(sp));
        b.store_register(BRP, public_register!(rp));
        b.store_register64(MEMORY, private_register!(memory));
        b.store_register(OPCODE, private_register!(opcode));
        b.store_register(STACK0, private_register!(stack0));
        b.store_register(STACK1, private_register!(stack1));
        b.store_register(LOOP_FLAG, private_register!(loop_flag));
        b.store_register(LOOP_STEP, private_register!(loop_step));
        b.store_register(LOOP_NEW, private_register!(loop_new));
        b.store_register(LOOP_OLD, private_register!(loop_old));
        b.0
    }

    #[allow(clippy::too_many_lines)]
    fn code(&self, state: Self::State) -> Vec<Case<Self::State>> {
        match state {
            State::Root => vec![
                build(TestOp::Always, |b| {
                    b.move_(OPCODE, BA);
                    b.const_binary(Asr, BA, BA, 8);
                }, State::Dispatch),
            ],
            State::Next => vec![
                build(TestOp::Always, |b| {
                    b.pop(BA, BEP);
                }, State::Root),
            ],
            State::Pick => {
                let mut pick = Vec::new();
                for u in 0..4 {
                    pick.push(build(eq(STACK0, u), |b| {
                        b.const_binary(Add, R2, BSP, cell_bytes(i64::from(u) + 1));
                        b.load(R2, R2);
                        b.store(R2, BSP);
                    }, State::Root));
                }
                pick
            },
            State::Roll => {
                let mut roll = Vec::new();
                for u in 0..4 {
                    roll.push(build(eq(STACK0, u as i32), |b| {
                        b.const_binary(Add, R5, BSP, cell_bytes(u));
                        b.load(R3, R5);
                        for v in 0..u {
                            b.const_binary(Add, R4, BSP, cell_bytes(v));
                            b.load(R2, R4);
                            b.store(R3, R4);
                            b.move_(R3, R2);
                        }
                        b.store(R3, R5);
                    }, State::Root));
                }
                roll
            },
            State::Qdup => vec![
                build(eq(STACK0, 0), |_| {}, State::Root),
                build(ne(STACK0, 0), |b| {
                    b.push(STACK0, BSP);
                }, State::Root),
            ],
            State::Lshift => vec![
                build(ult(STACK1, CELL_BITS as i32), |b| {
                    b.binary(Lsl, R2, STACK0, STACK1);
                    b.store(R2, BSP);
                }, State::Root),
                build(uge(STACK1, CELL_BITS as i32), |b| {
                    b.const_(R2, 0);
                    b.store(R2, BSP);
                }, State::Root),
            ],
            State::Rshift => vec![
                build(ult(STACK1, CELL_BITS as i32), |b| {
                    b.binary(Lsr, R2, STACK0, STACK1);
                    b.store(R2, BSP);
                }, State::Root),
                build(uge(STACK1, CELL_BITS as i32), |b| {
                    b.const_(R2, 0);
                    b.store(R2, BSP);
                }, State::Root),
            ],
            State::Branch => vec![
                build(TestOp::Always, |b| {
                    // Load EP from the cell it points to.
                    b.load(BEP, BEP); // FIXME: Add check that EP is valid.
                }, State::Next),
            ],
            State::Branchi => vec![
                build(TestOp::Always, |b| {
                    b.const_binary(Mul, R2, BA, cell_bytes(1));
                    b.binary(Add, BEP, BEP, R2); // FIXME: Add check that EP is valid.
                }, State::Next),
            ],
            State::Qbranch => vec![
                build(eq(STACK0, 0), |_| {}, State::Branch),
                build(ne(STACK0, 0), |b| {
                    b.const_binary(Add, BEP, BEP, cell_bytes(1));
                }, State::Root),
            ],
            State::Qbranchi => vec![
                build(eq(STACK0, 0), |_| {}, State::Branchi),
                build(ne(STACK0, 0), |_| {}, State::Next),
            ],
            State::Loop => vec![
                build(eq(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, State::Root),
                build(ne(LOOP_FLAG, 0), |_| {}, State::Branch),
            ],
            State::Loopi => vec![
                build(eq(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                }, State::Next),
                build(ne(LOOP_FLAG, 0), |_| {}, State::Branchi),
            ],
            State::Ploopp => vec![ // TODO: Seems to be identical with Ploopm?
                build(lt(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, State::Root),
                build(ge(LOOP_FLAG, 0), |_| {}, State::Branch),
            ],
            State::Ploopm => vec![
                build(lt(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, State::Root),
                build(ge(LOOP_FLAG, 0), |_| {}, State::Branch),
            ],
            State::Ploop => vec![
                build(ge(LOOP_STEP, 0), |b| {
                    b.unary(Not, LOOP_NEW, LOOP_NEW);
                    b.binary(And, LOOP_FLAG, LOOP_NEW, LOOP_OLD);
                }, State::Ploopp),
                build(lt(LOOP_STEP, 0), |b| {
                    b.unary(Not, LOOP_OLD, LOOP_OLD);
                    b.binary(And, LOOP_FLAG, LOOP_NEW, LOOP_OLD);
                }, State::Ploopm),
            ],
            State::Ploopip => vec![ // TODO: Seems to be identical with Ploopim?
                build(lt(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                }, State::Root),
                build(ge(LOOP_FLAG, 0), |_| {}, State::Branchi),
            ],
            State::Ploopim => vec![
                build(lt(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                }, State::Root),
                build(ge(LOOP_FLAG, 0), |_| {}, State::Branchi),
            ],
            State::Ploopi => vec![
                build(ge(LOOP_STEP, 0), |b| {
                    b.unary(Not, LOOP_NEW, LOOP_NEW);
                    b.binary(And, LOOP_FLAG, LOOP_NEW, LOOP_OLD);
                }, State::Ploopip),
                build(lt(LOOP_STEP, 0), |b| {
                    b.unary(Not, LOOP_OLD, LOOP_OLD);
                    b.binary(And, LOOP_FLAG, LOOP_NEW, LOOP_OLD);
                }, State::Ploopim),
            ],
            State::Halt => vec![],
            State::Dispatch => vec![
                // NEXT
                build(opcode(0x00), |_| {}, State::Next),

                // DUP
                build(opcode(0x01), |b| {
                    b.load(R2, BSP);
                    b.push(R2, BSP);
                }, State::Root),

                // DROP
                build(opcode(0x02), |b| {
                    b.const_binary(Add, BSP, BSP, cell_bytes(1));
                }, State::Root),

                // SWAP
                build(opcode(0x03), |b| {
                    b.pop(R4, BSP);
                    b.load(R3, BSP);
                    b.store(R4, BSP);
                    b.push(R3, BSP);
                }, State::Root),

                // OVER
                build(opcode(0x04), |b| {
                    b.const_binary(Add, R2, BSP, cell_bytes(1));
                    b.load(R3, R2);
                    b.push(R3, BSP);
                }, State::Root),

                // ROT
                build(opcode(0x05), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R5, BSP, cell_bytes(1));
                    b.load(R3, R5);
                    b.store(R2, R5);
                    b.const_binary(Add, R5, BSP, cell_bytes(2));
                    b.load(R2, R5);
                    b.store(R3, R5);
                    b.store(R2, BSP);
                }, State::Root),

                // -ROT
                build(opcode(0x06), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R5, BSP, cell_bytes(2));
                    b.load(R3, R5);
                    b.store(R2, R5);
                    b.const_binary(Add, R5, BSP, cell_bytes(1));
                    b.load(R2, R5);
                    b.store(R3, R5);
                    b.store(R2, BSP);
                }, State::Root),

                // TUCK
                build(opcode(0x07), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R5, BSP, cell_bytes(1));
                    b.load(R3, R5);
                    b.store(R2, R5);
                    b.store(R3, BSP);
                    b.push(R2, BSP);
                }, State::Root),

                // NIP
                build(opcode(0x08), |b| {
                    b.pop(R2, BSP);
                    b.store(R2, BSP);
                }, State::Root),

                // PICK
                build(opcode(0x09), |b| {
                    b.load(STACK0, BSP);
                }, State::Pick),

                // ROLL
                build(opcode(0x0a), |b| {
                    b.pop(STACK0, BSP);
                }, State::Roll),

                // ?DUP
                build(opcode(0x0b), |b| {
                    b.load(STACK0, BSP);
                }, State::Qdup),

                // >R
                build(opcode(0x0c), |b| {
                    b.pop(R2, BSP);
                    b.push(R2, BRP);
                }, State::Root),

                // R>
                build(opcode(0x0d), |b| {
                    b.pop(R2, BRP);
                    b.push(R2, BSP);
                }, State::Root),

                // R@
                build(opcode(0x0e), |b| {
                    b.load(R2, BRP);
                    b.push(R2, BSP);
                }, State::Root),

                // <
                build(opcode(0x0f), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Lt, R2, R4, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // >
                build(opcode(0x10), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Lt, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // =
                build(opcode(0x11), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Eq, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // <>
                build(opcode(0x12), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Eq, R2, R2, R4);
                    b.unary(Not, R2, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // 0<
                build(opcode(0x13), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Lt, R2, R2, 0);
                    b.store(R2, BSP);
                }, State::Root),

                // 0>
                build(opcode(0x14), |b| {
                    b.load(R2, BSP);
                    b.const_(R4, 0);
                    b.binary(Lt, R2, R4, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // 0=
                build(opcode(0x15), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Eq, R2, R2, 0);
                    b.store(R2, BSP);
                }, State::Root),

                // 0<>
                build(opcode(0x16), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Eq, R2, R2, 0);
                    b.unary(Not, R2, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // U<
                build(opcode(0x17), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Ult, R2, R4, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // U>
                build(opcode(0x18), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Ult, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // 0
                build(opcode(0x19), |b| {
                    b.const_(R4, 0);
                    b.push(R4, BSP);
                }, State::Root),

                // 1
                build(opcode(0x1a), |b| {
                    b.const_(R4, 1);
                    b.push(R4, BSP);
                }, State::Root),

                // -1
                build(opcode(0x1b), |b| {
                    b.const_(R4, -1);
                    b.push(R4, BSP);
                }, State::Root),

                // CELL
                build(opcode(0x1c), |b| {
                    b.const_(R4, cell_bytes(1));
                    b.push(R4, BSP);
                }, State::Root),

                // -CELL
                build(opcode(0x1d), |b| {
                    b.const_(R4, (-Wrapping(cell_bytes(1))).0);
                    b.push(R4, BSP);
                }, State::Root),

                // +
                build(opcode(0x1e), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Add, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // -
                build(opcode(0x1f), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Sub, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // >-<
                build(opcode(0x20), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Sub, R2, R4, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // 1+
                build(opcode(0x21), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R2, R2, 1);
                    b.store(R2, BSP);
                }, State::Root),

                // 1-
                build(opcode(0x22), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Sub, R2, R2, 1);
                    b.store(R2, BSP);
                }, State::Root),

                // CELL+
                build(opcode(0x23), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R2, R2, cell_bytes(1));
                    b.store(R2, BSP);
                }, State::Root),

                // CELL-
                build(opcode(0x24), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Sub, R2, R2, cell_bytes(1));
                    b.store(R2, BSP);
                }, State::Root),

                // *
                build(opcode(0x25), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Mul, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                /* TODO:
                // /
                build(opcode(0x26), |_| {
                    // TODO
                }, State::Root),

                // MOD
                build(opcode(0x27), |_| {
                    // TODO
                }, State::Root),

                // /MOD
                build(opcode(0x28), |_| {
                    // TODO
                }, State::Root),

                // U/MOD
                build(opcode(0x29), |b| {
                    b.pop(R2, BSP);
                    b.load(R1, BSP);
                    b.0.push(Division(UnsignedDivMod, P32, R1, R2, R1, R2));
                    b.store(R2, BSP);
                    b.push(R1, BSP);
                }, State::Root),

                // S/REM
                build(opcode(0x2a), |b| {
                    b.pop(R2, BSP);
                    b.load(R1, BSP);
                    b.0.push(Division(SignedDivMod, P32, R1, R2, R1, R2));
                    b.store(R2, BSP);
                    b.push(R1, BSP);
                }, State::Root),
                */

                // 2/
                build(opcode(0x2b), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Asr, R2, R2, 1);
                    b.store(R2, BSP);
                }, State::Root),

                // CELLS
                build(opcode(0x2c), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Mul, R2, R2, cell_bytes(1));
                    b.store(R2, BSP);
                }, State::Root),

                // ABS
                build(opcode(0x2d), |b| {
                    b.load(R2, BSP);
                    b.unary(Abs, R2, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // NEGATE
                build(opcode(0x2e), |b| {
                    b.load(R2, BSP);
                    b.unary(Negate, R2, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // MAX
                build(opcode(0x2f), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Max, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // MIN
                build(opcode(0x30), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Min, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // INVERT
                build(opcode(0x31), |b| {
                    b.load(R2, BSP);
                    b.unary(Not, R2, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // AND
                build(opcode(0x32), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(And, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // OR
                build(opcode(0x33), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Or, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // XOR
                build(opcode(0x34), |b| {
                    b.pop(R2, BSP);
                    b.load(R4, BSP);
                    b.binary(Xor, R2, R2, R4);
                    b.store(R2, BSP);
                }, State::Root),

                // LSHIFT
                build(opcode(0x35), |b| {
                    b.pop(STACK0, BSP);
                    b.load(STACK1, BSP);
                }, State::Lshift),

                // RSHIFT
                build(opcode(0x36), |b| {
                    b.pop(STACK0, BSP);
                    b.load(STACK1, BSP);
                }, State::Rshift),

                // 1LSHIFT
                build(opcode(0x37), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Lsl, R2, R2, 1);
                    b.store(R2, BSP);
                }, State::Root),

                // 1RSHIFT
                build(opcode(0x38), |b| {
                    b.load(R2, BSP);
                    b.const_binary(Lsr, R2, R2, 1);
                    b.store(R2, BSP);
                }, State::Root),

                // @
                build(opcode(0x39), |b| {
                    b.load(R2, BSP);
                    b.load(R2, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // !
                build(opcode(0x3a), |b| {
                    b.pop(R2, BSP);
                    b.pop(R3, BSP);
                    b.store(R3, R2);
                }, State::Root),

                // C@
                build(opcode(0x3b), |b| {
                    b.load(R2, BSP);
                    b.load_byte(R2, R2);
                    b.store(R2, BSP);
                }, State::Root),

                // C!
                build(opcode(0x3c), |b| {
                    b.pop(R2, BSP);
                    b.pop(R3, BSP);
                    b.store_byte(R3, R2);
                }, State::Root),

                // +!
                build(opcode(0x3d), |b| {
                    b.pop(R2, BSP);
                    b.pop(R3, BSP);
                    b.load(R5, R2);
                    b.binary(Add, R3, R5, R3);
                    b.store(R3, R2);
                }, State::Root),

                // BSP@
                build(opcode(0x3e), |b| {
                    b.move_(R1, BSP);
                    b.push(R1, BSP);
                }, State::Root),

                // BSP!
                build(opcode(0x3f), |b| {
                    b.load(BSP, BSP);
                }, State::Root),

                // BRP@
                build(opcode(0x40), |b| {
                    b.push(BRP, BSP);
                }, State::Root),

                // BRP!
                build(opcode(0x41), |b| {
                    b.pop(BRP, BSP);
                }, State::Root),

                // EP@
                build(opcode(0x42), |b| {
                    b.push(BEP, BSP);
                }, State::Root),

                // BS0@
                build(opcode(0x43), |b| {
                    b.load_register(R1, public_register!(s0));
                    b.push(R1, BSP);
                }, State::Root),

                // BS0!
                build(opcode(0x44), |b| {
                    b.pop(R1, BSP);
                    b.store_register(R1, public_register!(s0));
                }, State::Root),

                // BR0@
                build(opcode(0x45), |b| {
                    b.load_register(R1, public_register!(r0));
                    b.push(R1, BSP);
                }, State::Root),

                // BR0!
                build(opcode(0x46), |b| {
                    b.pop(R1, BSP);
                    b.store_register(R1, public_register!(r0));
                }, State::Root),

                // 'THROW@
                build(opcode(0x47), |b| {
                    b.load_register(R1, public_register!(throw));
                    b.push(R1, BSP);
                }, State::Root),

                // 'THROW!
                build(opcode(0x48), |b| {
                    b.pop(R1, BSP);
                    b.store_register(R1, public_register!(throw));
                }, State::Root),

                // MEMORY@
                build(opcode(0x49), |b| {
                    b.load_register(R1, private_register!(memory));
                    b.push(R1, BSP);
                }, State::Root),

                // 'BAD@
                build(opcode(0x4a), |b| {
                    b.load_register(R1, public_register!(bad));
                    b.push(R1, BSP);
                }, State::Root),

                // -ADDRESS@
                build(opcode(0x4b), |b| {
                    b.load_register(R1, public_register!(not_address));
                    b.push(R1, BSP);
                }, State::Root),

                // BRANCH
                build(opcode(0x4c), |_| {}, State::Branch),

                // BRANCHI
                build(opcode(0x4d), |_| {}, State::Branchi),

                // ?BRANCH
                build(opcode(0x4e), |b| {
                    b.pop(STACK0, BSP);
                }, State::Qbranch),

                // ?BRANCHI
                build(opcode(0x4f), |b| {
                    b.pop(STACK0, BSP);
                }, State::Qbranchi),

                // EXECUTE
                build(opcode(0x50), |b| {
                    b.push(BEP, BRP);
                    b.pop(BEP, BSP); // FIXME: Add check that EP is valid.
                }, State::Next),

                // @EXECUTE
                build(opcode(0x51), |b| {
                    b.push(BEP, BRP);
                    b.pop(R1, BSP);
                    b.load(BEP, R1); // FIXME: Add check that EP is valid.
                }, State::Next),

                // CALL
                build(opcode(0x52), |b| {
                    b.const_binary(Add, R1, BEP, cell_bytes(1));
                    b.push(R1, BRP);
                }, State::Branch),

                // CALLI
                build(opcode(0x53), |b| {
                    b.push(BEP, BRP);
                }, State::Branchi),

                // EXIT
                build(opcode(0x54), |b| {
                    b.pop(BEP, BRP); // FIXME: Add check that EP is valid.
                }, State::Next),

                // (DO)
                build(opcode(0x55), |b| {
                    // Pop two items from SP.
                    b.pop(R4, BSP);
                    b.pop(R3, BSP);
                    // Push two items to RP.
                    b.push(R3, BRP);
                    b.push(R4, BRP);
                }, State::Root),

                // (LOOP)
                build(opcode(0x56), |b| {
                    // Load the index and limit from RP.
                    b.pop(R3, BRP);
                    b.load(R4, BRP);
                    // Update the index.
                    b.const_binary(Add, R3, R3, 1);
                    b.push(R3, BRP);
                    b.binary(Sub, LOOP_FLAG, R3, R4);
                }, State::Loop),

                // (LOOP)I
                build(opcode(0x57), |b| {
                    // Load the index and limit from RP.
                    b.pop(R3, BRP);
                    b.load(R4, BRP);
                    // Update the index.
                    b.const_binary(Add, R3, R3, 1);
                    b.push(R3, BRP);
                    b.binary(Sub, LOOP_FLAG, R3, R4);
                }, State::Loopi),

                // (+LOOP)
                build(opcode(0x58), |b| {
                    // Pop the step from SP.
                    b.pop(LOOP_STEP, BSP);
                    // Load the index and limit from RP.
                    b.pop(R3, BRP);
                    b.load(R4, BRP);
                    // Update the index.
                    b.binary(Add, R5, R3, LOOP_STEP);
                    b.push(R5, BRP);
                    // Compute the differences between old and new indexes and limit.
                    b.binary(Sub, LOOP_OLD, R3, R4);
                    b.binary(Sub, LOOP_NEW, R5, R4);
                }, State::Ploop),

                // (+LOOP)I
                build(opcode(0x59), |b| {
                    // Pop the step from SP.
                    b.pop(LOOP_STEP, BSP);
                    // Load the index and limit from RP.
                    b.pop(R3, BRP);
                    b.load(R4, BRP);
                    // Update the index.
                    b.binary(Add, R5, R3, LOOP_STEP);
                    b.push(R5, BRP);
                    // Compute the differences between old and new indexes and limit.
                    b.binary(Sub, LOOP_OLD, R3, R4);
                    b.binary(Sub, LOOP_NEW, R5, R4);
                }, State::Ploopi),

                // UNLOOP
                build(opcode(0x5a), |b| {
                    // Discard two items from RP.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                }, State::Root),

                // J
                build(opcode(0x5b), |b| {
                    // Push the third item of RP to SP.
                    b.const_binary(Add, R1, BRP, cell_bytes(2));
                    b.load(R4, R1);
                    b.push(R4, BSP);
                }, State::Root),

                // (LITERAL)
                build(opcode(0x5c), |b| {
                    // Load R2 from cell pointed to by BEP, and add 4 to EP.
                    b.pop(R2, BEP); // FIXME: Add check that EP is now valid.
                    b.push(R2, BSP);
                }, State::Root),

                // (LITERAL)I
                build(opcode(0x5d), |b| {
                    b.push(BA, BSP);
                }, State::Next),

                // THROW
                build(opcode(0x5e), |b| {
                    b.store_register(BEP, public_register!(bad));
                    b.load_register(BEP, public_register!(throw)); // FIXME: Add check that EP is valid.
                }, State::Next),

                // HALT
                build(opcode(0x5f), |_| {}, State::Halt),
            ],
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Root]
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    use super::super::target::{native};

    pub fn ackermann_object() -> Vec<u32> {
        // Forth source:
        // : ACKERMANN   ( m n -- result )
        // OVER 0= IF                  \ m = 0
        //     NIP 1+                  \ n+1
        // ELSE
        //     DUP 0= IF               \ n = 0
        //         DROP 1- 1 RECURSE   \ A(m-1, 1)
        //     ELSE
        //         OVER 1- -ROT        \ m-1 m n
        //         1- RECURSE          \ m-1 A(m, n-1)
        //         RECURSE             \ A(m-1, A(m, n-1))
        //     THEN
        // THEN ;

        // Beetle assembler:
        // $00: OVER
        //      0=
        // $04: ?BRANCHI $10
        // $08: NIP
        //      1+
        // $0C: BRANCHI $30
        // $10: DUP
        //      0=
        // $14: ?BRANCHI $24
        // $18: DROP
        //      1-
        //      1
        // $1C: CALLI $0
        // $20: BRANCHI $30
        // $24: OVER
        //      1-
        //      -ROT
        //      1-
        // $28: CALLI $0
        // $2C: CALLI $0
        // $30: EXIT

        // Beetle object code:
        vec![
            0x00001504, 0x0000024F, 0x00002108, 0x0000084D,
            0x00001501, 0x0000034F, 0x001A2202, 0xFFFFF853,
            0x0000034D, 0x22062204, 0xFFFFF553, 0xFFFFF453,
            0x00000054,
        ]
    }

    #[test]
    pub fn ackermann() {
        let mut vm = VM::new(native(), MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        vm.load_object(ackermann_object().as_ref());
        vm.push(3);
        vm.push(5);
        vm.rpush(vm.halt_addr);
        vm = unsafe { vm.run(0) };
        let result = vm.pop();
        assert_eq!(vm.registers().s0, vm.registers().sp);
        assert_eq!(vm.registers().r0, vm.registers().rp);
        assert_eq!(result, 253);
    }

    // TODO: Test (LOOP) instructions.
}
