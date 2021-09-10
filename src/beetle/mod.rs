use std::convert::{TryFrom};
use std::num::{Wrapping};
use memoffset::{offset_of};

use super::target::{Target, Word};
use super::{jit};
use super::code::{
    self, Switch, Precision, UnaryOp, BinaryOp, Width,
    Global, Register, Variable, IntoVariable, REGISTERS, FAST_VARIABLES, Action, Case,
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
    PloopTest,
    Ploop,
    PloopiTest,
    Ploopi,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Trap {
    Halt,
    NotImplemented,
}

//-----------------------------------------------------------------------------

/** The suggested size of the Beetle memory, in cells. */
pub const MEMORY_CELLS: u32 = 1 << 20;
/** The suggested size of the Beetle data stack, in cells. */
pub const DATA_CELLS: u32 = 1 << 18;
/** The suggested size of the Beetle return stack, in cells. */
pub const RETURN_CELLS: u32 = 1 << 18;

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
        memory_cells: u32,
        data_cells: u32,
        return_cells: u32,
    ) -> Self {
        let mut vm = VM {
            jit: jit::Jit::new(&Machine, target),
            state: AllRegisters::default(),
            memory: vec![0; memory_cells as usize],
            free_cells: memory_cells,
            halt_addr: 0,
        };
        // Allocate the data stack.
        let sp = vm.allocate(data_cells).1;
        vm.registers_mut().s0 = sp;
        vm.registers_mut().sp = sp;
        // Allocate the return stack.
        let rp = vm.allocate(return_cells).1;
        vm.registers_mut().r0 = rp;
        vm.registers_mut().rp = rp;
        // Allocate a word to hold a HALT instruction.
        vm.halt_addr = vm.allocate(1).0;
        vm.store(vm.halt_addr, 0x5F);
        vm
    }

    /** Read the public registers. */
    pub fn registers(&self) -> &Registers { &self.state.public }

    /** Read or write the public registers. */
    pub fn registers_mut(&mut self) -> &mut Registers { &mut self.state.public }

    /**
     * Allocate `cells` cells and return a (start, end) Beetle pointer pair.
     * Allocation starts at the top of memory and is permanent.
     */
    pub fn allocate(&mut self, cells: u32) -> (u32, u32) {
        assert!(cells <= self.free_cells);
        let end = u32::try_from(
            cell_bytes(i64::from(self.free_cells))
        ).expect("Address out of range");
        self.free_cells -= cells;
        let start = u32::try_from(
            cell_bytes(i64::from(self.free_cells))
        ).expect("Address out of range");
        (start, end)
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
        *self.jit.global_mut(code::Global(0)) = Word {mp: (&mut self.state as *mut AllRegisters).cast()};
        let (jit, trap) = self.jit.execute(&State::Root).expect("Execute failed");
        assert_eq!(trap, Trap::Halt);
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

const BEP: Variable = FAST_VARIABLES[6];
const BA: Variable = FAST_VARIABLES[7];
const BSP: Variable = FAST_VARIABLES[8];
const BRP: Variable = FAST_VARIABLES[9];
const MEMORY: Variable = FAST_VARIABLES[10];
const OPCODE: Variable = FAST_VARIABLES[11];
const STACK0: Variable = FAST_VARIABLES[12];
const STACK1: Variable = FAST_VARIABLES[13];
const LOOP_NEW: Variable = FAST_VARIABLES[14];
const LOOP_OLD: Variable = FAST_VARIABLES[15];

//-----------------------------------------------------------------------------

/** Beetle's address space is unified, so we always use the same `AliasMask`. */
const AM_MEMORY: code::AliasMask = code::AliasMask(0x1);

/** Beetle's registers are not in Beetle's memory, so we use a different `AliasMask`. */
const AM_REGISTER: code::AliasMask = code::AliasMask(0x2);

/** Build a case, in the form that `Beetle::get_code()` returns. */
fn build(
    callback: impl FnOnce(&mut Builder),
    state_or_trap: Result<State, Trap>,
) -> Case<Result<State, Trap>> {
    let mut b = Builder::new();
    callback(&mut b);
    Case {actions: b.0, new_state: state_or_trap}
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

    fn move_(&mut self, dest: impl IntoVariable, src: impl IntoVariable) {
        if dest.into() != src.into() {
            self.0.push(Move(dest.into(), src.into()));
        }
    }

    fn const_(&mut self, dest: impl IntoVariable, constant: i64) {
        self.0.push(Constant(P32, TEMP, constant));
        self.move_(dest, TEMP);
    }

    fn const64(&mut self, dest: impl IntoVariable, constant: i64) {
        self.0.push(Constant(P64, TEMP, constant));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn unary(&mut self, op: UnaryOp, dest: impl IntoVariable, src: impl IntoVariable) {
        self.0.push(Unary(op, P32, TEMP, src.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src1` and `src2`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn binary(&mut self, op: BinaryOp, dest: impl IntoVariable, src1: impl IntoVariable, src2: impl IntoVariable) {
        self.0.push(Binary(op, P32, TEMP, src1.into(), src2.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 64-bit `op` to `src1` and `src2`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn binary64(&mut self, op: BinaryOp, dest: impl IntoVariable, src1: impl IntoVariable, src2: impl IntoVariable) {
        self.0.push(Binary(op, P64, TEMP, src1.into(), src2.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn const_binary(&mut self, op: BinaryOp, dest: impl IntoVariable, src: impl IntoVariable, constant: i64) {
        assert_ne!(src.into(), TEMP.into());
        self.const_(TEMP, constant);
        self.binary(op, dest, src, TEMP);
    }

    /**
     * Apply 64-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn const_binary64(&mut self, op: BinaryOp, dest: impl IntoVariable, src: impl IntoVariable, constant: i64) {
        assert_ne!(src.into(), TEMP.into());
        self.const64(TEMP, constant);
        self.binary64(op, dest, src, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`.
     * `TEMP` is corrupted.
     */
    fn native_address(&mut self, dest: impl IntoVariable, addr: impl IntoVariable) {
        self.binary64(Add, dest, MEMORY, addr);
    }

    /**
     * Compute the native address corresponding to `addr`, and load 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn load(&mut self, dest: impl IntoVariable, addr: impl IntoVariable) {
        self.native_address(TEMP, addr);
        self.0.push(Load(TEMP, (TEMP.into(), Four), AM_MEMORY));
        self.move_(dest, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`, and store 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn store(&mut self, src: impl IntoVariable, addr: impl IntoVariable) {
        assert_ne!(src.into(), TEMP.into());
        self.native_address(TEMP, addr);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_MEMORY));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn load_byte(&mut self, dest: impl IntoVariable, addr: impl IntoVariable) {
        self.native_address(TEMP, addr);
        self.0.push(Load(TEMP, (TEMP.into(), One), AM_MEMORY));
        self.move_(dest, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`, and store 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn store_byte(&mut self, src: impl IntoVariable, addr: impl IntoVariable) {
        assert_ne!(src.into(), TEMP.into());
        self.native_address(TEMP, addr);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), One), AM_MEMORY));
    }

    /**
     * Load 32 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn load_register(&mut self, dest: impl IntoVariable, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as i64);
        self.0.push(Load(TEMP, (TEMP.into(), Four), AM_REGISTER));
        self.move_(dest, TEMP);
    }

    /**
     * Load 64 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn load_register64(&mut self, dest: impl IntoVariable, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as i64);
        self.0.push(Load(TEMP, (TEMP.into(), Eight), AM_REGISTER));
        self.move_(dest, TEMP);
    }

    /**
     * Store 32 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn store_register(&mut self, src: impl IntoVariable, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as i64);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_REGISTER));
    }

    /**
     * Store 64 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn store_register64(&mut self, src: impl IntoVariable, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as i64);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Eight), AM_REGISTER));
    }

    /**
     * `load()` `dest` from `addr`, then increment `addr`.
     * `TEMP` is corrupted.
     */
    fn pop(&mut self, dest: impl IntoVariable, addr: impl IntoVariable) {
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
    fn push(&mut self, src: impl IntoVariable, addr: impl IntoVariable) {
        assert_ne!(src.into(), TEMP.into());
        assert_ne!(src.into(), addr.into());
        self.const_binary(Sub, TEMP, addr, cell_bytes(1));
        self.move_(addr, TEMP);
        self.store(src, TEMP);
    }

    #[allow(dead_code)]
    fn debug(&mut self, x: impl IntoVariable) {
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

    type Trap = Trap;

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
        let loop_new = 1 << 14;
        let loop_old = 1 << 15;
        #[allow(clippy::match_same_arms)]
        let ret = (ep | sp | rp | memory) | match state {
            State::Root => a,
            State::Next => 0,
            State::Pick => a | stack0,
            State::Roll => a | stack0,
            State::Qdup => a | stack0,
            State::Lshift => a | opcode | stack0 | stack1,
            State::Rshift => a | opcode | stack0 | stack1,
            State::Branch => 0,
            State::Branchi => a,
            State::Qbranch => a | stack0,
            State::Qbranchi => a | stack0,
            State::Loop => a | opcode,
            State::Loopi => a | opcode,
            State::PloopTest => a | opcode,
            State::Ploop => a | opcode | loop_new | loop_old,
            State::PloopiTest => a | opcode,
            State::Ploopi => a | opcode | loop_new | loop_old,
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
        b.store_register(LOOP_NEW, private_register!(loop_new));
        b.store_register(LOOP_OLD, private_register!(loop_old));
        b.0
    }

    #[allow(clippy::too_many_lines)]
    fn code(&self, state: Self::State) -> Switch<Case<Result<Self::State, Self::Trap>>> {
        match state {
            State::Root => Switch::always(build(|b| {
                b.const_binary(And, OPCODE, BA, 0xFF);
                b.const_binary(Asr, BA, BA, 8);
            }, Ok(State::Dispatch))),
            State::Next => Switch::always(build(|b| {
                b.pop(BA, BEP);
            }, Ok(State::Root))),
            State::Pick => Switch::new(
                STACK0,
                (0..4).map(|u| build(|b| {
                    b.const_binary(Add, R2, BSP, cell_bytes(i64::from(u) + 1));
                    b.load(R2, R2);
                    b.store(R2, BSP);
                }, Ok(State::Root))).collect(),
                build(|_| {}, Err(Trap::Halt)),
            ),
            State::Roll => Switch::new(
                STACK0,
                (0..4).map(|u| build(|b| {
                    b.const_binary(Add, R5, BSP, cell_bytes(u));
                    b.load(R3, R5);
                    for v in 0..u {
                        b.const_binary(Add, R4, BSP, cell_bytes(v));
                        b.load(R2, R4);
                        b.store(R3, R4);
                        b.move_(R3, R2);
                    }
                    b.store(R3, R5);
                }, Ok(State::Root))).collect(),
                build(|_| {}, Err(Trap::Halt)),
            ),
            State::Qdup => Switch::if_(
                STACK0,
                build(|b| {
                    b.push(STACK0, BSP);
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Root)),
            ),
            State::Lshift => Switch::if_(
                OPCODE, // `Ult(STACK0, CELL_BITS)`
                build(|b| {
                    b.binary(Lsl, R2, STACK0, STACK1);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
                build(|b| {
                    b.const_(R2, 0);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
            ),
            State::Rshift => Switch::if_(
                OPCODE, // `Ult(STACK0, CELL_BITS)`
                build(|b| {
                    b.binary(Lsr, R2, STACK0, STACK1);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
                build(|b| {
                    b.const_(R2, 0);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
            ),
            State::Branch => Switch::always(build(|b| {
                // Load EP from the cell it points to.
                b.load(BEP, BEP); // FIXME: Add check that EP is valid.
            }, Ok(State::Next))),
            State::Branchi => Switch::always(build(|b| {
                b.const_binary(Mul, R2, BA, cell_bytes(1));
                b.binary(Add, BEP, BEP, R2); // FIXME: Add check that EP is valid.
            }, Ok(State::Next))),
            State::Qbranch => Switch::if_(
                STACK0,
                build(|b| {
                    b.const_binary(Add, BEP, BEP, cell_bytes(1));
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branch)),
            ),
            State::Qbranchi => Switch::if_(
                STACK0,
                build(|_| {}, Ok(State::Next)),
                build(|_| {}, Ok(State::Branchi)),
            ),
            State::Loop => Switch::if_(
                OPCODE, // zero to exit the loop
                build(|_| {}, Ok(State::Branch)),
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, Ok(State::Root)),
            ),
            State::Loopi => Switch::if_(
                OPCODE, // zero to exit the loop
                build(|_| {}, Ok(State::Branchi)),
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                }, Ok(State::Next)),
            ),
            State::PloopTest => Switch::if_(
                OPCODE, // non-zero to exit the loop
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branch)),
            ),
            State::Ploop => Switch::if_(
                OPCODE, // Lt(step, 0)
                build(|b| {
                    b.unary(Not, LOOP_OLD, LOOP_OLD);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                    b.const_binary(Lt, OPCODE, LOOP_NEW, 0);
                }, Ok(State::PloopTest)),
                build(|b| {
                    b.unary(Not, LOOP_NEW, LOOP_NEW);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                    b.const_binary(Lt, OPCODE, LOOP_NEW, 0);
                }, Ok(State::PloopTest)),
            ),
            State::PloopiTest => Switch::if_(
                OPCODE, // non-zero to exit the loop
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branchi)),
            ),
            State::Ploopi => Switch::if_(
                OPCODE, // Lt(step, 0)
                build(|b| {
                    b.unary(Not, LOOP_OLD, LOOP_OLD);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                    b.const_binary(Lt, OPCODE, LOOP_NEW, 0);
                }, Ok(State::PloopiTest)),
                build(|b| {
                    b.unary(Not, LOOP_NEW, LOOP_NEW);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                    b.const_binary(Lt, OPCODE, LOOP_NEW, 0);
                }, Ok(State::PloopiTest)),
            ),
            State::Dispatch => Switch::new(
                OPCODE,
                Box::new([
                    // NEXT
                    build(|_| {}, Ok(State::Next)),

                    // DUP
                    build(|b| {
                        b.load(R2, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // DROP
                    build(|b| {
                        b.const_binary(Add, BSP, BSP, cell_bytes(1));
                    }, Ok(State::Root)),

                    // SWAP
                    build(|b| {
                        b.pop(R4, BSP);
                        b.load(R3, BSP);
                        b.store(R4, BSP);
                        b.push(R3, BSP);
                    }, Ok(State::Root)),

                    // OVER
                    build(|b| {
                        b.const_binary(Add, R2, BSP, cell_bytes(1));
                        b.load(R3, R2);
                        b.push(R3, BSP);
                    }, Ok(State::Root)),

                    // ROT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R5, BSP, cell_bytes(1));
                        b.load(R3, R5);
                        b.store(R2, R5);
                        b.const_binary(Add, R5, BSP, cell_bytes(2));
                        b.load(R2, R5);
                        b.store(R3, R5);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -ROT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R5, BSP, cell_bytes(2));
                        b.load(R3, R5);
                        b.store(R2, R5);
                        b.const_binary(Add, R5, BSP, cell_bytes(1));
                        b.load(R2, R5);
                        b.store(R3, R5);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // TUCK
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R5, BSP, cell_bytes(1));
                        b.load(R3, R5);
                        b.store(R2, R5);
                        b.store(R3, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // NIP
                    build(|b| {
                        b.pop(R2, BSP);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // PICK
                    build(|b| {
                        b.load(STACK0, BSP);
                    }, Ok(State::Pick)),

                    // ROLL
                    build(|b| {
                        b.pop(STACK0, BSP);
                    }, Ok(State::Roll)),

                    // ?DUP
                    build(|b| {
                        b.load(STACK0, BSP);
                    }, Ok(State::Qdup)),

                    // >R
                    build(|b| {
                        b.pop(R2, BSP);
                        b.push(R2, BRP);
                    }, Ok(State::Root)),

                    // R>
                    build(|b| {
                        b.pop(R2, BRP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // R@
                    build(|b| {
                        b.load(R2, BRP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // <
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Lt, R2, R4, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Lt, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // =
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Eq, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // <>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Eq, R2, R2, R4);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0<
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Lt, R2, R2, 0);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0>
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_(R4, 0);
                        b.binary(Lt, R2, R4, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0=
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Eq, R2, R2, 0);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0<>
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Eq, R2, R2, 0);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // U<
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Ult, R2, R4, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // U>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Ult, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0
                    build(|b| {
                        b.const_(R4, 0);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // 1
                    build(|b| {
                        b.const_(R4, 1);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // -1
                    build(|b| {
                        b.const_(R4, -1);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // CELL
                    build(|b| {
                        b.const_(R4, cell_bytes(1));
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // -CELL
                    build(|b| {
                        b.const_(R4, (-Wrapping(cell_bytes(1))).0);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // +
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Add, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Sub, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >-<
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Sub, R2, R4, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 1+
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 1-
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Sub, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL+
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R2, R2, cell_bytes(1));
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL-
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Sub, R2, R2, cell_bytes(1));
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // *
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Mul, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // /
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // MOD
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // /MOD
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // U/MOD
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // S/REM
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // 2/
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Asr, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELLS
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Mul, R2, R2, cell_bytes(1));
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // ABS
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Abs, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // NEGATE
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Negate, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // MAX
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Max, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // MIN
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Min, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // INVERT
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // AND
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(And, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // OR
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Or, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // XOR
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Xor, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // LSHIFT
                    build(|b| {
                        b.pop(STACK0, BSP);
                        b.load(STACK1, BSP);
                        b.const_binary(Ult, OPCODE, STACK1, CELL_BITS);
                    }, Ok(State::Lshift)),

                    // RSHIFT
                    build(|b| {
                        b.pop(STACK0, BSP);
                        b.load(STACK1, BSP);
                        b.const_binary(Ult, OPCODE, STACK1, CELL_BITS);
                    }, Ok(State::Rshift)),

                    // 1LSHIFT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Lsl, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 1RSHIFT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Lsr, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // @
                    build(|b| {
                        b.load(R2, BSP);
                        b.load(R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // !
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.store(R3, R2);
                    }, Ok(State::Root)),

                    // C@
                    build(|b| {
                        b.load(R2, BSP);
                        b.load_byte(R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // C!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.store_byte(R3, R2);
                    }, Ok(State::Root)),

                    // +!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.load(R5, R2);
                        b.binary(Add, R3, R5, R3);
                        b.store(R3, R2);
                    }, Ok(State::Root)),

                    // BSP@
                    build(|b| {
                        b.move_(R1, BSP);
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // BSP!
                    build(|b| {
                        b.load(BSP, BSP);
                    }, Ok(State::Root)),

                    // BRP@
                    build(|b| {
                        b.push(BRP, BSP);
                    }, Ok(State::Root)),

                    // BRP!
                    build(|b| {
                        b.pop(BRP, BSP);
                    }, Ok(State::Root)),

                    // EP@
                    build(|b| {
                        b.push(BEP, BSP);
                    }, Ok(State::Root)),

                    // BS0@
                    build(|b| {
                        b.load_register(R1, public_register!(s0));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // BS0!
                    build(|b| {
                        b.pop(R1, BSP);
                        b.store_register(R1, public_register!(s0));
                    }, Ok(State::Root)),

                    // BR0@
                    build(|b| {
                        b.load_register(R1, public_register!(r0));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // BR0!
                    build(|b| {
                        b.pop(R1, BSP);
                        b.store_register(R1, public_register!(r0));
                    }, Ok(State::Root)),

                    // 'THROW@
                    build(|b| {
                        b.load_register(R1, public_register!(throw));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // 'THROW!
                    build(|b| {
                        b.pop(R1, BSP);
                        b.store_register(R1, public_register!(throw));
                    }, Ok(State::Root)),

                    // MEMORY@
                    build(|b| {
                        b.load_register(R1, private_register!(memory));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // 'BAD@
                    build(|b| {
                        b.load_register(R1, public_register!(bad));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // -ADDRESS@
                    build(|b| {
                        b.load_register(R1, public_register!(not_address));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // BRANCH
                    build(|_| {}, Ok(State::Branch)),

                    // BRANCHI
                    build(|_| {}, Ok(State::Branchi)),

                    // ?BRANCH
                    build(|b| {
                        b.pop(STACK0, BSP);
                    }, Ok(State::Qbranch)),

                    // ?BRANCHI
                    build(|b| {
                        b.pop(STACK0, BSP);
                    }, Ok(State::Qbranchi)),

                    // EXECUTE
                    build(|b| {
                        b.push(BEP, BRP);
                        b.pop(BEP, BSP); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // @EXECUTE
                    build(|b| {
                        b.push(BEP, BRP);
                        b.pop(R1, BSP);
                        b.load(BEP, R1); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // CALL
                    build(|b| {
                        b.const_binary(Add, R1, BEP, cell_bytes(1));
                        b.push(R1, BRP);
                    }, Ok(State::Branch)),

                    // CALLI
                    build(|b| {
                        b.push(BEP, BRP);
                    }, Ok(State::Branchi)),

                    // EXIT
                    build(|b| {
                        b.pop(BEP, BRP); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // (DO)
                    build(|b| {
                        // Pop two items from SP.
                        b.pop(R4, BSP);
                        b.pop(R3, BSP);
                        // Push two items to RP.
                        b.push(R3, BRP);
                        b.push(R4, BRP);
                    }, Ok(State::Root)),

                    // (LOOP)
                    build(|b| {
                        // Load the index and limit from RP.
                        b.pop(R3, BRP);
                        b.load(R4, BRP);
                        // Update the index.
                        b.const_binary(Add, R3, R3, 1);
                        b.push(R3, BRP);
                        b.binary(Sub, OPCODE, R3, R4);
                    }, Ok(State::Loop)),

                    // (LOOP)I
                    build(|b| {
                        // Load the index and limit from RP.
                        b.pop(R3, BRP);
                        b.load(R4, BRP);
                        // Update the index.
                        b.const_binary(Add, R3, R3, 1);
                        b.push(R3, BRP);
                        b.binary(Sub, OPCODE, R3, R4);
                    }, Ok(State::Loopi)),

                    // (+LOOP)
                    build(|b| {
                        // Pop the step from SP.
                        b.pop(R1, BSP);
                        // Load the index and limit from RP.
                        b.pop(R3, BRP);
                        b.load(R4, BRP);
                        // Update the index.
                        b.binary(Add, R5, R3, R1);
                        b.push(R5, BRP);
                        // Compute the differences between old and new indexes and limit.
                        b.binary(Sub, LOOP_OLD, R3, R4);
                        b.binary(Sub, LOOP_NEW, R5, R4);
                        // Is the step negative?
                        b.const_binary(Lt, OPCODE, R1, 0);
                    }, Ok(State::Ploop)),

                    // (+LOOP)I
                    build(|b| {
                        // Pop the step from SP.
                        b.pop(R1, BSP);
                        // Load the index and limit from RP.
                        b.pop(R3, BRP);
                        b.load(R4, BRP);
                        // Update the index.
                        b.binary(Add, R5, R3, R1);
                        b.push(R5, BRP);
                        // Compute the differences between old and new indexes and limit.
                        b.binary(Sub, LOOP_OLD, R3, R4);
                        b.binary(Sub, LOOP_NEW, R5, R4);
                        // Is the step negative?
                        b.const_binary(Lt, OPCODE, R1, 0);
                    }, Ok(State::Ploopi)),

                    // UNLOOP
                    build(|b| {
                        // Discard two items from RP.
                        b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    }, Ok(State::Root)),

                    // J
                    build(|b| {
                        // Push the third item of RP to SP.
                        b.const_binary(Add, R1, BRP, cell_bytes(2));
                        b.load(R4, R1);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // (LITERAL)
                    build(|b| {
                        // Load R2 from cell pointed to by BEP, and add 4 to EP.
                        b.pop(R2, BEP); // FIXME: Add check that EP is now valid.
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // (LITERAL)I
                    build(|b| {
                        b.push(BA, BSP);
                    }, Ok(State::Next)),

                    // THROW
                    build(|b| {
                        b.store_register(BEP, public_register!(bad));
                        b.load_register(BEP, public_register!(throw)); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // HALT
                    build(|_| {}, Err(Trap::Halt)),
                ]),
                build(|_| {}, Err(Trap::Halt)),
            ),
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
    pub fn halt() {
        let mut vm = VM::new(native(), MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        let entry_address = vm.halt_addr;
        vm = unsafe { vm.run(entry_address) };
        assert_eq!(vm.registers().s0, vm.registers().sp);
        assert_eq!(vm.registers().r0, vm.registers().rp);
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
