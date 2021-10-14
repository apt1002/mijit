/*!
 * A partial implementation of the [Beetle] virtual machine in Mijit.
 * This serves as an illustrative example as an integration test.
 *
 * [Beetle]: https://github.com/rrthomas/beetle
 */

use memoffset::{offset_of};

use super::target::{Native, native, Word};
use super::{jit};
use super::code::{
    self, Switch, Precision, UnaryOp, BinaryOp, Width,
    Global, Register, Variable, REGISTERS,
    Action, Case, Convention, Marshal,
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
}

/** Beetle's registers, including those live in all `State`s. */
#[repr(C)]
#[derive(Default)]
struct AllRegisters {
    public: Registers,
    m0: u64,
    opcode: u32,
}

/** The number of bytes in a cell. */
pub const CELL: u32 = 4;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {
    Root,
    Dispatch,
    Next,
    Branchi,
    Qbranchi,
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

pub struct VM {
    /** The compiled code, registers, and other compiler state. */
    jit: jit::Jit<Machine, Native>,
    /** The Beetle state (other than the memory). */
    state: AllRegisters,
    /** The Beetle memory. */
    memory: Vec<u32>,
    /** The amount of unallocated memory, in cells. */
    free_cells: u32,
    /** The address of a HALT instruction. */
    halt_addr: u32,
}

impl VM {
    /**
     * Constructs a Beetle virtual machine with the specified parameters.
     *
     * The memory is `memory_cells` cells. The data stack occupies the last
     * `data_cells` cells of the memory, and the return stack occupies
     * the last `return_cells` cells before that. The cells before that
     * are free for the program's use.
     */
    pub fn new(
        memory_cells: u32,
        data_cells: u32,
        return_cells: u32,
    ) -> Self {
        let mut vm = VM {
            jit: jit::Jit::new(&Machine, native()),
            state: AllRegisters::default(),
            memory: vec![0; memory_cells as usize],
            free_cells: memory_cells,
            halt_addr: 0,
        };
        // Allocate the data stack.
        let sp = vm.allocate(data_cells).1;
        vm.registers_mut().sp = sp;
        // Allocate the return stack.
        let rp = vm.allocate(return_cells).1;
        vm.registers_mut().rp = rp;
        // Allocate a word to hold a HALT instruction.
        vm.halt_addr = vm.allocate(1).0;
        vm.store(vm.halt_addr, 0x55);
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
        let end = self.free_cells.checked_mul(CELL)
            .expect("Address out of range");
        self.free_cells = self.free_cells.checked_sub(cells)
            .expect("Out of memory");
        let start = self.free_cells.checked_mul(CELL)
            .expect("Address out of range");
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
        self.registers_mut().sp -= CELL;
        self.store(self.registers().sp, item);
    }

    /** Pop an item from the data stack. */
    pub fn pop(&mut self) -> u32 {
        let item = self.load(self.registers().sp);
        self.registers_mut().sp += CELL;
        item
    }

    /** Push `item` onto the return stack. */
    pub fn rpush(&mut self, item: u32) {
        self.registers_mut().rp -= CELL;
        self.store(self.registers().rp, item);
    }

    /** Pop an item from the return stack. */
    pub fn rpop(&mut self) -> u32 {
        let item = self.load(self.registers().rp);
        self.registers_mut().rp += CELL;
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
        self.state.m0 = self.memory.as_mut_ptr() as u64;
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
const BEP: Register = REGISTERS[4];
const BA: Register = REGISTERS[5];
const BSP: Register = REGISTERS[6];
const BRP: Register = REGISTERS[7];
const M0: Register = REGISTERS[8];
const OPCODE: Register = REGISTERS[9];

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

    fn const_(&mut self, dest: Register, constant: u32) {
        self.0.push(Constant(P32, dest, constant as i64));
    }

    fn const64(&mut self, dest: Register, constant: u64) {
        self.0.push(Constant(P64, dest, constant as i64));
    }

    /** Apply 32-bit `op` to `src`, writing `dest`. */
    fn unary(&mut self, op: UnaryOp, dest: Register, src: Register) {
        self.0.push(Unary(op, P32, dest, src.into()));
    }

    /** Apply 32-bit `op` to `src1` and `src2`, writing `dest`. */
    fn binary(&mut self, op: BinaryOp, dest: Register, src1: Register, src2: Register) {
        self.0.push(Binary(op, P32, dest, src1.into(), src2.into()));
    }

    /**
     * Apply 32-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn const_binary(&mut self, op: BinaryOp, dest: Register, src: Register, constant: u32) {
        assert_ne!(src, TEMP);
        self.const_(TEMP, constant);
        self.binary(op, dest, src, TEMP);
    }

    /** Compute the native address corresponding to `addr`. */
    pub fn native_address(&mut self, dest: Register, addr: Register) {
        self.0.push(Binary(Add, P64, dest, M0.into(), addr.into()));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 32 bits.
     */
    fn load(&mut self, dest: Register, addr: Register) {
        self.native_address(dest, addr);
        self.0.push(Load(dest, (dest.into(), Four), AM_MEMORY));
    }

    /**
     * Compute the native address corresponding to `addr`, and store 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn store(&mut self, src: Register, addr: Register) {
        assert_ne!(src, TEMP);
        self.native_address(TEMP, addr);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_MEMORY));
    }

    /** Compute the native address `Global(0) + offset`. */
    pub fn register_address(&mut self, dest: Register, offset: usize) {
        self.const64(dest, offset as u64);
        self.0.push(Binary(Add, P64, dest, Global(0).into(), dest.into()));
    }

    /**
     * Load 32 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn load_register(&mut self, dest: Register, offset: usize) {
        self.register_address(TEMP, offset);
        self.0.push(Load(dest, (TEMP.into(), Four), AM_REGISTER));
    }

    /**
     * Load 64 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn load_register64(&mut self, dest: Register, offset: usize) {
        self.register_address(TEMP, offset);
        self.0.push(Load(dest, (TEMP.into(), Eight), AM_REGISTER));
    }

    /**
     * Store 32 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn store_register(&mut self, src: Register, offset: usize) {
        self.register_address(TEMP, offset);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_REGISTER));
    }

    /**
     * Store 64 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    fn store_register64(&mut self, src: Register, offset: usize) {
        self.register_address(TEMP, offset);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Eight), AM_REGISTER));
    }

    /**
     * `load()` `dest` from `addr`, then increment `addr`.
     * `TEMP` is corrupted.
     */
    fn pop(&mut self, dest: Register, addr: Register) {
        assert_ne!(dest, addr);
        assert_ne!(dest, TEMP);
        self.load(dest, addr);
        self.const_binary(Add, addr, addr, CELL);
    }

    /**
     * Decrement `addr` by `CELL`, then `store()` `src` at `addr`.
     * `TEMP` is corrupted.
     */
    fn push(&mut self, src: Register, addr: Register) {
        assert_ne!(src, TEMP);
        assert_ne!(src, addr);
        self.const_binary(Sub, addr, addr, CELL);
        self.store(src, addr);
    }

    /** Returns all the [`Action`]s that this `Builder` has accumulated. */
    fn finish(self) -> Box<[Action]> {
        self.0.into()
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

    fn marshal(&self, state: Self::State) -> Marshal {
        let mut live_values = vec![Global(0).into(), BEP.into(), BSP.into(), BRP.into(), M0.into()];
        #[allow(clippy::match_same_arms)]
        live_values.extend(match state {
            State::Root => vec![BA],
            State::Next => vec![],
            State::Branchi => vec![BA],
            State::Qbranchi => vec![BA, OPCODE],
            State::Dispatch => vec![BA, OPCODE],
        }.into_iter().map(Variable::Register));
        let prologue = {
            let mut b = Builder::new();
            b.load_register(BEP, public_register!(ep));
            b.load_register(BA, public_register!(a));
            b.load_register(BSP, public_register!(sp));
            b.load_register(BRP, public_register!(rp));
            b.load_register64(M0, private_register!(m0));
            b.load_register(OPCODE, private_register!(opcode));
            b.finish()
        };
        let epilogue = {
            let mut b = Builder::new();
            for v in [BA, OPCODE] {
                if !live_values.contains(&v.into()) {
                    b.const64(v, 0xDEADDEADDEADDEADu64);
                }
            }
            b.store_register(BEP, public_register!(ep));
            b.store_register(BA, public_register!(a));
            b.store_register(BSP, public_register!(sp));
            b.store_register(BRP, public_register!(rp));
            b.store_register64(M0, private_register!(m0));
            b.store_register(OPCODE, private_register!(opcode));
            b.finish()
        };
        let convention = Convention {
            slots_used: 0,
            live_values: live_values.into(),
        };
        Marshal {prologue, convention, epilogue}
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
            State::Branchi => Switch::always(build(|b| {
                b.const_binary(Mul, R2, BA, CELL);
                b.binary(Add, BEP, BEP, R2); // FIXME: Add check that EP is valid.
            }, Ok(State::Next))),
            State::Qbranchi => Switch::if_(
                OPCODE.into(), // Top of stack.
                build(|_| {}, Ok(State::Next)),
                build(|_| {}, Ok(State::Branchi)),
            ),
            State::Dispatch => Switch::new(
                OPCODE.into(),
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
                        b.const_binary(Add, BSP, BSP, CELL);
                    }, Ok(State::Root)),

                    // SWAP
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.store(R2, BSP);
                        b.push(R3, BSP);
                    }, Ok(State::Root)),

                    // OVER
                    build(|b| {
                        b.const_binary(Add, R2, BSP, CELL);
                        b.load(R3, R2);
                        b.push(R3, BSP);
                    }, Ok(State::Root)),

                    // ROT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R3, R1);
                        b.store(R2, R1);
                        b.const_binary(Add, R1, BSP, 2 * CELL);
                        b.load(R2, R1);
                        b.store(R3, R1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -ROT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R1, BSP, 2 * CELL);
                        b.load(R3, R1);
                        b.store(R2, R1);
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R2, R1);
                        b.store(R3, R1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // TUCK
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R3, R1);
                        b.store(R2, R1);
                        b.store(R3, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // NIP
                    build(|b| {
                        b.pop(R2, BSP);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // PICK
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // ROLL
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // ?DUP
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // >R
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // R>
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // R@
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // <
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Lt, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Lt, R2, R2, R3);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // =
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Eq, R2, R2, R3);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // <>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Eq, R2, R2, R3);
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
                        b.const_(R3, 0);
                        b.binary(Lt, R2, R3, R2);
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
                        b.load(R3, BSP);
                        b.binary(Ult, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // U>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Ult, R2, R2, R3);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0
                    build(|b| {
                        b.const_(R2, 0);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // 1
                    build(|b| {
                        b.const_(R2, 1);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // -1
                    build(|b| {
                        b.const_(R2, !0);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // -CELL
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // +
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Add, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Sub, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >-<
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Sub, R2, R2, R3);
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
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // CELL-
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // *
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Mul, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // /
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // MOD
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // /MOD
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // U/MOD
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // S/REM
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // 2/
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // CELLS
                    build(|_| {}, Err(Trap::NotImplemented)),

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
                        b.load(R3, BSP);
                        b.binary(Max, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // MIN
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Min, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // INVERT
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // AND
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // OR
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // XOR
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // LSHIFT
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // RSHIFT
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // 1LSHIFT
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // 1RSHIFT
                    build(|_| {}, Err(Trap::NotImplemented)),

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
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // C!
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // +!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.load(R1, R2);
                        b.binary(Add, R3, R1, R3);
                        b.store(R3, R2);
                    }, Ok(State::Root)),

                    // SP@
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // SP!
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // RP@
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // RP!
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // BRANCH
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // BRANCHI
                    build(|_| {}, Ok(State::Branchi)),

                    // ?BRANCH
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // ?BRANCHI
                    build(|b| {
                        b.pop(OPCODE, BSP);
                    }, Ok(State::Qbranchi)),

                    // EXECUTE
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // @EXECUTE
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // CALL
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // CALLI
                    build(|b| {
                        b.push(BEP, BRP);
                    }, Ok(State::Branchi)),

                    // EXIT
                    build(|b| {
                        b.pop(BEP, BRP); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // (DO)
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // (LOOP)
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // (LOOP)I
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // (+LOOP)
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // (+LOOP)I
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // UNLOOP
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // J
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // (LITERAL)
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // (LITERAL)I
                    build(|b| {
                        b.push(BA, BSP);
                    }, Ok(State::Next)),

                    // THROW
                    build(|_| {}, Err(Trap::NotImplemented)),

                    // HALT
                    build(|_| {}, Err(Trap::Halt)),
                ]),
                build(|_| {}, Err(Trap::NotImplemented)),
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
            0x00001504, 0x00000245, 0x00002108, 0x00000843,
            0x00001501, 0x00000345, 0x001A2202, 0xFFFFF849,
            0x00000343, 0x22062204, 0xFFFFF549, 0xFFFFF449,
            0x0000004A,
        ]
    }

    #[test]
    pub fn halt() {
        let mut vm = VM::new(MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        let initial_sp = vm.registers().sp;
        let initial_rp = vm.registers().rp;
        let entry_address = vm.halt_addr;
        vm = unsafe { vm.run(entry_address) };
        assert_eq!(vm.registers().sp, initial_sp);
        assert_eq!(vm.registers().rp, initial_rp);
    }

    #[test]
    pub fn ackermann() {
        let mut vm = VM::new(MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        vm.load_object(ackermann_object().as_ref());
        let initial_sp = vm.registers().sp;
        let initial_rp = vm.registers().rp;
        vm.push(3);
        vm.push(5);
        vm.rpush(vm.halt_addr);
        vm = unsafe { vm.run(0) };
        let result = vm.pop();
        assert_eq!(vm.registers().sp, initial_sp);
        assert_eq!(vm.registers().rp, initial_rp);
        assert_eq!(result, 253);
    }

    // TODO: Test (LOOP) instructions.
}
