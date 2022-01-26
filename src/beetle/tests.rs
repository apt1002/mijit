use super::super::target::{Native, native};

use super::{Registers, CELL, Beetle};

/** The suggested size of the Beetle memory, in cells. */
pub const MEMORY_CELLS: u32 = 1 << 20;
/** The suggested size of the Beetle data stack, in cells. */
pub const DATA_CELLS: u32 = 1 << 18;
/** The suggested size of the Beetle return stack, in cells. */
pub const RETURN_CELLS: u32 = 1 << 18;

pub struct VM {
    /** The compiled code, registers, and other compiler state. */
    beetle: Option<super::Beetle<Native>>,
    /** The Beetle state (other than the memory). */
    state: Registers,
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
            beetle: Some(Beetle::new(native())),
            state: Registers::default(),
            memory: vec![0; memory_cells as usize],
            free_cells: memory_cells,
            halt_addr: 0,
        };
        // Allocate the return stack.
        let rp = vm.allocate(return_cells).1;
        vm.registers_mut().rp = rp;
        // Allocate the data stack.
        let sp = vm.allocate(data_cells).1;
        vm.registers_mut().sp = sp;
        // Allocate a word to hold a HALT instruction.
        vm.halt_addr = vm.allocate(1).0;
        vm.store(vm.halt_addr, 0x5519);
        vm
    }

    /** Read the public registers. */
    pub fn registers(&self) -> &Registers { &self.state }

    /** Read or write the public registers. */
    pub fn registers_mut(&mut self) -> &mut Registers { &mut self.state }

    /** Read the `M0` register. */
    pub fn memory(&self) -> &[u32] { &self.memory }

    /**
     * Allocate `cells` cells and return a (start, end) Beetle pointer pair.
     * Allocation starts at the top of memory and is permanent.
     */
    pub fn allocate(&mut self, cells: u32) -> (u32, u32) {
        assert!(cells <= self.free_cells);
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

    /** Run the code at address `ep`. If it `HALT`s, return the code. */
    pub unsafe fn run(&mut self, ep: u32) -> Option<u32> {
        assert!(Self::is_aligned(ep));
        self.registers_mut().ep = ep;
        let beetle = self.beetle.take().expect("Trying to call run() after error");
        let beetle = beetle.run(&mut self.state, self.memory.as_mut()).expect("Execute failed");
        self.beetle = Some(beetle);
        if self.registers_mut().a & 0xFF == 0x55 {
            // Halt.
            self.registers_mut().a >>= 8;
            Some(self.pop())
        } else {
            // Some other not implemented case.
            None
        }
    }

    /** Indicate whether an address is cell-aligned. */
    pub fn is_aligned(addr: u32) -> bool {
        addr & 0x3 == 0
    }
}

impl std::fmt::Debug for VM {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.debug_struct("VM")
            .field("state", &self.state)
            .field("m0", &format!("{:#x}", self.memory().as_ptr() as u64))
            .finish()
    }
}

//-----------------------------------------------------------------------------

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
    let exit = unsafe { vm.run(entry_address) };
    assert_eq!(exit, Some(0));
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
    let exit = unsafe { vm.run(0) };
    assert_eq!(exit, Some(0));
    let result = vm.pop();
    assert_eq!(vm.registers().sp, initial_sp);
    assert_eq!(vm.registers().rp, initial_rp);
    assert_eq!(result, 253);
}
