# Goal

We want to generate AArch64 code directly into RAM, fast. We don't need to be
able to assemble any AArch64 instruction. I think a small and fairly regular
subset will suffice. This document chooses the subset and copies the necessary
data from reference manuals.


## Sources

 - [Overview](https://armkeil.blob.core.windows.net/developer/Files/pdf/graphics-and-multimedia/ARMv8_InstructionSetOverview.pdf)
 - [Decodings](https://github.com/CAS-Atlantic/AArch64-Encoding)
 - [Calling convention](https://github.com/ARM-software/abi-aa/blob/2bcab1e3b22d55170c563c3c7940134089176746/aapcs64/aapcs64.rst)
 - [ARM's documentation](https://documentation-service.arm.com/static/60119835773bb020e3de6fee) (8538 pages!) including:
   - General concepts (section C1: The A64 Instruction Set)
   - Overview (section C3: Instruction Set Overview)
   - Decoding (section C4: Instruction Set Encoding)
   - Encodings (section C6.2: Alphabetical list of A64 base instructions)


## Compatibility

The basic ARMv8-A instruction set is supported by all AArch64 CPU cores, of
which the first were the Cortex A53 and A57 (2012) and the Apple A7 (2013).

### Calling conventions

It seems that everybody uses the ARM Procedure Call Standard (APCS). There are slight variations, most of which are irrelevant. Details are in the section on call instructions.

### Vector extensions

We won't have a requirement to vectorise loops for quite some time, but vector
registers might be useful for copying bits of memory around and possibly as
spill slots.

Although SVE is the future of ARM vector instructions, Neon is the right choice
at the moment. It is a standard part of ARMv8-A and implemented ubiquitously.

### CPU differences

TODO

### Obsolete

TODO



# Encoding concepts

ARMv8 instructions are always 32 bits long. It is an error to jump to an address that is not 4-byte aligned.

Generally, 32 bits is too much for a RISC instruction. The available bits have generally been filled by adding features to instructions (making them more CISC) and then using the remaining (roughly) 5 to 12 bits for an immediate constant of some sort.


## Large immediates

Some instructions ideally require large immediate constants that don't easily fit in 32 bits. For example (ARMv8 limits in brackets):

 - Jumps and calls (±128MB).
 - Conditional branches (±1MB).
 - Accessing global variables in shared libraries (±1MB).
 - Put a constant in a register (±2¹⁶ usually).
 - Offsets in large structs (+2¹⁵ for 8-byte access).

Although instructions exist to construct a large constant from smaller pieces, it is generally not efficient to do so. The preferred method is to use a short PC-relative load to fetch a 64-bit constant from memory into a register, which can then be used by the following instruction. For this purpose it is necessary to reserve some memory every 2MB or so, to hold all the constants required in the intervening 2MB of code.


## Word sizes

Words (ARM calls them "double words") are 64 bits long, and little-endian. Integer registers hold 64-bit values (enough for a pointer). Integer registers can be used to hold 32-bit values by zero-padding them; the instruction set has extensive support for zero- and sign-extending values cheaply.

The most efficient unit of memory access is 16 bytes, 16-byte-aligned. It is possible to load and store 1, 2, 4 or 8 bytes at a time, and values loaded from memory can be sign-extended for free. It is efficient to access aligned memory addresses (i.e. addresses that are a multiple of the number of bytes transferred) but I don't think it is a requirement.


## Registers

There are 31 general-purpose 64-bit integer registers, named `R0` to `R30`. ARM calls these `W0` to `W30` when they are used to hold a 32-bit value and `X0` to `X30` when they are used to hold a 64-bit value, but I won't.

There is a zero register `ZR`. Reads from `ZR` always read zero, and writes to `ZR` have no effect.

There is a 64-bit stack pointer `SP`.

The bit pattern `0b11111`, which one might expect to mean `R31`, is used in some contexts to represent the stack pointer `SP`, and in others to represent the zero register `ZR`. It is necessary to know, for each register in every instruction, which interpretation is correct. Generally speaking, any operand or result that could plausibly be a memory address interprets `0b11111` as `SP`, whereas any operand that is small or could plausibly be an array index interprets it as `ZR`.

There are 32 128-bit vector registers `V0` to `V31`, used for vector operations and also for floating-point operations.

There is a 64-bit program counter `PC` which is not encodable as a register. It can only be written by branch (`B`) instructions (and by exceptions). Various instructions can read it, including PC-relative address calculations (`ADR`), PC-relative loads and stores, and subroutine calls (`BL`).

There is a status register. For our purposes, the only part of its contents that is relevant are the condition flags `N`, `C`, `V` and `Z`. They are written mainly by variants of arithmetic instructions that end in "S", e.g. `ANDS`, `SUBS` and `ANDS`. They are tested mainly by instructions that include a condition code (see below).

### Link register

Register `R30` (also called the "link register" `LR`) is written by subroutine calls (`BL`). The value written is the address that the subroutine should return to. In all other respects, `R30` is a general-purpose register.


## Condition codes

There are fifteen condition codes, organised as 7 pairs (a condition and its inverse) plus the true condition `AL`:

```
Bits    Asm Meaning     Interpretation after `SUBS`
0000    EQ  Z=1         Equal (result is zero)
0001    NE
0010    CS  C=1         Carry (no borrow)
0011    CC
0100    MI  N=1         Minus (result is negative)
0101    PL
0110    VS  V=1         Overflow (signed result too large)
0111    VC
1000    HI  C=1 & Z=0   Higher (unsigned result >0)
1001    LS
1010    GE  N=V         Greater or equal (signed result >=0)
1011    LT
1100    GT  N=V & Z=0   Greater than (signed result >0)
1101    LE
1110    AL  true        Always
```


## Register size flag

Most instructions have two variants, distinguished by bit `sf` (usually bit 31) of the instruction word. One variant operates on 32-bit values and the other operates on 64-bit values. The 32-bit variant ignores the upper 32 bits of source registers and sets the upper 32 bits of the destination register to zero.

There are a few other differences, most of which are obvious:

 - 32-bit right shifts behave as if the upper 32 bits are not present.
 - 32-bit rotations behave as if the upper 32 bits are not present.
 - 32-bit instructions that set the condition flags do so based on the lower 32 bits.

In addition to the register size flag, some 64-bit instructions have the ability to zero-extend (`UXT`) or sign-extend (`SXT`) one of their operands from 32 bits to 64 bits before combining it with the other (64-bit) operand.


# Recommended instructions


## Load and store

PC-relative.
Register plus scaled constant.
Register plus scaled register.

We mostly don't need the pair versions and the pre- and post-indexed versions, except to implement Push and Pop.


## Move

Move register to register (including constant shifts and extensions).
Move constant to register (consider ORR constant with ZR; consider PC-relative load).


## Arithmetic

ADD, SUB, ADDS, SUBS, each with immediate or shifted register.
ADC, SBC, ADCS, SBCS, if easy.
AND, ORR, EOR, ANDS, each with immeidate or shifted register, and each with second operand inverted.


## Shifts

LSLV, LSRV, ASRV, RORV.


## Multiply

MULA, MULH.


## Divide

UDIV, SDIV


## Conditional branch

B.cond, CBZ, CBNZ.


## Jump, call and return

B, BL, BR, BRL, RET

### Calling convention

[APCS](https://developer.arm.com/documentation/ihi0055/latest/) specifies:

 - Arguments:
   - The first eight integer or pointer arguments are passed in R0 to R7.
   - The first eight floating point arguments are passed in V0 to V7.
   - Additional arguments are pushed onto the stack from right to left.
   - If a return block is needed, it is allocated by the caller and a pointer to it is passed in R8.
   - The frame pointer is in FP (=R29).
   - The hardware puts the return address in LR (=R30).
 - At all times:
   - FP points to a two-word struct containing the caller's frame pointer and the callee's return address.
   - SP is 16-byte-aligned.
 - Return values:
   - R0 to R7 and V0 to V7 are used exactly as for arguments.
   - Additional return values are stored in the return block pointed to by R8 on entry.
 
APCS permits variations in the following areas:

 - Size of ints and pointers. Linux uses variant LP64 I think: 32-bit int and 64-bit pointer. Not particularly relevant.
 - R16 and R17 are documented as being corrupted by code inserted by the linker to implement long jumps and calls. Effectively, this makes them ordinary caller-saves registers, which is how GCC treats them.
 - R18 is used on some platforms (Windows?) to point to the thread context, and cannot be used. ARM says "Software developers creating platform-independent code are advised to avoid using r18 if at all possible". As far as I can tell, Linux has no such restriction, and GCC uses R18.
 - R29 is used on some platforms as a frame pointer. Doing so is the more choice, and probably improves the debugging experience, at the expense of adding one instruction per call and losing the use of R29.
 - SP is always required to be 16-byte aligned at calls, but on some platforms it is required to be 16-byte aligned at other times too.

I suggest we treat R16, R17 and R18 as ordinary caller-saves registers, use R29 as a frame pointer, and keep SP 16-byte-aligned at all times. If and when using R18 turns out to be a problem, we can easily stop using it.
