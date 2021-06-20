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

ARMv8 includes many variants of load (`LDR`) and store (`STR`) instructions, most of which are omitted here. The main axes of variation are:

 - How much data is transferred:
    - An 8-, 16-, 32- or 64-bit value
    - A pair of 32- or 64-bit values

 - (For loads) whether the data is sign-extended, and to what size

 - How the address is calculated:
    - PC + offset
    - Register + unsigned offset
    - Register + optionally shifted register
    - Register + signed offset
    - Register plus extended register, optionally shifted

 - (For register + offset) whether the base address register is modified.

In addition, there are lots of variants that control cache behaviour, that synchronise with other cores, and that perform various security checks.

An `LDRS` of 64 bits would be useless (it is equivalent to `LDR`), and a special case applies. Instead of the regular meaning, the bit pattern encodes a prefetch instruction (`PRFM`). Be careful not to assemble this by accident.

### PC-relative

This variant of `LDR` computes the address as `PC + constant`.

```
Mask        Asm     Rt      imm     Meaning
0x58000000  LDR     0:4     5:23    Rt <- [PC + 4 * imm]
```

### Register + immediate

These variants of `LDR` and `STR` compute the address as `Rn + constant`. `Rn` can be `SP`, and `Rt` can be `ZR`.

The amount of data transferred is determined by the `size` field (bits 30:31) as follows:

```
size    Asm bits
0       B   8
1       H   16
2       W   32
3           64
```

Unsigned scaled offset:

```
Mask        Asm         Rt      Rn      imm     Size    Meaning
0x39000000  STR[BHW]?   0:4     5:9     10:21   30:31   [Rn + (imm << size)] <- Rt
0x39400000  LDR[BHW]?   0:4     5:9     10:21   30:31   Rt <- zero_extend([Rn + (imm << size)])
0x39800000  LDRS[BHW]?  0:4     5:9     10:21   30:31   Rt <- sign_extend([Rn + (imm << size)])
```

Signed unscaled offset:

```
Mask        Asm         Rt      Rn      imm     Size    Meaning
0x38000000  STRU[BHW]?  0:4     5:9     12:20   30:31   [Rn + imm] <- Rt
0x38400000  LDRU[BHW]?  0:4     5:9     12:20   30:31   Rt <- zero_extend([Rn + imm])
0x38800000  LDRUS[BHW]? 0:4     5:9     12:20   30:31   Rt <- sign_extend([Rn + imm])
```

### Register + shifted register

These variants of `LDR` and `STR` compute the address as `Rn + (Rm << shift)`. The data is transferred to/from `Rt`. `Rn` can be `SP`, and `Rm` and `Rt` can be `ZR`.

```
Mask        Asm         Rt      Rn      S   Rm      size    Meaning
0x38206800  STR[BHW]?   0:4     5:9     12  16:20   30:31   [Rm + (Rn << shift)] <- Rt
0x38606800  LDR[BHW]?   0:4     5:9     12  16:20   30:31   Rt <- zero_extend([Rm + (Rn << shift)])
0x38A06800  LDRS[BHW]?  0:4     5:9     12  16:20   30:31   Rt <- sign_extend([Rm + (Rn << shift)])
```

The amount of data transferred is determined by the `size` field (bits 30:31) as follows:

```
size    Asm bits
0       B   8
1       H   16
2       W   32
3           64
```

The `S` flag (bit 12) and the `size` field (bits 30:31) together determine `shift` as follows:

```
S   size    Meaning
0   -       0
1   0       1
1   1       1
1   2       2
1   3       3
```

TODO:
 - Push and pop pair.


## Move

For moving a register to a register, `ORR` it with `RZR`.

For moving a constant to a register, there are several cases to consider:
 - If the constant PC-relative, use `ADR`.
 - If the constant fits in 16 bits, use `MOVZ`.
 - If the inverse of the constant fits in 16 bits, use `MOVN`.
 - If the constant is an allowed logic immediate, `ORR` it with `RZR`.
 - A few more options...
 - Otherwise use a PC-relative load from a constant pool.

```
Mask        Asm     Rd      imm     Siz Meaning
0x10000000  ADR     0:4     5:23    64  Rd <- PC + 4*imm
0x12800000  MOVN    0:4     5:20    32  Rd <- ~imm
0x92800000  MOVN    0:4     5:20    64  Rd <- ~imm
0x52800000  MOVZ    0:4     5:20    32  Rd <- imm
0xD2800000  MOVZ    0:4     5:20    64  Rd <- imm
```


## Arithmetic

The third operand of an arithmetic instructions can be:
 - a sign-extended register (omitted)
 - an unsigned 12-bit immediate operand (shift omitted)
 - a shifted register (all but `LSL` omitted).

Variants that end with "S" set the condition flags.

There are variants that read the carry flag (omitted).

With an immediate operand:

```
Mask        Asm     Rd      Rn      imm     Siz Meaning
0x11000000  ADD     0:4     5:9     10:21   32  Rd <- Rn + imm
0x31000000  ADDS    0:4     5:9     10:21   32  Rd <- Rn + imm
0x51000000  SUB     0:4     5:9     10:21   32  Rd <- Rn - imm
0x71000000  SUBS    0:4     5:9     10:21   32  Rd <- Rn - imm
0x91000000  ADD     0:4     5:9     10:21   64  Rd <- Rn + imm
0xB1000000  ADDS    0:4     5:9     10:21   64  Rd <- Rn + imm
0xD1000000  SUB     0:4     5:9     10:21   64  Rd <- Rn - imm
0xF1000000  SUBS    0:4     5:9     10:21   64  Rd <- Rn - imm
```

With a shifted register operand:

```
Mask        Asm     Rd      Rn      imm     Rm      Siz Meaning
0x0B000000  ADD     0:4     5:9     10:14   16:20   32  Rd <- Rn + (Rm << imm)
0x2B000000  ADDS    0:4     5:9     10:14   16:20   32  Rd <- Rn + (Rm << imm)
0x4B000000  SUB     0:4     5:9     10:14   16:20   32  Rd <- Rn - (Rm << imm)
0x6B000000  SUBS    0:4     5:9     10:14   16:20   32  Rd <- Rn - (Rm << imm)
0x8B000000  ADD     0:4     5:9     10:15   16:20   64  Rd <- Rn + (Rm << imm)
0xAB000000  ADDS    0:4     5:9     10:15   16:20   64  Rd <- Rn + (Rm << imm)
0xCB000000  SUB     0:4     5:9     10:15   16:20   64  Rd <- Rn - (Rm << imm)
0xEB000000  SUBS    0:4     5:9     10:15   16:20   64  Rd <- Rn - (Rm << imm)
```

The following table indicates which registers can be `SP`; the rest can be `ZR`.

```
Asm         ADD     ADDS    SUB     SUBS
Variant     i s     i s     i s     i s
Rd=SP?      y n     n n     y n     n n
Rn=SP?      y n     y n     y n     y n
Rm=SP?      - n     - n     - n     - n
```


## Logic

The third operand of an arithmetic instructions can be:
 - a patterned bitmask immediate operand, encoded into a 13-bit field in a complicated way.
 - a shifted register (all but `LSL` omitted).
 - the inverse of a shifted register (omitted).

Variants that end with "S" set the condition flags.

With an immediate operand:

```
Mask        Asm     Rd      Rn      l_imm   Siz Meaning
0x12000000  AND     0:4     5:9     10:21   32  Rd <- Rn & l_imm
0x32000000  ORR     0:4     5:9     10:21   32  Rd <- Rn | l_imm
0x52000000  EOR     0:4     5:9     10:21   32  Rd <- Rn ^ l_imm
0x72000000  ANDS    0:4     5:9     10:21   32  Rd <- Rn & l_imm
0x92000000  AND     0:4     5:9     10:22   64  Rd <- Rn & l_imm
0xB2000000  ORR     0:4     5:9     10:22   64  Rd <- Rn | l_imm
0xD2000000  EOR     0:4     5:9     10:22   64  Rd <- Rn ^ l_imm
0xF2000000  ANDS    0:4     5:9     10:22   64  Rd <- Rn & l_imm
```

With a shifted register operand or its inverse:

```
Mask        Asm     Rd      Rn      imm     Rm      Siz Meaning
0x0A000000  AND     0:4     5:9     10:14   16:20   32  Rd <- Rn & (Rm << imm)
0x0A200000  BIC     0:4     5:9     10:14   16:20   32  Rd <- Rn & ~(Rm << imm)
0x2A000000  ORR     0:4     5:9     10:14   16:20   32  Rd <- Rn | (Rm << imm)
0x2A200000  ORN     0:4     5:9     10:14   16:20   32  Rd <- Rn | ~(Rm << imm)
0x4A000000  EOR     0:4     5:9     10:14   16:20   32  Rd <- Rn ^ (Rm << imm)
0x4A200000  EON     0:4     5:9     10:14   16:20   32  Rd <- Rn ^ ~(Rm << imm)
0x6A000000  ANDS    0:4     5:9     10:14   16:20   32  Rd <- Rn & (Rm << imm)
0x6A200000  BICS    0:4     5:9     10:14   16:20   32  Rd <- Rn & ~(Rm << imm)
0x8A000000  AND     0:4     5:9     10:15   16:20   64  Rd <- Rn & (Rm << imm)
0x8A200000  BIC     0:4     5:9     10:15   16:20   64  Rd <- Rn & ~(Rm << imm)
0xAA000000  ORR     0:4     5:9     10:15   16:20   64  Rd <- Rn | (Rm << imm)
0xAA200000  ORN     0:4     5:9     10:15   16:20   64  Rd <- Rn | ~(Rm << imm)
0xCA000000  EOR     0:4     5:9     10:15   16:20   64  Rd <- Rn ^ (Rm << imm)
0xCA200000  EON     0:4     5:9     10:15   16:20   64  Rd <- Rn ^ ~(Rm << imm)
0xEA000000  ANDS    0:4     5:9     10:15   16:20   64  Rd <- Rn & (Rm << imm)
0xEA200000  BICS    0:4     5:9     10:15   16:20   64  Rd <- Rn & ~(Rm << imm)
```

The following table indicates which registers can be `SP`; the rest can be `ZR`.

```
Asm         AND     ORR     EOR     ANDS
Variant     i s     i s     i s     i s
Rd=RSP?     y n     y n     y n     n n
Rn=RSP?     n n     n n     n n     n n
Rm=RSP?     - n     - n     - n     - n
```


## Bit fields

`BFM` can be used to implement:
 - Bit field clear.
 - Bit field insert.
 - Bit field extract and insert low.

`SBFM` can be used to implement:
 - `ASR` by a constant.
 - Signed bit field insert into zero.
 - Signed bit field extract.
 - Sign-extend.

`UBFM` can be used to implement:
 - `LSL` and `LSR` by a constant.
 - Bit field insert into zero.
 - Bit field extract.
 - Zero-extend.

```
Mask        Asm     Rd      Rn      imms    immr    Siz Meaning
0x13000000  SBFM    0:4     5:9     10:14   16:20   32  See section C6.2.234
0x33000000  BFM     0:4     5:9     10:14   16:20   32  See section C6.2.29
0x53000000  UBFM    0:4     5:9     10:14   16:20   32  See section C6.2.337
0x93400000  SBFM    0:4     5:9     10:15   16:21   64  See section C6.2.234
0xB3400000  BFM     0:4     5:9     10:15   16:21   64  See section C6.2.29
0xD3400000  UBFM    0:4     5:9     10:15   16:21   64  See section C6.2.337
```


## Shifts

None of the registers can be SP; any can be ZR.

```
Mask        Asm     Rd      Rn      Rm      Siz Meaning
0x1AC02000  LSLV    0:4     5:9     16:20   32  Rd <- Rn << Rm
0x1AC02400  LSRV    0:4     5:9     16:20   32  Rd <- Rn >>> Rm
0x1AC02800  ASRV    0:4     5:9     16:20   32  Rd <- Rn >> Rm
0x1AC02C00  RORV    0:4     5:9     16:20   32  Rd <- Rn ROR Rm
0x9AC02000  LSLV    0:4     5:9     16:20   32  Rd <- Rn << Rm
0x9AC02400  LSRV    0:4     5:9     16:20   32  Rd <- Rn >>> Rm
0x9AC02800  ASRV    0:4     5:9     16:20   32  Rd <- Rn >> Rm
0x9AC02C00  RORV    0:4     5:9     16:20   32  Rd <- Rn ROR Rm
```

LSLV, LSRV, ASRV, RORV.


## Multiply

There are variants that compute the high word of the result (omitted).

None of the registers can be SP; any can be ZR.

```
Mask        Asm     Rd      Rn      Ra      Rm      Siz Meaning
0x1B000000  MADD    0:4     5:9     10:14   16:20   32  Rd <- Ra + Rn * Rm
0x1B008000  MSUB    0:4     5:9     10:14   16:20   32  Rd <- Ra - Rn * Rm
0x9B000000  MADD    0:4     5:9     10:14   16:20   64  Rd <- Ra + Rn * Rm
0x9B008000  MSUB    0:4     5:9     10:14   16:20   64  Rd <- Ra - Rn * Rm
```


## Divide

None of the registers can be SP; any can be ZR.

```
Mask        Asm     Rd      Rn      Rm      Siz Meaning
0x1AC00800  UDIV    0:4     5:9     16:20   32  Rd <- Rn / Rm
0x1AC00C00  SDIV    0:4     5:9     16:20   32  Rd <- Rn / Rm
0x9AC00800  UDIV    0:4     5:9     16:20   64  Rd <- Rn / Rm
0x9AC00C00  SDIV    0:4     5:9     16:20   64  Rd <- Rn / Rm
```


# Conditional select

None of the registers can be SP; any can be ZR.

```
Mask        Asm     Rd      Rn      cond    Rm      Siz Meaning
0x1A800000  CSEL    0:4     5:9     12:15   16:20   32  Rd <- cond ? Rn : Rm
0x1A800400  CSINC   0:4     5:9     12:15   16:20   32  Rd <- cond ? Rn : Rm+1
0x5A800000  CSINV   0:4     5:9     12:15   16:20   32  Rd <- cond ? Rn : ~Rm
0x5A800400  CSNEG   0:4     5:9     12:15   16:20   32  Rd <- cond ? Rn : -Rm
0x9A800000  CSEL    0:4     5:9     12:15   16:20   64  Rd <- cond ? Rn : Rm
0x9A800400  CSINC   0:4     5:9     12:15   16:20   64  Rd <- cond ? Rn : Rm+1
0xDA800000  CSINV   0:4     5:9     12:15   16:20   64  Rd <- cond ? Rn : ~Rm
0xDA800400  CSNEG   0:4     5:9     12:15   16:20   64  Rd <- cond ? Rn : -Rm
```


## Conditional branch

```
Mask        Asm     cond    imm     Meaning
0x54000000  B.cond  0:3     5:23    if cond { PC <- PC + 4*imm }
```

```
Mask        Asm     Rt      imm     Siz Meaning
0x34000000  CBZ     0:4     5:23    32  if Rt == 0 { PC <- PC + 4*imm }
0xB4000000  CBZ     0:4     5:23    64  if Rt == 0 { PC <- PC + 4*imm }
0x35000000  CBNZ    0:4     5:23    32  if Rt != 0 { PC <- PC + 4*imm }
0xB5000000  CBNZ    0:4     5:23    64  if Rt != 0 { PC <- PC + 4*imm }
```

```
Mask        Asm     Rt      imm     bit         Meaning
0x36000000  TBZ     0:4     5:18    19:23,31    if (Rt & (1<<bit)) == 0 { PC <- PC + 4*imm }
0x37000000  TBNZ    0:4     5:18    19:23,31    if (Rt & (1<<bit)) != 0 { PC <- PC + 4*imm }
```


## Jump, call and return

Jump or call a constant:

```
Mask        Asm     imm     Meaning
0x14000000  B       0::25   PC <- PC + 4*imm
0x94000000  BL      0::25   LR <- PC + 4; PC <- PC + 4*imm
```

Jump or call a register:

```
Mask        Asm     Rn      Meaning
0xD61F0000  BR      5:9     PC <- Rn
0xD63F0000  BLR     5:9     LR <- PC + 4; PC <- Rn
0xD65F0000  RET     5:9     PC <- Rn
```

The difference between BR and RET is the branch prediction behaviour.


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

I suggest we treat R16 and R17 as ordinary caller-saves registers, use R29 as a frame pointer, and keep SP 16-byte-aligned at all times. I'm on the fence about R18.
