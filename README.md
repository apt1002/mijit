Mijit
=====

An experimental JIT compiler generator.

Mijit consists of the following components:

- A domain-specific language ("Mijit code") that is
  particularly amenable to optimising, and barely
  expressive enough for writing interpreters.
- A back-end that lowers Mijit code to machine code
  (in RAM) and executes it.
- A profile-guided optimizer that reads and writes
  Mijit code.

Use
---

Suppose you are writing a high-level programming
language. It compiles to some kind of virtual code,
which runs on an interpreter, written in C, say. You
want it to go faster.

You write a Rust program that uses crate `mijit`. You
implement trait `Machine`, porting the performance-
critical parts of your interpreter to Mijit code.
Mijit provides you with an equivalent JIT compiler.
You wrap it in an ergonomic Rust API that is specific
to your language. You write C bindings for your Rust
API. You drop it in as a replacement for your
interpreter, reusing the existing non-performance-
critical parts.

Status
------

Early, unfinished. The specification of Mijit code
is in flux. There is one example interpreter. It does
not yet have C bindings. There is one back-end, for
x86_64. Other 64-bit targets are planned, but the
portable abstraction has not been designed yet.
It can run some trivial programs, but the generated
code is poor. The optimizer is still just a collection
of ideas.

Building
--------

```
    $ ./compile
```

Running
-------

```
    $ LD_LIBRARY_PATH=target/debug ./main
```
