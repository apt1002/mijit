## Mijit

An experimental JIT compiler generator.

Mijit consists of the following components:

- A domain-specific language ("Mijit code") that is particularly amenable to
  optimising, and barely expressive enough for writing interpreters.
- A back-end that lowers Mijit code to machine code (in RAM) and executes it.
- A profile-guided optimizer that reads and writes Mijit code.

# Use

Suppose you are writing a high-level programming language. It compiles to some
kind of virtual code, which runs on an interpreter, written in C, say. You want
it to go faster.

You write a Rust program that uses crate `mijit`. You construct a `Jit`,
porting the performance-critical parts of your interpreter to Mijit code.
Mijit provides you with an equivalent JIT compiler. You wrap it in an ergonomic
Rust API that is specific to your language. You write C bindings for your Rust
API. You drop it in as a replacement for your interpreter, reusing the existing
non-performance-critical parts.

# Examples

The best example of using Mijit is [Bee]. Pass the "--with-mijit" flag to its
"./configure" to enable the Mijit backend. A cut-down version of the related
[Beetle] is included in Mijit as a unit test.

[Bee]: https://github.com/rrthomas/bee
[Beetle]: https://github.com/rrthomas/beetle

# Status

Working, but unfinished. The specification of Mijit code is in flux. There are
two back-ends, for x86_64 and AArch64. Other 64-bit targets are planned. Mijit
can run some programs, but the generated code is poor, and it only runs at
about 40% of the speed of compiled C. A rough outline of the optimizer has been
written and is enabled, but so far it doesn't know many optimizations. The
profiler is not written yet.

# Versions

Versions 0.1.x are obsolete. Versions 0.2.0 to 0.2.4 improve the API and the
internals in backwards-incompatible ways, adding missing features and removing
unnecessary ones. Version 0.3.0 will be a major redesign ([#48]). As long as
the version number begins with a "0" I reserve the right to change the design
arbitrarily.

[#48]: https://github.com/apt1002/mijit/issues/48

# Building

```
    $ cargo build --release
```

# Running

Mijit is primarily a library. However, it does provide some executable tests.

```
    $ cargo test
```
