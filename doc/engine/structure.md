# Introduction

The core of Mijit is a data structure called `Engine` which owns the compiled code and remembers information about it. The code is represented by a collection of `Switch`es and `Case`s. A `Switch` is (generally) a multi-way branch which selects from a menu of `Case`s. A `Case` is a straight-line block of code.

Every `Switch` is directly reachable from exactly one `Case`, and every `Case` is directly reachable from exactly one `Switch`. `Case`s can alternatively end by jumping to another `Case`, which is called "retiring", and is the only form of control-flow merging.


## Specialization

When the `Engine` notices that a `Case` is hot it specializes it: it mutates it in place to make it faster. Specialization is transparent to the user; the only observable effect of specialization is a brief pause while the faster code is compiled, followed by better performance.

The unit of specialization is a control-flow tree rooted at a `Case` and with `Case`s as its leaves. Specialization creates a semantically equivalent, optimized tree which shares its root `Case` and whose leaves retire to the corresponding leaves of the unoptimized tree. The optimized tree need not have the same structure as the unoptimized tree; internal `Case`s of the optimized tree do not necessarily correspond to internal `Case`s of the unoptimized tree.

As a result, a `Case` can be in one of three states:

1. A `Case` that is internal to an optimized tree has a `Fetch`: a path that leads via a `Switch` to `Cases` that are more specialized.

2. A `Case` that is peripheral to an optimized tree has a `Retire`: a path that retires to a `Case` of the unoptimized tree.

3. A `Case` that is the root of an optimized tree has both a `Fetch` and a `Retire`, being the respectively the paths that lead to the optimized and unoptimized trees.

A `Case` is first created in state 1 or 2. Either way, all of its exits must be to existing `Case`s. Specializing a tree converts its root `Case` from state 1 to state 3. `Case`s created in state 2 remain in that state forever.


## Bootstrapping

The caller of an `Engine`'s compiled code is modelled as a distinguished `Case` called the "root". Everything the caller does is imagined to be part of the `Fetch` of the root. Calling into Mijit is considered to be executing the root's `Switch`, which selects the correct entry point into the compiled code. Returning from Mijit is considered to be retiring to the root.

An `Entry` models an entry point into the compiled code. It is a wrapper around a `Case`. `Case`s are internal to the `Engine`; the API of `Engine` only uses `Entry`s.

`Engine` provides the following methods, which suffice to construct an arbitrary control-flow graph:

 - Construct a fresh `Engine` with no `Entry`s.
 - Construct an `Entry`. The `Case` initially retires to the root. The caller provides the `Case`'s `Retire`.
 - Specialize an `Entry`. The caller provides the `Case`'s `Fetch` and the `Entry`s that the `Switch`'s `Case`s retire to.

In addition, `Engine` provides a `run()` method which executes the compiled code starting from an `Entry`. Execution continues until the compiled code retires to the root. 64-bit values can be passed to and from the compiled code in global variables, which are specified when the `Engine` is constructed.


## Interrupts

An `Engine`'s `run()` method normally executes compiled code until it retires to the root. However, it is desirable to occasionally force an immediate retirement to the root, in order to observe what the compiled code is doing. This interruption is triggered by a counter, and it is the mechanism for detecting hot code and specializing it. Interrupting execution must be done in such a way that execution can be restarted seamlessly.

To achieve this, when we specialize a `Case`, we retain its `Retire` alongside its new `Fetch`. In normal execution, the `Fetch` is preferred, but when the counter overflows the `Retire` is used as a short path to the root.
