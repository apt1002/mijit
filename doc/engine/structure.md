# Introduction

The core of Mijit is a data structure called `Engine` which owns the compiled code and remembers information about it. The code is represented by a collection of `Switch`es and `Case`s. A `Switch` is (generally) a multi-way branch which selects from a menu of `Case`s. A `Case` is a straight-line block of code.

Every `Switch` is directly reachable from exactly one `Case`, and every `Case` is directly reachable from exactly one `Switch`. `Case`s can alternatively end by jumping to another `Case`, which is called "retiring", and is the only form of control-flow merging.


## Specialization

When the `Engine` notices that a `Case` is hot it specializes it: it mutates it in place to make it faster. Specialization is transparent to the user; the only observable effect of specialization is a brief pause while the faster code is compiled, followed by better performance.

Each `Case` is specialized at most once. Thus there are two kinds of `Case`: unspecialized and specialized. These are called `Retire` and `Fetch` respectively.

When a `Case` is first created, it is a `Retire`. When executed, it increments a profiling counter, runs some straight-line code called its `retire_code`, and jumps to another `Case`. The profiling counter is used to decide when to specialize the `Case`.

Specializing a `Case` turns it into a `Fetch`, and creates a new `Switch` with new `Case`s. The profiling counter and `retire_code` are no longer needed. When executed, the `Case` runs some different straight-line code called its `fetch_code`, then executes the `Switch`. The `fetch_code` and its new `Switch` are intuitively an optimized copy of the control flow path starting with the `retire_code` and continuing until the next `Switch`. The new `Case`s initially retire to the old `Case`s.


## Bootstrapping

The caller of an `Engine`'s compiled code is modelled as a distinguished `Case` called the "root". It is intuitively a `Fetch`. Everything the caller does is imagined to be part of the `fetch_code` of the root. Calling into Mijit is considered to be executing the root's `Switch`, which selects the correct entry point into the compiled code. Returning from Mijit is considered to be retiring to the root.

An `Entry` models an entry point into the compiled code. It is a wrapper around a `Case`. `Case`s are internal to the `Engine`; the API of `Engine` only uses `Entry`s.

`Engine` provides the following methods, which suffice to construct an arbitrary control-flow graph:

 - Construct a fresh `Engine` with no `Entry`s.
 - Construct an `Entry`. The `Case` initially retires to the root. The caller provides the `Case`'s `retire_code`.
 - Specialize an `Entry`. The caller provides the `Case`'s `fetch_code` and `Switch`, and the `Entry`s that the `Switch`'s `Case`s retire to.

In addition, `Engine` provides a `run()` method which executes the compiled code starting from an `Entry`. Execution continues until the compiled code retires to the root. 64-bit values can be passed to and from the compiled code in global variables, which are specified when the `Engine` is constructed.


## Interrupts

An `Engine`'s `run()` method normally executes compiled code until it retires to the root. However, when a profiling counter overflows, it is desirable to force an immediate retirement to the root, in order to specialize a `Case` and compile new code. This must be done in such a way that execution can be restarted seamlessly.

To achieve this, every `Case` has some straight-line code called its `exit_code`. Intuitively, the `exit_code` is the shortest path to the root. It is an exact copy of the `Case`'s `retire_code` and jumps to the same other `Case`, but to its `exit_code`. Unlike its `retire_code`, a `Case`'s `exit_code` is not replaced when the `Case` is specialized.
