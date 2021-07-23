# Introduction


## Concepts

The core of Mijit is a data structure called `Engine` which owns the compiled code and remembers information about it. It has the following abilities:

 - Create a new entry/exit point.
 - Compile a new `Specialization`, and patch it into the existing code.
 - Run the code starting at any entry point.
 - Examine the profiling data.

### Entry points

Entry points are the only control-flow points where execution of the VM can be interrupted, e.g. by a profiling counter overflowing or by some other exception. The initial code at each entry point just throws a `NotImplemented` exception. Every entry point is also a `Vector`.

### Vectors

A `Vector` is a place in the code where new code can be patched in. The new code completely replaces the (non-exception) code at the `Vector`. Each `Vector` can only be patched once.

A `Vector` is also a control-flow merge point.

### Specializations

The unit of new code is a `Specialization`. The new code path starts at a `Vector`, and completely replaces its (non-exception) code. A `Specialization` consists of a basic block followed by a `Switch`.

### Switch

A `Switch` is (generally) a multi-way branch. Each `Case` of the `Switch` is a `Vector`, and initially it jumps to some other `Vector`. The `Case`s are instrumented to collect profiling data.

### Exceptions

When Mijit runs the code, it continues until the code throws an exception. Common kinds of exception include:

 - `NotImplemented` - execution reaches some code that does not exist yet.
 - `Hot` - execution reaches a `Case` often enough that it is worth trying to optmise it.
 - User-defined exceptions, including:
    - Unrecoverable errors.
    - "System calls", which require Mijit to stop running temporarily.


## Representation of code

`Engine` owns the native machine code that it runs. However, machine code is effectively a write-only format which, while it is sufficient to run the code, does not adequately express its meaning. Therefore, `Engine` also keeps other copy of the code in a more useful form.

The code is organised into `Specialization`s, each of which has:

 - A starting `Vector`.
 - A basic block of code, represented as a `Dataflow` graph.
 - A `Switch`, each of whose `Case`s has:
    - A `Vector`.
    - A profiling counter.
    - A basic block of code.
    - An ending `Vector`.
