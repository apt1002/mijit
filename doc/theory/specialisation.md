# Contents

- Introduction
  - What is a JIT compiler for?
  - How does a JIT compiler work?
  - A JIT compiler is really an interpreter
- Specialisation
  - Limits on specialisation
  - Fetching and retiring
  - Information theory
  - Instruction traces
- Conclusion


# Introduction

Let's suppose we want to write a Just-In-Time (JIT) compiler. I will briefly explain why this is an interesting thing to do; you may disagree, but it is a premise of this document. I will explain what a JIT compiler is, and how it is supposed to work. Merely by taking those as truths, and arguing by rejecting inferior designs and avoiding complications, we can deduce many features and properties that a good JIT compiler must exhibit. Encouragingly, many of these features and properties have analogues in hardware CPUs, which have similar goals and constraints. The arguments provide useful terminology and concepts and constrain a JIT compiler's design.


## What is a JIT compiler for?

A JIT compiler is a way of executing programs that simultaneously achieves three important goals:

1. We want code to be easy to write and to maintain for a long time.
2. We want it to run efficiently, to save time, energy and money.
3. We don't want to do any preparation before running new code.

Without 1, we'd write the code in assembly language. Without 2, we'd use an interpreter. Without 3, we'd use an ahead-of-time compiler. All of these approaches cover a lot of interesting cases. However, software engineering is increasingly throwing up cases where we need all three goals to be met.


## How does a JIT compiler work?

The key insight is the 80/20 rule: 80% of the time is spent executing 20% of the code. This is a massive and inaccurate simplification, but the essential concept is right, and the vocabulary is useful. We can compile only 20% of a program (the "hot code"), yet spend only 20% of the time interpreting the rest of the program (the "cold code"). We can avoid 80% of the ineffciency of an interpreter, and also avoid 80% of the costs of a compiler.

The hard part is to decide which 20% of the program to compile. A good general way to make the decision is to run the program, and observe its behaviour. If the program does the same thing 100 times, it's probably going to do it many more times, and so we can decide that this part is "hot code", worthy of special compiled code to do the job more efficiently.

There are many important complications, in practice. In particular:

 - The numbers "80" and "20" vary between programs and within programs. Either number can be increased if the other number is also increased. Techniques exist to vary the two numbers independently, e.g. inlining functions or adding a layer of interpretation. And even for a particular version of a particular program, the concept of "doing the same thing" is insufficiently defined to measure the amount of hot code meaningfully.

 - The "interpreter" and "compiler" are just two possible execution "tiers". Many JIT compilers have additional tiers, each with a different compromise between efficiency and up-front cost, and some omit the interpreter altogether. In a well optimised design, the concepts are all a bit blurry.

We must refine these concepts.


## A JIT compiler is really an interpreter

There are many different kinds of JIT compiler. Some compile only basic blocks; some compile whole functions; and others adopt yet other strategies. If we wish to say anything in general, then we need a definition of what *is* a JIT compiler. The opening paragraphs of the [Wikipedia article] may be summaried in two criteria:

1. It involves compilation during execution.
2. It combines compilation with interpretation.

[Wikipedia article]: https://en.wikipedia.org/wiki/Just-in-time_compilation

Criterion 2 implies that the compiled code is incomplete, and does not express the full meaning of the program that is running. At any moment the JIT compiler might encounter a novel situation for which there is no compiled code, and resort to interpreting the program instead. The code compiled by a JIT compiler must maintain, or at least be able to reconstruct, all the data structures needed for correct operation of the interpreter, including the virtual code, the virtual program counter, the virtual registers, and so on. The ultimate arbiter of "correct" program behaviour is the interpreter. The compiled code is merely an approximation that is efficient when it is accurate.

In other words, the compiled code *is* an interpreter. The only part that deserves to be called a compiler is the part that kicks in when new hot code is discovered. The purpose of the compiler is to modify the interpreter: to give it the ability to run the new hot code efficiently. It must do this without changing the behaviour of the interpreter.

This is an essential feature of a JIT compiler. Fundamentally, the compiler recompiles the interpreter, not the user program. It nonetheless compiles code that behaves approximately like the user program, and a compiled form of the user program is a useful point of comparison.


# Specialisation

Suppose we run a program on a JIT compiler, and then without warning we substitute a different program. Indeed, this is actually pretty typical behaviour; many programs go through several "phases" of operation. How will the JIT compiler behave?

It is probably worth first emphasising that the JIT compiler will run all the phases correctly. The question is about the internal behaviour: when the compiler activates, and what code it compiles.

Neglecting the possibility of code that is common to more than one phase, the best we can hope for is that the JIT compiler behaves as well as if it were restarted in between each phase. At the start of phase 2, the JIT compiler will have lots of compiled code that is useful for phase 1. This compiled code is largely useless for phase 2, but we can at least hope that it is not a handicap.

A better way to say this is that over time the interpreter becomes specialised for the program it is running. Each piece of compiled code is a specialisation for a particular task, which makes the interpreter more efficient if it ever has to perform that task. If the interpreter does not have to perform the task, the specialisation is useless.

This is another essential feature of a JIT compiler. Fundamentally, the efficiency gain of a JIT compiler over an interpreter is achieved by specialising the interpreter.

It is difficult to prove a limit on the effectiveness of specialisation. A theoretical example of what a JIT compiler can produce is an interpreter that says "Is the user program the expected one? If so, run the compiled version of the program, otherwise run the interpreter". Thus, it is not unreasonable to believe that, in theory, the steady-state performance of a JIT-compiled program can exceed that of an ahead-of-time compiled program.


## Limits on specialisation

It is not possible to compile an interpeter that is specialised for every program simultaneously. Each specialisation consumes resources, and it is therefore necessary to be selective about specialisation, and to do a cost/benefit analysis.

The costs of specialisation include: compile time (which must be accounted as part of run time); the memory needed to hold the compiled code; the space consumed in the instruction cache and branch predictor by the compiled code. All of these are roughly proportional to the amount of compiled code. Therefore, our attention should focus on the benefit per compiled specialisation.

Let's first consider whether there is an alternative to compiling dedicated code per specialisation. Could we get the benefit of the specialisation without the cost?

The main benefit of compiling dedicated code for a specialisation is that it provides a way for the interpreter to remember that it is "in" the specialisation, and to execute different instructions from those it would execute otherwise. Essentially, the JIT compiler reserves a branch target, i.e. a possible value of the program counter (EIP on x86, PC on ARM), to mean "the specialisation is active", and it compiles at that address the code it wants to run.

Is there any other way to remember that a specialisation is active? I think the answer is no. We can rule out any mechanism that is as inefficient as an interpreter; we already have one of those. That includes any mechanism that tests a state variable at run time; we might as well interpret an instruction opcode instead (or test some other aspect of the virtual machine code). To put it another way, if specialisations share code then we lose the benefits of specialisation.

So the total amount of storage available for remembering which specialisation is active is limited to about 20 bits, being the parts of the program counter that the JIT compiler can choose freely without straying outside the compiled code and without the basic blocks overlapping. This budget is extremely constraining, and I can't see a way around it.


## Fetching and retiring

If we accept that there is a one-to-one correspondence between branch targets and specialisations, we obtain some insight into the design of CPUs. Concepts that naturally arise in a specialising interpreter correspond to ubiquitous CPU features, as follows:

 - Entering a specialisation is exactly the process of incorporating into the program counter information from somewhere else. The corresponding CPU feature is a conditional (or indirect) branch instruction. In an interpreter, the most common example is reading some virtual machine code before executing it; we will therefore call this "fetching" (but please note that the concept is more general than just fetching virtual machine instructions).

 - Leaving a specialisation is exactly the process of removing information from the program counter, i.e. collapsing several program counter values to the same value. The corresponding CPU feature is a direct jump to a control-flow merge point. In an interpreter, the most common example is forgetting some virtual machine code after executing it; we therefore call this "retiring".

 - Sequential execution may be understood as an arbitrary way to generate unique program counter values when not fetching or retiring.

 - The CPU's branch history register may be understood as a clever way to supplement the information in the program counter, and thereby to get more specialisations out of a given amount of code. Essentially, information that is retired from the program counter is briefly retained in the branch history register in the hope that correlated information is fetched soon afterwards.


## Information theory

Control-flow branch and merge-points are expensive on real CPUs. The expense is partly the cost of the branch instructions themselves, and partly the cost of code not being sequential in memory. However the main cost of branch- and merge-points is that they inhibit optimisations. They constrain register allocation and instruction scheduling. They confuse analyses. They hide common subexpressions and dead values. They prevent peephole optmisations.

The foregoing analysis identifies branches and merges with fetching and retiring. To minimise their cost, we must therefore minimise the amount of *information* that needs to be fetched (and later retired) in order to run the user program. Predictable control flow is efficient; surprises are costly.

A traditional interpreter is pessimal according to this metric; after executing each instruction it returns to the top of the interpreter loop, thereby retiring all the information it has. The next virtual machine instruction is a complete surprise, every time, thus maximising the amount of information fetched (which is bad).

Specialisation may be understood as delaying the retirement of information, so as to predict (and therefore reduce the information content of) subsequent fetches. From the information theory viewpoint, this task is equivalent to compressing the instruction stream.

We remark in passing that delaying retirements and avancing fetches makes a JIT compiler a software analogue of the reorder buffer in a CPU. In both cases, the technique is used to reveal opportunities for optimisation.


## Instruction traces

A hard limit on the effectiveness of specialisation is the total information content of the instruction trace. If we run the user program, and record everything it does (with one byte per executed virtual instruction, say), then compress that file as much as possible, we obtain a lower bound on the amount of information that we have to fetch in order to execute the program.

Fortunately, instruction traces are remarkably compressible. Off-the-shelf tools such as `zstd` can compress typical instruction traces by a factor of 300 or more. A Huffman code (which is roughly analogous to the tree of "if" statements in a traditional interpreter) can only compress them by a factor of about 3.

Of course, the `zstd` compression algorithm has much more than the 20 bits of state available to the compiled code of a JIT compiler. How well can we compress instruction traces using a Markov machine with up to 2²⁰ states? Actually, pretty well. We are allowed to choose the Markov machine to suit the particular user program; that's basically the JIT compiler's main job. A machine with that many states contains a lot of information: enough to hold large portions of the user program, plus profile-based decisions. It is not fair to compare the performance of such a Markov machine to that of `zstd`, because the latter is a completely general algorithm with no prior information. Nonetheless, if we do so, we get similar compression ratios: within an order of magnitude.

In summary, there is *plenty* of opportunity for a JIT compiler to improve on an interpreter, according to this analysis. Of course, many existing JIT compilers do indeed work well; we did not need to prove that. The main value of the information-theoretic analysis is that it can be used to refute ideas that have no hope of working well, and to guide the choice of specialisations.


# Conclusion

We have presented an argument with the following structure:

- From the definition of a JIT compiler, its external behaviour is indistinguishable from an interpreter.
- The benefits of a JIT compiler over an interpreter arise from specialising the interpreter for the program it is running.
- The only sensible way this can work is by compiling new code at run-time and patching it into the running interpreter.
- Transitions between specialisations are costly, because they prevent optimisations.
- Avoiding transitions between specialisations is equivalent to compressing the instruction trace.
- The compression algorithm must be a Markov model with one state per specialisation.
- Practical limits on the amount of code we can compile limits the number of specialisations.
- This gives a theoretical but very generous limit on the perfomance of a JIT compiler.
- Information-theoretically suboptimal designs tighten this limit, and cannot possibly perform as well.
