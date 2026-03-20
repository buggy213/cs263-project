# Program Representation
A program is represented as `n: ℕ` and `stmts: List (Stmt n))`, where `n` indicates how many unique non-control-flow instructions there are in the program.

# Statement Representation
Statements are a representation of the LuisaCompute XIR which directly embed the fact that it only has _structured_ control flow. In particular, there are only three types of control flow that we need to worry about: conditionals, switch, and loop. Constructs like `break`, `return`, can all be mapped down to just these three.
Note that actually doing this transformation isn't super efficient, it requires masking for instructions that shouldn't run and auxiliary flags to check whether that masking should apply. Also, the real `loop` construct in XIR is more like a `do-while`, but this is trivially equivalent (just unroll the body once).
Since the control flow is _structured_, we can adopt a tree-like structure that hopefully makes proofs go through more easily, rather than directly trying to prove things about a linear IR. 

Everything except control flow statements is shallowly embedded as a `ShallowInstr (id: Fin n) : Stmt`. These represent basically everything else the real program would be allowed to do: modifying memory, doing IO, launching ray tracing operations, etc. The *state* of a program is represented by a trace of `id`s of `ShallowInstr`s that the program executed. In terms of the mapping from "real" program, you can create two `ShallowInstr` with the same `id`, as long as they are guaranteed to "do the same thing" under the same state. This is a bit hand-wavy, but restricting ourselves to this shallow embedding should make proofs much more tractable. 

```lean
inductive Stmt (n: ℕ) : Type where
  | ShallowInstr (id: Fin n)
  | Switch (num_cases: ℕ) (cond: (List (Fin n)) → Fin num_cases → Prop) (cases: Vector (List (Stmt n)) num_cases) -- `If` is really just `Switch` with 2 cases
  | Loop (cond: (List (Fin n)) → Prop) (body: List (Stmt n))

structure State (n: ℕ) where
  trace: List (Fin n)

structure Program where
  n : ℕ
  stmts: List (Stmt n)
```

# Operational Semantics
We can define the following small-step operational semantics for a program:
1. `(ShallowInstr id :: rest, trace) ⇒ (rest, trace ++ [id])`
   `ShallowInstr` statement just appends its `id` into the state
2. `(Switch cases :: rest, trace) ⇒ (cases[i] ++ rest, trace) if cond(trace, i)`
   `Switch` statement can evaluate one of its cases. Otherwise, it is pure in that it doesn't do memory operations, IO, etc. (and thus doesn't modify the state)
3. `(Loop body :: rest, trace) ⇒ (body ++ [Loop body] ++ rest, trace) if cond(trace)`
   `Loop` statement can evaluate its body, and doesn't modify state
4. `(Loop body :: rest, trace) ⇒ (rest, trace) if ¬cond(trace)`
   `Loop` statement is also allowed to terminate


# Program Equivalence
For the purposes of proving stuff, it's easiest to assume that the programs actually terminate, so theorems will have that assumption. Otherwise, you would need to consider set of all configurations reachable from initial configuration, which seems annoying. 

For two programs `p1` and `p2` that have the same value of `n` and both terminate (so we have assumptions `p1_terminates: (p1, []) ⇒* ([], t1)` and `p2_terminates: (p2, []) ⇒* ([], t2)`), they are equivalent if `t1 = t2`. 

# Coroutine Transformation
The transformation we are interested in (a very simplified version of LuisaCompute's coroutine transformation passes) works as follows:
1. We augment the original `Stmt` inductive type with a new variant named `Suspend`
  ```lean
  inductive StmtExt (n: ℕ) : Type where
    ...
    | Suspend
  
  structure ProgramExt where
    n : ℕ
    stmts: List (StmtExt n)
  ```

  Inputs to the coroutine transformation are `ProgramExt`
2. We augment the original small-step semantics with a new rule: `(Suspend :: rest, trace) ⇒ (rest, trace)`
  Effectively, this represents straight-line semantics that just plow through `Suspend`s by treating them as no-ops
3. We define new types `StmtCo`, `StateCo`, `ProgramCo` for result of coroutine transformation; all `Suspend` have been ripped out and replaced with `Yield`.
  ```lean
  inductive StmtCo (n: ℕ) (k: ℕ) : Type where
    | ShallowInstr (id: Fin n)
    | Switch (num_cases: ℕ) (cond: (List (Fin n)) → Fin num_cases → Prop) (cases: Vector (List (StmtCo n k)) num_cases) -- `If` is really just `Switch` with 2 cases
    | Loop (cond: (List (Fin n)) → Prop) (body: List (StmtCo n k))
    | Yield (next: Option (Fin k))
  
  structure StateCo (n: ℕ) (k: ℕ) where
    trace: List (Fin n)
    next: Option (Fin k)
  
  structure ProgramCo where
    n: ℕ
    k: ℕ
    subroutines: Vector (List (StmtCo n)) k
  ```

  `k` represents the number of suspend points, and `next` is which continuation the program should go to next (or terminate, if `none`)
3. The **coroutine semantics** are mostly the same, but with the additional rules:
  - `(Yield next :: rest, state) ⇒ ([], state[next ↦ next])`
  - `([], state[next ↦ some i]) ⇒ (subroutines[i], state)`

  The subroutines are carried along as part of the relation too (i.e. small-step inductive predicate is dependent on specific subroutines it's "simulating")

We make the assumption that `state` is able to be carried through the scheduler without any difficulty. Of course, those values need to somehow be spilled and rematerialized in the "real" program / XIR (requiring the *coroutine frame*), but modelling that formally seems hard.
