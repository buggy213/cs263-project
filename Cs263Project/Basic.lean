import Mathlib
import Aesop

set_option autoImplicit false

section
variable {n : ℕ}
variable {k : ℕ}

inductive StmtExt : Type where
  | ShallowInstr (id: Fin n)
  | Sequence (head: StmtExt) (tail: StmtExt)
  | If
    (cond: List (Fin n) → Prop)
    (then_body: StmtExt)
  | Loop
    (cond: List (Fin n) → Prop)
    (body: StmtExt)
  | Suspend

structure State where
  trace: List (Fin n)

def State.update (self: @State n) (id: Fin n) : @State n :=
  ⟨self.trace ++ [id]⟩

structure ProgramExt where
  stmt: @StmtExt n

inductive StmtCo : Type where
  | ShallowInstr (id: Fin n)
  | Sequence (head: StmtCo) (tail: StmtCo)
  | If
    (cond: List (Fin n) → Prop)
    (then_body: StmtCo)
  | Loop
    (cond: List (Fin n) → Prop)
    (body: StmtCo)
  | Yield (next: Fin k)
  | Skip

structure StateCo where
  trace: List (Fin n)

def StateCo.update (self: @StateCo n) (id: Fin n) : @StateCo n :=
  ⟨self.trace ++ [id]⟩

structure ProgramCo where
  main: @StmtCo n k
  subroutines: List (@StmtCo n k)
  hsubr_count: subroutines.length = k

inductive StraightLineStep : (StmtExt × State) → State → Prop where
| ShallowInstr (id: Fin n)
  (s: State) :
  StraightLineStep (StmtExt.ShallowInstr id, s) (s.update id)
| Sequence (A B : StmtExt)
  (a b c: State)
  (hA : StraightLineStep (A, a) b)
  (hB : StraightLineStep (B, b) c) :
  StraightLineStep (StmtExt.Sequence A B, a) c
| IfTrue (cond: List (Fin n) → Prop) (then_body: StmtExt)
  (s t: State)
  (hcond : cond s.trace)
  (hbody : StraightLineStep (then_body, s) t) :
  StraightLineStep (StmtExt.If cond then_body, s) t
| IfFalse (cond: List (Fin n) → Prop) (then_body: StmtExt)
  (s: State)
  (hcond: ¬(cond s.trace)) :
  StraightLineStep (StmtExt.If cond then_body, s) s
| LoopContinue (cond: List (Fin n) → Prop) (body: StmtExt)
  (s t u: State)
  (hcond : cond s.trace)
  (hbody : StraightLineStep (body, s) t)
  (hrest : StraightLineStep (StmtExt.Loop cond body, t) u) :
  StraightLineStep (StmtExt.Loop cond body, s) u
| LoopTerminate (cond: List (Fin n) → Prop) (body: StmtExt)
  (s: State)
  (hcond : ¬(cond s.trace)) :
  StraightLineStep (StmtExt.Loop cond body, s) s
| Suspend (s: State) :
  StraightLineStep (StmtExt.Suspend, s) s

inductive CoroutineStep {program: @ProgramCo n k} : ((@StmtCo n k) × (@StateCo n)) → (@StateCo n) → Prop where
| ShallowInstr (id: Fin n)
  (s: StateCo) :
  CoroutineStep (StmtCo.ShallowInstr id, s) (s.update id)
| Sequence (A B : StmtCo)
  (a b c: StateCo)
  (hA : @CoroutineStep program (A, a) b)
  (hB : @CoroutineStep program (B, b) c) :
  CoroutineStep (StmtCo.Sequence A B, a) c
| IfTrue (cond: List (Fin n) → Prop) (then_body: StmtCo)
  (s t: StateCo)
  (hcond : cond s.trace)
  (hbody : @CoroutineStep program (then_body, s) t) :
  CoroutineStep (StmtCo.If cond then_body, s) t
| IfFalse (cond: List (Fin n) → Prop) (then_body: StmtCo)
  (s: StateCo)
  (hcond: ¬(cond s.trace)) :
  CoroutineStep (StmtCo.If cond then_body, s) s
| LoopContinue (cond: List (Fin n) → Prop) (body: StmtCo)
  (s t u: StateCo)
  (hcond : cond s.trace)
  (hbody : @CoroutineStep program (body, s) t)
  (hrest : @CoroutineStep program (StmtCo.Loop cond body, t) u) :
  CoroutineStep (StmtCo.Loop cond body, s) u
| LoopTerminate (cond: List (Fin n) → Prop) (body: StmtCo)
  (s: StateCo)
  (hcond : ¬(cond s.trace)) :
  CoroutineStep (StmtCo.Loop cond body, s) s
| Yield (next: Fin k)
  (s t: StateCo)
  (hsubr : @CoroutineStep program (program.subroutines[next]'(by simp [program.hsubr_count]), s) t) :
  CoroutineStep (StmtCo.Yield next, s) t
| Skip (s: StateCo) :
  CoroutineStep (StmtCo.Skip, s) s

-- use "direct unrolling" idea as first implementation

def countSuspendsStmt : @StmtExt n → ℕ
  | .ShallowInstr _ => 0
  | .Sequence head tail => countSuspendsStmt head + countSuspendsStmt tail
  | .If _ then_body => countSuspendsStmt then_body
  | .Loop _ body => countSuspendsStmt body
  | .Suspend => 1


/-
the general structure of the mutually recursive `split` functions is as follows
arguments:
  stmt/stmts - the yet unprocessed statement(s)
  cont - the (already transformed) continuation of what comes after a given statement, or list of statements
  subr_index - next subroutine index in final list of subroutines created by `split`
  hbound: a proof that subr_index + countSuspends of stmt/stmts doesn't overflow the index set [k]
returns:
  tuple of 3 values
    1. transformed statement / list of statements / list of list of statements
    2. any created subroutines
    3. updated subroutine index
  proof that updated subroutine index = subr_index + countSuspends of stmt/stmts
  proof that number of subroutines created = countSuspends of stmt/stmts
-/

def splitStmt (stmt: @StmtExt n) (cont: @StmtCo n k) (subr_index: ℕ) (hbound: subr_index + countSuspendsStmt stmt ≤ k) :
  { result: (@StmtCo n k × List (@StmtCo n k) × ℕ) // result.snd.snd = subr_index + countSuspendsStmt stmt ∧ result.snd.fst.length = countSuspendsStmt stmt } :=
  match stmt with
  | .ShallowInstr id => ⟨
    (StmtCo.ShallowInstr id, [], subr_index),
    by simp [countSuspendsStmt]
  ⟩
  | .Sequence head tail =>
    -- split tail first. add it to cont for head
    let ⟨⟨tail_stmt_co, tail_subrs, tail_subr_index⟩, ⟨tail_hindex, tail_hlen⟩⟩ :=
      splitStmt
        tail
        cont
        subr_index
        (by simp [countSuspendsStmt] at hbound; omega)
    let ⟨⟨head_stmt_co, head_subrs, head_subr_index⟩, ⟨head_hindex, head_hlen⟩⟩ :=
      splitStmt
        head
        (StmtCo.Sequence tail_stmt_co cont)
        tail_subr_index
        (by simp_all; rw [countSuspendsStmt] at hbound; omega)

    ⟨
      (StmtCo.Sequence head_stmt_co tail_stmt_co, head_subrs ++ tail_subrs, head_subr_index),
      by
        simp_all;
        constructor;
        . simp [countSuspendsStmt]
          ac_rfl
        . simp [countSuspendsStmt]
    ⟩
  | .If cond then_body =>
    let ⟨⟨body_stmt_co, body_subrs, body_subr_index⟩, ⟨body_hindex, body_hlen⟩⟩ :=
      splitStmt
        then_body
        cont
        subr_index
        (by simp [countSuspendsStmt] at hbound; assumption)

    ⟨
      (StmtCo.If cond body_stmt_co, body_subrs, body_subr_index),
      by simp_all; simp [countSuspendsStmt]
    ⟩

  | .Loop cond body =>
    -- to handle loops, we pass in an empty continuation so we can get the transformed body, then append
    -- that transformed_body + real cont onto the resulting subrs

    let ⟨⟨body_stmt_co, body_subrs, body_subr_index⟩, ⟨body_hindex, body_hlen⟩⟩ :=
      splitStmt
        body
        StmtCo.Skip
        subr_index
        (by simp [countSuspendsStmt] at hbound; assumption)

    let transformed_loop := StmtCo.Loop cond body_stmt_co
    let unrolled_subrs := List.map
      (fun subr ↦ StmtCo.Sequence (StmtCo.Sequence subr transformed_loop) cont)
      body_subrs

    ⟨
      (StmtCo.Loop cond body_stmt_co, unrolled_subrs, body_subr_index),
      by
        simp_all;
        constructor;
        . simp [countSuspendsStmt]
        . simp [countSuspendsStmt, unrolled_subrs, body_hlen]
    ⟩
  | .Suspend =>
    let next : Fin k := ⟨subr_index, by simp [countSuspendsStmt] at hbound; omega⟩
    ⟨
      (StmtCo.Yield next, [cont], subr_index + 1),
      by simp_all [countSuspendsStmt]
    ⟩

def split (orig: @ProgramExt n) : @ProgramCo n (countSuspendsStmt orig.stmt) :=
  let k := countSuspendsStmt orig.stmt
  let ⟨⟨stmts, subrs, _⟩, ⟨_, hlen⟩⟩ :=
    @splitStmt n k orig.stmt StmtCo.Skip 0 (by simp [k])
  @ProgramCo.mk n k stmts (subrs) (by simp_all; rfl)

-- "for all straight-line programs that halt, the final state is equal to the split program run using coroutine semantics"
-- include initial_state to reflect to model (external) inputs to program
theorem splitPreservesSemantics :
  ∀ (program : @ProgramExt n)
    (initial_state: List (Fin n))
    (final_state: List (Fin n))
    (hrun : StraightLineStep (program.stmt, ⟨initial_state⟩) ⟨final_state⟩),

  have split_program := split program
  @CoroutineStep
    n (countSuspendsStmt program.stmt)
    split_program
    (split_program.main, ⟨initial_state⟩) ⟨final_state⟩ := by

  intro original_program final_state hhalts split_program
  sorry

-- helper lemmas

-- if the `@StmtCo n k` created by `splitStmt` is executed with initial state `⟨initial_trace⟩`, it completely matches
-- the behavior of `@StmtExt n` passed into `splitList` with initial state `⟨initial_trace, .none⟩`
-- if `stmts` doesn't contain any suspends, this should basically be trivial
lemma splitStmtSimulation
  (stmt: @StmtExt n)
  (cont: @StmtCo n k)
  (subr_index: ℕ)
  (hbound: subr_index + countSuspendsStmt stmt ≤ k)

  (program : @ProgramCo n k)
  (initial_trace final_trace : List (Fin n))
  (hrun : StraightLineStep (stmt, ⟨initial_trace⟩) ⟨final_trace⟩) :
  have ⟨⟨result, subrs, _⟩, ⟨_, hlen⟩⟩ := splitStmt stmt cont subr_index hbound

  @CoroutineStep
    n k
    program
    (result, ⟨initial_trace⟩)
    ⟨final_trace⟩ :=
  by
    sorry
