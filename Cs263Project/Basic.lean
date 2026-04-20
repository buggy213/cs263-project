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

inductive Outcome : Type where
| Yielded
| Completed

inductive CoroutineStep {program: @ProgramCo n k} : ((@StmtCo n k) × (@State n)) → (@State n) → Outcome → Prop where
| ShallowInstr (id: Fin n)
  (s: State) :
  CoroutineStep (StmtCo.ShallowInstr id, s) (s.update id) Outcome.Completed
| SequenceNormal (A B : StmtCo)
  (a b c: State)
  (B_outcome: Outcome)
  (hA : @CoroutineStep program (A, a) b Outcome.Completed)
  (hB : @CoroutineStep program (B, b) c B_outcome) :
  CoroutineStep (StmtCo.Sequence A B, a) c B_outcome
| SequenceEarlyYield (A B : StmtCo)
  (a b : State)
  (hA : @CoroutineStep program (A, a) b Outcome.Yielded) :
  CoroutineStep (StmtCo.Sequence A B, a) b Outcome.Yielded
| IfTrue (cond: List (Fin n) → Prop) (then_body: StmtCo)
  (s t: State)
  (hcond : cond s.trace)
  (body_outcome: Outcome)
  (hbody : @CoroutineStep program (then_body, s) t body_outcome) :
  CoroutineStep (StmtCo.If cond then_body, s) t body_outcome
| IfFalse (cond: List (Fin n) → Prop) (then_body: StmtCo)
  (s: State)
  (hcond: ¬(cond s.trace)) :
  CoroutineStep (StmtCo.If cond then_body, s) s Outcome.Completed
| LoopContinueNormal (cond: List (Fin n) → Prop) (body: StmtCo)
  (s t u: State)
  (hcond : cond s.trace)
  (rest_outcome : Outcome)
  (hbody : @CoroutineStep program (body, s) t Outcome.Completed)
  (hrest : @CoroutineStep program (StmtCo.Loop cond body, t) u rest_outcome) :
  CoroutineStep (StmtCo.Loop cond body, s) u rest_outcome
| LoopEarlyYield (cond: List (Fin n) → Prop) (body: StmtCo)
  (s t: State)
  (hcond : cond s.trace)
  (hbody: @CoroutineStep program (body, s) t Outcome.Yielded) :
  CoroutineStep (StmtCo.Loop cond body, s) t Outcome.Yielded
| LoopTerminate (cond: List (Fin n) → Prop) (body: StmtCo)
  (s: State)
  (hcond : ¬(cond s.trace)) :
  CoroutineStep (StmtCo.Loop cond body, s) s Outcome.Completed
| Yield (next: Fin k)
  (s t: State)
  (subr_outcome: Outcome)
  (hsubr : @CoroutineStep program (program.subroutines[next]'(by simp [program.hsubr_count]), s) t subr_outcome) :
  CoroutineStep (StmtCo.Yield next, s) t Outcome.Yielded
| Skip (s: State) :
  CoroutineStep (StmtCo.Skip, s) s Outcome.Completed

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
      (StmtCo.Sequence head_stmt_co tail_stmt_co, tail_subrs ++ head_subrs, head_subr_index),
      by
        simp_all
        constructor
        . simp [countSuspendsStmt]
          ac_rfl
        . simp [countSuspendsStmt]
          ac_rfl
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
    -- two-call technique: first call with Skip gives the (continuation-independent)
    -- transformed body statement we need to build transformed_loop; second call with
    -- the real continuation yields the correct subroutine bodies.
    let body_fake :=
      splitStmt body StmtCo.Skip subr_index
        (by simp [countSuspendsStmt] at hbound; assumption)
    let body_stmt_co := body_fake.val.1
    let transformed_loop : @StmtCo n k := StmtCo.Loop cond body_stmt_co
    let correct_cont : @StmtCo n k := StmtCo.Sequence transformed_loop cont
    let ⟨⟨body_stmt_co, body_subrs, body_subr_index⟩, ⟨body_hindex, body_hlen⟩⟩ :=
      splitStmt body correct_cont subr_index
        (by simp [countSuspendsStmt] at hbound; assumption)

    ⟨
      (StmtCo.Loop cond body_stmt_co, body_subrs, body_subr_index),
      by
        refine ⟨?_, ?_⟩
        · simp [countSuspendsStmt]; exact body_hindex
        · simp [countSuspendsStmt]; exact body_hlen
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


-- ==========================================================================
-- helper lemmas
-- ==========================================================================

-- semantic associativity of Sequence (right-rotation)
lemma coroutineSeqAssocLR {program : @ProgramCo n k}
    {A B C : @StmtCo n k} {s u : @State n} {out : Outcome}
    (h : @CoroutineStep n k program (StmtCo.Sequence A (StmtCo.Sequence B C), s) u out) :
    @CoroutineStep n k program (StmtCo.Sequence (StmtCo.Sequence A B) C, s) u out := by
  cases h with
  | SequenceNormal _ _ _ b _ _ hA hBC =>
    cases hBC with
    | SequenceNormal _ _ _ b' _ _ hB hC =>
      exact CoroutineStep.SequenceNormal _ _ _ b' _ _
        (CoroutineStep.SequenceNormal _ _ _ b _ _ hA hB) hC
    | SequenceEarlyYield _ _ _ _ hB =>
      exact CoroutineStep.SequenceEarlyYield _ _ _ _
        (CoroutineStep.SequenceNormal _ _ _ b _ _ hA hB)
  | SequenceEarlyYield _ _ _ _ hA =>
    exact CoroutineStep.SequenceEarlyYield _ _ _ _
      (CoroutineStep.SequenceEarlyYield _ _ _ _ hA)

-- semantic associativity of Sequence (left-rotation)
lemma coroutineSeqAssocRL {program : @ProgramCo n k}
    {A B C : @StmtCo n k} {s u : @State n} {out : Outcome}
    (h : @CoroutineStep n k program (StmtCo.Sequence (StmtCo.Sequence A B) C, s) u out) :
    @CoroutineStep n k program (StmtCo.Sequence A (StmtCo.Sequence B C), s) u out := by
  cases h with
  | SequenceNormal _ _ _ _ _ _ hAB hC =>
    cases hAB with
    | SequenceNormal _ _ _ a _ _ hA hB =>
      exact CoroutineStep.SequenceNormal _ _ _ a _ _ hA
        (CoroutineStep.SequenceNormal _ _ _ _ _ _ hB hC)
  | SequenceEarlyYield _ _ _ _ hAB =>
    cases hAB with
    | SequenceNormal _ _ _ a _ _ hA hB =>
      exact CoroutineStep.SequenceNormal _ _ _ a _ _ hA
        (CoroutineStep.SequenceEarlyYield _ _ _ _ hB)
    | SequenceEarlyYield _ _ _ _ hA =>
      exact CoroutineStep.SequenceEarlyYield _ _ _ _ hA

-- Skip can only step from a state to itself with outcome Completed
lemma skipCoroutineStep {program : @ProgramCo n k} {s u : @State n} {out : Outcome}
    (h : @CoroutineStep n k program (StmtCo.Skip, s) u out) :
    u = s ∧ out = Outcome.Completed := by
  cases h; exact ⟨rfl, rfl⟩

-- continuation-independence: the stmt_co produced by splitStmt does not depend on cont,
-- only on the stmt and the starting subroutine index.
lemma splitStmt_result_cont_indep (stmt : @StmtExt n) :
    ∀ (cont1 cont2 : @StmtCo n k) (idx : ℕ)
      (hb1 : idx + countSuspendsStmt stmt ≤ k)
      (hb2 : idx + countSuspendsStmt stmt ≤ k),
      (splitStmt stmt cont1 idx hb1).val.1 = (splitStmt stmt cont2 idx hb2).val.1 := by
  induction stmt with
  | ShallowInstr id =>
    intros; rfl
  | Sequence head tail ih_head ih_tail =>
    intro cont1 cont2 idx hb1 hb2
    -- all the sub-calls have the same indices (by property) and continuation-free stmt_cos
    sorry
  | If cond body ih =>
    intro cont1 cont2 idx hb1 hb2
    sorry
  | Loop cond body _ih =>
    intros; sorry
  | Suspend =>
    intros; rfl

-- ==========================================================================
-- Main simulation lemma: running (split_result; cont) under coroutine semantics
-- reaches the same end state as cont does from the straight-line final state.
-- ==========================================================================

lemma splitStmtSimulation
    (program : @ProgramCo n k)
    (stmt : @StmtExt n)
    (cont : @StmtCo n k)
    (subr_index : ℕ)
    (hbound : subr_index + countSuspendsStmt stmt ≤ k)

    (s t u : State)
    (cfg : @StmtExt n × State)
    (hcfg : cfg = (stmt, s))
    (hrun : StraightLineStep cfg t)

    (stmt_co : @StmtCo n k)
    (subrs : List (@StmtCo n k))
    (new_subr_index : ℕ)
    (hindex : new_subr_index = subr_index + countSuspendsStmt stmt)
    (hlen : subrs.length = countSuspendsStmt stmt)
    (hsplit : splitStmt stmt cont subr_index hbound = ⟨(stmt_co, subrs, new_subr_index), ⟨hindex, hlen⟩⟩)

    (hwell_formed : ∀ i (hi : i < subrs.length),
      program.subroutines[subr_index + i]'(by rw [program.hsubr_count]; rw [hlen] at hi; omega) = subrs[i])

    (cont_outcome : Outcome)
    (hcont : @CoroutineStep n k program (cont, t) u cont_outcome) :
    ∃ outcome, @CoroutineStep n k program
      (StmtCo.Sequence stmt_co cont, s)
      u outcome := by
  induction hrun with
  | ShallowInstr id st =>
    sorry
  | Sequence A B a b c hA hB hA_ih hB_ih =>
    sorry
  | IfTrue cond body s' t' hcond hbody hbody_ih =>
    sorry
  | IfFalse cond body s' hcond =>
    sorry
  | LoopContinue cond body s' t' u' hcond hbody hrest hbody_ih hrest_ih =>
    sorry
  | LoopTerminate cond body s' hcond =>
    sorry
  | Suspend st =>
    sorry


-- ==========================================================================
-- Top-level theorem: split preserves big-step semantics.
-- ==========================================================================

-- "for all straight-line programs that halt, the final state is equal to the split program run using coroutine semantics"
theorem splitPreservesSemantics :
  ∀ (program : @ProgramExt n)
    (initial_state: List (Fin n))
    (final_state: List (Fin n))
    (hrun : StraightLineStep (program.stmt, ⟨initial_state⟩) ⟨final_state⟩),

  have split_program := split program

  ∃outcome,
  @CoroutineStep
    n (countSuspendsStmt program.stmt)
    split_program
    (split_program.main, ⟨initial_state⟩) ⟨final_state⟩
    outcome := by
  intro orig init_trace final_trace hrun
  sorry
