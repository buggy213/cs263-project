import Mathlib
import Aesop

set_option autoImplicit false
set_option trace.split.failure true

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

-- tests
namespace tests

-- sugar
infixr:100 ";\n" => StmtExt.Sequence
abbrev SI (id: Fin n) := StmtExt.ShallowInstr id

def print_program_ext (program: @ProgramExt n) : IO Unit :=
  let rec print_stmt_with_indent (stmt: @StmtExt n) (indent: ℕ) : IO Unit :=
    do
      match stmt with
      | .ShallowInstr id =>
        IO.print (String.join (List.replicate indent " "))
        IO.println s!"SI {id}"
      | .Sequence head tail =>
        print_stmt_with_indent head indent
        print_stmt_with_indent tail indent
      | .If _cond then_body =>
        IO.print (String.join (List.replicate indent " "))
        IO.println "If (...)"
        print_stmt_with_indent then_body (indent + 4)
      | .Loop _cond body =>
        IO.print (String.join (List.replicate indent " "))
        IO.println "Loop (...)"
        print_stmt_with_indent body (indent + 4)
      | .Suspend =>
        IO.print (String.join (List.replicate indent " "))
        IO.println "Suspend"

  print_stmt_with_indent program.stmt 0

def print_program_co (program: @ProgramCo n k) : IO Unit :=
  let rec print_stmt_with_indent (stmt: @StmtCo n k) (indent: ℕ) : IO Unit :=
    do
      match stmt with
      | .ShallowInstr id =>
        IO.print (String.join (List.replicate indent " "))
        IO.println s!"SI {id}"
      | .Sequence head tail =>
        print_stmt_with_indent head indent
        print_stmt_with_indent tail indent
      | .If _cond then_body =>
        IO.print (String.join (List.replicate indent " "))
        IO.println "If (...)"
        print_stmt_with_indent then_body (indent + 4)
      | .Loop _cond body =>
        IO.print (String.join (List.replicate indent " "))
        IO.println "Loop (...)"
        print_stmt_with_indent body (indent + 4)
      | .Yield next =>
        IO.print (String.join (List.replicate indent " "))
        IO.println s!"Yield {next}"
      | .Skip =>
        IO.print (String.join (List.replicate indent " "))
        IO.println "Skip"

  do
    IO.println "main: "
    print_stmt_with_indent program.main 4
    IO.println ""

    for (subr, subr_idx) in program.subroutines.zipIdx do
      IO.println s!"subr_{subr_idx}: "
      print_stmt_with_indent subr 4
      IO.println ""

def test_0 : @StmtExt 5 :=
  let loop_cond (trace : List (Fin 5)) : Prop :=
    trace.length ≥ 5

  let if_cond (_trace : List (Fin 5)) : Prop := True

  SI 0;
  StmtExt.Loop loop_cond (
    SI 1;
    StmtExt.If if_cond (
      StmtExt.Suspend;
      SI 2
    );
    SI 3
  );
  SI 4

#eval print_program_ext ⟨test_0⟩

def test_0_split : @ProgramCo 5 1 := split ⟨test_0⟩

#eval print_program_co test_0_split

end tests

-- ==========================================================================
-- Helper lemma: the transformed statement produced by `splitStmt` does not
-- depend on the continuation `cont`. This is needed because `splitStmt`'s
-- `Loop` case calls `splitStmt body ...` twice (once with `Skip` to form the
-- self-referential cont, once with the real cont to populate subroutines),
-- and the `let`-shadowing makes the two transformed bodies definitionally
-- distinct even though they are propositionally equal.
-- ==========================================================================

lemma splitStmt_stmt_cont_invariant
    (stmt : @StmtExt n)
    (cont₁ cont₂ : @StmtCo n k)
    (subr_index : ℕ)
    (hindex : subr_index + countSuspendsStmt stmt ≤ k) :
    (splitStmt stmt cont₁ subr_index hindex).val.1 = (splitStmt stmt cont₂ subr_index hindex).val.1 := by

  induction stmt generalizing cont₁ cont₂ subr_index with
  | ShallowInstr id => rfl
  | Suspend => rfl
  | If cond body ih =>
    simp [splitStmt]
    split
    split
    grind
  | Loop cond body ih =>
    simp [splitStmt]
    split
    split
    grind
  | Sequence head tail ih_head ih_tail =>
    simp [splitStmt]
    split
    split
    split
    split
    grind

-- main simulation lemma
-- assuming (stmt, s) straight-line-steps to t
-- then letting stmt_co be the output of splitStmt
-- (and a "well-formedness" hypothesis to constrain program to match the subroutines splitStmt created)
-- (as well as "hcont", which says that the continuation passed into splitStmt satisfies (cont, t) coroutine-steps to u)
-- either one of two cases
-- 1. the big-step of stmt didn't contain a suspend
--    in this case, we have that (stmt_co, s) coroutine-steps to t
-- 2. the big-step of stmt did contain a suspend
--    in this case, we have that (stmt_co, s) coroutine-steps to u, because
--    the yield that the suspend turned into "extends" the coroutine-step into a different subroutine,
--    which includes both the part of the straight-line-step following the suspend which ends up at t,
--    and the continuation which goes from t to u.
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
    ∃ outcome,
    (outcome = Outcome.Completed ∧ @CoroutineStep n k program (stmt_co, s) t outcome) ∨
    (outcome = Outcome.Yielded ∧ @CoroutineStep n k program (stmt_co, s) u outcome) := by
  induction hrun generalizing stmt cont subrs subr_index new_subr_index stmt_co s hwell_formed cont_outcome with
  | ShallowInstr id state =>
    -- this case is straightforward, ShallowInstr cannot contain a Suspend, so it's always in case 1
    -- and the semantics for ShallowInstr after splitting is totally equivalent;
    -- just need to compute through splitStmt to get that stmt_co is `StmtCo.ShallowInstr id`
    refine ⟨Outcome.Completed, ?_⟩
    simp
    have hstmt : stmt = StmtExt.ShallowInstr id := by
      subst hindex
      simp_all only [Prod.mk.injEq]
    subst stmt
    have hstate : state = s := by simp_all only [Prod.mk.injEq, true_and]
    subst state
    simp [splitStmt] at hsplit
    obtain ⟨stmt_co_is_shallowinstr, _, _⟩ := hsplit
    subst stmt_co
    apply CoroutineStep.ShallowInstr id s
  | Sequence A B a b c hA hB hA_ih hB_ih =>
    -- prologue here simplifies the context a bit to undo the generalization required for `induction`
    -- and remove redundant variables
    have hstmt : stmt = A; B := by
      subst hindex
      simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff]
    have ha : a = s := by
      subst hindex hstmt
      simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff, true_and]
    subst a
    subst stmt
    clear hcfg

    -- compute through two recursive calls to splitStmt in the `Sequence` case for splitStmt
    -- give the results names (`heq` hypothesis links these names to splitStmt applied to arguments)
    rw [splitStmt] at hsplit
    split at hsplit
    rename_i B_result B_stmt_co B_subrs B_subr_index B_hindex B_hlen B_heq
    split at hsplit
    rename_i A_result A_stmt_co A_subrs A_subr_index A_hindex A_hlen A_heq
    clear A_result B_result

    have hsubrs : subrs = B_subrs ++ A_subrs := by
      subst hindex
      simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff, Subtype.mk.injEq]
    subst subrs

    -- apply hB's inductive hypothesis first
    have hB_app := hB_ih
      B cont subr_index
      (by simp [countSuspendsStmt] at hbound; omega)
      b (by rfl)
      B_stmt_co B_subrs B_subr_index B_hindex B_hlen B_heq
      (by
        intro i hi
        have hidx : i < (B_subrs ++ A_subrs).length := by
          simp [List.length_append]
          omega
        have hidx_in_B := by
          apply List.getElem_append
          exact hidx
        simp only [hi, dif_pos] at hidx_in_B
        have hwell_formed_app := hwell_formed
          i (by assumption)
        simp [hwell_formed_app, hidx_in_B])
      cont_outcome hcont
    clear hB_ih

    obtain ⟨B_outcome, hB_co⟩ := hB_app

    cases B_outcome
    . simp at hB_co
      -- this is true, because if B_outcome is Yielded, then the continuation is "skipped"
      have hB_cont : @CoroutineStep n k program (StmtCo.Sequence B_stmt_co cont, b) u Outcome.Yielded := by
        apply CoroutineStep.SequenceEarlyYield B_stmt_co cont b u hB_co

      -- then, apply hA's inductive hypothesis
      simp at A_hindex B_hindex B_hlen
      simp [countSuspendsStmt] at hbound hindex
      have hA_app := hA_ih
        A (StmtCo.Sequence B_stmt_co cont) B_subr_index
        (by
          rw [B_hindex]
          omega)
        s (by rfl)
        A_stmt_co A_subrs A_subr_index A_hindex A_hlen A_heq
        (by
          intro i hi
          subst B_subr_index
          have hidx : B_subrs.length + i < (B_subrs ++ A_subrs).length := by
            simp [List.length_append]
            omega
          have hwell_formed_app := hwell_formed
            (B_subrs.length + i) (by omega)

          have hidx_in_A := List.getElem_append_right' B_subrs hi
          simp [B_hlen, Nat.add_comm, Nat.add_left_comm] at *
          exact hwell_formed_app)
        Outcome.Yielded hB_cont
      clear hA_ih

      obtain ⟨A_outcome, hA_co⟩ := hA_app

      cases A_outcome
      . simp at hA_co
        refine ⟨Outcome.Yielded, ?_⟩
        simp
        have stmt_co_is_seq : stmt_co = .Sequence A_stmt_co B_stmt_co := by
          subst hindex B_hindex A_hindex
          simp_all only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
        rw [stmt_co_is_seq]
        apply CoroutineStep.SequenceEarlyYield A_stmt_co B_stmt_co s u hA_co
      . simp at hA_co
        refine ⟨Outcome.Yielded, ?_⟩
        simp
        have stmt_co_is_seq : stmt_co = .Sequence A_stmt_co B_stmt_co := by
          subst hindex B_hindex A_hindex
          simp_all only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
        rw [stmt_co_is_seq]
        apply CoroutineStep.SequenceNormal A_stmt_co B_stmt_co s b u Outcome.Yielded hA_co hB_co

    . simp at hB_co
      -- otherwise, outcome for (B; cont) depends on outcome of cont
      have hB_cont : @CoroutineStep n k program (StmtCo.Sequence B_stmt_co cont, b) u cont_outcome := by
        apply CoroutineStep.SequenceNormal B_stmt_co cont b c u cont_outcome hB_co hcont

      -- then, apply hA's inductive hypothesis
      simp at A_hindex B_hindex B_hlen
      simp [countSuspendsStmt] at hbound hindex
      have hA_app := hA_ih
        A (StmtCo.Sequence B_stmt_co cont) B_subr_index
        (by
          rw [B_hindex]
          omega)
        s (by rfl)
        A_stmt_co A_subrs A_subr_index A_hindex A_hlen A_heq
        (by
          intro i hi
          subst B_subr_index
          have hidx : B_subrs.length + i < (B_subrs ++ A_subrs).length := by
            simp [List.length_append]
            omega
          have hwell_formed_app := hwell_formed
            (B_subrs.length + i) (by omega)

          have hidx_in_A := List.getElem_append_right' B_subrs hi
          simp [B_hlen, Nat.add_comm, Nat.add_left_comm] at *
          exact hwell_formed_app)
        cont_outcome hB_cont
      clear hA_ih

      obtain ⟨A_outcome, hA_co⟩ := hA_app

      cases A_outcome
      . simp at hA_co
        refine ⟨Outcome.Yielded, ?_⟩
        simp
        have stmt_co_is_seq : stmt_co = .Sequence A_stmt_co B_stmt_co := by
          subst hindex B_hindex A_hindex
          simp_all only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
        rw [stmt_co_is_seq]
        apply CoroutineStep.SequenceEarlyYield A_stmt_co B_stmt_co s u hA_co
      . simp at hA_co
        refine ⟨Outcome.Completed, ?_⟩
        simp
        have stmt_co_is_seq : stmt_co = .Sequence A_stmt_co B_stmt_co := by
          subst hindex B_hindex A_hindex
          simp_all only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
        rw [stmt_co_is_seq]
        apply CoroutineStep.SequenceNormal A_stmt_co B_stmt_co s b c Outcome.Completed hA_co hB_co



  | IfTrue cond body s' t' hcond hbody hbody_ih =>
    have hstmt : stmt = StmtExt.If cond body := by
      subst hindex
      simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff]
    have hs' : s' = s := by
      subst hindex hstmt
      simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff, true_and]
    subst s'
    subst stmt
    clear hcfg

    rw [splitStmt] at hsplit
    split at hsplit
    rename_i body_result body_stmt_co body_subrs body_subr_index body_hindex body_hlen body_heq
    clear body_result

    have hbody_ih_app := hbody_ih
      body cont subr_index
      (by simp [countSuspendsStmt] at hbound; omega)
      s (by rfl)
      body_stmt_co body_subrs body_subr_index
      body_hindex body_hlen body_heq
      (by
        have body_subrs_is_subrs : body_subrs = subrs := by
          subst hindex
          simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff, Subtype.mk.injEq]
        subst body_subrs
        exact hwell_formed)
      cont_outcome hcont
    clear hbody_ih

    have stmt_co_is_if : stmt_co = StmtCo.If cond body_stmt_co := by
      subst hindex
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq]

    obtain ⟨body_outcome, hbody_co⟩ := hbody_ih_app
    cases body_outcome
    . simp_all
      refine ⟨Outcome.Yielded, ?_⟩
      simp
      apply CoroutineStep.IfTrue
      . exact hcond
      . exact hbody_co
    . simp_all
      refine ⟨Outcome.Completed, ?_⟩
      simp
      apply CoroutineStep.IfTrue
      . exact hcond
      . exact hbody_co


  | IfFalse cond body s' hcond =>
    refine ⟨Outcome.Completed, ?_⟩
    simp
    have hstmt : stmt = StmtExt.If cond body := by
      subst hindex
      simp_all only [Prod.mk.injEq]
    subst stmt
    have hs' : s' = s := by simp_all only [Prod.mk.injEq, true_and]
    subst s'
    simp [splitStmt] at hsplit
    split at hsplit
    rename StmtCo => body_stmt_co
    have stmt_co_is_if : stmt_co = StmtCo.If cond body_stmt_co := by
      subst hindex
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq]
    subst stmt_co
    apply CoroutineStep.IfFalse
    exact hcond
  | LoopContinue cond body s' t' u' hcond hbody hrest hbody_ih hrest_ih =>
    have hstmt : stmt = StmtExt.Loop cond body := by
      subst hindex
      simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff]
    have hs' : s' = s := by
      subst hindex hstmt
      simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff, true_and]
    subst s'
    subst stmt
    clear hcfg

    have hrest_ih_app := hrest_ih
      (StmtExt.Loop cond body) cont subr_index hbound
      t' (by rfl)
      stmt_co subrs new_subr_index hindex hlen hsplit
      hwell_formed cont_outcome hcont
    clear hrest_ih

    rw [splitStmt] at hsplit
    split at hsplit
    rename_i body_result body_stmt_co body_subrs body_subr_index body_hindex body_hlen body_heq
    clear body_result

    have stmt_co_is_loop : stmt_co = StmtCo.Loop cond body_stmt_co := by
      subst hindex
      simp_all only [Prod.mk.injEq, Subtype.mk.injEq]
    subst stmt_co
    have subrs_is_body_subrs : subrs = body_subrs := by
      subst hindex
      simp_all only [Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff, Subtype.mk.injEq, true_and]
    subst subrs

    have body_invariance :
      (splitStmt body StmtCo.Skip subr_index
        (by simp [countSuspendsStmt] at hbound; assumption)).val.1
        = body_stmt_co := by
      have split_invariance := splitStmt_stmt_cont_invariant
        body
        StmtCo.Skip
        (StmtCo.Sequence (StmtCo.Loop cond (splitStmt body StmtCo.Skip subr_index hbound).val.1) cont)
        subr_index
        hbound
      rw [split_invariance]
      grind


    obtain ⟨rest_outcome, hrest_co⟩ := hrest_ih_app
    -- rest either goes from t' → u' (if rest completed) or t' → u (if rest yielded)
    rcases hrest_co with ⟨rfl, hrest_completed⟩ | ⟨rfl, hrest_yielded⟩
    . -- body was split (2nd time) using (Loop (...); cont) as continuation
      -- so we pass that into hbody_ih
      -- to make use of inductive hypothesis, we need to prove that (Loop (...); cont) takes t' → u
      have hrest_completed_then_cont :
        @CoroutineStep
          n k program
          (StmtCo.Sequence (StmtCo.Loop cond (splitStmt body StmtCo.Skip subr_index hbound).val.1) cont, t') u cont_outcome := by
           rw [body_invariance]
           exact CoroutineStep.SequenceNormal
            _ cont t' u' u
            cont_outcome hrest_completed hcont

      have hbody_ih_app := hbody_ih
        body
        (StmtCo.Sequence (StmtCo.Loop cond (splitStmt body StmtCo.Skip subr_index hbound).val.1) cont)
        subr_index
        (by simp [countSuspendsStmt] at hbound; omega)
        s (by rfl)
        body_stmt_co body_subrs body_subr_index
        body_hindex body_hlen body_heq
        hwell_formed
        cont_outcome hrest_completed_then_cont
      clear hbody_ih

      obtain ⟨body_outcome, hbody_co⟩ := hbody_ih_app
      rcases hbody_co with ⟨rfl, hbody_completed⟩ | ⟨rfl, hbody_yielded⟩
      . refine ⟨Outcome.Completed, Or.inl ⟨rfl, ?_⟩⟩
        exact CoroutineStep.LoopContinueNormal
          cond body_stmt_co s t' u'
          hcond Outcome.Completed hbody_completed hrest_completed
      . refine ⟨Outcome.Yielded, Or.inr ⟨rfl, ?_⟩⟩
        exact CoroutineStep.LoopEarlyYield cond body_stmt_co s u hcond hbody_yielded
    . have itwantsthis :
        @CoroutineStep
          n k program
          (StmtCo.Sequence (StmtCo.Loop cond (splitStmt body StmtCo.Skip subr_index hbound).val.1) cont, t') u Outcome.Yielded := by
          rw [body_invariance]; clear body_invariance
          exact CoroutineStep.SequenceEarlyYield _ cont t' u hrest_yielded

      -- Apply hbody_ih with cont_outcome = Yielded (NOT the outer cont_outcome).
      have hbody_ih_app := hbody_ih body _
        subr_index (by simp [countSuspendsStmt] at hbound; omega)
        s (by rfl)
        body_stmt_co body_subrs body_subr_index
        body_hindex body_hlen body_heq
        hwell_formed
        Outcome.Yielded itwantsthis
      clear hbody_ih

      obtain ⟨body_outcome, hbody_co⟩ := hbody_ih_app
      rcases hbody_co with ⟨rfl, hbody_completed⟩ | ⟨rfl, hbody_yielded⟩
      . -- body completed at t', rest yielded at u: LoopContinueNormal w/ Yielded.
        refine ⟨Outcome.Yielded, Or.inr ⟨rfl, ?_⟩⟩
        exact CoroutineStep.LoopContinueNormal
          cond body_stmt_co s t' u
          hcond Outcome.Yielded
          hbody_completed hrest_yielded

      . refine ⟨Outcome.Yielded, Or.inr ⟨rfl, ?_⟩⟩
        exact CoroutineStep.LoopEarlyYield cond body_stmt_co s u hcond hbody_yielded

  | LoopTerminate cond body s' hcond =>
    refine ⟨Outcome.Completed, ?_⟩
    simp
    have hstmt : stmt = StmtExt.Loop cond body := by
      subst hindex
      simp_all only [Prod.mk.injEq]
    subst stmt
    have hs' : s' = s := by simp_all only [Prod.mk.injEq, true_and]
    subst s'
    simp [splitStmt] at hsplit
    split at hsplit
    rename StmtCo => body_stmt_co
    have stmt_co_is_if : stmt_co = StmtCo.Loop cond body_stmt_co := by
      subst hindex
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq]
    subst stmt_co
    apply CoroutineStep.LoopTerminate
    exact hcond
  | Suspend st =>
    refine ⟨Outcome.Yielded, ?_⟩
    simp
    have st_is_s : st = s := by
      subst hindex
      simp_all only [Prod.mk.injEq]
    subst st
    have hstmt : stmt = StmtExt.Suspend := by
      subst hindex
      simp_all only [Prod.mk.injEq, and_true]
    subst stmt
    clear hcfg
    simp [splitStmt] at hsplit
    obtain ⟨stmt_co_is_yield, subrs_is_cont, subr_index_inc⟩ := hsplit
    subst stmt_co
    subst subrs
    apply CoroutineStep.Yield _ _ _ cont_outcome
    simp
    have hcont_matches : program.subroutines[subr_index]'(by rw [program.hsubr_count]; omega) = cont :=
      hwell_formed 0 (by simp)
    rw [hcont_matches]
    exact hcont

-- ==========================================================================
-- Top-level theorem: split preserves big-step semantics.
-- ==========================================================================

-- "for all straight-line programs that halt, the final state is equal to the split program run using coroutine semantics"
theorem splitPreservesSemantics
  (program : @ProgramExt n)
  (initial_state: List (Fin n))
  (final_state: List (Fin n))
  (hrun : StraightLineStep (program.stmt, ⟨initial_state⟩) ⟨final_state⟩)
  (split_program : @ProgramCo n (countSuspendsStmt program.stmt))
  (hsplit_program : split_program = split program):
  ∃outcome,
  @CoroutineStep
    n (countSuspendsStmt program.stmt)
    split_program
    (split_program.main, ⟨initial_state⟩) ⟨final_state⟩
    outcome := by
  have splitStmtSimulation_app := splitStmtSimulation
    split_program
    program.stmt
    StmtCo.Skip
    0
    (by omega)
    ⟨initial_state⟩
    ⟨final_state⟩
    ⟨final_state⟩
    (program.stmt, ⟨initial_state⟩)
    (by rfl)
    hrun
    split_program.main
    split_program.subroutines
    (countSuspendsStmt program.stmt)
    (by simp)
    split_program.hsubr_count
    (by
      rw [split] at hsplit_program
      split at hsplit_program
      rename_i hindex hlen heq
      simp at hindex
      simp [heq, hsplit_program, hindex])
    (by intros; simp)
    Outcome.Completed
    (by apply CoroutineStep.Skip)
  grind
