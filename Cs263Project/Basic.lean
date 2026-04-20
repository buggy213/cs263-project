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
  (initial_state final_state : State)
  (initial_config : (@StmtExt n × @State n))
  (hinitial_config : initial_config.1 = stmt ∧ initial_config.2 = initial_state)
  (hrun : StraightLineStep initial_config final_state) :
  have ⟨⟨result, subrs, new_subr_index⟩, ⟨hindex, hlen⟩⟩ := splitStmt stmt cont subr_index hbound

  @CoroutineStep
    n k program
    (result, ⟨initial_state.trace⟩)
    ⟨final_state.trace⟩ :=
  by
    induction hrun generalizing stmt initial_state cont subr_index with
    | ShallowInstr id state =>
      obtain ⟨hstmt, hstate⟩ := hinitial_config
      subst stmt
      simp_all [splitStmt]

      split
      rename_i
        packed_result
        result
        subrs
        new_subr_index
        hindex
        hlen
        heq

      have result_is_shallowinstr : result = StmtCo.ShallowInstr id :=
        by aesop

      rw [result_is_shallowinstr]
      have h := @CoroutineStep.ShallowInstr n k program id ⟨state.trace⟩
      aesop

    | Sequence A B a b c hA hB hA_ih hB_ih =>
      obtain ⟨hstmt, hstate⟩ := hinitial_config
      subst stmt

      split
      rename_i
        result
        stmt_co
        subrs
        new_subr_index
        hindex
        hlen
        heq

      simp [splitStmt] at heq

      split at heq
      rename_i
        tail_result
        tail_stmt_co
        tail_subrs
        tail_subr_index
        tail_hindex
        tail_hlen
        tail_heq

      split at heq
      rename_i
        head_result
        head_stmt_co
        head_subrs
        head_subr_index
        head_hindex
        head_hlen
        head_heq

      simp_all

      have stmt_co_is_sequence : stmt_co = StmtCo.Sequence head_stmt_co tail_stmt_co :=
        by grind
      rw [stmt_co_is_sequence]

      have hB_app := hB_ih B cont subr_index (by simp [countSuspendsStmt] at hbound; omega) (by rfl)
      split at hB_app
      rename_i hB_heq
      rename StmtCo => hB_stmt_co
      have hB_stmt_co_is_tail_stmt_co : hB_stmt_co = tail_stmt_co := by aesop

      have tail_stmt_co_step :
        @CoroutineStep n k program (tail_stmt_co, ⟨b.trace⟩) ⟨c.trace⟩ :=
        by aesop

      have hA_app := hA_ih A (StmtCo.Sequence tail_stmt_co cont) tail_subr_index (by simp [countSuspendsStmt] at hbound; simp at tail_hindex; omega) (by rfl)
      split at hA_app
      rename_i hA_heq
      rename StmtCo => hA_stmt_co
      have hA_stmt_co_is_head_stmt_co : hA_stmt_co = head_stmt_co := by aesop


      have head_stmt_co_step :
        @CoroutineStep n k program (head_stmt_co, ⟨initial_state.trace⟩) ⟨b.trace⟩ :=
        by aesop

      apply CoroutineStep.Sequence
        head_stmt_co tail_stmt_co
        ⟨initial_state.trace⟩ ⟨b.trace⟩ ⟨c.trace⟩
        head_stmt_co_step tail_stmt_co_step

    | IfTrue cond then_body s t hcond hbody hbody_ih =>
      simp_all
      obtain ⟨hstmt, hstate⟩ := hinitial_config
      clear s hstate final_state
      rename' t => final_state
      subst stmt

      split
      rename_i
        result
        head_stmt_co
        head_subrs
        head_subr_index
        head_hindex
        head_hlen
        head_heq

      simp at head_hlen head_hindex
      simp [splitStmt] at head_heq
      split at head_heq
      rename_i
        tail_result
        tail_stmt_co
        tail_subrs
        tail_subr_index
        tail_hindex
        tail_hlen
        tail_heq

      have head_stmt_co_is_if : head_stmt_co = StmtCo.If cond tail_stmt_co := by aesop
      subst head_stmt_co

      apply CoroutineStep.IfTrue
      . aesop
      . have hbody_ih_app := hbody_ih then_body cont subr_index (by simp [countSuspendsStmt] at hbound; omega) (by rfl)
        aesop

    | IfFalse cond then_body s hcond =>
      simp_all
      obtain ⟨hstmt, hstate⟩ := hinitial_config
      clear s hstate final_state
      subst stmt

      split
      rename_i
        result
        head_stmt_co
        head_subrs
        head_subr_index
        head_hindex
        head_hlen
        head_heq

      simp [splitStmt] at head_heq
      split at head_heq
      rename_i
        body_result
        body_stmt_co
        body_subrs
        body_subr_index
        body_hindex
        body_hlen
        body_heq

      have head_stmt_co_is_if : head_stmt_co = StmtCo.If cond body_stmt_co := by aesop
      subst head_stmt_co
      apply CoroutineStep.IfFalse
      . aesop

    | LoopContinue cond body s t u hcond hbody hrest hbody_ih hrest_ih =>
      simp at hinitial_config hbody_ih ⊢
      obtain ⟨hstmt, hstate⟩ := hinitial_config
      subst s
      clear final_state
      rename' u => final_state
      subst stmt

      split
      rename_i
        result
        stmt_co
        subrs
        new_subr_index
        hindex
        hlen
        heq

      simp [splitStmt] at heq
      split at heq
      rename_i
        body_result
        body_stmt_co
        body_subrs
        body_subr_index
        body_hindex
        body_hlen
        body_heq

      have stmt_co_is_loop : stmt_co = StmtCo.Loop cond body_stmt_co := by aesop
      subst stmt_co

      apply CoroutineStep.LoopContinue _ _ _ ⟨t.trace⟩
      . aesop
      . have hbody_ih_app := hbody_ih body StmtCo.Skip subr_index (by simp [countSuspendsStmt] at hbound; omega) (by rfl)
        aesop
      . have hrest_ih_app := hrest_ih (StmtExt.Loop cond body) cont subr_index (by assumption) t (by constructor <;> rfl)
        split at hrest_ih_app
        rename_i heq'
        rename StmtCo => stmt_co'
        simp [splitStmt] at heq'
        split at heq'
        aesop
    | LoopTerminate cond body s hcond =>
      simp_all
      obtain ⟨hstmt, hstate⟩ := hinitial_config
      subst s
      clear final_state
      subst stmt
      split
      rename_i
        result
        stmt_co
        subrs
        new_subr_index
        hindex
        hlen
        heq

      simp [splitStmt] at heq
      split at heq
      rename_i
        body_result
        body_stmt_co
        body_subrs
        body_subr_index
        body_hindex
        body_hlen
        body_heq

      have stmt_co_is_loop : stmt_co = StmtCo.Loop cond body_stmt_co := by aesop
      subst stmt_co
      apply CoroutineStep.LoopTerminate
      . aesop
    | Suspend s =>

      sorry
