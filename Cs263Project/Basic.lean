import Mathlib
import Aesop

set_option autoImplicit false

section
variable {n : ℕ}
variable {k : ℕ}

inductive StmtExt : Type where
  | ShallowInstr (id: Fin n)
  | Switch
    (num_cases: ℕ)
    (cond: List (Fin n) → Fin num_cases → Prop)
    (cases: List (List StmtExt))
  | Loop
    (cond: List (Fin n) → Prop)
    (body: List StmtExt)
  | Suspend

structure State where
  trace: List (Fin n)

def State.update (self: @State n) (id: Fin n) : @State n :=
  ⟨self.trace ++ [id]⟩

structure ProgramExt where
  stmts: List (@StmtExt n)

inductive StmtCo : Type where
  | ShallowInstr (id: Fin n)
  | Switch
    (num_cases: ℕ)
    (cond: List (Fin n) → Fin num_cases → Prop)
    (cases: List (List StmtCo))
  | Loop
    (cond: List (Fin n) → Prop)
    (body: List StmtCo)
  | Yield (next: Option (Fin k))

structure StateCo where
  trace: List (Fin n)
  next: Option (Fin k)

def StateCo.update (self: @StateCo n k) (id: Fin n) : @StateCo n k :=
  ⟨self.trace ++ [id], self.next⟩

def StateCo.setNext (self: @StateCo n k) (next: Option (Fin k)) : @StateCo n k :=
  ⟨self.trace, next⟩

structure ProgramCo where
  main: List (@StmtCo n k)
  subroutines: List (List (@StmtCo n k))
  hsubr_count: subroutines.length = k

inductive StraightLineStep : (List StmtExt × State) → (List StmtExt × State) → Prop where
| ShallowInstr (id: Fin n) rest state :
  StraightLineStep (StmtExt.ShallowInstr id :: rest, state) (rest, state.update id)
| Switch num_cases cond cases i rest state (hi: cond state.trace i) (hcases: cases.length = num_cases) :
  StraightLineStep (StmtExt.Switch num_cases cond cases :: rest, state) (cases[i.val] ++ rest, state)
| LoopContinue cond body rest state (hcond: cond state.trace) :
  StraightLineStep (StmtExt.Loop cond body :: rest, state) (body ++ [StmtExt.Loop cond body] ++ rest, state)
| LoopTerminate cond body rest state (hcond: ¬cond state.trace) :
  StraightLineStep (StmtExt.Loop cond body :: rest, state) (rest, state)
| Suspend rest state :
  StraightLineStep (StmtExt.Suspend :: rest, state) (rest, state)

inductive CoroutineStep {program: @ProgramCo n k} : (List (@StmtCo n k) × (@StateCo n k)) → (List (@StmtCo n k) × (@StateCo n k)) → Prop where
| ShallowInstr (id: Fin n) rest state :
  CoroutineStep (StmtCo.ShallowInstr id :: rest, state) (rest, state.update id)
| Switch num_cases cond cases i rest state (hi: cond state.trace i) (hcases: cases.length = num_cases) :
  CoroutineStep (StmtCo.Switch num_cases cond cases :: rest, state) (cases[i.val] ++ rest, state)
| LoopContinue cond body rest state (hcond: cond state.trace) :
  CoroutineStep (StmtCo.Loop cond body :: rest, state) (body ++ [StmtCo.Loop cond body] ++ rest, state)
| LoopTerminate cond body rest state (hcond: ¬cond state.trace) :
  CoroutineStep (StmtCo.Loop cond body :: rest, state) (rest, state)
| Yield (next: Option (Fin k)) rest state :
  CoroutineStep (StmtCo.Yield next :: rest, state) ([], state.setNext next)
| Schedule trace next :
  CoroutineStep ([], ⟨trace, Option.some next⟩) (program.subroutines[next]'(by have len := program.hsubr_count; simp [len]), ⟨trace, .none⟩)

-- use "direct unrolling" idea as first implementation

mutual
def countSuspendsStmt : @StmtExt n → ℕ
  | .ShallowInstr _ => 0
  | .Switch _ _ cases => countSuspendsListList cases
  | .Loop _ body => countSuspendsList body
  | .Suspend => 1

def countSuspendsList : List (@StmtExt n) → ℕ
  | [] => 0
  | s :: rest => countSuspendsStmt s + countSuspendsList rest

def countSuspendsListList : List (List (@StmtExt n)) → ℕ
  | [] => 0
  | l :: rest => countSuspendsList l + countSuspendsListList rest
end

def countSuspends (pext: @ProgramExt n) : ℕ :=
  countSuspendsList pext.stmts

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
mutual
def splitStmt (stmt: @StmtExt n) (cont: List (@StmtCo n k)) (subr_index: ℕ) (hbound: subr_index + countSuspendsStmt stmt ≤ k) :
  { result: (@StmtCo n k × List (List (@StmtCo n k)) × ℕ) // result.snd.snd = subr_index + countSuspendsStmt stmt ∧ result.snd.fst.length = countSuspendsStmt stmt } :=
  match stmt with
  | .ShallowInstr id => ⟨
    (StmtCo.ShallowInstr id, [], subr_index),
    by simp [countSuspendsStmt]
  ⟩
  | .Loop cond body =>
    -- to handle loops, we pass in an empty continuation so we can get the transformed body, then append
    -- that transformed_body + real cont onto the resulting subrs
    let ⟨⟨transformed_body, new_subrs, new_subr_index⟩, ⟨hindex, hlen⟩⟩ :=
      splitList body [] subr_index (by simp [countSuspendsStmt] at hbound; assumption)
    let unrolled_subrs := List.map (fun subr ↦ subr ++ transformed_body ++ cont) new_subrs
    ⟨
      (StmtCo.Loop cond transformed_body, unrolled_subrs, new_subr_index),
      by simp_all [countSuspendsStmt, unrolled_subrs]
    ⟩
  | .Suspend =>
    ⟨
      (StmtCo.Yield (.some ⟨subr_index, by simp [countSuspendsStmt] at hbound; assumption⟩), [cont], subr_index + 1),
      by simp [countSuspendsStmt]
    ⟩
  | .Switch num_cases cond cases =>
    let ⟨⟨transformed_cases, new_subrs, new_subr_index⟩, ⟨hindex, hlen⟩⟩ :=
      splitListList cases cont subr_index (by simp [countSuspendsStmt] at hbound; assumption)
    ⟨
      (StmtCo.Switch num_cases cond transformed_cases, new_subrs, new_subr_index),
      by simp_all [countSuspendsStmt]
    ⟩

def splitList (stmts: List (@StmtExt n)) (cont: List (@StmtCo n k)) (subr_index: ℕ) (hbound: subr_index + countSuspendsList stmts ≤ k):
  { result: (List (@StmtCo n k) × List (List (@StmtCo n k)) × ℕ) // result.snd.snd = subr_index + countSuspendsList stmts ∧ result.snd.fst.length = countSuspendsList stmts } :=
  match stmts with
  | [] => ⟨
    ([], [], subr_index),
    by simp [countSuspendsList]
  ⟩
  | head :: tail =>
    let ⟨⟨transformed_stmts_tail, new_subrs_tail, new_subr_index_tail⟩, ⟨hindex_tail, hlen_tail⟩⟩ :=
      splitList tail cont subr_index (by simp [countSuspendsList] at hbound; omega)
    let ⟨⟨transformed_stmt, new_subrs, new_subr_index⟩, ⟨hindex_head, hlen_head⟩⟩ :=
      splitStmt head (transformed_stmts_tail ++ cont) new_subr_index_tail (by simp_all [countSuspendsList]; omega)
    ⟨
      (transformed_stmt :: transformed_stmts_tail, new_subrs_tail ++ new_subrs, new_subr_index),
      by
        simp_all [countSuspendsList]
        constructor
        . ac_rfl
        . omega
    ⟩

def splitListList (stmts: List (List (@StmtExt n))) (cont: List (@StmtCo n k)) (subr_index: ℕ) (hbound: subr_index + countSuspendsListList stmts ≤ k):
  { result: (List (List (@StmtCo n k)) × List (List (@StmtCo n k)) × ℕ) // result.snd.snd = subr_index + countSuspendsListList stmts ∧ result.snd.fst.length = countSuspendsListList stmts } :=
  match stmts with
  | [] => ⟨
    ([], [], subr_index),
    by simp [countSuspendsListList]
  ⟩
  | head :: tail =>
    let ⟨⟨transformed_stmts_tail, new_subrs_tail, new_subr_index_tail⟩, ⟨hindex_tail, hlen_tail⟩⟩ :=
      splitListList tail cont subr_index (by simp [countSuspendsListList] at hbound; omega)
    let ⟨⟨transformed_stmts, new_subrs, new_subr_index⟩, ⟨hindex_head, hlen_head⟩⟩ :=
      splitList head cont new_subr_index_tail (by simp_all [countSuspendsListList]; omega)
    ⟨
      (transformed_stmts :: transformed_stmts_tail, new_subrs_tail ++ new_subrs, new_subr_index),
      by
        simp_all [countSuspendsListList]
        constructor
        . ac_rfl
        . omega
    ⟩

end

def split (orig: @ProgramExt n) : @ProgramCo n (countSuspends orig) :=
  let k := countSuspends orig
  let ⟨⟨stmts, subrs, _⟩, ⟨_, hlen⟩⟩ :=
    @splitList n k orig.stmts [] 0 (by simp [countSuspends, k])
  @ProgramCo.mk n k stmts (subrs) (by simp_all; rfl)

abbrev StraightLineRTC := Relation.ReflTransGen (@StraightLineStep n)
abbrev CoroutineRTC (program: @ProgramCo n k) := Relation.ReflTransGen (@CoroutineStep n k program)

infixr:100 " ⇒ " => StraightLineStep
infixr:100 " ⇒* " => StraightLineRTC

#check Relation.ReflTransGen.refl

-- "for all straight-line programs that halt, the final state is equal to the split program run using coroutine semantics"
-- include initial_state to reflect to model (external) inputs to program
theorem splitPreservesSemantics :
  ∀ (program : @ProgramExt n)
    (initial_state: List (Fin n))
    (final_state: List (Fin n))
    (hhalts: (program.stmts, ⟨initial_state⟩) ⇒* ([], ⟨final_state⟩)),
  have split_program := (split program)
  CoroutineRTC (split_program) (split_program.main, ⟨[], .none⟩) ([], ⟨final_state, .none⟩) := by

  intro original_program final_state hhalts split_program

  sorry

-- helper lemmas


-- if the `List (@StmtCo n k)` created by `splitList` is executed with initial state `⟨initial_trace, .none⟩`, it completely matches
-- the behavior of `List (@StmtExt n)` passed into `splitList` with initial state `⟨initial_trace, .none⟩`
-- if `stmts` doesn't contain any suspends, this should basically be trivial

lemma splitListSimulation
  (stmts : List (@StmtExt n))
  (cont : List (@StmtCo n k))
  (subr_index : ℕ)
  (hbound : subr_index + countSuspendsList stmts ≤ k)
  (program : @ProgramCo n k)
  {result : List (@StmtCo n k)}
  {coros : List (List (@StmtCo n k))}
  {new_subr_index : ℕ}
  (h_split : (splitList stmts cont subr_index hbound).val = (result, coros, new_subr_index))
  (h_subrs : program.subroutines.extract subr_index (countSuspendsList stmts) = coros)
  (initial_trace final_trace : List (Fin n))
  (hrun : (stmts, (⟨initial_trace⟩ : @State n)) ⇒* ([], ⟨final_trace⟩)) :
  CoroutineRTC program
    (result ++ cont, ⟨initial_trace, .none⟩)
    (cont, ⟨final_trace, .none⟩) :=
  by
    cases hrun with
    | refl =>
      simp [splitList] at h_split
      simp [h_split]
      exact Relation.ReflTransGen.refl
    | tail previous_steps final_step =>
      rename_i final_step_config
      sorry


lemma splitStmtSimulation
  (stmt: @StmtExt n)
  (cont: List (@StmtCo n k))
  (subr_index: ℕ)
  (hbound: subr_index + countSuspendsStmt stmt ≤ k)

  (program : @ProgramCo n k)
  (h_subrs : Prop /- not sure how to express this? -/)
  (initial_trace final_trace : List (Fin n))
  (hrun : ([stmt], ⟨initial_trace⟩) ⇒* ([], ⟨final_trace⟩)) :
  have ⟨⟨result, coros, _⟩, ⟨_, _⟩⟩ := splitStmt stmt cont subr_index hbound
  CoroutineRTC program
    ([result] ++ cont, ⟨initial_trace, .none⟩)
    (cont, ⟨final_trace, .none⟩) :=
  by
    sorry

lemma splitListListSimulation
  (stmts: List (List (@StmtExt n)))
  (cont: List (@StmtCo n k))
  (subr_index: ℕ)
  (hbound: subr_index + countSuspendsListList stmts ≤ k)

  (program: @ProgramCo n k)
  (h_subrs: Prop /- not sure how to express this? -/)
  (initial_trace : List (Fin n))
  (final_trace : List (Fin n))
  (hruns : Prop) :
  have ⟨⟨result, coros, _⟩, ⟨_, _⟩⟩ := splitListList stmts cont subr_index hbound
  CoroutineRTC program
    ([result] ++ cont, ⟨initial_trace, .none⟩)
    (cont, ⟨final_trace, .none⟩) :=
  by
    sorry
