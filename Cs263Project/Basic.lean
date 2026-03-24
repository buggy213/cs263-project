import Aesop

set_option autoImplicit false

section
variable {n : Nat}
variable {k : Nat}

inductive StmtExt : Type where
  | ShallowInstr (id: Fin n)
  | Switch
    (num_cases: Nat)
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
    (num_cases: Nat)
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
  CoroutineStep ([], ⟨trace, Option.some next⟩) (program.subroutines[next]'(by have len := program.hsubr_count; rw [len]; simp), ⟨trace, Option.some next⟩)

-- use "direct unrolling" idea as first implementation

mutual
def countSuspendsStmt : @StmtExt n → Nat
  | .ShallowInstr _ => 0
  | .Switch _ _ cases => countSuspendsListList cases
  | .Loop _ body => countSuspendsList body
  | .Suspend => 1

def countSuspendsList : List (@StmtExt n) → Nat
  | [] => 0
  | s :: rest => countSuspendsStmt s + countSuspendsList rest

def countSuspendsListList : List (List (@StmtExt n)) → Nat
  | [] => 0
  | l :: rest => countSuspendsList l + countSuspendsListList rest
end

def countSuspends (pext: @ProgramExt n) : Nat :=
  countSuspendsList pext.stmts

mutual
-- splitStmt turns a single statement (StmtExt) + the (already transformed) continuation of what comes
-- after this statement (StmtCo) + current subroutine index
-- and returns the transformed statement (Option StmtExt) or a new subroutine (if it was a suspend) +
-- any subroutines that were created + updated subroutine index
def splitStmt (stmt: @StmtExt n) (cont: List (@StmtCo n k)) (subr_index: Nat) (hbound: subr_index + countSuspendsStmt stmt ≤ k) :
  { result: (@StmtCo n k × List (List (@StmtCo n k)) × Nat) // result.snd.snd = subr_index + countSuspendsStmt stmt ∧ result.snd.fst.length = countSuspendsStmt stmt } :=
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
      by
        simp
        simp at hindex
        simp at hlen
        simp [countSuspendsStmt]
        constructor
        . assumption
        . subst hindex
          simp_all only [List.append_assoc, List.length_map, unrolled_subrs]
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
      by
        simp
        simp at hindex
        simp at hlen
        simp [countSuspendsStmt]
        constructor
        . assumption
        . assumption
    ⟩

-- splitList turns a list of statements (StmtExt) + the (already transformed) continuation of what comes
-- after this list of statements (StmtCo) + current subroutine index
-- and returns the list of statements (StmtCo) + any subroutines that were created + the next subroutine index
def splitList (stmts: List (@StmtExt n)) (cont: List (@StmtCo n k)) (subr_index: Nat) (hbound: subr_index + countSuspendsList stmts ≤ k):
  { result: (List (@StmtCo n k) × List (List (@StmtCo n k)) × Nat) // result.snd.snd = subr_index + countSuspendsList stmts ∧ result.snd.fst.length = countSuspendsList stmts } :=
  match stmts with
  | [] => ⟨
    ([], [], subr_index),
    by simp [countSuspendsList]
  ⟩
  | head :: tail =>
    let ⟨⟨transformed_stmts_tail, new_subrs_tail, new_subr_index_tail⟩, ⟨hindex_tail, hlen_tail⟩⟩ :=
      splitList tail cont subr_index (by simp [countSuspendsList] at hbound; omega)
    let ⟨⟨transformed_stmt, new_subrs, new_subr_index⟩, ⟨hindex_head, hlen_head⟩⟩ :=
      splitStmt head (transformed_stmts_tail ++ cont) new_subr_index_tail (by simp at hindex_tail; rw [hindex_tail]; simp [countSuspendsList] at hbound; omega)
    ⟨
      (transformed_stmt :: transformed_stmts_tail, new_subrs_tail ++ new_subrs, new_subr_index),
      by
        simp
        simp at hindex_tail
        simp at hindex_head
        simp at hlen_tail
        simp at hlen_head
        rw [hindex_head, hindex_tail]
        rw [countSuspendsList]
        constructor
        . ac_rfl
        . omega
    ⟩

-- splitListList turns a list of list of statements (StmtExt) + the (already transformed) continuation of what postdominates
-- all of these cases (this is used for switch-cases) + current subroutine index
-- and returns the list of list of statements (StmtCo) + any subroutines that were created + the next subroutine index
def splitListList (stmts: List (List (@StmtExt n))) (cont: List (@StmtCo n k)) (subr_index: Nat) (hbound: subr_index + countSuspendsListList stmts ≤ k):
  { result: (List (List (@StmtCo n k)) × List (List (@StmtCo n k)) × Nat) // result.snd.snd = subr_index + countSuspendsListList stmts ∧ result.snd.fst.length = countSuspendsListList stmts } :=
  match stmts with
  | [] => ⟨
    ([], [], subr_index),
    by simp [countSuspendsListList]
  ⟩
  | head :: tail =>
    let ⟨⟨transformed_stmts_tail, new_subrs_tail, new_subr_index_tail⟩, ⟨hindex_tail, hlen_tail⟩⟩ :=
      splitListList tail cont subr_index (by simp [countSuspendsListList] at hbound; omega)
    let ⟨⟨transformed_stmts, new_subrs, new_subr_index⟩, ⟨hindex_head, hlen_head⟩⟩ :=
      splitList head cont new_subr_index_tail (by simp at hindex_tail; rw [hindex_tail]; simp [countSuspendsListList] at hbound; omega)
    ⟨
      (transformed_stmts :: transformed_stmts_tail, new_subrs_tail ++ new_subrs, new_subr_index),
      by
        simp
        simp at hindex_head
        simp at hindex_tail
        simp at hlen_head
        simp at hlen_tail
        rw [hindex_head, hindex_tail]
        rw [countSuspendsListList]
        constructor
        . ac_rfl
        . omega
    ⟩

end


def split (orig: @ProgramExt n) : @ProgramCo n (countSuspends orig + 1) :=
  let k := countSuspends orig + 1
  let ⟨⟨stmts, subrs, _⟩, ⟨_, hlen⟩⟩ :=
    @splitList n k orig.stmts [] 0 (by simp [countSuspends, k])
  @ProgramCo.mk n k (subrs ++ [stmts]) (by simp_all; rfl)
