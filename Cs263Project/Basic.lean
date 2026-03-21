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
    (cases: Fin num_cases → List StmtExt)
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
    (cases: Fin num_cases → List StmtCo)
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
  subroutines: Vector (List (@StmtCo n k)) k

inductive StraightLineStep : (List StmtExt × State) → (List StmtExt × State) → Prop where
| ShallowInstr (id: Fin n) rest state :
  StraightLineStep (StmtExt.ShallowInstr id :: rest, state) (rest, state.update id)
| Switch num_cases cond cases i rest state (hi: cond state.trace i) :
  StraightLineStep (StmtExt.Switch num_cases cond cases :: rest, state) (cases i ++ rest, state)
| LoopContinue cond body rest state (hcond: cond state.trace) :
  StraightLineStep (StmtExt.Loop cond body :: rest, state) (body ++ [StmtExt.Loop cond body] ++ rest, state)
| LoopTerminate cond body rest state (hcond: ¬cond state.trace) :
  StraightLineStep (StmtExt.Loop cond body :: rest, state) (rest, state)
| Suspend rest state :
  StraightLineStep (StmtExt.Suspend :: rest, state) (rest, state)

inductive CoroutineStep {program: @ProgramCo n k} : (List (@StmtCo n k) × (@StateCo n k)) → (List (@StmtCo n k) × (@StateCo n k)) → Prop where
| ShallowInstr (id: Fin n) rest state :
  CoroutineStep (StmtCo.ShallowInstr id :: rest, state) (rest, state.update id)
| Switch num_cases cond cases i rest state (hi: cond state.trace i) :
  CoroutineStep (StmtCo.Switch num_cases cond cases :: rest, state) (cases i ++ rest, state)
| LoopContinue cond body rest state (hcond: cond state.trace) :
  CoroutineStep (StmtCo.Loop cond body :: rest, state) (body ++ [StmtCo.Loop cond body] ++ rest, state)
| LoopTerminate cond body rest state (hcond: ¬cond state.trace) :
  CoroutineStep (StmtCo.Loop cond body :: rest, state) (rest, state)
| Yield (next: Option (Fin k)) rest state :
  CoroutineStep (StmtCo.Yield next :: rest, state) ([], state.setNext next)
| Schedule trace next :
  CoroutineStep ([], ⟨trace, Option.some next⟩) (program.subroutines[next], ⟨trace, Option.some next⟩)

-- use "direct unrolling" idea as first implementation

end
