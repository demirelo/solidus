import EvmCompiler.Structured.Semantics
import EvmCompiler.Assembly.GasParametric

namespace EvmCompiler
namespace Structured

abbrev GasOracle := Assembly.GasParametric.GasOracle

namespace BasicOp

def stepWithGasOracle (op : BasicOp)
    (oracle : GasOracle) (cursor : Nat)
    (state : EVMState) : Except EVMException (EVMState × Nat) :=
  Assembly.GasParametric.Target.stepInstrWithGasOracle oracle cursor
    (.prim op.toPrimOp) state

end BasicOp

namespace BasicInstr

def stepWithGasOracle (instr : BasicInstr)
    (oracle : GasOracle) (cursor : Nat)
    (state : EVMState) : Except EVMException (EVMState × Nat) :=
  match instr with
  | .push value =>
      Assembly.GasParametric.Target.stepInstrWithGasOracle oracle cursor
        (.push32 value) state
  | BasicInstr.op basicOp =>
      basicOp.stepWithGasOracle oracle cursor state

end BasicInstr

namespace Code

def runWithGasOracle :
    Code → GasOracle → Nat → EVMState →
      Except EVMException (EVMState × Nat)
  | [], _oracle, cursor, state => .ok (state, cursor)
  | instr :: rest, oracle, cursor, state => do
      let (state', cursor') ← instr.stepWithGasOracle oracle cursor state
      runWithGasOracle rest oracle cursor' state'

def runStateWithGasOracle (code : Code)
    (oracle : GasOracle) (cursor : Nat)
    (state : RunState) : Except EVMException (RunState × Nat) := do
  let (evm, cursor') ← runWithGasOracle code oracle cursor state.evm
  .ok (state.withEVM evm, cursor')

def runConditionWithGasOracle (code : Code)
    (oracle : GasOracle) (cursor : Nat)
    (state : EVMState) : Except EVMException (EVMState × Bool × Nat) := do
  let (state', cursor') ← runWithGasOracle code oracle cursor state
  let (stateAfterPop, cond) ← popCondition state'
  .ok (stateAfterPop, cond, cursor')

def runConditionStateWithGasOracle (code : Code)
    (oracle : GasOracle) (cursor : Nat)
    (state : RunState) : Except EVMException (RunState × Bool × Nat) := do
  let (evm, cond, cursor') ←
    runConditionWithGasOracle code oracle cursor state.evm
  .ok (state.withEVM evm, cond, cursor')

@[simp] theorem runWithGasOracle_nil
    (oracle : GasOracle) (cursor : Nat)
    (state : EVMState) :
    runWithGasOracle [] oracle cursor state = .ok (state, cursor) :=
  rfl

end Code

namespace Terminal

def stepWithGasOracle (kind : Assembly.HaltKind)
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (EVMState × Nat) :=
  Assembly.GasParametric.Target.stepInstrWithGasOracle oracle cursor
    (.prim kind.toPrimOp) state

end Terminal

namespace BasicOp

theorem stepWithGasOracle_cursor_le
    {op : BasicOp} {oracle : GasOracle} {cursor : Nat}
    {state state' : EVMState} {cursor' : Nat}
    (hStep : op.stepWithGasOracle oracle cursor state =
      .ok (state', cursor')) :
    cursor ≤ cursor' :=
  Assembly.GasParametric.Target.stepInstrWithGasOracle_cursor_le
    (by simpa [stepWithGasOracle] using hStep)

theorem stepWithGasOracle_withAnswer_of_run_le
    {op : BasicOp} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state state' : EVMState} {cursor' : Nat}
    (hRun : op.stepWithGasOracle oracle cursor state =
      .ok (state', cursor'))
    (hLe : cursor' ≤ answerCursor) :
    op.stepWithGasOracle
        (Assembly.GasParametric.GasOracle.withAnswer oracle answerCursor
          answer) cursor state =
      .ok (state', cursor') := by
  simpa [stepWithGasOracle] using
    Assembly.GasParametric.Target.stepInstrWithGasOracle_withAnswer_of_run_le
      (answer := answer) (by simpa [stepWithGasOracle] using hRun) hLe

end BasicOp

namespace BasicInstr

theorem stepWithGasOracle_cursor_le
    {instr : BasicInstr} {oracle : GasOracle} {cursor : Nat}
    {state state' : EVMState} {cursor' : Nat}
    (hStep : instr.stepWithGasOracle oracle cursor state =
      .ok (state', cursor')) :
    cursor ≤ cursor' := by
  cases instr with
  | push value =>
      exact
        Assembly.GasParametric.Target.stepInstrWithGasOracle_cursor_le
          (by simpa [stepWithGasOracle] using hStep)
  | op op =>
      exact BasicOp.stepWithGasOracle_cursor_le
        (by simpa [stepWithGasOracle] using hStep)

theorem stepWithGasOracle_withAnswer_of_run_le
    {instr : BasicInstr} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state state' : EVMState} {cursor' : Nat}
    (hRun : instr.stepWithGasOracle oracle cursor state =
      .ok (state', cursor'))
    (hLe : cursor' ≤ answerCursor) :
    instr.stepWithGasOracle
        (Assembly.GasParametric.GasOracle.withAnswer oracle answerCursor
          answer) cursor state =
      .ok (state', cursor') := by
  cases instr with
  | push value =>
      simpa [stepWithGasOracle] using
        Assembly.GasParametric.Target.stepInstrWithGasOracle_withAnswer_of_run_le
          (answer := answer) (by simpa [stepWithGasOracle] using hRun) hLe
  | op op =>
      exact BasicOp.stepWithGasOracle_withAnswer_of_run_le
        (answer := answer) (by simpa [stepWithGasOracle] using hRun) hLe

end BasicInstr

namespace Code

theorem runWithGasOracle_cursor_le
    {code : Code} {oracle : GasOracle} {cursor : Nat}
    {state state' : EVMState} {cursorFinal : Nat}
    (hRun : runWithGasOracle code oracle cursor state =
      .ok (state', cursorFinal)) :
    cursor ≤ cursorFinal := by
  induction code generalizing cursor state with
  | nil =>
      simp [runWithGasOracle] at hRun
      exact Nat.le_of_eq hRun.2
  | cons instr rest ih =>
      unfold runWithGasOracle at hRun
      cases hStep : instr.stepWithGasOracle oracle cursor state with
      | error err =>
          rw [hStep] at hRun
          simp [Bind.bind, Except.bind] at hRun
      | ok pair =>
          rcases pair with ⟨mid, cursorMid⟩
          have hLeStep := BasicInstr.stepWithGasOracle_cursor_le hStep
          rw [hStep] at hRun
          exact Nat.le_trans hLeStep (ih hRun)

theorem runStateWithGasOracle_cursor_le
    {code : Code} {oracle : GasOracle} {cursor : Nat}
    {state state' : RunState} {cursorFinal : Nat}
    (hRun : runStateWithGasOracle code oracle cursor state =
      .ok (state', cursorFinal)) :
    cursor ≤ cursorFinal := by
  unfold runStateWithGasOracle at hRun
  cases hCode : runWithGasOracle code oracle cursor state.evm with
  | error err =>
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind] at hRun
  | ok pair =>
      rcases pair with ⟨evm, cursor'⟩
      have hLeCode := runWithGasOracle_cursor_le hCode
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind] at hRun
      rcases hRun with ⟨_, hCursor⟩
      subst cursorFinal
      exact hLeCode

theorem runConditionWithGasOracle_cursor_le
    {code : Code} {oracle : GasOracle} {cursor : Nat}
    {state state' : EVMState} {cond : Bool} {cursorFinal : Nat}
    (hRun : runConditionWithGasOracle code oracle cursor state =
      .ok (state', cond, cursorFinal)) :
    cursor ≤ cursorFinal := by
  unfold runConditionWithGasOracle at hRun
  cases hCode : runWithGasOracle code oracle cursor state with
  | error err =>
      simp [hCode, Bind.bind, Except.bind] at hRun
  | ok pair =>
      rcases pair with ⟨mid, cursorMid⟩
      have hLeCode := runWithGasOracle_cursor_le hCode
      cases hPop : popCondition mid with
      | error err =>
          simp [hCode, hPop, Bind.bind, Except.bind] at hRun
      | ok pop =>
          rcases pop with ⟨stateAfterPop, cond'⟩
          simp [hCode, hPop, Bind.bind, Except.bind] at hRun
          rcases hRun with ⟨_, _, hCursor⟩
          subst cursorFinal
          exact hLeCode

theorem runConditionStateWithGasOracle_cursor_le
    {code : Code} {oracle : GasOracle} {cursor : Nat}
    {state state' : RunState} {cond : Bool} {cursorFinal : Nat}
    (hRun : runConditionStateWithGasOracle code oracle cursor state =
      .ok (state', cond, cursorFinal)) :
    cursor ≤ cursorFinal := by
  unfold runConditionStateWithGasOracle at hRun
  cases hCond :
      runConditionWithGasOracle code oracle cursor state.evm with
  | error err =>
      rw [hCond] at hRun
      simp [Bind.bind, Except.bind] at hRun
  | ok result =>
      rcases result with ⟨evm, cond', cursor'⟩
      have hLeCond := runConditionWithGasOracle_cursor_le hCond
      rw [hCond] at hRun
      simp [Bind.bind, Except.bind] at hRun
      rcases hRun with ⟨_, _, hCursor⟩
      subst cursorFinal
      exact hLeCond

theorem runWithGasOracle_withAnswer_of_run_le
    {code : Code} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state state' : EVMState} {cursorFinal : Nat}
    (hRun : runWithGasOracle code oracle cursor state =
      .ok (state', cursorFinal))
    (hLe : cursorFinal ≤ answerCursor) :
    runWithGasOracle code
        (Assembly.GasParametric.GasOracle.withAnswer oracle answerCursor
          answer) cursor state =
      .ok (state', cursorFinal) := by
  induction code generalizing cursor state with
  | nil =>
      simp [runWithGasOracle] at hRun ⊢
      exact hRun
  | cons instr rest ih =>
      unfold runWithGasOracle at hRun ⊢
      cases hStep : instr.stepWithGasOracle oracle cursor state with
      | error err =>
          rw [hStep] at hRun
          simp [Bind.bind, Except.bind] at hRun
      | ok pair =>
          rcases pair with ⟨mid, cursorMid⟩
          rw [hStep] at hRun
          have hTailLe := runWithGasOracle_cursor_le hRun
          have hStepLe : cursorMid ≤ answerCursor :=
            Nat.le_trans hTailLe hLe
          have hStepExtend :=
            BasicInstr.stepWithGasOracle_withAnswer_of_run_le
              (answer := answer) hStep hStepLe
          rw [hStepExtend]
          exact ih (hRun := hRun)

theorem runStateWithGasOracle_withAnswer_of_run_le
    {code : Code} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state state' : RunState} {cursorFinal : Nat}
    (hRun : runStateWithGasOracle code oracle cursor state =
      .ok (state', cursorFinal))
    (hLe : cursorFinal ≤ answerCursor) :
    runStateWithGasOracle code
        (Assembly.GasParametric.GasOracle.withAnswer oracle answerCursor
          answer) cursor state =
      .ok (state', cursorFinal) := by
  unfold runStateWithGasOracle at hRun ⊢
  cases hCode : runWithGasOracle code oracle cursor state.evm with
  | error err =>
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind] at hRun
  | ok pair =>
      rcases pair with ⟨evm, cursor'⟩
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind] at hRun
      rcases hRun with ⟨hState, hCursor⟩
      subst state'
      subst cursorFinal
      have hCodeExtend :=
        runWithGasOracle_withAnswer_of_run_le
          (answer := answer) hCode hLe
      rw [hCodeExtend]
      simp [Bind.bind, Except.bind]

theorem runConditionWithGasOracle_withAnswer_of_run_le
    {code : Code} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state state' : EVMState} {cond : Bool} {cursorFinal : Nat}
    (hRun : runConditionWithGasOracle code oracle cursor state =
      .ok (state', cond, cursorFinal))
    (hLe : cursorFinal ≤ answerCursor) :
    runConditionWithGasOracle code
        (Assembly.GasParametric.GasOracle.withAnswer oracle answerCursor
          answer) cursor state =
      .ok (state', cond, cursorFinal) := by
  unfold runConditionWithGasOracle at hRun ⊢
  cases hCode : runWithGasOracle code oracle cursor state with
  | error err =>
      rw [hCode] at hRun
      simp [Bind.bind, Except.bind] at hRun
  | ok pair =>
      rcases pair with ⟨mid, cursorMid⟩
      rw [hCode] at hRun
      cases hPop : popCondition mid with
      | error err =>
          simp [Bind.bind, Except.bind, hPop] at hRun
      | ok pop =>
          rcases pop with ⟨stateAfterPop, cond'⟩
          simp [Bind.bind, Except.bind, hPop] at hRun
          rcases hRun with ⟨hState, hCond, hCursor⟩
          subst state'
          subst cond
          subst cursorFinal
          have hCodeExtend :=
            runWithGasOracle_withAnswer_of_run_le
              (answer := answer) hCode hLe
          simp [hCodeExtend, hPop, Bind.bind, Except.bind]

theorem runConditionStateWithGasOracle_withAnswer_of_run_le
    {code : Code} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state state' : RunState} {cond : Bool} {cursorFinal : Nat}
    (hRun : runConditionStateWithGasOracle code oracle cursor state =
      .ok (state', cond, cursorFinal))
    (hLe : cursorFinal ≤ answerCursor) :
    runConditionStateWithGasOracle code
        (Assembly.GasParametric.GasOracle.withAnswer oracle answerCursor
          answer) cursor state =
      .ok (state', cond, cursorFinal) := by
  unfold runConditionStateWithGasOracle at hRun ⊢
  cases hCond :
      runConditionWithGasOracle code oracle cursor state.evm with
  | error err =>
      rw [hCond] at hRun
      simp [Bind.bind, Except.bind] at hRun
  | ok result =>
      rcases result with ⟨evm, cond', cursor'⟩
      rw [hCond] at hRun
      simp [Bind.bind, Except.bind] at hRun
      rcases hRun with ⟨hState, hCondEq, hCursor⟩
      subst state'
      subst cond
      subst cursorFinal
      have hCondExtend :=
        runConditionWithGasOracle_withAnswer_of_run_le
          (answer := answer) hCond hLe
      rw [hCondExtend]
      simp [Bind.bind, Except.bind]

end Code

namespace Terminal

theorem stepWithGasOracle_cursor_le
    {kind : Assembly.HaltKind} {oracle : GasOracle} {cursor : Nat}
    {state state' : EVMState} {cursor' : Nat}
    (hStep : stepWithGasOracle kind oracle cursor state =
      .ok (state', cursor')) :
    cursor ≤ cursor' :=
  Assembly.GasParametric.Target.stepInstrWithGasOracle_cursor_le
    (by simpa [stepWithGasOracle] using hStep)

theorem stepWithGasOracle_withAnswer_of_run_le
    {kind : Assembly.HaltKind} {oracle : GasOracle}
    {cursor answerCursor : Nat} {answer : Word}
    {state state' : EVMState} {cursor' : Nat}
    (hRun : stepWithGasOracle kind oracle cursor state =
      .ok (state', cursor'))
    (hLe : cursor' ≤ answerCursor) :
    stepWithGasOracle kind
        (Assembly.GasParametric.GasOracle.withAnswer oracle answerCursor
          answer) cursor state =
      .ok (state', cursor') := by
  simpa [stepWithGasOracle] using
    Assembly.GasParametric.Target.stepInstrWithGasOracle_withAnswer_of_run_le
      (answer := answer) (by simpa [stepWithGasOracle] using hRun) hLe

end Terminal

mutual
  def Block.runWithGasOracle (program : Program) (oracle : GasOracle) :
      Nat → Block → Nat → RunState → Except EVMException (Outcome × Nat)
    | 0, _block, _cursor, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, cursor, state =>
        .ok (Outcome.regular state, cursor)
    | fuel + 1, ⟨stmt :: rest⟩, cursor, state => do
        let (outcome, cursor') ←
          Stmt.runWithGasOracle program oracle fuel stmt cursor state
        match outcome.mode with
        | .regular =>
            Block.runWithGasOracle program oracle fuel ⟨rest⟩ cursor'
              outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, cursor')

  def Stmt.runForLoopWithGasOracle (program : Program) (oracle : GasOracle)
      (fuel : Nat) (cond : Code) (post body : Block) (cursor : Nat)
      (state : RunState) : Except EVMException (Outcome × Nat) :=
    match fuel with
    | 0 =>
        invalid
    | fuel' + 1 =>
        match Code.runConditionStateWithGasOracle cond oracle cursor state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue, cursorAfterCond) =>
            if condTrue then
              match Block.runWithGasOracle program oracle fuel' body
                  cursorAfterCond stateAfterCond with
              | .error err => .error err
              | .ok (bodyOutcome, cursorAfterBody) =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state, cursorAfterBody)
                  | .regular | .cont =>
                      match Block.runWithGasOracle program oracle fuel' post
                          cursorAfterBody bodyOutcome.state with
                      | .error err => .error err
                      | .ok (postOutcome, cursorAfterPost) =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoopWithGasOracle program oracle fuel'
                                cond post body cursorAfterPost postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok (postOutcome, cursorAfterPost)
                  | .leave | .halt _ =>
                      .ok (bodyOutcome, cursorAfterBody)
            else
              .ok (Outcome.regular stateAfterCond, cursorAfterCond)

  def Stmt.runWithGasOracle (program : Program) (oracle : GasOracle) :
      Nat → Stmt → Nat → RunState → Except EVMException (Outcome × Nat)
    | _fuel, Stmt.code code, cursor, state => do
        let (state', cursor') ←
          Code.runStateWithGasOracle code oracle cursor state
        .ok (Outcome.regular state', cursor')
    | 0, Stmt.if_ _cond _body, _cursor, _state =>
        invalid
    | fuel + 1, Stmt.if_ cond body, cursor, state => do
        let (stateAfterCond, condTrue, cursorAfterCond) ←
          Code.runConditionStateWithGasOracle cond oracle cursor state
        if condTrue then
          Block.runWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond
        else
          .ok (Outcome.regular stateAfterCond, cursorAfterCond)
    | 0, Stmt.switch _scrutinee _cases _defaultBody, _cursor, _state =>
        invalid
    | fuel + 1, Stmt.switch scrutinee cases defaultBody, cursor, state => do
        let (stateAfterScrutinee, cursorAfterScrutinee) ←
          Code.runStateWithGasOracle scrutinee oracle cursor state
        match stateAfterScrutinee.evm.stack.pop with
        | none =>
            .error .StackUnderflow
        | some ⟨stack, value⟩ =>
            let evmAfterPop := { stateAfterScrutinee.evm with stack := stack }
            let stateAfterPop := stateAfterScrutinee.withEVM evmAfterPop
            match Switch.select value cases defaultBody with
            | some body =>
                Block.runWithGasOracle program oracle fuel body
                  cursorAfterScrutinee stateAfterPop
            | none =>
                .ok (Outcome.regular stateAfterPop, cursorAfterScrutinee)
    | 0, Stmt.for_ _init _cond _post _body, _cursor, _state =>
        invalid
    | fuel + 1, Stmt.for_ init cond post body, cursor, state => do
        let (initOutcome, cursorAfterInit) ←
          Block.runWithGasOracle program oracle fuel init cursor state
        match initOutcome.mode with
        | .regular =>
            Stmt.runForLoopWithGasOracle program oracle fuel cond post body
              cursorAfterInit initOutcome.state
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok (initOutcome, cursorAfterInit)
    | _fuel, Stmt.brk, cursor, state =>
        .ok (Outcome.brk state, cursor)
    | _fuel, Stmt.cont, cursor, state =>
        .ok (Outcome.cont state, cursor)
    | _fuel, Stmt.leave, cursor, state =>
        match state.returns with
        | [] => invalid
        | _ :: _ => .ok (Outcome.leave state, cursor)
    | 0, Stmt.call _name, _cursor, _state =>
        invalid
    | fuel + 1, Stmt.call name, cursor, state =>
        match ProcList.lookup? name program.procs with
        | none =>
            invalid
        | some proc =>
            match StackFrame.splitArgs? proc.argc state.evm.stack with
            | none =>
                .error .StackUnderflow
            | some (args, callerStack) =>
                let callEVM := { state.evm with stack := args }
                let callState :=
                  (state.withEVM callEVM).pushReturn callerStack proc.retc
                match Block.runWithGasOracle program oracle fuel proc.body cursor
                    callState with
                | .error err => .error err
                | .ok (outcome, cursorAfterBody) =>
                    match outcome.mode with
                    | .regular | .leave =>
                        match outcome.state.popReturn? with
                        | none => invalid
                        | some (frame, returned) =>
                            match StackFrame.attachReturns? frame
                                outcome.state.evm.stack with
                            | none => invalid
                            | some stack =>
                                let evm := { outcome.state.evm with stack := stack }
                                .ok
                                  ( Outcome.regular (returned.withEVM evm)
                                  , cursorAfterBody
                                  )
                    | .brk | .cont =>
                        invalid
                    | .halt kind =>
                        .ok (Outcome.halt kind outcome.state, cursorAfterBody)
    | _fuel, Stmt.terminal kind, cursor, state => do
        let (evm, cursor') ←
          Terminal.stepWithGasOracle kind oracle cursor state.evm
        .ok (Outcome.halt kind (state.withEVM evm), cursor')
end

namespace Program

def runStateWithGasOracle (fuel : Nat) (program : Program)
    (oracle : GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (Outcome × Nat) :=
  Block.runWithGasOracle program oracle fuel program.body cursor state

def runWithGasOracle (fuel : Nat) (program : Program)
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (Outcome × Nat) :=
  runStateWithGasOracle fuel program oracle cursor (initialState state)

end Program

mutual
  inductive Block.EvalWithGasOracle (program : Program) (oracle : GasOracle) :
      Nat → Block → Nat → RunState → Outcome → Nat → Prop where
    | nil {fuel cursor : Nat} {state : RunState} :
        Block.EvalWithGasOracle program oracle (fuel + 1) { stmts := [] }
          cursor state (Outcome.regular state) cursor
    | cons_regular {fuel cursor cursorMid cursorFinal : Nat}
        {stmt : Stmt} {rest : List Stmt}
        {state mid : RunState} {outcome : Outcome}
        (hStmt :
          Stmt.EvalWithGasOracle program oracle fuel stmt cursor state
            (Outcome.regular mid) cursorMid)
        (hRest :
          Block.EvalWithGasOracle program oracle fuel { stmts := rest }
            cursorMid mid outcome cursorFinal) :
        Block.EvalWithGasOracle program oracle (fuel + 1)
          { stmts := stmt :: rest } cursor state outcome cursorFinal
    | cons_brk {fuel cursor cursor' : Nat} {stmt : Stmt}
        {rest : List Stmt} {state outState : RunState}
        (hStmt :
          Stmt.EvalWithGasOracle program oracle fuel stmt cursor state
            (Outcome.brk outState) cursor') :
        Block.EvalWithGasOracle program oracle (fuel + 1)
          { stmts := stmt :: rest } cursor state (Outcome.brk outState)
          cursor'
    | cons_cont {fuel cursor cursor' : Nat} {stmt : Stmt}
        {rest : List Stmt} {state outState : RunState}
        (hStmt :
          Stmt.EvalWithGasOracle program oracle fuel stmt cursor state
            (Outcome.cont outState) cursor') :
        Block.EvalWithGasOracle program oracle (fuel + 1)
          { stmts := stmt :: rest } cursor state (Outcome.cont outState)
          cursor'
    | cons_leave {fuel cursor cursor' : Nat} {stmt : Stmt}
        {rest : List Stmt} {state outState : RunState}
        (hStmt :
          Stmt.EvalWithGasOracle program oracle fuel stmt cursor state
            (Outcome.leave outState) cursor') :
        Block.EvalWithGasOracle program oracle (fuel + 1)
          { stmts := stmt :: rest } cursor state (Outcome.leave outState)
          cursor'
    | cons_halt {fuel cursor cursor' : Nat} {stmt : Stmt}
        {rest : List Stmt} {state outState : RunState}
        {kind : Assembly.HaltKind}
        (hStmt :
          Stmt.EvalWithGasOracle program oracle fuel stmt cursor state
            (Outcome.halt kind outState) cursor') :
        Block.EvalWithGasOracle program oracle (fuel + 1)
          { stmts := stmt :: rest } cursor state (Outcome.halt kind outState)
          cursor'

  inductive Stmt.EvalWithGasOracle (program : Program) (oracle : GasOracle) :
      Nat → Stmt → Nat → RunState → Outcome → Nat → Prop where
    | code {fuel cursor cursor' : Nat} {code : Code}
        {state final : RunState}
        (hCode :
          Code.runStateWithGasOracle code oracle cursor state =
            .ok (final, cursor')) :
        Stmt.EvalWithGasOracle program oracle fuel (.code code) cursor state
          (Outcome.regular final) cursor'
    | if_false {fuel cursor cursor' : Nat} {cond : Code} {body : Block}
        {state stateAfterCond : RunState}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, false, cursor')) :
        Stmt.EvalWithGasOracle program oracle (fuel + 1) (.if_ cond body)
          cursor state (Outcome.regular stateAfterCond) cursor'
    | if_true {fuel cursor cursorAfterCond cursorFinal : Nat}
        {cond : Code} {body : Block}
        {state stateAfterCond : RunState} {outcome : Outcome}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond outcome cursorFinal) :
        Stmt.EvalWithGasOracle program oracle (fuel + 1) (.if_ cond body)
          cursor state outcome cursorFinal
    | switch_none {fuel cursor cursor' : Nat} {scrutinee : Code}
        {cases : List (Word × Block)} {defaultBody : Option Block}
        {state stateAfterScrutinee : RunState}
        {stack : EvmYul.Stack Word} {value : Word}
        (hScrutinee :
          Code.runStateWithGasOracle scrutinee oracle cursor state =
            .ok (stateAfterScrutinee, cursor'))
        (hPop : stateAfterScrutinee.evm.stack.pop = some (stack, value))
        (hSelect : Switch.select value cases defaultBody = none) :
        Stmt.EvalWithGasOracle program oracle (fuel + 1)
          (.switch scrutinee cases defaultBody) cursor state
          (Outcome.regular
            (stateAfterScrutinee.withEVM
              { stateAfterScrutinee.evm with stack := stack }))
          cursor'
    | switch_some {fuel cursor cursorAfterScrutinee cursorFinal : Nat}
        {scrutinee : Code} {cases : List (Word × Block)}
        {defaultBody : Option Block}
        {state stateAfterScrutinee stateAfterPop : RunState}
        {stack : EvmYul.Stack Word} {value : Word} {body : Block}
        {outcome : Outcome}
        (hScrutinee :
          Code.runStateWithGasOracle scrutinee oracle cursor state =
            .ok (stateAfterScrutinee, cursorAfterScrutinee))
        (hPop : stateAfterScrutinee.evm.stack.pop = some (stack, value))
        (hStateAfterPop :
          stateAfterPop =
            stateAfterScrutinee.withEVM
              { stateAfterScrutinee.evm with stack := stack })
        (hSelect : Switch.select value cases defaultBody = some body)
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body
            cursorAfterScrutinee stateAfterPop outcome cursorFinal) :
        Stmt.EvalWithGasOracle program oracle (fuel + 1)
          (.switch scrutinee cases defaultBody) cursor state outcome
          cursorFinal
    | for_init_regular {fuel cursor cursorAfterInit cursorFinal : Nat}
        {init : Block} {cond : Code} {post body : Block}
        {state initState : RunState} {outcome : Outcome}
        (hInit :
          Block.EvalWithGasOracle program oracle fuel init cursor state
            (Outcome.regular initState) cursorAfterInit)
        (hLoop :
          For.EvalWithGasOracle program oracle fuel cond post body
            cursorAfterInit initState outcome cursorFinal) :
        Stmt.EvalWithGasOracle program oracle (fuel + 1)
          (.for_ init cond post body) cursor state outcome cursorFinal
    | for_init_leave {fuel cursor cursor' : Nat} {init : Block}
        {cond : Code} {post body : Block} {state outState : RunState}
        (hInit :
          Block.EvalWithGasOracle program oracle fuel init cursor state
            (Outcome.leave outState) cursor') :
        Stmt.EvalWithGasOracle program oracle (fuel + 1)
          (.for_ init cond post body) cursor state (Outcome.leave outState)
          cursor'
    | for_init_halt {fuel cursor cursor' : Nat} {init : Block}
        {cond : Code} {post body : Block} {state outState : RunState}
        {kind : Assembly.HaltKind}
        (hInit :
          Block.EvalWithGasOracle program oracle fuel init cursor state
            (Outcome.halt kind outState) cursor') :
        Stmt.EvalWithGasOracle program oracle (fuel + 1)
          (.for_ init cond post body) cursor state (Outcome.halt kind outState)
          cursor'
    | brk {fuel cursor : Nat} {state : RunState} :
        Stmt.EvalWithGasOracle program oracle fuel .brk cursor state
          (Outcome.brk state) cursor
    | cont {fuel cursor : Nat} {state : RunState} :
        Stmt.EvalWithGasOracle program oracle fuel .cont cursor state
          (Outcome.cont state) cursor
    | leave {fuel cursor : Nat} {state : RunState}
        (hReturns : state.returns ≠ []) :
        Stmt.EvalWithGasOracle program oracle fuel .leave cursor state
          (Outcome.leave state) cursor
    | call_regular {fuel cursor cursor' : Nat} {name : Name}
        {state : RunState} {proc : Proc}
        {args callerStack stack : EvmYul.Stack Word}
        {bodyState returned : RunState} {frame : ReturnDest}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc state.evm.stack =
            some (args, callerStack))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel proc.body cursor
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Outcome.regular bodyState) cursor')
        (hPop : bodyState.popReturn? = some (frame, returned))
        (hAttach :
          StackFrame.attachReturns? frame bodyState.evm.stack = some stack) :
        Stmt.EvalWithGasOracle program oracle (fuel + 1) (.call name)
          cursor state
          (Outcome.regular
            (returned.withEVM { bodyState.evm with stack := stack }))
          cursor'
    | call_leave {fuel cursor cursor' : Nat} {name : Name}
        {state : RunState} {proc : Proc}
        {args callerStack stack : EvmYul.Stack Word}
        {bodyState returned : RunState} {frame : ReturnDest}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc state.evm.stack =
            some (args, callerStack))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel proc.body cursor
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Outcome.leave bodyState) cursor')
        (hPop : bodyState.popReturn? = some (frame, returned))
        (hAttach :
          StackFrame.attachReturns? frame bodyState.evm.stack = some stack) :
        Stmt.EvalWithGasOracle program oracle (fuel + 1) (.call name)
          cursor state
          (Outcome.regular
            (returned.withEVM { bodyState.evm with stack := stack }))
          cursor'
    | call_halt {fuel cursor cursor' : Nat} {name : Name}
        {state : RunState} {proc : Proc}
        {args callerStack : EvmYul.Stack Word}
        {bodyState : RunState} {kind : Assembly.HaltKind}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc state.evm.stack =
            some (args, callerStack))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel proc.body cursor
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Outcome.halt kind bodyState) cursor') :
        Stmt.EvalWithGasOracle program oracle (fuel + 1) (.call name)
          cursor state (Outcome.halt kind bodyState) cursor'
    | terminal {fuel cursor cursor' : Nat} {kind : Assembly.HaltKind}
        {state : RunState} {evm : EVMState}
        (hStep : Terminal.stepWithGasOracle kind oracle cursor state.evm =
          .ok (evm, cursor')) :
        Stmt.EvalWithGasOracle program oracle fuel (.terminal kind) cursor
          state (Outcome.halt kind (state.withEVM evm)) cursor'

  inductive For.EvalWithGasOracle (program : Program) (oracle : GasOracle) :
      Nat → Code → Block → Block → Nat → RunState → Outcome → Nat → Prop where
    | false {fuel cursor cursor' : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond : RunState}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, false, cursor')) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state (Outcome.regular stateAfterCond) cursor'
    | body_brk {fuel cursor cursorAfterCond cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : RunState}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.brk bodyState) cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state (Outcome.regular bodyState) cursorFinal
    | body_leave {fuel cursor cursorAfterCond cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : RunState}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.leave bodyState) cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state (Outcome.leave bodyState) cursorFinal
    | body_halt {fuel cursor cursorAfterCond cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : RunState}
        {kind : Assembly.HaltKind}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.halt kind bodyState) cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state (Outcome.halt kind bodyState) cursorFinal
    | regular_post_regular
        {fuel cursor cursorAfterCond cursorAfterBody cursorAfterPost cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        {outcome : Outcome}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.regular bodyState) cursorAfterBody)
        (hPost :
          Block.EvalWithGasOracle program oracle fuel post cursorAfterBody
            bodyState (Outcome.regular postState) cursorAfterPost)
        (hLoop :
          For.EvalWithGasOracle program oracle fuel cond post body
            cursorAfterPost postState outcome cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state outcome cursorFinal
    | cont_post_regular
        {fuel cursor cursorAfterCond cursorAfterBody cursorAfterPost cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        {outcome : Outcome}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.cont bodyState) cursorAfterBody)
        (hPost :
          Block.EvalWithGasOracle program oracle fuel post cursorAfterBody
            bodyState (Outcome.regular postState) cursorAfterPost)
        (hLoop :
          For.EvalWithGasOracle program oracle fuel cond post body
            cursorAfterPost postState outcome cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state outcome cursorFinal
    | regular_post_leave
        {fuel cursor cursorAfterCond cursorAfterBody cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.regular bodyState) cursorAfterBody)
        (hPost :
          Block.EvalWithGasOracle program oracle fuel post cursorAfterBody
            bodyState (Outcome.leave postState) cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state (Outcome.leave postState) cursorFinal
    | cont_post_leave
        {fuel cursor cursorAfterCond cursorAfterBody cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.cont bodyState) cursorAfterBody)
        (hPost :
          Block.EvalWithGasOracle program oracle fuel post cursorAfterBody
            bodyState (Outcome.leave postState) cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state (Outcome.leave postState) cursorFinal
    | regular_post_halt
        {fuel cursor cursorAfterCond cursorAfterBody cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        {kind : Assembly.HaltKind}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.regular bodyState) cursorAfterBody)
        (hPost :
          Block.EvalWithGasOracle program oracle fuel post cursorAfterBody
            bodyState (Outcome.halt kind postState) cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state (Outcome.halt kind postState) cursorFinal
    | cont_post_halt
        {fuel cursor cursorAfterCond cursorAfterBody cursorFinal : Nat}
        {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        {kind : Assembly.HaltKind}
        (hCond :
          Code.runConditionStateWithGasOracle cond oracle cursor state =
            .ok (stateAfterCond, true, cursorAfterCond))
        (hBody :
          Block.EvalWithGasOracle program oracle fuel body cursorAfterCond
            stateAfterCond (Outcome.cont bodyState) cursorAfterBody)
        (hPost :
          Block.EvalWithGasOracle program oracle fuel post cursorAfterBody
            bodyState (Outcome.halt kind postState) cursorFinal) :
        For.EvalWithGasOracle program oracle (fuel + 1) cond post body
          cursor state (Outcome.halt kind postState) cursorFinal
end

set_option linter.unusedSimpArgs false in
mutual
  theorem Block.evalWithGasOracle_of_run {program : Program}
      {oracle : GasOracle} {fuel : Nat} {block : Block}
      {cursor cursorFinal : Nat} {state : RunState} {outcome : Outcome}
      (hRun :
        Block.runWithGasOracle program oracle fuel block cursor state =
          .ok (outcome, cursorFinal)) :
      Block.EvalWithGasOracle program oracle fuel block cursor state outcome
        cursorFinal := by
    cases fuel with
    | zero =>
        simp [Block.runWithGasOracle, invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                simp [Block.runWithGasOracle] at hRun
                cases hRun
                subst outcome
                subst cursorFinal
                exact Block.EvalWithGasOracle.nil
            | cons stmt rest =>
                unfold Block.runWithGasOracle at hRun
                cases hStmtRun :
                    Stmt.runWithGasOracle program oracle fuel stmt cursor state with
                | error err =>
                    rw [hStmtRun] at hRun
                    cases hRun
                | ok stmtPair =>
                    rcases stmtPair with ⟨stmtOutcome, cursorMid⟩
                    rw [hStmtRun] at hRun
                    have hStmtEval := Stmt.evalWithGasOracle_of_run hStmtRun
                    cases stmtOutcome with
                    | mk stmtState stmtMode =>
                        cases stmtMode with
                        | regular =>
                            exact
                              Block.EvalWithGasOracle.cons_regular
                                (by
                                  simpa [Outcome.regular] using hStmtEval)
                                (Block.evalWithGasOracle_of_run hRun)
                        | brk =>
                            cases hRun
                            exact
                              Block.EvalWithGasOracle.cons_brk
                                (by simpa [Outcome.brk] using hStmtEval)
                        | cont =>
                            cases hRun
                            exact
                              Block.EvalWithGasOracle.cons_cont
                                (by simpa [Outcome.cont] using hStmtEval)
                        | leave =>
                            cases hRun
                            exact
                              Block.EvalWithGasOracle.cons_leave
                                (by simpa [Outcome.leave] using hStmtEval)
                        | halt kind =>
                            cases hRun
                            exact
                              Block.EvalWithGasOracle.cons_halt
                                (by simpa [Outcome.halt] using hStmtEval)

  theorem Stmt.evalWithGasOracle_of_run {program : Program}
      {oracle : GasOracle} {fuel : Nat} {stmt : Stmt}
      {cursor cursorFinal : Nat} {state : RunState} {outcome : Outcome}
      (hRun :
        Stmt.runWithGasOracle program oracle fuel stmt cursor state =
          .ok (outcome, cursorFinal)) :
      Stmt.EvalWithGasOracle program oracle fuel stmt cursor state outcome
        cursorFinal := by
    cases stmt with
    | code code =>
        cases hCode :
            Code.runStateWithGasOracle code oracle cursor state with
        | error err =>
            simp [Stmt.runWithGasOracle, hCode, Bind.bind, Except.bind] at hRun
        | ok codePair =>
            rcases codePair with ⟨final, cursor'⟩
            simp [Stmt.runWithGasOracle, hCode, Bind.bind, Except.bind] at hRun
            cases hRun
            subst outcome
            subst cursorFinal
            exact Stmt.EvalWithGasOracle.code hCode
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid] at hRun
        | succ fuel =>
            unfold Stmt.runWithGasOracle at hRun
            cases hCond :
                Code.runConditionStateWithGasOracle cond oracle cursor state with
            | error err =>
                rw [hCond] at hRun
                cases hRun
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue, cursorAfterCond⟩
                rw [hCond] at hRun
                cases condTrue with
                | false =>
                    simp at hRun
                    cases hRun
                    exact Stmt.EvalWithGasOracle.if_false hCond
                | true =>
                    exact
                      Stmt.EvalWithGasOracle.if_true hCond
                        (Block.evalWithGasOracle_of_run hRun)
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid] at hRun
        | succ fuel =>
            unfold Stmt.runWithGasOracle at hRun
            cases hScrutinee :
                Code.runStateWithGasOracle scrutinee oracle cursor state with
            | error err =>
                simp [hScrutinee, Bind.bind, Except.bind] at hRun
            | ok scrutineePair =>
                rcases scrutineePair with ⟨stateAfterScrutinee, cursorAfterScrutinee⟩
                simp [hScrutinee, Bind.bind, Except.bind] at hRun
                cases hPop : stateAfterScrutinee.evm.stack.pop with
                | none =>
                    simp [hPop] at hRun
                | some popped =>
                    rcases popped with ⟨stack, value⟩
                    simp [hPop] at hRun
                    let stateAfterPop :=
                      stateAfterScrutinee.withEVM
                        { stateAfterScrutinee.evm with stack := stack }
                    cases hSelect : Switch.select value cases defaultBody with
                    | none =>
                        simp [hSelect] at hRun
                        cases hRun
                        subst outcome
                        subst cursorFinal
                        exact
                          Stmt.EvalWithGasOracle.switch_none hScrutinee hPop
                            hSelect
                    | some body =>
                        simp [hSelect] at hRun
                        exact
                          Stmt.EvalWithGasOracle.switch_some hScrutinee hPop
                            (show stateAfterPop =
                              stateAfterScrutinee.withEVM
                                { stateAfterScrutinee.evm with stack := stack } from
                              rfl)
                            hSelect (Block.evalWithGasOracle_of_run hRun)
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid] at hRun
        | succ fuel =>
            unfold Stmt.runWithGasOracle at hRun
            cases hInitRun :
                Block.runWithGasOracle program oracle fuel init cursor state with
            | error err =>
                simp [hInitRun, Bind.bind, Except.bind] at hRun
            | ok initPair =>
                rcases initPair with ⟨initOutcome, cursorAfterInit⟩
                simp [hInitRun, Bind.bind, Except.bind] at hRun
                have hInitEval := Block.evalWithGasOracle_of_run hInitRun
                cases initOutcome with
                | mk initState initMode =>
                    cases initMode with
                    | regular =>
                        exact
                          Stmt.EvalWithGasOracle.for_init_regular
                            (by simpa [Outcome.regular] using hInitEval)
                            (For.evalWithGasOracle_of_run hRun)
                    | brk =>
                        dsimp [Bind.bind, Except.bind, invalid] at hRun
                        cases hRun
                    | cont =>
                        dsimp [Bind.bind, Except.bind, invalid] at hRun
                        cases hRun
                    | leave =>
                        change
                          Except.ok (Outcome.leave initState, cursorAfterInit) =
                            Except.ok (outcome, cursorFinal) at hRun
                        cases hRun
                        exact
                          Stmt.EvalWithGasOracle.for_init_leave
                            (by simpa [Outcome.leave] using hInitEval)
                    | halt kind =>
                        change
                          Except.ok (Outcome.halt kind initState, cursorAfterInit) =
                            Except.ok (outcome, cursorFinal) at hRun
                        cases hRun
                        exact
                          Stmt.EvalWithGasOracle.for_init_halt
                            (by simpa [Outcome.halt] using hInitEval)
    | brk =>
        simp [Stmt.runWithGasOracle] at hRun
        cases hRun
        subst outcome
        subst cursorFinal
        exact Stmt.EvalWithGasOracle.brk
    | cont =>
        simp [Stmt.runWithGasOracle] at hRun
        cases hRun
        subst outcome
        subst cursorFinal
        exact Stmt.EvalWithGasOracle.cont
    | leave =>
        unfold Stmt.runWithGasOracle at hRun
        cases hReturns : state.returns with
        | nil =>
            simp [hReturns, invalid] at hRun
        | cons frame returns =>
            simp [hReturns] at hRun
            cases hRun
            subst outcome
            subst cursorFinal
            exact Stmt.EvalWithGasOracle.leave (by simp [hReturns])
    | call name =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid] at hRun
        | succ fuel =>
            unfold Stmt.runWithGasOracle at hRun
            cases hLookup : ProcList.lookup? name program.procs with
            | none =>
                simp [hLookup, Bind.bind, Except.bind, invalid] at hRun
            | some proc =>
                simp [hLookup, Bind.bind, Except.bind] at hRun
                cases hSplit :
                    StackFrame.splitArgs? proc.argc state.evm.stack with
                | none =>
                    simp [hSplit, Bind.bind, Except.bind] at hRun
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    simp [hSplit, Bind.bind, Except.bind] at hRun
                    let callState : RunState :=
                      (state.withEVM { state.evm with stack := args }).pushReturn
                        callerStack proc.retc
                    cases hBodyRun :
                        Block.runWithGasOracle program oracle fuel proc.body
                          cursor callState with
                    | error err =>
                        simp [callState, hBodyRun, Bind.bind, Except.bind] at hRun
                    | ok bodyPair =>
                        rcases bodyPair with ⟨bodyOutcome, cursorAfterBody⟩
                        simp [callState, hBodyRun, Bind.bind, Except.bind] at hRun
                        have hBodyEval := Block.evalWithGasOracle_of_run hBodyRun
                        cases bodyOutcome with
                        | mk bodyState bodyMode =>
                            cases bodyMode with
                            | regular =>
                                simp [Outcome.regular] at hRun
                                cases hPop : bodyState.popReturn? with
                                | none =>
                                    simp [hPop, invalid] at hRun
                                | some popped =>
                                    rcases popped with ⟨frame, returned⟩
                                    simp [hPop] at hRun
                                    cases hAttach :
                                        StackFrame.attachReturns? frame
                                          bodyState.evm.stack with
                                    | none =>
                                        simp [hAttach, invalid] at hRun
                                    | some stack =>
                                        simp [hAttach] at hRun
                                        cases hRun
                                        subst outcome
                                        subst cursorFinal
                                        exact
                                          Stmt.EvalWithGasOracle.call_regular
                                            hLookup hSplit
                                            (by
                                              simpa [callState, Outcome.regular]
                                                using hBodyEval)
                                            hPop hAttach
                            | brk =>
                                simp [Outcome.brk, invalid] at hRun
                            | cont =>
                                simp [Outcome.cont, invalid] at hRun
                            | leave =>
                                simp [Outcome.leave] at hRun
                                cases hPop : bodyState.popReturn? with
                                | none =>
                                    simp [hPop, invalid] at hRun
                                | some popped =>
                                    rcases popped with ⟨frame, returned⟩
                                    simp [hPop] at hRun
                                    cases hAttach :
                                        StackFrame.attachReturns? frame
                                          bodyState.evm.stack with
                                    | none =>
                                        simp [hAttach, invalid] at hRun
                                    | some stack =>
                                        simp [hAttach] at hRun
                                        cases hRun
                                        subst outcome
                                        subst cursorFinal
                                        exact
                                          Stmt.EvalWithGasOracle.call_leave
                                            hLookup hSplit
                                            (by
                                              simpa [callState, Outcome.leave]
                                                using hBodyEval)
                                            hPop hAttach
                            | halt kind =>
                                simp [Outcome.halt] at hRun
                                cases hRun
                                subst outcome
                                subst cursorFinal
                                exact
                                  Stmt.EvalWithGasOracle.call_halt hLookup hSplit
                                    (by
                                      simpa [callState, Outcome.halt]
                                        using hBodyEval)
    | terminal kind =>
        cases hStep :
            Terminal.stepWithGasOracle kind oracle cursor state.evm with
        | error err =>
            simp [Stmt.runWithGasOracle, hStep] at hRun
            cases hRun
        | ok stepPair =>
            rcases stepPair with ⟨evm, cursor'⟩
            simp [Stmt.runWithGasOracle, hStep] at hRun
            cases hRun
            exact Stmt.EvalWithGasOracle.terminal hStep

  theorem For.evalWithGasOracle_of_run {program : Program}
      {oracle : GasOracle} {fuel : Nat} {cond : Code} {post body : Block}
      {cursor cursorFinal : Nat} {state : RunState} {outcome : Outcome}
      (hRun :
        Stmt.runForLoopWithGasOracle program oracle fuel cond post body cursor
            state =
          .ok (outcome, cursorFinal)) :
      For.EvalWithGasOracle program oracle fuel cond post body cursor state
        outcome cursorFinal := by
    cases fuel with
    | zero =>
        simp [Stmt.runForLoopWithGasOracle, invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoopWithGasOracle at hRun
        cases hCond :
            Code.runConditionStateWithGasOracle cond oracle cursor state with
        | error err =>
            simp [hCond, Bind.bind, Except.bind] at hRun
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue, cursorAfterCond⟩
            simp [hCond, Bind.bind, Except.bind] at hRun
            cases condTrue with
            | false =>
                simp at hRun
                cases hRun
                subst outcome
                subst cursorFinal
                exact For.EvalWithGasOracle.false hCond
            | true =>
                cases hBodyRun :
                    Block.runWithGasOracle program oracle fuel body
                      cursorAfterCond stateAfterCond with
                | error err =>
                    simp [hBodyRun, Bind.bind, Except.bind] at hRun
                | ok bodyPair =>
                    rcases bodyPair with ⟨bodyOutcome, cursorAfterBody⟩
                    simp [hBodyRun, Bind.bind, Except.bind] at hRun
                    have hBodyEval := Block.evalWithGasOracle_of_run hBodyRun
                    cases bodyOutcome with
                    | mk bodyState bodyMode =>
                        cases bodyMode with
                        | regular =>
                            simp [Outcome.regular] at hRun
                            cases hPostRun :
                                Block.runWithGasOracle program oracle fuel post
                                  cursorAfterBody bodyState with
                            | error err =>
                                simp [hPostRun, Bind.bind, Except.bind] at hRun
                            | ok postPair =>
                                rcases postPair with
                                  ⟨postOutcome, cursorAfterPost⟩
                                simp [hPostRun, Bind.bind, Except.bind] at hRun
                                have hPostEval :=
                                  Block.evalWithGasOracle_of_run hPostRun
                                cases postOutcome with
                                | mk postState postMode =>
                                    cases postMode with
                                    | regular =>
                                        exact
                                          For.EvalWithGasOracle.regular_post_regular
                                            hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.regular]
                                                using hPostEval)
                                            (For.evalWithGasOracle_of_run hRun)
                                    | brk =>
                                        simp [invalid] at hRun
                                    | cont =>
                                        simp [invalid] at hRun
                                    | leave =>
                                        simp at hRun
                                        cases hRun
                                        subst outcome
                                        subst cursorFinal
                                        exact
                                          For.EvalWithGasOracle.regular_post_leave
                                            hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.leave]
                                                using hPostEval)
                                    | halt kind =>
                                        simp at hRun
                                        cases hRun
                                        subst outcome
                                        subst cursorFinal
                                        exact
                                          For.EvalWithGasOracle.regular_post_halt
                                            hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.halt]
                                                using hPostEval)
                        | brk =>
                            simp [Outcome.brk] at hRun
                            cases hRun
                            subst outcome
                            subst cursorFinal
                            exact
                              For.EvalWithGasOracle.body_brk hCond
                                (by simpa [Outcome.brk] using hBodyEval)
                        | cont =>
                            simp [Outcome.cont] at hRun
                            cases hPostRun :
                                Block.runWithGasOracle program oracle fuel post
                                  cursorAfterBody bodyState with
                            | error err =>
                                simp [hPostRun, Bind.bind, Except.bind] at hRun
                            | ok postPair =>
                                rcases postPair with
                                  ⟨postOutcome, cursorAfterPost⟩
                                simp [hPostRun, Bind.bind, Except.bind] at hRun
                                have hPostEval :=
                                  Block.evalWithGasOracle_of_run hPostRun
                                cases postOutcome with
                                | mk postState postMode =>
                                    cases postMode with
                                    | regular =>
                                        exact
                                          For.EvalWithGasOracle.cont_post_regular
                                            hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.regular]
                                                using hPostEval)
                                            (For.evalWithGasOracle_of_run hRun)
                                    | brk =>
                                        simp [invalid] at hRun
                                    | cont =>
                                        simp [invalid] at hRun
                                    | leave =>
                                        simp at hRun
                                        cases hRun
                                        subst outcome
                                        subst cursorFinal
                                        exact
                                          For.EvalWithGasOracle.cont_post_leave
                                            hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.leave]
                                                using hPostEval)
                                    | halt kind =>
                                        simp at hRun
                                        cases hRun
                                        subst outcome
                                        subst cursorFinal
                                        exact
                                          For.EvalWithGasOracle.cont_post_halt
                                            hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.halt]
                                                using hPostEval)
                        | leave =>
                            simp [Outcome.leave] at hRun
                            cases hRun
                            subst outcome
                            subst cursorFinal
                            exact
                              For.EvalWithGasOracle.body_leave hCond
                                (by simpa [Outcome.leave] using hBodyEval)
                        | halt kind =>
                            simp [Outcome.halt] at hRun
                            cases hRun
                            subst outcome
                            subst cursorFinal
                            exact
                              For.EvalWithGasOracle.body_halt hCond
                                (by simpa [Outcome.halt] using hBodyEval)
end

namespace Program

theorem evalWithGasOracle_of_runState {fuel : Nat} {program : Program}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    {state : RunState} {outcome : Outcome}
    (hRun :
      program.runStateWithGasOracle fuel oracle cursor state =
        .ok (outcome, cursorFinal)) :
    Block.EvalWithGasOracle program oracle fuel program.body cursor state
      outcome cursorFinal := by
  exact Block.evalWithGasOracle_of_run hRun

theorem evalWithGasOracle_of_run {fuel : Nat} {program : Program}
    {oracle : GasOracle} {cursor cursorFinal : Nat}
    {initial : EVMState} {outcome : Outcome}
    (hRun :
      program.runWithGasOracle fuel oracle cursor initial =
        .ok (outcome, cursorFinal)) :
    Block.EvalWithGasOracle program oracle fuel program.body cursor
      (Program.initialState initial) outcome cursorFinal := by
  exact evalWithGasOracle_of_runState hRun

end Program

namespace GasParametric

def targetInstrOfBasicInstr : BasicInstr → Assembly.TargetInstr
  | .push value => .push32 value
  | BasicInstr.op basicOp => .prim basicOp.toPrimOp

def targetCodeOfCode (code : Code) : List Assembly.TargetInstr :=
  code.map targetInstrOfBasicInstr

def targetRunListWithGasOracle :
    List Assembly.TargetInstr → GasOracle →
      Nat → EVMState → Except EVMException (EVMState × Nat)
  | [], _oracle, cursor, state => .ok (state, cursor)
  | instr :: rest, oracle, cursor, state => do
      let (state', cursor') ←
        Assembly.GasParametric.Target.stepInstrWithGasOracle oracle cursor
          instr state
      targetRunListWithGasOracle rest oracle cursor' state'

def targetRunStateWithGasOracle (code : Code) (oracle : GasOracle)
    (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Nat) := do
  let (evm, cursor') ←
    targetRunListWithGasOracle (targetCodeOfCode code) oracle cursor state.evm
  .ok (state.withEVM evm, cursor')

def targetRunConditionWithGasOracle (code : Code) (oracle : GasOracle)
    (cursor : Nat) (state : EVMState) :
    Except EVMException (EVMState × Bool × Nat) := do
  let (state', cursor') ←
    targetRunListWithGasOracle (targetCodeOfCode code) oracle cursor state
  let (stateAfterPop, cond) ← Code.popCondition state'
  .ok (stateAfterPop, cond, cursor')

def targetRunConditionStateWithGasOracle (code : Code)
    (oracle : GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Bool × Nat) := do
  let (evm, cond, cursor') ←
    targetRunConditionWithGasOracle code oracle cursor state.evm
  .ok (state.withEVM evm, cond, cursor')

theorem step_targetInstrOfBasicInstr (instr : BasicInstr)
    (oracle : GasOracle) (cursor : Nat)
    (state : EVMState) :
    Assembly.GasParametric.Target.stepInstrWithGasOracle oracle cursor
        (targetInstrOfBasicInstr instr) state =
      instr.stepWithGasOracle oracle cursor state := by
  cases instr <;>
    simp [targetInstrOfBasicInstr, BasicInstr.stepWithGasOracle,
      BasicOp.stepWithGasOracle]

theorem run_targetCodeOfCode (code : Code)
    (oracle : GasOracle) (cursor : Nat)
    (state : EVMState) :
    targetRunListWithGasOracle (targetCodeOfCode code) oracle cursor state =
      Code.runWithGasOracle code oracle cursor state := by
  induction code generalizing cursor state with
  | nil =>
      rfl
  | cons instr rest ih =>
      simp [targetCodeOfCode, targetRunListWithGasOracle,
        Code.runWithGasOracle, step_targetInstrOfBasicInstr]
      cases hStep : instr.stepWithGasOracle oracle cursor state with
      | error err =>
          simp [Bind.bind, Except.bind]
      | ok stepResult =>
          rcases stepResult with ⟨state', cursor'⟩
          simp [Bind.bind, Except.bind]
          simpa [targetCodeOfCode] using ih cursor' state'

theorem targetRunStateWithGasOracle_eq_code (code : Code)
    (oracle : GasOracle) (cursor : Nat) (state : RunState) :
    targetRunStateWithGasOracle code oracle cursor state =
      Code.runStateWithGasOracle code oracle cursor state := by
  simp [targetRunStateWithGasOracle, Code.runStateWithGasOracle,
    run_targetCodeOfCode]

theorem targetRunConditionWithGasOracle_eq_code (code : Code)
    (oracle : GasOracle) (cursor : Nat) (state : EVMState) :
    targetRunConditionWithGasOracle code oracle cursor state =
      Code.runConditionWithGasOracle code oracle cursor state := by
  simp [targetRunConditionWithGasOracle, Code.runConditionWithGasOracle,
    run_targetCodeOfCode]

theorem targetRunConditionStateWithGasOracle_eq_code (code : Code)
    (oracle : GasOracle) (cursor : Nat) (state : RunState) :
    targetRunConditionStateWithGasOracle code oracle cursor state =
      Code.runConditionStateWithGasOracle code oracle cursor state := by
  simp [targetRunConditionStateWithGasOracle,
    Code.runConditionStateWithGasOracle,
    targetRunConditionWithGasOracle_eq_code]

theorem stmt_code_runWithGasOracle_eq_target (program : Program)
    (fuel : Nat) (code : Code) (oracle : GasOracle) (cursor : Nat)
    (state : RunState) :
    Stmt.runWithGasOracle program oracle fuel (.code code) cursor state =
      (do
        let (state', cursor') ←
          targetRunStateWithGasOracle code oracle cursor state
        .ok (Outcome.regular state', cursor')) := by
  simp [Stmt.runWithGasOracle, targetRunStateWithGasOracle_eq_code]

end GasParametric

end Structured
end EvmCompiler
