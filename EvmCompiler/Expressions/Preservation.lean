import EvmCompiler.Expressions.Semantics
import EvmCompiler.Structured.GasParametricPreservation

namespace EvmCompiler
namespace Expressions

@[simp] theorem except_bind_error {ε α β : Type} (err : ε)
    (f : α → Except ε β) :
    (Except.error err >>= f) = Except.error err := rfl

@[simp] theorem except_bind_ok {ε α β : Type} (value : α)
    (f : α → Except ε β) :
    (Except.ok value >>= f) = f value := rfl

@[simp] theorem RunState.withEVM_withEVM (state : RunState)
    (first second : EVMState) :
    (state.withEVM first).withEVM second = state.withEVM second := rfl

namespace Structured.Code

theorem run_append (left right : Structured.Code) (state : EVMState) :
    Structured.Code.run (left ++ right) state =
      (do
        let state' ← Structured.Code.run left state
        Structured.Code.run right state') := by
  induction left generalizing state with
  | nil =>
      rfl
  | cons instr rest ih =>
      simp [Structured.Code.run, ih]

theorem runWithGasOracle_append (left right : Structured.Code)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    Structured.Code.runWithGasOracle (left ++ right) oracle cursor state =
      (do
        let (state', cursor') ←
          Structured.Code.runWithGasOracle left oracle cursor state
        Structured.Code.runWithGasOracle right oracle cursor' state') := by
  induction left generalizing cursor state with
  | nil =>
      rfl
  | cons instr rest ih =>
      simp [Structured.Code.runWithGasOracle, ih]

end Structured.Code

mutual
  theorem Expr.run_eq_compile {results : Nat} (expr : Expr results)
      (state : EVMState) :
      expr.run state = Structured.Code.run expr.compile state := by
    cases expr with
    | lit value =>
        rfl
    | code code =>
        rfl
    | prim op args =>
        simp [Expr.run, Expr.compile, Structured.Code.run_append,
          ExprSeq.run_eq_compile]
        cases hArgs : Structured.Code.run args.compile state with
        | error err =>
            rfl
        | ok state' =>
            cases hStep : op.step state' <;>
              simp [Structured.Code.run, Structured.BasicInstr.step, hStep]

  theorem ExprSeq.run_eq_compile {results : Nat} (exprs : ExprSeq results)
      (state : EVMState) :
      exprs.run state = Structured.Code.run exprs.compile state := by
    cases exprs with
    | nil =>
        rfl
    | cons head tail =>
        simp [ExprSeq.run, ExprSeq.compile, Structured.Code.run_append,
          Expr.run_eq_compile, ExprSeq.run_eq_compile]
end

namespace Expr

theorem runState_eq_compile {results : Nat} (expr : Expr results)
    (state : RunState) :
    expr.runState state = Structured.Code.runState expr.compile state := by
  unfold runState Structured.Code.runState
  rw [Expr.run_eq_compile]

theorem runCondition_eq_compile (cond : Expr 1) (state : EVMState) :
    cond.runCondition state =
      Structured.Code.runCondition cond.compile state := by
  unfold runCondition Structured.Code.runCondition
  rw [Expr.run_eq_compile]
  cases Structured.Code.run cond.compile state <;> rfl

theorem runConditionState_eq_compile (cond : Expr 1) (state : RunState) :
    cond.runConditionState state =
      Structured.Code.runConditionState cond.compile state := by
  unfold runConditionState Structured.Code.runConditionState
  rw [Expr.runCondition_eq_compile]

end Expr

namespace ProcList

theorem lookup?_toStructured (name : Name) (procs : List Proc) :
    Structured.ProcList.lookup? name (ProcList.toStructured procs) =
      Option.map Proc.toStructured (lookup? name procs) := by
  induction procs with
  | nil =>
      rfl
  | cons proc rest ih =>
      unfold lookup? Structured.ProcList.lookup? ProcList.toStructured
      by_cases hName : proc.name = name
      · simp [hName, Proc.toStructured]
      · simp [hName, ih, Proc.toStructured]

theorem lookup?_program_toStructured (name : Name) (program : Program) :
    Structured.ProcList.lookup? name program.toStructured.procs =
      Option.map Proc.toStructured (lookup? name program.procs) := by
  exact lookup?_toStructured name program.procs

end ProcList

namespace Switch

theorem select_toStructured (scrutinee : Word)
    (cases : List (Word × Block)) (defaultBody : Option Block) :
    Structured.Switch.select scrutinee (CaseList.toStructured cases)
        (Default.toStructured defaultBody) =
      Option.map Block.toStructured
        (Switch.select scrutinee cases defaultBody) := by
  induction cases with
  | nil =>
      cases defaultBody <;> rfl
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      unfold Switch.select Structured.Switch.select CaseList.toStructured
      by_cases hEq : value = scrutinee
      · simp [hEq]
      · simp [hEq, ih]

end Switch

set_option maxHeartbeats 1200000 in
mutual
  theorem Block.run_toStructured (program : Program) :
      ∀ (fuel : Nat) (block : Block) (state : RunState),
        Block.run program fuel block state =
          Structured.Block.run program.toStructured fuel block.toStructured state := by
    intro fuel block state
    cases fuel with
    | zero =>
        cases block
        rfl
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                rfl
            | cons stmt rest =>
                simp [Block.run, Structured.Block.run, Block.toStructured,
                  StmtList.toStructured]
                rw [Stmt.run_toStructured program fuel stmt state]
                cases hStmt :
                    Structured.Stmt.run program.toStructured fuel
                      stmt.toStructured state with
                | error err =>
                    simp [hStmt]
                | ok outcome =>
                    simp [hStmt]
                    cases outcome.mode <;>
                      simp [Block.toStructured,
                        Block.run_toStructured program fuel
                        { stmts := rest } outcome.state]

  theorem Stmt.runForLoop_toStructured (program : Program)
      (fuel : Nat) (cond : Expr 1) (post body : Block) (state : RunState) :
      Stmt.runForLoop program fuel cond post body state =
        Structured.Stmt.runForLoop program.toStructured fuel cond.compile
          post.toStructured body.toStructured state := by
    cases fuel with
    | zero =>
        rfl
    | succ fuel =>
        unfold Stmt.runForLoop Structured.Stmt.runForLoop
        rw [Expr.runConditionState_eq_compile]
        cases hCond : Structured.Code.runConditionState cond.compile state with
        | error err =>
            simp [hCond]
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue⟩
            simp [hCond]
            cases condTrue with
            | false =>
                rfl
            | true =>
                rw [Block.run_toStructured program fuel body
                  stateAfterCond]
                cases hBody :
                    Structured.Block.run program.toStructured fuel
                      body.toStructured stateAfterCond with
                | error err =>
                    simp [hBody]
                | ok bodyOutcome =>
                    simp [hBody]
                    cases bodyOutcome.mode with
                    | brk =>
                        rfl
                    | regular =>
                        rw [Block.run_toStructured program fuel post
                          bodyOutcome.state]
                        cases hPost :
                            Structured.Block.run program.toStructured fuel
                              post.toStructured bodyOutcome.state with
                        | error err =>
                            simp [hPost]
                        | ok postOutcome =>
                            simp [hPost, invalid, Structured.invalid]
                            cases postOutcome.mode <;>
                              simp [invalid, Structured.invalid,
                                Stmt.runForLoop_toStructured program fuel
                                cond post body postOutcome.state]
                    | cont =>
                        rw [Block.run_toStructured program fuel post
                          bodyOutcome.state]
                        cases hPost :
                            Structured.Block.run program.toStructured fuel
                              post.toStructured bodyOutcome.state with
                        | error err =>
                            simp [hPost]
                        | ok postOutcome =>
                            simp [hPost, invalid, Structured.invalid]
                            cases postOutcome.mode <;>
                              simp [invalid, Structured.invalid,
                                Stmt.runForLoop_toStructured program fuel
                                cond post body postOutcome.state]
                    | leave =>
                        rfl
                    | halt kind =>
                        rfl

  theorem Stmt.run_toStructured (program : Program) :
      ∀ (fuel : Nat) (stmt : Stmt) (state : RunState),
        Stmt.run program fuel stmt state =
          Structured.Stmt.run program.toStructured fuel stmt.toStructured state := by
    intro fuel stmt state
    cases stmt with
    | code code =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured]
    | expr expr =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured,
          Expr.runState_eq_compile, Structured.Code.runState]
    | if_ cond body =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.run Structured.Stmt.run
            simp [Stmt.toStructured]
            rw [Expr.runConditionState_eq_compile]
            cases hCond : Structured.Code.runConditionState cond.compile state with
            | error err =>
                simp [hCond, Except.bind]
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                simp [hCond]
                cases condTrue with
                | false =>
                    rfl
                | true =>
                    exact Block.run_toStructured program fuel body
                      stateAfterCond
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.run Structured.Stmt.run
            simp [Stmt.toStructured]
            rw [Expr.run_eq_compile]
            cases hScrutinee :
                Structured.Code.run scrutinee.compile state.evm with
            | error err =>
                simp [hScrutinee, Structured.Code.runState, Except.bind]
            | ok evmAfterScrutinee =>
                simp [hScrutinee, Structured.Code.runState]
                cases hPop : evmAfterScrutinee.stack.pop with
                | none =>
                    simp [hPop]
                | some pair =>
                    rcases pair with ⟨stack, value⟩
                    simp [hPop]
                    rw [Switch.select_toStructured value cases defaultBody]
                    cases hSelected : Switch.select value cases defaultBody with
                    | none =>
                        simp [hSelected]
                    | some selected =>
                        simp [hSelected]
                        exact Block.run_toStructured program fuel selected
                          (state.withEVM { evmAfterScrutinee with stack := stack })
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.run Structured.Stmt.run
            simp [Stmt.toStructured]
            rw [Block.run_toStructured program fuel init state]
            cases hInit :
                Structured.Block.run program.toStructured fuel
                  init.toStructured state with
            | error err =>
                simp [hInit]
            | ok initOutcome =>
                simp [hInit]
                cases initOutcome.mode <;>
                  simp [invalid, Structured.invalid,
                    Stmt.runForLoop_toStructured program fuel cond post body
                    initOutcome.state]
    | brk =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured]
    | cont =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured]
    | leave =>
        cases hReturns : state.returns <;>
          simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured,
            invalid, Structured.invalid, hReturns, Outcome.leave,
            Structured.Outcome.leave]
    | call name =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.run Structured.Stmt.run
            simp [Stmt.toStructured]
            rw [ProcList.lookup?_program_toStructured name program]
            cases hLookup : ProcList.lookup? name program.procs with
            | none =>
                rfl
            | some proc =>
                simp [hLookup, Proc.toStructured]
                cases hSplit :
                    Structured.StackFrame.splitArgs? proc.argc state.evm.stack with
                | none =>
                    simp [hSplit]
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    simp [hSplit]
                    rw [Block.run_toStructured program fuel proc.body
                      ((state.withEVM { state.evm with stack := args }).pushReturn
                        callerStack proc.retc)]
                    cases hBody :
                        Structured.Block.run program.toStructured fuel
                          proc.body.toStructured
                          ((state.withEVM { state.evm with stack := args }).pushReturn
                            callerStack proc.retc) with
                    | error err =>
                        simp [hBody]
                    | ok outcome =>
                        simp [hBody, invalid, Structured.invalid]
                        cases outcome.mode <;>
                          simp [hBody, invalid, Structured.invalid]
                        · cases hPop : outcome.state.popReturn? with
                          | none =>
                              simp [hPop, invalid, Structured.invalid]
                          | some pair =>
                              rcases pair with ⟨frame, returned⟩
                              simp [hPop, invalid, Structured.invalid]
                              cases hAttach :
                                  Structured.StackFrame.attachReturns? frame
                                    outcome.state.evm.stack with
                              | none =>
                                  simp [hAttach, invalid, Structured.invalid]
                              | some stack =>
                                  simp [hAttach, invalid, Structured.invalid]
                        · cases hPop : outcome.state.popReturn? with
                          | none =>
                              simp [hPop, invalid, Structured.invalid]
                          | some pair =>
                              rcases pair with ⟨frame, returned⟩
                              simp [hPop, invalid, Structured.invalid]
                              cases hAttach :
                                  Structured.StackFrame.attachReturns? frame
                                    outcome.state.evm.stack with
                              | none =>
                                  simp [hAttach, invalid, Structured.invalid]
                              | some stack =>
                                  simp [hAttach, invalid, Structured.invalid]
    | terminal kind =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured,
          Structured.Terminal.step]
end

mutual
  def Expr.runWithGasOracle {results : Nat} (expr : Expr results)
      (oracle : Structured.GasOracle) (cursor : Nat)
      (state : EVMState) : Except EVMException (EVMState × Nat) :=
    match expr with
    | .lit value =>
        Structured.BasicInstr.stepWithGasOracle (.push value) oracle cursor
          state
    | .code code =>
        Structured.Code.runWithGasOracle code oracle cursor state
    | .prim op args => do
        let (state', cursor') ← ExprSeq.runWithGasOracle args oracle cursor state
        op.stepWithGasOracle oracle cursor' state'

  def ExprSeq.runWithGasOracle {results : Nat} (exprs : ExprSeq results)
      (oracle : Structured.GasOracle) (cursor : Nat)
      (state : EVMState) : Except EVMException (EVMState × Nat) :=
    match exprs with
    | .nil => .ok (state, cursor)
    | .cons head tail => do
        let (state', cursor') ← Expr.runWithGasOracle head oracle cursor state
        ExprSeq.runWithGasOracle tail oracle cursor' state'
end

namespace Expr

def runStateWithGasOracle {results : Nat} (expr : Expr results)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Nat) := do
  let (evm, cursor') ← expr.runWithGasOracle oracle cursor state.evm
  .ok (state.withEVM evm, cursor')

def runConditionWithGasOracle (cond : Expr 1)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (EVMState × Bool × Nat) := do
  let (state', cursor') ← cond.runWithGasOracle oracle cursor state
  let (stateAfterPop, condTrue) ← Structured.Code.popCondition state'
  .ok (stateAfterPop, condTrue, cursor')

def runConditionStateWithGasOracle (cond : Expr 1)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Bool × Nat) := do
  let (evm, condTrue, cursor') ←
    runConditionWithGasOracle cond oracle cursor state.evm
  .ok (state.withEVM evm, condTrue, cursor')

end Expr

mutual
  def Block.runWithGasOracle (program : Program)
      (oracle : Structured.GasOracle) :
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

  def Stmt.runForLoopWithGasOracle (program : Program)
      (oracle : Structured.GasOracle) (fuel : Nat) (cond : Expr 1)
      (post body : Block) (cursor : Nat) (state : RunState) :
      Except EVMException (Outcome × Nat) :=
    match fuel with
    | 0 =>
        invalid
    | fuel' + 1 =>
        match Expr.runConditionStateWithGasOracle cond oracle cursor state with
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
                                cond post body cursorAfterPost
                                postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok (postOutcome, cursorAfterPost)
                  | .leave | .halt _ =>
                      .ok (bodyOutcome, cursorAfterBody)
            else
              .ok (Outcome.regular stateAfterCond, cursorAfterCond)

  def Stmt.runWithGasOracle (program : Program)
      (oracle : Structured.GasOracle) :
      Nat → Stmt → Nat → RunState → Except EVMException (Outcome × Nat)
    | _fuel, Stmt.code code, cursor, state => do
        let (state', cursor') ←
          Structured.Code.runStateWithGasOracle code oracle cursor state
        .ok (Outcome.regular state', cursor')
    | _fuel, Stmt.expr expr, cursor, state => do
        let (state', cursor') ←
          Expr.runStateWithGasOracle expr oracle cursor state
        .ok (Outcome.regular state', cursor')
    | 0, Stmt.if_ _cond _body, _cursor, _state =>
        invalid
    | fuel + 1, Stmt.if_ cond body, cursor, state =>
        match Expr.runConditionStateWithGasOracle cond oracle cursor state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue, cursorAfterCond) =>
            if condTrue then
              Block.runWithGasOracle program oracle fuel body cursorAfterCond
                stateAfterCond
            else
              .ok (Outcome.regular stateAfterCond, cursorAfterCond)
    | 0, Stmt.switch _scrutinee _cases _defaultBody, _cursor, _state =>
        invalid
    | fuel + 1, Stmt.switch scrutinee cases defaultBody, cursor, state => do
        let (evmAfterScrutinee, cursorAfterScrutinee) ←
          Expr.runWithGasOracle scrutinee oracle cursor state.evm
        match evmAfterScrutinee.stack.pop with
        | none =>
            .error .StackUnderflow
        | some ⟨stack, value⟩ =>
            let evmAfterPop := { evmAfterScrutinee with stack := stack }
            let stateAfterPop := state.withEVM evmAfterPop
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
            match Structured.StackFrame.splitArgs? proc.argc state.evm.stack with
            | none =>
                .error .StackUnderflow
            | some (args, callerStack) =>
                let callEVM := { state.evm with stack := args }
                let callState :=
                  (state.withEVM callEVM).pushReturn callerStack proc.retc
                match Block.runWithGasOracle program oracle fuel proc.body
                    cursor callState with
                | .error err => .error err
                | .ok (outcome, cursorAfterBody) =>
                    match outcome.mode with
                    | .regular | .leave =>
                        match outcome.state.popReturn? with
                        | none => invalid
                        | some (frame, returned) =>
                            match Structured.StackFrame.attachReturns? frame
                                outcome.state.evm.stack with
                            | none => invalid
                            | some stack =>
                                let evm :=
                                  { outcome.state.evm with stack := stack }
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
          Structured.Terminal.stepWithGasOracle kind oracle cursor state.evm
        .ok (Outcome.halt kind (state.withEVM evm), cursor')
end

namespace Program

def runWithGasOracle (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (Outcome × Nat) :=
  Block.runWithGasOracle program oracle fuel program.body cursor
    (Structured.Program.initialState state)

end Program

mutual
  theorem Expr.runWithGasOracle_eq_compile {results : Nat}
      (expr : Expr results) (oracle : Structured.GasOracle) (cursor : Nat)
      (state : EVMState) :
      expr.runWithGasOracle oracle cursor state =
        Structured.Code.runWithGasOracle expr.compile oracle cursor state := by
    cases expr with
    | lit value =>
        rfl
    | code code =>
        rfl
    | prim op args =>
        simp [Expr.runWithGasOracle, Expr.compile,
          Structured.Code.runWithGasOracle_append,
          ExprSeq.runWithGasOracle_eq_compile]
        cases hArgs : Structured.Code.runWithGasOracle args.compile oracle
            cursor state with
        | error err =>
            rfl
        | ok pair =>
            rcases pair with ⟨state', cursor'⟩
            simp [hArgs, Structured.Code.runWithGasOracle,
              Structured.BasicInstr.stepWithGasOracle,
              Structured.BasicOp.stepWithGasOracle]
            cases
              Assembly.GasParametric.Target.stepInstrWithGasOracle oracle
                cursor' (.prim op.toPrimOp) state' <;>
              rfl

  theorem ExprSeq.runWithGasOracle_eq_compile {results : Nat}
      (exprs : ExprSeq results) (oracle : Structured.GasOracle) (cursor : Nat)
      (state : EVMState) :
      exprs.runWithGasOracle oracle cursor state =
        Structured.Code.runWithGasOracle exprs.compile oracle cursor state := by
    cases exprs with
    | nil =>
        rfl
    | cons head tail =>
        simp [ExprSeq.runWithGasOracle, ExprSeq.compile,
          Structured.Code.runWithGasOracle_append,
          Expr.runWithGasOracle_eq_compile,
          ExprSeq.runWithGasOracle_eq_compile]
end

namespace Expr

theorem runStateWithGasOracle_eq_compile {results : Nat}
    (expr : Expr results) (oracle : Structured.GasOracle) (cursor : Nat)
    (state : RunState) :
    expr.runStateWithGasOracle oracle cursor state =
      Structured.Code.runStateWithGasOracle expr.compile oracle cursor state := by
  unfold runStateWithGasOracle Structured.Code.runStateWithGasOracle
  rw [Expr.runWithGasOracle_eq_compile]

theorem runConditionWithGasOracle_eq_compile (cond : Expr 1)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    cond.runConditionWithGasOracle oracle cursor state =
      Structured.Code.runConditionWithGasOracle cond.compile oracle cursor
        state := by
  unfold runConditionWithGasOracle Structured.Code.runConditionWithGasOracle
  rw [Expr.runWithGasOracle_eq_compile]

theorem runConditionStateWithGasOracle_eq_compile (cond : Expr 1)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    cond.runConditionStateWithGasOracle oracle cursor state =
      Structured.Code.runConditionStateWithGasOracle cond.compile oracle cursor
        state := by
  unfold runConditionStateWithGasOracle
    Structured.Code.runConditionStateWithGasOracle
  rw [Expr.runConditionWithGasOracle_eq_compile]

end Expr

set_option maxHeartbeats 1400000 in
mutual
  theorem Block.runWithGasOracle_toStructured (program : Program) :
      ∀ (fuel : Nat) (block : Block) (oracle : Structured.GasOracle)
          (cursor : Nat) (state : RunState),
        Block.runWithGasOracle program oracle fuel block cursor state =
          Structured.Block.runWithGasOracle program.toStructured oracle fuel
            block.toStructured cursor state := by
    intro fuel block oracle cursor state
    cases fuel with
    | zero =>
        cases block
        rfl
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                rfl
            | cons stmt rest =>
                simp [Block.runWithGasOracle, Structured.Block.runWithGasOracle,
                  Block.toStructured, StmtList.toStructured]
                rw [Stmt.runWithGasOracle_toStructured program fuel stmt oracle
                  cursor state]
                cases hStmt :
                    Structured.Stmt.runWithGasOracle program.toStructured oracle
                      fuel stmt.toStructured cursor state with
                | error err =>
                    simp [hStmt]
                | ok pair =>
                    rcases pair with ⟨outcome, cursor'⟩
                    simp [hStmt]
                    cases outcome.mode <;>
                      simp [Block.toStructured,
                        Block.runWithGasOracle_toStructured program fuel
                        { stmts := rest } oracle cursor' outcome.state]

  theorem Stmt.runForLoopWithGasOracle_toStructured (program : Program)
      (fuel : Nat) (cond : Expr 1) (post body : Block)
      (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
      Stmt.runForLoopWithGasOracle program oracle fuel cond post body cursor
          state =
        Structured.Stmt.runForLoopWithGasOracle program.toStructured oracle fuel
          cond.compile post.toStructured body.toStructured cursor state := by
    cases fuel with
    | zero =>
        rfl
    | succ fuel =>
        unfold Stmt.runForLoopWithGasOracle
          Structured.Stmt.runForLoopWithGasOracle
        rw [Expr.runConditionStateWithGasOracle_eq_compile]
        cases hCond :
            Structured.Code.runConditionStateWithGasOracle cond.compile oracle
              cursor state with
        | error err =>
            simp [hCond]
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue, cursorAfterCond⟩
            simp [hCond]
            cases condTrue with
            | false =>
                rfl
            | true =>
                rw [Block.runWithGasOracle_toStructured program fuel body
                  oracle cursorAfterCond stateAfterCond]
                cases hBody :
                    Structured.Block.runWithGasOracle program.toStructured oracle
                      fuel body.toStructured cursorAfterCond stateAfterCond with
                | error err =>
                    simp [hBody]
                | ok bodyPair =>
                    rcases bodyPair with ⟨bodyOutcome, cursorAfterBody⟩
                    simp [hBody]
                    cases bodyOutcome.mode with
                    | brk =>
                        rfl
                    | regular =>
                        rw [Block.runWithGasOracle_toStructured program fuel
                          post oracle cursorAfterBody bodyOutcome.state]
                        cases hPost :
                            Structured.Block.runWithGasOracle
                              program.toStructured oracle fuel
                              post.toStructured cursorAfterBody
                              bodyOutcome.state with
                        | error err =>
                            simp [hPost]
                        | ok postPair =>
                            rcases postPair with ⟨postOutcome, cursorAfterPost⟩
                            simp [hPost, invalid, Structured.invalid]
                            cases postOutcome.mode <;>
                              simp [invalid, Structured.invalid,
                                Stmt.runForLoopWithGasOracle_toStructured
                                  program fuel cond post body oracle
                                  cursorAfterPost postOutcome.state]
                    | cont =>
                        rw [Block.runWithGasOracle_toStructured program fuel
                          post oracle cursorAfterBody bodyOutcome.state]
                        cases hPost :
                            Structured.Block.runWithGasOracle
                              program.toStructured oracle fuel
                              post.toStructured cursorAfterBody
                              bodyOutcome.state with
                        | error err =>
                            simp [hPost]
                        | ok postPair =>
                            rcases postPair with ⟨postOutcome, cursorAfterPost⟩
                            simp [hPost, invalid, Structured.invalid]
                            cases postOutcome.mode <;>
                              simp [invalid, Structured.invalid,
                                Stmt.runForLoopWithGasOracle_toStructured
                                  program fuel cond post body oracle
                                  cursorAfterPost postOutcome.state]
                    | leave =>
                        rfl
                    | halt kind =>
                        rfl

  theorem Stmt.runWithGasOracle_toStructured (program : Program) :
      ∀ (fuel : Nat) (stmt : Stmt) (oracle : Structured.GasOracle)
          (cursor : Nat) (state : RunState),
        Stmt.runWithGasOracle program oracle fuel stmt cursor state =
          Structured.Stmt.runWithGasOracle program.toStructured oracle fuel
            stmt.toStructured cursor state := by
    intro fuel stmt oracle cursor state
    cases stmt with
    | code code =>
        simp [Stmt.runWithGasOracle, Structured.Stmt.runWithGasOracle,
          Stmt.toStructured]
    | expr expr =>
        simp [Stmt.runWithGasOracle, Structured.Stmt.runWithGasOracle,
          Stmt.toStructured, Expr.runStateWithGasOracle_eq_compile,
          Structured.Code.runStateWithGasOracle]
    | if_ cond body =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.runWithGasOracle Structured.Stmt.runWithGasOracle
            simp [Stmt.toStructured]
            rw [Expr.runConditionStateWithGasOracle_eq_compile]
            cases hCond :
                Structured.Code.runConditionStateWithGasOracle cond.compile
                  oracle cursor state with
            | error err =>
                simp [hCond, Except.bind]
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue, cursorAfterCond⟩
                simp [hCond]
                cases condTrue with
                | false =>
                    rfl
                | true =>
                    exact Block.runWithGasOracle_toStructured program fuel body
                      oracle cursorAfterCond stateAfterCond
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.runWithGasOracle Structured.Stmt.runWithGasOracle
            simp [Stmt.toStructured]
            rw [Expr.runWithGasOracle_eq_compile]
            cases hScrutinee :
                Structured.Code.runWithGasOracle scrutinee.compile oracle
                  cursor state.evm with
            | error err =>
                simp [hScrutinee, Structured.Code.runStateWithGasOracle,
                  Except.bind]
            | ok scrutineePair =>
                rcases scrutineePair with
                  ⟨evmAfterScrutinee, cursorAfterScrutinee⟩
                simp [hScrutinee, Structured.Code.runStateWithGasOracle]
                cases hPop : evmAfterScrutinee.stack.pop with
                | none =>
                    simp [hPop]
                | some pair =>
                    rcases pair with ⟨stack, value⟩
                    simp [hPop]
                    rw [Switch.select_toStructured value cases defaultBody]
                    cases hSelected :
                        Switch.select value cases defaultBody with
                    | none =>
                        simp [hSelected]
                    | some selected =>
                        simp [hSelected]
                        exact
                          Block.runWithGasOracle_toStructured program fuel
                            selected oracle cursorAfterScrutinee
                            (state.withEVM
                              { evmAfterScrutinee with stack := stack })
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.runWithGasOracle Structured.Stmt.runWithGasOracle
            simp [Stmt.toStructured]
            rw [Block.runWithGasOracle_toStructured program fuel init oracle
              cursor state]
            cases hInit :
                Structured.Block.runWithGasOracle program.toStructured oracle
                  fuel init.toStructured cursor state with
            | error err =>
                simp [hInit]
            | ok initPair =>
                rcases initPair with ⟨initOutcome, cursorAfterInit⟩
                simp [hInit]
                cases initOutcome.mode <;>
                  simp [invalid, Structured.invalid,
                    Stmt.runForLoopWithGasOracle_toStructured program fuel cond
                    post body oracle cursorAfterInit initOutcome.state]
    | brk =>
        simp [Stmt.runWithGasOracle, Structured.Stmt.runWithGasOracle,
          Stmt.toStructured]
    | cont =>
        simp [Stmt.runWithGasOracle, Structured.Stmt.runWithGasOracle,
          Stmt.toStructured]
    | leave =>
        cases hReturns : state.returns <;>
          simp [Stmt.runWithGasOracle, Structured.Stmt.runWithGasOracle,
            Stmt.toStructured, invalid, Structured.invalid, hReturns,
            Outcome.leave, Structured.Outcome.leave]
    | call name =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.runWithGasOracle Structured.Stmt.runWithGasOracle
            simp [Stmt.toStructured]
            rw [ProcList.lookup?_program_toStructured name program]
            cases hLookup : ProcList.lookup? name program.procs with
            | none =>
                rfl
            | some proc =>
                simp [hLookup, Proc.toStructured]
                cases hSplit :
                    Structured.StackFrame.splitArgs? proc.argc state.evm.stack with
                | none =>
                    simp [hSplit]
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    simp [hSplit]
                    rw [Block.runWithGasOracle_toStructured program fuel
                      proc.body oracle cursor
                      ((state.withEVM { state.evm with stack := args }).pushReturn
                        callerStack proc.retc)]
                    cases hBody :
                        Structured.Block.runWithGasOracle
                          program.toStructured oracle fuel
                          proc.body.toStructured cursor
                          ((state.withEVM
                              { state.evm with stack := args }).pushReturn
                            callerStack proc.retc) with
                    | error err =>
                        simp [hBody]
                    | ok bodyPair =>
                        rcases bodyPair with ⟨outcome, cursorAfterBody⟩
                        simp [hBody, invalid, Structured.invalid]
                        cases outcome.mode <;>
                          simp [hBody, invalid, Structured.invalid]
                        · cases hPop : outcome.state.popReturn? with
                          | none =>
                              simp [hPop, invalid, Structured.invalid]
                          | some pair =>
                              rcases pair with ⟨frame, returned⟩
                              simp [hPop, invalid, Structured.invalid]
                              cases hAttach :
                                  Structured.StackFrame.attachReturns? frame
                                    outcome.state.evm.stack with
                              | none =>
                                  simp [hAttach, invalid, Structured.invalid]
                              | some stack =>
                                  simp [hAttach, invalid, Structured.invalid]
                        · cases hPop : outcome.state.popReturn? with
                          | none =>
                              simp [hPop, invalid, Structured.invalid]
                          | some pair =>
                              rcases pair with ⟨frame, returned⟩
                              simp [hPop, invalid, Structured.invalid]
                              cases hAttach :
                                  Structured.StackFrame.attachReturns? frame
                                    outcome.state.evm.stack with
                              | none =>
                                  simp [hAttach, invalid, Structured.invalid]
                              | some stack =>
                                  simp [hAttach, invalid, Structured.invalid]
    | terminal kind =>
        simp [Stmt.runWithGasOracle, Structured.Stmt.runWithGasOracle,
          Stmt.toStructured, Structured.Terminal.stepWithGasOracle]
end

namespace Program

theorem run_toStructured (fuel : Nat) (program : Program) (state : EVMState) :
    program.run fuel state =
      Structured.Program.run fuel program.toStructured state := by
  exact Block.run_toStructured program fuel program.body
    (Structured.Program.initialState state)

noncomputable def compileChecked? (program : Program) :
    Option Assembly.Program :=
  Structured.Preservation.ProcedurePreservation.compileChecked?
    program.toStructured

theorem compileChecked?_noCallCreate {program : Program}
    {asm : Assembly.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  exact
    Structured.Preservation.ProcedurePreservation.compileChecked?_noCallCreate
      (program := program.toStructured) (asm := asm)
      (by simpa [CompilerFacts.Program.toStructured_usesCallCreate] using
        hProgram)
      hCompile

theorem compile_preserves {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        program.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  have hStructuredRun :
      Structured.Program.run fuel program.toStructured initial = .ok outcome := by
    simpa [run_toStructured fuel program initial] using hRun
  exact
    Structured.Preservation.compile_preserves hCompile hInitialPc hStructuredRun

theorem compile_preserves_checked {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        program.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome :=
  compile_preserves hCompile hInitialPc hRun

theorem compile_preserves_of_compileChecked {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  exact compile_preserves_checked hCompile hInitialPc hRun

theorem runWithGasOracle_toStructured (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    program.runWithGasOracle fuel oracle cursor state =
      Structured.Program.runWithGasOracle fuel program.toStructured oracle
        cursor state := by
  exact Block.runWithGasOracle_toStructured program fuel program.body oracle
    cursor (Structured.Program.initialState state)

noncomputable def compileCheckedWithGasOracle? (program : Program) :
    Option Assembly.Program :=
  Structured.Preservation.GasParametric.compileCheckedWithGasOracle?
    program.toStructured

theorem compileCheckedWithGasOracle?_eq_some {program : Program}
    {asm : Assembly.Program}
    (hCompile : compileCheckedWithGasOracle? program = some asm) :
    Structured.Preservation.GasParametric.compileCheckedWithGasOracle?
      program.toStructured = some asm := by
  exact hCompile

theorem compile_preserves_withGasOracle {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {oracle : Structured.GasOracle} {cursor cursorFinal : Nat}
    {outcome : Outcome}
    (hCompile :
      Structured.Preservation.GasParametric.compileCheckedWithGasOracle?
        program.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      program.runWithGasOracle fuel oracle cursor initial =
        .ok (outcome, cursorFinal)) :
    ∃ targetFuel targetOutcome,
      Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
          targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  have hStructuredRun :
      Structured.Program.runWithGasOracle fuel program.toStructured oracle
          cursor initial =
        .ok (outcome, cursorFinal) := by
    simpa [runWithGasOracle_toStructured fuel program oracle cursor initial]
      using hRun
  exact
    Structured.Preservation.GasParametric.compile_preserves_withGasOracle
      hCompile hInitialPc hStructuredRun

theorem compile_preserves_of_compileCheckedWithGasOracle {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {oracle : Structured.GasOracle} {cursor cursorFinal : Nat}
    {outcome : Outcome}
    (hCompile : compileCheckedWithGasOracle? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      program.runWithGasOracle fuel oracle cursor initial =
        .ok (outcome, cursorFinal)) :
    ∃ targetFuel targetOutcome,
      Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
          targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  exact compile_preserves_withGasOracle hCompile hInitialPc hRun

end Program

end Expressions
end EvmCompiler
