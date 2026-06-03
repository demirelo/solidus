import EvmCompiler.Yul.Reference

/-!
Open source-tower semantics for compiler-generated code.

The imported `Functions.Source` and `Locals.Source` interpreters are closed:
primitive evaluation asks `PrimitiveSemantics.eval` for a concrete result.  For
CALL-family proof work we need the compiler side to stop at the same observable
external request as open Yul evaluation, then resume for every shared response.

This module mirrors the stack-free source interpreters, using the same closed
semantics for ordinary primitives and user functions, while suspending at
CALL/CALLCODE/DELEGATECALL/STATICCALL primitive expressions.
-/

namespace EvmCompiler
namespace Yul
namespace Reference
namespace SourceBridgeFacts
namespace CompilerOpen

abbrev Result (α : Type) :=
  OpenExternal.OpenResult Functions.EVMException α

def invalid {α : Type} : Result α :=
  .done Functions.Source.invalid

namespace Primitive

def openCall?
    (state : Objects.Source.State) (op : Structured.BasicOp)
    (values : List Word) :
    Option
      (OpenExternal.OpenCall
        (Except Functions.EVMException
          (Objects.Source.State × List Word))) :=
  match OpenExternal.CallKind.ofBasicOp? op with
  | none => none
  | some kind =>
      match SourceStateRel.compilerPrimitiveOpenCall? state kind values with
      | none => none
      | some call =>
          some
            { site := call.site
              resume := fun response => .ok (call.resume response) }

def eval (prim : Objects.Source.PrimitiveSemantics)
    (op : Structured.BasicOp) (state : Objects.Source.State)
    (values : List Word) :
    Result (Objects.Source.State × List Word) :=
  match openCall? state op values with
  | some call =>
      .call
        { site := call.site
          resume := fun response => .done (call.resume response) }
  | none =>
      match prim.eval op state.shared values with
      | .ok (sharedAfter, valuesAfter) =>
          .ok (state.withShared sharedAfter, valuesAfter)
      | .error err => .error err

theorem openCall?_none_of_not_callKind
    {state : Objects.Source.State} {op : Structured.BasicOp}
    {values : List Word}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = none) :
    openCall? state op values = none := by
  simp [openCall?, hKind]

theorem eval_of_not_callKind
    {prim : Objects.Source.PrimitiveSemantics}
    {state : Objects.Source.State} {op : Structured.BasicOp}
    {values : List Word}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = none) :
    eval prim op state values =
      match prim.eval op state.shared values with
      | .ok (sharedAfter, valuesAfter) =>
          .ok (state.withShared sharedAfter, valuesAfter)
      | .error err => .error err := by
  simp [eval, openCall?_none_of_not_callKind hKind]

theorem eval_resolves_closed_ok_of_not_callKind
    {prim : Objects.Source.PrimitiveSemantics}
    {state : Objects.Source.State} {op : Structured.BasicOp}
    {values valuesAfter : List Word}
    {sharedAfter : EvmYul.SharedState .EVM}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = none)
    (hEval : prim.eval op state.shared values =
      .ok (sharedAfter, valuesAfter)) :
    OpenExternal.OpenResultResolves (eval prim op state values) []
      (.ok (state.withShared sharedAfter, valuesAfter)) := by
  rw [eval_of_not_callKind hKind, hEval]
  exact OpenExternal.OpenResultResolves.done

theorem eval_resolves_closed_error_of_not_callKind
    {prim : Objects.Source.PrimitiveSemantics}
    {state : Objects.Source.State} {op : Structured.BasicOp}
    {values : List Word} {err : Functions.EVMException}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = none)
    (hEval : prim.eval op state.shared values = .error err) :
    OpenExternal.OpenResultResolves (eval prim op state values) []
      (.error err) := by
  rw [eval_of_not_callKind hKind, hEval]
  exact OpenExternal.OpenResultResolves.done

theorem callKind_none_of_no_callCreate
    {op : Structured.BasicOp}
    (hNoCallCreate : op.toPrimOp.isCallCreate = false) :
    OpenExternal.CallKind.ofBasicOp? op = none := by
  cases op <;>
    simp [OpenExternal.CallKind.ofBasicOp?, Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.isCallCreate] at hNoCallCreate ⊢

theorem openCall?_none_of_no_callCreate
    {state : Objects.Source.State} {op : Structured.BasicOp}
    {values : List Word}
    (hNoCallCreate : op.toPrimOp.isCallCreate = false) :
    openCall? state op values = none :=
  openCall?_none_of_not_callKind
    (callKind_none_of_no_callCreate hNoCallCreate)

theorem eval_of_no_callCreate
    {prim : Objects.Source.PrimitiveSemantics}
    {state : Objects.Source.State} {op : Structured.BasicOp}
    {values : List Word}
    (hNoCallCreate : op.toPrimOp.isCallCreate = false) :
    eval prim op state values =
      match prim.eval op state.shared values with
      | .ok (sharedAfter, valuesAfter) =>
          .ok (state.withShared sharedAfter, valuesAfter)
      | .error err => .error err :=
  eval_of_not_callKind (callKind_none_of_no_callCreate hNoCallCreate)

theorem openCall?_of_basicOp
    {state : Objects.Source.State} {op : Structured.BasicOp}
    {kind : OpenExternal.CallKind} {values : List Word}
    {call : OpenExternal.OpenCall (Objects.Source.State × List Word)}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (hCall :
      SourceStateRel.compilerPrimitiveOpenCall? state kind values =
        some call) :
    openCall? state op values =
      some
        { site := call.site
          resume := fun response => .ok (call.resume response) } := by
  simp [openCall?, hKind, hCall]

theorem eval_suspends_of_basicOp
    {prim : Objects.Source.PrimitiveSemantics}
    {state : Objects.Source.State} {op : Structured.BasicOp}
    {kind : OpenExternal.CallKind} {values : List Word}
    {call : OpenExternal.OpenCall (Objects.Source.State × List Word)}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (hCall :
      SourceStateRel.compilerPrimitiveOpenCall? state kind values =
        some call) :
    eval prim op state values =
      .call
        { site := call.site
          resume := fun response => .done (.ok (call.resume response)) } := by
  simp [eval, openCall?_of_basicOp hKind hCall]

theorem openCall?_toBasicOp
    {state : Objects.Source.State} (kind : OpenExternal.CallKind)
    {values : List Word}
    {call : OpenExternal.OpenCall (Objects.Source.State × List Word)}
    (hCall :
      SourceStateRel.compilerPrimitiveOpenCall? state kind values =
        some call) :
    openCall? state kind.toBasicOp values =
      some
        { site := call.site
          resume := fun response => .ok (call.resume response) } :=
  openCall?_of_basicOp
    (kind := kind) (OpenExternal.CallKind.ofBasicOp?_toBasicOp kind) hCall

theorem eval_suspends_toBasicOp
    {prim : Objects.Source.PrimitiveSemantics}
    {state : Objects.Source.State} (kind : OpenExternal.CallKind)
    {values : List Word}
    {call : OpenExternal.OpenCall (Objects.Source.State × List Word)}
    (hCall :
      SourceStateRel.compilerPrimitiveOpenCall? state kind values =
        some call) :
    eval prim kind.toBasicOp state values =
      .call
        { site := call.site
          resume := fun response => .done (.ok (call.resume response)) } :=
  eval_suspends_of_basicOp
    (kind := kind) (OpenExternal.CallKind.ofBasicOp?_toBasicOp kind) hCall

def ResultRel (cfg : StateRelConfig) (layout : List Name) :
    Except EvmYul.Yul.Exception (EvmYul.Yul.State × List Word) →
      Except Functions.EVMException (Objects.Source.State × List Word) →
        Prop
  | .ok sourceResult, .ok compilerResult =>
      SourceStateRel.OpenPrimitiveResultRel cfg layout sourceResult
        compilerResult
  | _, _ => False

theorem yulCompilerOpenCallRel_toYulOperation
    {cfg : StateRelConfig} {layout : List Name}
    {sourceShared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {compiler : Objects.Source.State}
    (hRel :
      SourceStateRel cfg layout (.Ok sourceShared store) compiler)
    (kind : OpenExternal.CallKind)
    (operands : OpenExternal.CallOperands) :
    ∃ sourceCall :
        OpenExternal.OpenCall
          (Except EvmYul.Yul.Exception
            (EvmYul.Yul.State × List Word)),
    ∃ compilerCall :
        OpenExternal.OpenCall
          (Except Functions.EVMException
            (Objects.Source.State × List Word)),
      OpenExternal.CallKind.yulPrimitiveEvalValuesOpenCall?
          (.Ok sourceShared store) kind.toYulOperation
          (kind.args operands) =
        some sourceCall ∧
      openCall? compiler kind.toBasicOp (kind.args operands).reverse =
        some compilerCall ∧
      OpenExternal.OpenCallRel
        (SharedStateRel.OpenExternalResponseRel cfg sourceShared
          compiler.shared)
        (ResultRel cfg layout) sourceCall compilerCall := by
  rcases
      SourceStateRel.openExternalPrimitiveOpenCallRel_of_args
        hRel kind operands with
    ⟨sourceCall, compilerCall, hSourceCall, hCompilerCall, hCallRel⟩
  let sourceExceptCall :
      OpenExternal.OpenCall
        (Except EvmYul.Yul.Exception (EvmYul.Yul.State × List Word)) :=
    { site := sourceCall.site
      resume := fun response => .ok (sourceCall.resume response) }
  let compilerExceptCall :
      OpenExternal.OpenCall
        (Except Functions.EVMException
          (Objects.Source.State × List Word)) :=
    { site := compilerCall.site
      resume := fun response => .ok (compilerCall.resume response) }
  refine ⟨sourceExceptCall, compilerExceptCall, ?_, ?_, ?_⟩
  · simp [OpenExternal.CallKind.yulPrimitiveEvalValuesOpenCall?,
      OpenExternal.CallKind.ofYulOperation?_toYulOperation, hSourceCall,
      sourceExceptCall]
  · simpa [compilerExceptCall] using
      openCall?_toBasicOp (state := compiler) kind hCompilerCall
  · constructor
    · simpa [sourceExceptCall, compilerExceptCall] using hCallRel.sameSite
    · intro response hResponse
      dsimp [sourceExceptCall, compilerExceptCall, ResultRel]
      exact hCallRel.preservesAllResponses response hResponse

end Primitive

namespace LocalsExpr

mutual
  def eval {results : Nat}
      (prim : Objects.Source.PrimitiveSemantics)
      (expr : Locals.Expr results) (state : Objects.Source.State) :
      Result (Objects.Source.State × List Word) :=
    match expr with
    | .lit value => .ok (state, [value])
    | .var name =>
        match state.vars name with
        | some value => .ok (state, [value])
        | none => invalid
    | .code _code => invalid
    | .prim op args =>
        OpenExternal.OpenResult.bind (evalSeq prim args state)
          fun argResult =>
            Primitive.eval prim op argResult.1 argResult.2

  def evalSeq {results : Nat}
      (prim : Objects.Source.PrimitiveSemantics)
      (exprs : Locals.ExprSeq results) (state : Objects.Source.State) :
      Result (Objects.Source.State × List Word) :=
    match exprs with
    | .nil => .ok (state, [])
    | .cons head tail =>
        OpenExternal.OpenResult.bind (eval prim head state)
          fun headResult =>
            OpenExternal.OpenResult.bind
              (evalSeq prim tail headResult.1)
              fun tailResult =>
                .ok (tailResult.1, headResult.2 ++ tailResult.2)
end

def evalOne {results : Nat}
    (prim : Objects.Source.PrimitiveSemantics)
    (expr : Locals.Expr results) (state : Objects.Source.State) :
    Result (Objects.Source.State × Word) :=
  OpenExternal.OpenResult.bind (eval prim expr state)
    fun result =>
      match result.2 with
      | [value] => .ok (result.1, value)
      | _ => invalid

def evalCondition
    (prim : Objects.Source.PrimitiveSemantics)
    (expr : Locals.Expr 1) (state : Objects.Source.State) :
    Result (Objects.Source.State × Bool) :=
  OpenExternal.OpenResult.bind (evalOne prim expr state)
    fun result =>
      .ok (result.1, result.2 != EvmYul.UInt256.ofNat 0)

end LocalsExpr

namespace FunctionsOpen

abbrev State := Objects.Source.State
abbrev Ctx := Functions.Source.Ctx
abbrev Outcome := Functions.Source.Outcome
abbrev CallResult := Functions.Source.CallResult

namespace ArgList

def eval (prim : Objects.Source.PrimitiveSemantics) :
    List (Functions.Expr 1) → State → Result (State × List Word)
  | [], state => .ok (state, [])
  | arg :: rest, state =>
      OpenExternal.OpenResult.bind
        (LocalsExpr.evalOne prim arg state)
        fun argResult =>
          OpenExternal.OpenResult.bind
            (eval prim rest argResult.1)
            fun restResult =>
              .ok (restResult.1, argResult.2 :: restResult.2)

end ArgList

mutual
  def Block.runOpen (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) (ctx : Ctx) :
      Nat → Functions.Block → State → Result (Outcome × Ctx)
    | 0, _block, _state => invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Functions.Source.Outcome.regular state, ctx)
    | fuel + 1, ⟨stmt :: rest⟩, state =>
        OpenExternal.OpenResult.bind
          (Stmt.run prim program ctx fuel stmt state)
          fun stmtResult =>
            match stmtResult.1.mode with
            | .regular =>
                Block.runOpen prim program stmtResult.2 fuel
                  { stmts := rest } stmtResult.1.state
            | .brk | .cont | .leave | .halt _ =>
                .ok (stmtResult.1, ctx)
  termination_by fuel block _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScoped (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) (ctx : Ctx)
      (block : Functions.Block) (fuel : Nat) (state : State) :
      Result Outcome :=
    OpenExternal.OpenResult.bind
      (Block.runOpen prim program ctx fuel block state)
      fun result =>
        match result.1.mode with
        | .regular =>
            .ok (Functions.Source.Outcome.regular
              (result.1.state.restrictTo ctx.scope))
        | .brk | .cont | .leave | .halt _ =>
            .ok result.1
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def FunDef.runBody (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) (fn : Functions.FunDef)
      (args : List Word) :
      Nat → EvmYul.SharedState .EVM → Result CallResult
    | 0, _shared => invalid
    | fuel + 1, shared =>
        match Functions.Source.Store.insertMany fn.params args
            Locals.Source.Store.empty with
        | none => invalid
        | some paramStore =>
            let initialStore :=
              Functions.Source.Store.initReturns fn.returns paramStore
            let initialState : State :=
              { shared := shared, vars := initialStore }
            let functionScope := fn.returns ++ fn.params
            let bodyCtx :=
              (Functions.Source.Ctx.initial.withLeaveScope functionScope)
            let bodyCtx := { bodyCtx with scope := functionScope }
            OpenExternal.OpenResult.bind
              (Block.runOpen prim program bodyCtx fuel fn.body
                initialState)
              fun bodyResult =>
                match bodyResult.1.mode with
                | .regular | .leave =>
                    match Functions.Source.Store.lookupMany fn.returns
                        bodyResult.1.state.vars with
                    | none => invalid
                    | some values =>
                        .ok (.returned bodyResult.1.state.shared values)
                | .brk | .cont => invalid
                | .halt kind =>
                    .ok (.halted kind bodyResult.1.state)
  termination_by fuel _shared => (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.runForLoop (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) (loopCtx : Ctx)
      (cond : Functions.Expr 1) (postBase : Ctx)
      (post : Functions.Block) (bodyBase : Ctx)
      (body : Functions.Block) :
      Nat → State → Result Outcome
    | 0, _state => invalid
    | fuel + 1, state =>
        OpenExternal.OpenResult.bind
          (LocalsExpr.evalCondition prim cond state)
          fun condResult =>
            if condResult.2 then
              OpenExternal.OpenResult.bind
                (Block.runScoped prim program bodyBase body fuel
                  condResult.1)
                fun bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Functions.Source.Outcome.regular
                        bodyOutcome.state)
                  | .regular | .cont =>
                      OpenExternal.OpenResult.bind
                        (Block.runScoped prim program postBase post fuel
                          bodyOutcome.state)
                        fun postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop prim program loopCtx cond
                                postBase post bodyBase body fuel
                                postOutcome.state
                          | .brk | .cont => invalid
                          | .leave | .halt _ => .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok (Functions.Source.Outcome.regular
                (condResult.1.restrictTo loopCtx.scope))
  termination_by fuel _state => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run (prim : Objects.Source.PrimitiveSemantics)
      (program : Functions.Program) (ctx : Ctx) :
      Nat → Functions.Stmt → State → Result (Outcome × Ctx)
    | _fuel, .expr expr, state =>
        OpenExternal.OpenResult.bind
          (LocalsExpr.eval prim expr state)
          fun result =>
            .ok (Functions.Source.Outcome.regular result.1, ctx)
    | _fuel, .let_ name value, state =>
        OpenExternal.OpenResult.bind
          (LocalsExpr.evalOne prim value state)
          fun result =>
            .ok
              (Functions.Source.Outcome.regular
                (result.1.insert name result.2),
                { ctx with scope := name :: ctx.scope })
    | _fuel, .assign name value, state =>
        if state.vars.contains name then
          OpenExternal.OpenResult.bind
            (LocalsExpr.evalOne prim value state)
            fun result =>
              .ok
                (Functions.Source.Outcome.regular
                  (result.1.withVars
                    (Locals.Source.Store.insert result.1.vars name
                      result.2)),
                  ctx)
        else
          invalid
    | fuel, .block body, state =>
        OpenExternal.OpenResult.bind
          (Block.runScoped prim program ctx body fuel state)
          fun outcome =>
            .ok (outcome, ctx)
    | 0, .if_ _cond _body, _state => invalid
    | fuel + 1, .if_ cond body, state =>
        OpenExternal.OpenResult.bind
          (LocalsExpr.evalCondition prim cond state)
          fun condResult =>
            if condResult.2 then
              OpenExternal.OpenResult.bind
                (Block.runScoped prim program ctx body fuel condResult.1)
                fun outcome =>
                  .ok (outcome, ctx)
            else
              .ok (Functions.Source.Outcome.regular condResult.1, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state => invalid
    | fuel + 1, .switch scrutinee cases defaultBody, state =>
        OpenExternal.OpenResult.bind
          (LocalsExpr.evalOne prim scrutinee state)
          fun scrutineeResult =>
            match Functions.Source.Switch.select scrutineeResult.2 cases
                defaultBody with
            | none =>
                .ok (Functions.Source.Outcome.regular scrutineeResult.1, ctx)
            | some body =>
                OpenExternal.OpenResult.bind
                  (Block.runScoped prim program ctx body fuel
                    scrutineeResult.1)
                  fun outcome =>
                    .ok (outcome, ctx)
    | 0, .for_ _init _cond _post _body, _state => invalid
    | fuel + 1, .for_ init cond post body, state =>
        let initBase := ctx.withoutLoopControl
        OpenExternal.OpenResult.bind
          (Block.runOpen prim program initBase fuel init state)
          fun initResult =>
            match initResult.1.mode with
            | .regular =>
                let loopCtx := initResult.2
                let postBase := initResult.2.withoutLoopControl
                let bodyBase :=
                  initResult.2.withLoopControl initResult.2.scope
                    initResult.2.scope
                OpenExternal.OpenResult.bind
                  (Stmt.runForLoop prim program loopCtx cond postBase post
                    bodyBase body fuel initResult.1.state)
                  fun loopOutcome =>
                    match loopOutcome.mode with
                    | .regular =>
                        .ok
                          (Functions.Source.Outcome.regular
                            (loopOutcome.state.restrictTo ctx.scope),
                            ctx)
                    | .brk | .cont => invalid
                    | .leave | .halt _ =>
                        .ok (loopOutcome, ctx)
            | .brk | .cont => invalid
            | .leave | .halt _ =>
                .ok (initResult.1, ctx)
    | _fuel, .brk, state =>
        match ctx.breakScope? with
        | none => invalid
        | some scope =>
            .ok (Functions.Source.Outcome.brk (state.restrictTo scope), ctx)
    | _fuel, .cont, state =>
        match ctx.continueScope? with
        | none => invalid
        | some scope =>
            .ok (Functions.Source.Outcome.cont (state.restrictTo scope), ctx)
    | _fuel, .leave, state =>
        match ctx.leaveScope? with
        | none => invalid
        | some scope =>
            .ok (Functions.Source.Outcome.leave (state.restrictTo scope),
              ctx)
    | 0, .call _targets _functionName _args, _state => invalid
    | fuel + 1, .call targets functionName args, state =>
        if targets.Nodup then
          OpenExternal.OpenResult.bind
            (ArgList.eval prim args state)
            fun argResult =>
              match Functions.Source.FunList.find? functionName
                  program.functions with
              | none => invalid
              | some fn =>
                  OpenExternal.OpenResult.bind
                    (FunDef.runBody prim program fn argResult.2 fuel
                      argResult.1.shared)
                    fun callResult =>
                      match callResult with
                      | .returned sharedAfterCall returnValues =>
                          match Functions.Source.Store.assignMany targets
                              returnValues argResult.1.vars with
                          | none => invalid
                          | some returnStore =>
                              .ok
                                (Functions.Source.Outcome.regular
                                  { shared := sharedAfterCall
                                    vars := returnStore },
                                  ctx)
                      | .halted kind haltedState =>
                          .ok (Functions.Source.Outcome.halt kind haltedState,
                            ctx)
        else
          invalid
    | _fuel, .terminal kind, state =>
        match prim.terminal kind state.shared [] with
        | .ok sharedAfter =>
            .ok (Functions.Source.Outcome.halt kind
              (state.withShared sharedAfter), ctx)
        | .error err => .error err
    | _fuel, .terminalArgs kind args, state =>
        OpenExternal.OpenResult.bind
          (LocalsExpr.evalSeq prim args state)
          fun argResult =>
            match prim.terminal kind argResult.1.shared argResult.2 with
            | .ok sharedAfter =>
                .ok
                  (Functions.Source.Outcome.halt kind
                    (argResult.1.withShared sharedAfter),
                    ctx)
            | .error err => .error err
  termination_by fuel stmt _state => (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

def runState (prim : Objects.Source.PrimitiveSemantics)
    (fuel : Nat) (program : Functions.Program) (initial : State) :
    Result Outcome :=
  Block.runScoped prim program Functions.Source.Ctx.initial program.body fuel
    initial

def run (prim : Objects.Source.PrimitiveSemantics)
    (fuel : Nat) (program : Functions.Program) (state : EVMState) :
    Result Outcome :=
  runState prim fuel program
    (Functions.Source.Program.initialState state.toSharedState)

end Program

end FunctionsOpen

end CompilerOpen
end SourceBridgeFacts
end Reference
end Yul
end EvmCompiler
