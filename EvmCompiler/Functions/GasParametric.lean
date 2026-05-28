import EvmCompiler.Functions.Semantics

namespace EvmCompiler
namespace Functions
namespace Direct

def evalArgsWithGasOracle (ctx : Ctx) : List (Expr 1) →
    Structured.GasOracle → Nat → RunState →
      Except EVMException (RunState × Nat)
  | [], _oracle, cursor, state => .ok (state, cursor)
  | arg :: rest, oracle, cursor, state => do
      let (evm, cursor') ←
        Locals.Direct.Expr.ExprSeq.runCodeWithGasOracle ctx 0
          (Lower.argExprs (arg :: rest)) oracle cursor state.evm
      .ok (state.withEVM evm, cursor')

def pushReturnsWithGasOracle (ctx : Ctx) : List Name →
    Structured.GasOracle → Nat → RunState →
      Except EVMException (RunState × Nat)
  | [], _oracle, cursor, state => .ok (state, cursor)
  | name :: rest, oracle, cursor, state => do
      let (evm, cursor') ←
        Locals.Direct.Expr.ExprSeq.runCodeWithGasOracle ctx 0
          (Lower.returnExprs (name :: rest)) oracle cursor state.evm
      .ok (state.withEVM evm, cursor')

def initReturnsWithGasOracle : List Name → Ctx → Structured.GasOracle →
    Nat → RunState → Except EVMException (RunState × Ctx × Nat)
  | [], ctx, _oracle, cursor, state => .ok (state, ctx, cursor)
  | name :: rest, ctx, oracle, cursor, state => do
      let (state', cursor') ←
        Locals.Direct.Expr.runStateWithGasOracle ctx (.lit zero) oracle cursor
          state
      initReturnsWithGasOracle rest (ctx.withLayout (name :: ctx.layout))
        oracle cursor' state'

def assignTopWithGasOracle (ctx : Ctx) (name : Name)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Nat) := do
  let depth ← (Locals.Layout.lookupDepth? name ctx.layout).elim
    Structured.invalid pure
  let swapOp ← (Locals.StackOp.swap? depth).elim Structured.invalid pure
  let (evmAfterSwap, cursorAfterSwap) ←
    swapOp.stepWithGasOracle oracle cursor state.evm
  let (evmAfterPop, cursorAfterPop) ←
    Structured.BasicOp.pop.stepWithGasOracle oracle cursorAfterSwap
      evmAfterSwap
  .ok (state.withEVM evmAfterPop, cursorAfterPop)

def assignTopWithOffsetWithGasOracle (ctx : Ctx) (offset : Nat)
    (name : Name) (oracle : Structured.GasOracle) (cursor : Nat)
    (state : RunState) :
    Except EVMException (RunState × Nat) := do
  let depth ← (Locals.Layout.lookupDepth? name ctx.layout).elim
    Structured.invalid pure
  let swapOp ← (Locals.StackOp.swap? (offset + depth)).elim
    Structured.invalid pure
  let (evmAfterSwap, cursorAfterSwap) ←
    swapOp.stepWithGasOracle oracle cursor state.evm
  let (evmAfterPop, cursorAfterPop) ←
    Structured.BasicOp.pop.stepWithGasOracle oracle cursorAfterSwap
      evmAfterSwap
  .ok (state.withEVM evmAfterPop, cursorAfterPop)

def assignReturnedTopsWithGasOracle (ctx : Ctx) : List Name →
    Structured.GasOracle → Nat → RunState →
      Except EVMException (RunState × Nat)
  | [], _oracle, cursor, state => .ok (state, cursor)
  | name :: rest, oracle, cursor, state => do
      let (state', cursor') ←
        assignTopWithOffsetWithGasOracle ctx rest.length name oracle cursor state
      assignReturnedTopsWithGasOracle ctx rest oracle cursor' state'

set_option maxHeartbeats 800000 in
mutual
  def Block.runOpenWithGasOracle (program : Program) (returns : List Name)
      (ctx : Ctx) (oracle : Structured.GasOracle) :
      Nat → Block → Nat → RunState →
        Except EVMException (Outcome × Ctx × Nat)
    | 0, _block, _cursor, _state =>
        Structured.invalid
    | _fuel + 1, ⟨[]⟩, cursor, state =>
        .ok (Structured.Outcome.regular state, ctx, cursor)
    | fuel + 1, ⟨stmt :: rest⟩, cursor, state => do
        let (outcome, ctx', cursor') ←
          Stmt.runWithGasOracle program returns ctx oracle fuel stmt cursor
            state
        match outcome.mode with
        | .regular =>
            Block.runOpenWithGasOracle program returns ctx' oracle fuel
              { stmts := rest } cursor' outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, ctx, cursor')
  termination_by fuel block _cursor _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScopedWithGasOracle (program : Program) (returns : List Name)
      (ctx : Ctx) (block : Block) (oracle : Structured.GasOracle)
      (fuel : Nat) (cursor : Nat) (state : RunState) :
      Except EVMException (Outcome × Nat) := do
    let (outcome, finalCtx, cursor') ←
      Block.runOpenWithGasOracle program returns ctx oracle fuel block cursor
        state
    match outcome.mode with
    | .regular =>
        let (state', cursor'') ←
          Locals.Direct.Ctx.runCleanupToWithGasOracle finalCtx
            ctx.layout.length oracle cursor' outcome.state
        .ok (Structured.Outcome.regular state', cursor'')
    | .brk | .cont | .leave | .halt _ =>
        .ok (outcome, cursor')
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def FunDef.runBodyWithGasOracle (program : Program) (fn : FunDef)
      (oracle : Structured.GasOracle) :
      Nat → Nat → RunState → Except EVMException (Outcome × Nat)
    | 0, _cursor, _state =>
        Structured.invalid
    | fuel + 1, cursor, state => do
        let entryCtx :=
          Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length
        let (stateAfterInit, initCtx, cursorAfterInit) ←
          initReturnsWithGasOracle fn.returns entryCtx oracle cursor state
        let (bodyOutcome, bodyCtx, cursorAfterBody) ←
          Block.runOpenWithGasOracle program fn.returns initCtx oracle fuel
            fn.body cursorAfterInit stateAfterInit
        match bodyOutcome.mode with
        | .regular =>
            let (stateAfterReturns, cursorAfterReturns) ←
              pushReturnsWithGasOracle bodyCtx fn.returns oracle
                cursorAfterBody bodyOutcome.state
            let (stateAfterCleanup, cursorAfterCleanup) ←
              Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle bodyCtx
                fn.returns.length 0 oracle cursorAfterReturns
                stateAfterReturns
            .ok (Structured.Outcome.regular stateAfterCleanup,
              cursorAfterCleanup)
        | .brk | .cont =>
            Structured.invalid
        | .leave | .halt _ =>
            .ok (bodyOutcome, cursorAfterBody)
  termination_by fuel _cursor _state => (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.runForLoopWithGasOracle (program : Program)
      (returns : List Name) (loopCtx : Ctx) (cond : Expr 1)
      (postBase : Ctx) (post : Block) (bodyBase : Ctx) (body : Block)
      (oracle : Structured.GasOracle) :
      Nat → Nat → RunState → Except EVMException (Outcome × Nat)
    | 0, _cursor, _state =>
        Structured.invalid
    | fuel + 1, cursor, state =>
        match Locals.Direct.Expr.runConditionWithGasOracle loopCtx cond oracle
            cursor state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue, cursorAfterCond) =>
            if condTrue then
              match Block.runScopedWithGasOracle program returns bodyBase body
                  oracle fuel cursorAfterCond stateAfterCond with
              | .error err => .error err
              | .ok (bodyOutcome, cursorAfterBody) =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Structured.Outcome.regular bodyOutcome.state,
                        cursorAfterBody)
                  | .regular | .cont =>
                      match Block.runScopedWithGasOracle program returns postBase
                          post oracle fuel cursorAfterBody bodyOutcome.state with
                      | .error err => .error err
                      | .ok (postOutcome, cursorAfterPost) =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoopWithGasOracle program returns
                                loopCtx cond postBase post bodyBase body oracle
                                fuel cursorAfterPost postOutcome.state
                          | .brk | .cont =>
                              Structured.invalid
                          | .leave | .halt _ =>
                              .ok (postOutcome, cursorAfterPost)
                  | .leave | .halt _ =>
                      .ok (bodyOutcome, cursorAfterBody)
            else
              .ok (Structured.Outcome.regular stateAfterCond, cursorAfterCond)
  termination_by fuel _cursor _state => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.runWithGasOracle (program : Program) (returns : List Name)
      (ctx : Ctx) (oracle : Structured.GasOracle) :
      Nat → Stmt → Nat → RunState →
        Except EVMException (Outcome × Ctx × Nat)
    | _fuel, .expr expr, cursor, state => do
        let (state', cursor') ←
          Locals.Direct.Expr.runStateWithGasOracle ctx expr oracle cursor state
        .ok (Structured.Outcome.regular state', ctx, cursor')
    | _fuel, .let_ name value, cursor, state => do
        let (state', cursor') ←
          Locals.Direct.Expr.runStateWithGasOracle ctx value oracle cursor state
        .ok (Structured.Outcome.regular state',
          ctx.withLayout (name :: ctx.layout), cursor')
    | _fuel, .assign name value, cursor, state => do
        let (stateAfterValue, cursorAfterValue) ←
          Locals.Direct.Expr.runStateWithGasOracle ctx value oracle cursor state
        let (stateAfterAssign, cursorAfterAssign) ←
          assignTopWithGasOracle ctx name oracle cursorAfterValue
            stateAfterValue
        .ok (Structured.Outcome.regular stateAfterAssign, ctx,
          cursorAfterAssign)
    | fuel, .block body, cursor, state => do
        let (outcome, cursor') ←
          Block.runScopedWithGasOracle program returns ctx body oracle fuel
            cursor state
        .ok (outcome, ctx, cursor')
    | 0, .if_ _cond _body, _cursor, _state =>
        Structured.invalid
    | fuel + 1, .if_ cond body, cursor, state =>
        match Locals.Direct.Expr.runConditionWithGasOracle ctx cond oracle
            cursor state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue, cursorAfterCond) =>
            if condTrue then do
              let (outcome, cursor') ←
                Block.runScopedWithGasOracle program returns ctx body oracle
                  fuel cursorAfterCond stateAfterCond
              .ok (outcome, ctx, cursor')
            else
              .ok (Structured.Outcome.regular stateAfterCond, ctx,
                cursorAfterCond)
    | 0, .switch _scrutinee _cases _defaultBody, _cursor, _state =>
        Structured.invalid
    | fuel + 1, .switch scrutinee cases defaultBody, cursor, state => do
        let (stateAfterScrutinee, cursorAfterScrutinee) ←
          Locals.Direct.Expr.runStateWithGasOracle ctx scrutinee oracle cursor
            state
        let (stack, value) ← stateAfterScrutinee.evm.stack.pop.elim
          Structured.invalid pure
        let stateAfterPop :=
          stateAfterScrutinee.withEVM
            { stateAfterScrutinee.evm with stack := stack }
        match Switch.select value cases defaultBody with
        | none =>
            .ok (Structured.Outcome.regular stateAfterPop, ctx,
              cursorAfterScrutinee)
        | some body =>
            let (outcome, cursor') ←
              Block.runScopedWithGasOracle program returns ctx body oracle fuel
                cursorAfterScrutinee stateAfterPop
            .ok (outcome, ctx, cursor')
    | 0, .for_ _init _cond _post _body, _cursor, _state =>
        Structured.invalid
    | fuel + 1, .for_ init cond post body, cursor, state => do
        let initBase := ctx.withoutLoopControl
        let (initOutcome, initCtx, cursorAfterInit) ←
          Block.runOpenWithGasOracle program returns initBase oracle fuel init
            cursor state
        match initOutcome.mode with
        | .regular =>
            let postBase := initCtx.withoutLoopControl
            let bodyBase := initCtx.withLoopControl initCtx.layout.length
            let (loopOutcome, cursorAfterLoop) ←
              Stmt.runForLoopWithGasOracle program returns initCtx cond
                postBase post bodyBase body oracle fuel cursorAfterInit
                initOutcome.state
            match loopOutcome.mode with
            | .regular =>
                let (state', cursor') ←
                  Locals.Direct.Ctx.runCleanupToWithGasOracle initCtx
                    ctx.layout.length oracle cursorAfterLoop loopOutcome.state
                .ok (Structured.Outcome.regular state', ctx, cursor')
            | .brk | .cont =>
                Structured.invalid
            | .leave | .halt _ =>
                .ok (loopOutcome, ctx, cursorAfterLoop)
        | .brk | .cont =>
            Structured.invalid
        | .leave | .halt _ =>
            .ok (initOutcome, ctx, cursorAfterInit)
    | _fuel, .brk, cursor, state => do
        let target ← ctx.breakDepth?.elim Structured.invalid pure
        let (state', cursor') ←
          Locals.Direct.Ctx.runCleanupToWithGasOracle ctx target oracle cursor
            state
        .ok (Structured.Outcome.brk state', ctx, cursor')
    | _fuel, .cont, cursor, state => do
        let target ← ctx.continueDepth?.elim Structured.invalid pure
        let (state', cursor') ←
          Locals.Direct.Ctx.runCleanupToWithGasOracle ctx target oracle cursor
            state
        .ok (Structured.Outcome.cont state', ctx, cursor')
    | _fuel, .leave, cursor, state => do
        let (stateAfterReturns, cursorAfterReturns) ←
          pushReturnsWithGasOracle ctx returns oracle cursor state
        let target ← ctx.leaveDepth?.elim Structured.invalid pure
        let (state', cursor') ←
          Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle ctx
            ctx.leaveRetc target oracle cursorAfterReturns stateAfterReturns
        match state'.returns with
        | [] => Structured.invalid
        | _ :: _ => .ok (Structured.Outcome.leave state', ctx, cursor')
    | 0, .call _targets _functionName _args, _cursor, _state =>
        Structured.invalid
    | fuel + 1, .call targets functionName args, cursor, state => do
        let (stateAfterArgs, cursorAfterArgs) ←
          evalArgsWithGasOracle ctx args oracle cursor state
        let fn ← (FunList.find? functionName program.functions).elim
          Structured.invalid pure
        let (argStack, callerStack) ←
          (Structured.StackFrame.splitArgs? fn.params.length
            stateAfterArgs.evm.stack).elim Structured.invalid pure
        let callState :=
          (stateAfterArgs.withEVM { stateAfterArgs.evm with stack := argStack })
            |>.pushReturn callerStack fn.returns.length
        let (outcome, cursorAfterBody) ←
          FunDef.runBodyWithGasOracle program fn oracle fuel cursorAfterArgs
            callState
        match outcome.mode with
        | .regular | .leave =>
            let (frame, returned) ← outcome.state.popReturn?.elim
              Structured.invalid pure
            let stack ← (Structured.StackFrame.attachReturns? frame
              outcome.state.evm.stack).elim Structured.invalid pure
            let stateWithReturns :=
              returned.withEVM { outcome.state.evm with stack := stack }
            let (stateAfterAssign, cursorAfterAssign) ←
              assignReturnedTopsWithGasOracle ctx targets.reverse oracle
                cursorAfterBody stateWithReturns
            .ok (Structured.Outcome.regular stateAfterAssign, ctx,
              cursorAfterAssign)
        | .brk | .cont =>
            Structured.invalid
        | .halt kind =>
            .ok (Structured.Outcome.halt kind outcome.state, ctx,
              cursorAfterBody)
    | _fuel, .terminal kind, cursor, state => do
        let (stateAfterCleanup, cursorAfterCleanup) ←
          Locals.Direct.Ctx.runCleanupAllWithGasOracle ctx oracle cursor state
        let (evm, cursor') ←
          Structured.Terminal.stepWithGasOracle kind oracle cursorAfterCleanup
            stateAfterCleanup.evm
        .ok (Structured.Outcome.halt kind (stateAfterCleanup.withEVM evm),
          ctx, cursor')
    | _fuel, .terminalArgs kind args, cursor, state => do
        let (evmAfterArgs, cursorAfterArgs) ←
          Locals.Direct.Expr.ExprSeq.runCodeWithGasOracle ctx 0 args oracle
            cursor state.evm
        let (evm, cursor') ←
          Structured.Terminal.stepWithGasOracle kind oracle cursorAfterArgs
            evmAfterArgs
        .ok (Structured.Outcome.halt kind (state.withEVM evm), ctx, cursor')
  termination_by fuel stmt _cursor _state => (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

def runStateWithGasOracle (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (Outcome × Nat) :=
  Block.runScopedWithGasOracle program [] Locals.Ctx.initial program.body
    oracle fuel cursor state

def runWithGasOracle (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (Outcome × Nat) :=
  runStateWithGasOracle fuel program oracle cursor
    (Structured.RunState.initial state)

end Program

end Direct

namespace Program

def runWithGasOracle (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (Outcome × Nat) :=
  Direct.Program.runWithGasOracle fuel program oracle cursor state

end Program

end Functions
end EvmCompiler
