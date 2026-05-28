import EvmCompiler.Locals.Compiler
import EvmCompiler.Structured.GasParametric

namespace EvmCompiler
namespace Locals

abbrev Outcome := Structured.Outcome
abbrev RunState := Structured.RunState

abbrev invalid {α : Type} : Except EVMException α :=
  Structured.invalid

namespace Outcome

abbrev regular := Structured.Outcome.regular
abbrev brk := Structured.Outcome.brk
abbrev cont := Structured.Outcome.cont
abbrev leave := Structured.Outcome.leave
abbrev halt := Structured.Outcome.halt

end Outcome

namespace Direct

namespace ProcList

def lookup? (name : Name) : List Proc → Option Proc
  | [] => none
  | proc :: rest =>
      if proc.name = name then
        some proc
      else
        lookup? name rest

end ProcList

namespace Switch

def select (scrutinee : Word) :
    List (Word × Block) → Option Block → Option Block
  | [], defaultBody => defaultBody
  | (value, body) :: rest, defaultBody =>
      if value = scrutinee then
        some body
      else
        select scrutinee rest defaultBody

end Switch

namespace Expr

mutual
  def runCode {results : Nat} (ctx : Ctx) (offset : Nat)
      (expr : Expr results) (state : EVMState) :
      Except EVMException EVMState :=
    match expr with
    | .lit value =>
        Structured.BasicInstr.step (.push value) state
    | .var name =>
        match Layout.lookupDepth? name ctx.layout with
        | none => invalid
        | some depth =>
            match StackOp.dup? (offset + depth) with
            | none => invalid
            | some op => op.step state
    | .code code =>
        Structured.Code.run code state
    | .prim op args => do
        let state' ← ExprSeq.runCode ctx offset args state
        op.step state'

  def ExprSeq.runCode {results : Nat} (ctx : Ctx) (offset : Nat)
      (exprs : ExprSeq results) (state : EVMState) :
      Except EVMException EVMState :=
    match exprs with
    | .nil => .ok state
    | .cons (left := left) head tail => do
        let state' ← runCode ctx offset head state
        ExprSeq.runCode ctx (offset + left) tail state'
end

def runState {results : Nat} (ctx : Ctx) (expr : Expr results)
    (state : RunState) : Except EVMException RunState := do
  let evm ← runCode ctx 0 expr state.evm
  .ok (state.withEVM evm)

def runCondition (ctx : Ctx) (cond : Expr 1) (state : RunState) :
    Except EVMException (RunState × Bool) := do
  let evm ← runCode ctx 0 cond state.evm
  let (evm', condTrue) ← Structured.Code.popCondition evm
  .ok (state.withEVM evm', condTrue)

mutual
  def runCodeWithGasOracle {results : Nat} (ctx : Ctx) (offset : Nat)
      (expr : Expr results) (oracle : Structured.GasOracle) (cursor : Nat)
      (state : EVMState) : Except EVMException (EVMState × Nat) :=
    match expr with
    | .lit value =>
        Structured.BasicInstr.stepWithGasOracle (.push value) oracle cursor
          state
    | .var name =>
        match Layout.lookupDepth? name ctx.layout with
        | none => invalid
        | some depth =>
            match StackOp.dup? (offset + depth) with
            | none => invalid
            | some op => op.stepWithGasOracle oracle cursor state
    | .code code =>
        Structured.Code.runWithGasOracle code oracle cursor state
    | .prim op args => do
        let (state', cursor') ←
          ExprSeq.runCodeWithGasOracle ctx offset args oracle cursor state
        op.stepWithGasOracle oracle cursor' state'

  def ExprSeq.runCodeWithGasOracle {results : Nat} (ctx : Ctx)
      (offset : Nat) (exprs : ExprSeq results)
      (oracle : Structured.GasOracle) (cursor : Nat)
      (state : EVMState) : Except EVMException (EVMState × Nat) :=
    match exprs with
    | .nil => .ok (state, cursor)
    | .cons (left := left) head tail => do
        let (state', cursor') ←
          runCodeWithGasOracle ctx offset head oracle cursor state
        ExprSeq.runCodeWithGasOracle ctx (offset + left) tail oracle cursor'
          state'
end

def runStateWithGasOracle {results : Nat} (ctx : Ctx) (expr : Expr results)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Nat) := do
  let (evm, cursor') ←
    runCodeWithGasOracle ctx 0 expr oracle cursor state.evm
  .ok (state.withEVM evm, cursor')

def runConditionWithGasOracle (ctx : Ctx) (cond : Expr 1)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Bool × Nat) := do
  let (evm, cursor') ←
    runCodeWithGasOracle ctx 0 cond oracle cursor state.evm
  let (evm', condTrue) ← Structured.Code.popCondition evm
  .ok (state.withEVM evm', condTrue, cursor')

end Expr

namespace Ctx

def runCleanupTo (ctx : Ctx) (targetDepth : Nat) (state : RunState) :
    Except EVMException RunState :=
  match ctx.cleanupTo? targetDepth with
  | none => invalid
  | some code => Structured.Code.runState code state

def runCleanupToPreserving (ctx : Ctx) (preserve targetDepth : Nat)
    (state : RunState) :
    Except EVMException RunState :=
  match ctx.cleanupToPreserving? preserve targetDepth with
  | none => invalid
  | some code => Structured.Code.runState code state

def runCleanupAll (ctx : Ctx) (state : RunState) :
    Except EVMException RunState :=
  Structured.Code.runState ctx.cleanupAll state

def runCleanupToWithGasOracle (ctx : Ctx) (targetDepth : Nat)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Nat) :=
  match ctx.cleanupTo? targetDepth with
  | none => invalid
  | some code => Structured.Code.runStateWithGasOracle code oracle cursor state

def runCleanupToPreservingWithGasOracle (ctx : Ctx) (preserve targetDepth : Nat)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Nat) :=
  match ctx.cleanupToPreserving? preserve targetDepth with
  | none => invalid
  | some code => Structured.Code.runStateWithGasOracle code oracle cursor state

def runCleanupAllWithGasOracle (ctx : Ctx) (oracle : Structured.GasOracle)
    (cursor : Nat) (state : RunState) :
    Except EVMException (RunState × Nat) :=
  Structured.Code.runStateWithGasOracle ctx.cleanupAll oracle cursor state

namespace CleanupFacts

/--
Running the plain scoped-cleanup code made of `POP`s drops exactly that many
stack entries and preserves the shared EVM state.
-/
theorem run_replicate_pop_ok (state : EVMState) :
    ∀ n final,
      Structured.Code.run
          (List.replicate n (Structured.BasicInstr.op .pop)) state =
        .ok final →
      final.stack = state.stack.drop n ∧
        final.toSharedState = state.toSharedState := by
  intro n
  induction n generalizing state with
  | zero =>
      intro final hRun
      simp [Structured.Code.run] at hRun
      cases hRun
      simp
  | succ n ih =>
      intro final hRun
      cases state with
      | mk shared pc stack execLength =>
          cases stack with
          | nil =>
              simp [Structured.Code.run, Structured.BasicInstr.step,
                Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
                Assembly.Target.stepInstr, Assembly.PrimOp.step,
                Assembly.PrimStep.run, Assembly.PrimOp.continuingStep?,
                EvmYul.Stack.pop, List.replicate_succ] at hRun
          | cons top rest =>
              let state0 : EVMState :=
                { toSharedState := shared, pc := pc, stack := top :: rest,
                  execLength := execLength }
              let stepState : EVMState :=
                state0.replaceStackAndIncrPC rest
              have hStep :
                  Structured.BasicInstr.step (Structured.BasicInstr.op .pop)
                      state0 =
                    .ok stepState := by
                simp [state0, stepState, Structured.BasicInstr.step,
                  Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
                  Assembly.Target.stepInstr, Assembly.PrimOp.step,
                  Assembly.PrimStep.run, Assembly.PrimOp.continuingStep?,
                  EvmYul.Stack.pop]
              have hTail :
                  Structured.Code.run
                      (List.replicate n (Structured.BasicInstr.op .pop))
                      stepState =
                    .ok final := by
                simpa [Structured.Code.run, List.replicate_succ, state0,
                  hStep] using hRun
              rcases ih stepState final hTail with
                ⟨hStack, hShared⟩
              exact ⟨by simpa [state0, stepState] using hStack,
                by simpa [state0, stepState] using hShared⟩

end CleanupFacts

/--
Successful cleanup to a target depth drops exactly the locals above that depth.
It does not change the ghost return stack.
-/
theorem runCleanupTo_stack_drop {ctx : Ctx} {targetDepth : Nat}
    {state cleaned : RunState}
    (hRun : runCleanupTo ctx targetDepth state = .ok cleaned) :
    targetDepth ≤ ctx.layout.length ∧
      cleaned.evm.stack =
        state.evm.stack.drop (ctx.layout.length - targetDepth) ∧
      cleaned.evm.toSharedState = state.evm.toSharedState ∧
      cleaned.returns = state.returns := by
  unfold runCleanupTo at hRun
  unfold Locals.Ctx.cleanupTo? at hRun
  by_cases hTarget : targetDepth ≤ ctx.layout.length
  · simp [hTarget, Structured.Code.runState] at hRun
    cases hCode :
        Structured.Code.run
          (List.replicate (ctx.layout.length - targetDepth)
            (Structured.BasicInstr.op .pop)) state.evm with
    | error err =>
        simp [hCode] at hRun
    | ok evmClean =>
        simp [hCode] at hRun
        cases hRun
        rcases CleanupFacts.run_replicate_pop_ok state.evm
            (ctx.layout.length - targetDepth) evmClean hCode with
          ⟨hStack, hShared⟩
        exact ⟨hTarget, hStack, hShared, by simp⟩
  · simp [hTarget, invalid, Structured.invalid] at hRun

end Ctx

mutual
  def Block.runOpen (program : Program) (ctx : Ctx) :
      Nat → Block → RunState → Except EVMException (Outcome × Ctx)
    | 0, _block, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Outcome.regular state, ctx)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let (outcome, ctx') ← Stmt.run program ctx fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.runOpen program ctx' fuel { stmts := rest } outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, ctx)
  termination_by fuel block _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScoped (program : Program) (ctx : Ctx) (block : Block)
      (fuel : Nat) (state : RunState) :
      Except EVMException Outcome := do
    let (outcome, finalCtx) ← Block.runOpen program ctx fuel block state
    match outcome.mode with
    | .regular =>
        let state' ← Ctx.runCleanupTo finalCtx ctx.layout.length outcome.state
        .ok (Outcome.regular state')
    | .brk | .cont | .leave | .halt _ =>
        .ok outcome
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def Stmt.runForLoop (program : Program) (loopCtx : Ctx) (cond : Expr 1)
      (postBase : Ctx) (post : Block) (bodyBase : Ctx) (body : Block) :
      Nat → RunState → Except EVMException Outcome
    | 0, _state =>
        invalid
    | fuel + 1, state =>
        match Expr.runCondition loopCtx cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match Block.runScoped program bodyBase body fuel stateAfterCond with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match Block.runScoped program postBase post fuel
                          bodyOutcome.state with
                      | .error err => .error err
                      | .ok postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop program loopCtx cond postBase post
                                bodyBase body fuel postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok (Outcome.regular stateAfterCond)
  termination_by fuel _state => (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run (program : Program) (ctx : Ctx) :
      Nat → Stmt → RunState → Except EVMException (Outcome × Ctx)
    | _fuel, .expr expr, state => do
        let state' ← Expr.runState ctx expr state
        .ok (Outcome.regular state', ctx)
    | _fuel, .exprs exprs, state => do
        let evm ← Expr.ExprSeq.runCode ctx 0 exprs state.evm
        .ok (Outcome.regular (state.withEVM evm), ctx)
    | _fuel, .let_ name value, state => do
        let state' ← Expr.runState ctx value state
        .ok (Outcome.regular state', ctx.withLayout (name :: ctx.layout))
    | _fuel, .assign name value, state => do
        let depth ← (Layout.lookupDepth? name ctx.layout).elim invalid pure
        let swapOp ← (StackOp.swap? depth).elim invalid pure
        let evmAfterValue ← Expr.runCode ctx 0 value state.evm
        let evmAfterSwap ← swapOp.step evmAfterValue
        let evmAfterPop ← Structured.BasicOp.pop.step evmAfterSwap
        .ok (Outcome.regular (state.withEVM evmAfterPop), ctx)
    | _fuel, .assignTop name, state => do
        let depth ← (Layout.lookupDepth? name ctx.layout).elim invalid pure
        let swapOp ← (StackOp.swap? depth).elim invalid pure
        let evmAfterSwap ← swapOp.step state.evm
        let evmAfterPop ← Structured.BasicOp.pop.step evmAfterSwap
        .ok (Outcome.regular (state.withEVM evmAfterPop), ctx)
    | _fuel, .assignTopWithOffset offset name, state => do
        let depth ← (Layout.lookupDepth? name ctx.layout).elim invalid pure
        let swapOp ← (StackOp.swap? (offset + depth)).elim invalid pure
        let evmAfterSwap ← swapOp.step state.evm
        let evmAfterPop ← Structured.BasicOp.pop.step evmAfterSwap
        .ok (Outcome.regular (state.withEVM evmAfterPop), ctx)
    | _fuel, .block body, state => do
        let outcome ← Block.runScoped program ctx body _fuel state
        .ok (outcome, ctx)
    | 0, .if_ _cond _body, _state =>
        invalid
    | fuel + 1, .if_ cond body, state =>
        match Expr.runCondition ctx cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then do
              let outcome ← Block.runScoped program ctx body fuel stateAfterCond
              .ok (outcome, ctx)
            else
              .ok (Outcome.regular stateAfterCond, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        invalid
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let stateAfterScrutinee ← Expr.runState ctx scrutinee state
        match stateAfterScrutinee.evm.stack.pop with
        | none =>
            .error .StackUnderflow
        | some ⟨stack, value⟩ =>
            let stateAfterPop :=
              stateAfterScrutinee.withEVM
                { stateAfterScrutinee.evm with stack := stack }
            match Switch.select value cases defaultBody with
            | none => .ok (Outcome.regular stateAfterPop, ctx)
            | some body => do
                let outcome ← Block.runScoped program ctx body fuel stateAfterPop
                .ok (outcome, ctx)
    | 0, .for_ _init _cond _post _body, _state =>
        invalid
    | fuel + 1, .for_ init cond post body, state => do
        let initBase := ctx.withoutLoopControl
        let (initOutcome, initCtx) ← Block.runOpen program initBase fuel init state
        match initOutcome.mode with
        | .regular =>
            let postBase := initCtx.withoutLoopControl
            let bodyBase := initCtx.withLoopControl initCtx.layout.length
            let loopOutcome ←
              Stmt.runForLoop program initCtx cond postBase post bodyBase body
                fuel initOutcome.state
            match loopOutcome.mode with
            | .regular =>
                let state' ← Ctx.runCleanupTo initCtx ctx.layout.length
                  loopOutcome.state
                .ok (Outcome.regular state', ctx)
            | .brk | .cont =>
                invalid
            | .leave | .halt _ =>
                .ok (loopOutcome, ctx)
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok (initOutcome, ctx)
    | _fuel, .brk, state => do
        let target ← ctx.breakDepth?.elim invalid pure
        let state' ← Ctx.runCleanupTo ctx target state
        .ok (Outcome.brk state', ctx)
    | _fuel, .cont, state => do
        let target ← ctx.continueDepth?.elim invalid pure
        let state' ← Ctx.runCleanupTo ctx target state
        .ok (Outcome.cont state', ctx)
    | _fuel, .leave, state => do
        let target ← ctx.leaveDepth?.elim invalid pure
        let state' ← Ctx.runCleanupToPreserving ctx ctx.leaveRetc target state
        match state'.returns with
        | [] => invalid
        | _ :: _ => .ok (Outcome.leave state', ctx)
    | 0, .call _name, _state =>
        invalid
    | fuel + 1, .call name, state =>
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
                match Block.runOpen program
                    (Ctx.procEntryWithLayoutAndRetc
                      proc.entryLayout proc.retc) fuel proc.body
                    callState with
                | .error err => .error err
                | .ok (outcome, bodyCtx) =>
                    match outcome.mode with
                    | .regular => do
                        let bodyState ←
                          Ctx.runCleanupToPreserving bodyCtx proc.retc 0
                            outcome.state
                        match bodyState.popReturn? with
                        | none => invalid
                        | some (frame, returned) =>
                            match Structured.StackFrame.attachReturns? frame
                                bodyState.evm.stack with
                            | none => invalid
                            | some stack =>
                                let evm := { bodyState.evm with stack := stack }
                                .ok (Outcome.regular (returned.withEVM evm), ctx)
                    | .leave =>
                        match outcome.state.popReturn? with
                        | none => invalid
                        | some (frame, returned) =>
                            match Structured.StackFrame.attachReturns? frame
                                outcome.state.evm.stack with
                            | none => invalid
                            | some stack =>
                                let evm := { outcome.state.evm with stack := stack }
                                .ok (Outcome.regular (returned.withEVM evm), ctx)
                    | .brk | .cont =>
                        invalid
                    | .halt kind =>
                        .ok (Outcome.halt kind outcome.state, ctx)
    | _fuel, .terminal kind, state => do
        let stateAfterCleanup ← Ctx.runCleanupAll ctx state
        let evm ← Structured.Terminal.step kind stateAfterCleanup.evm
        .ok (Outcome.halt kind (stateAfterCleanup.withEVM evm), ctx)
    | _fuel, .terminalArgs kind args, state => do
        let evmAfterArgs ← Expr.ExprSeq.runCode ctx 0 args state.evm
        let evm ← Structured.Terminal.step kind evmAfterArgs
        .ok (Outcome.halt kind (state.withEVM evm), ctx)
  termination_by fuel stmt _state => (fuel, 3, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

mutual
  def Block.runOpenWithGasOracle (program : Program) (ctx : Ctx)
      (oracle : Structured.GasOracle) :
      Nat → Block → Nat → RunState →
        Except EVMException (Outcome × Ctx × Nat)
    | 0, _block, _cursor, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, cursor, state =>
        .ok (Outcome.regular state, ctx, cursor)
    | fuel + 1, ⟨stmt :: rest⟩, cursor, state => do
        let (outcome, ctx', cursor') ←
          Stmt.runWithGasOracle program ctx oracle fuel stmt cursor state
        match outcome.mode with
        | .regular =>
            Block.runOpenWithGasOracle program ctx' oracle fuel
              { stmts := rest } cursor' outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, ctx, cursor')
  termination_by fuel block _cursor _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScopedWithGasOracle (program : Program) (ctx : Ctx)
      (block : Block) (oracle : Structured.GasOracle) (fuel : Nat)
      (cursor : Nat) (state : RunState) :
      Except EVMException (Outcome × Nat) := do
    let (outcome, finalCtx, cursor') ←
      Block.runOpenWithGasOracle program ctx oracle fuel block cursor state
    match outcome.mode with
    | .regular =>
        let (state', cursor'') ←
          Ctx.runCleanupToWithGasOracle finalCtx ctx.layout.length oracle
            cursor' outcome.state
        .ok (Outcome.regular state', cursor'')
    | .brk | .cont | .leave | .halt _ =>
        .ok (outcome, cursor')
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def Stmt.runForLoopWithGasOracle (program : Program) (loopCtx : Ctx)
      (cond : Expr 1) (postBase : Ctx) (post : Block) (bodyBase : Ctx)
      (body : Block) (oracle : Structured.GasOracle) :
      Nat → Nat → RunState → Except EVMException (Outcome × Nat)
    | 0, _cursor, _state =>
        invalid
    | fuel + 1, cursor, state =>
        match Expr.runConditionWithGasOracle loopCtx cond oracle cursor state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue, cursorAfterCond) =>
            if condTrue then
              match Block.runScopedWithGasOracle program bodyBase body oracle fuel
                  cursorAfterCond stateAfterCond with
              | .error err => .error err
              | .ok (bodyOutcome, cursorAfterBody) =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state, cursorAfterBody)
                  | .regular | .cont =>
                      match Block.runScopedWithGasOracle program postBase post
                          oracle fuel cursorAfterBody bodyOutcome.state with
                      | .error err => .error err
                      | .ok (postOutcome, cursorAfterPost) =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoopWithGasOracle program loopCtx cond
                                postBase post bodyBase body oracle fuel
                                cursorAfterPost postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok (postOutcome, cursorAfterPost)
                  | .leave | .halt _ =>
                      .ok (bodyOutcome, cursorAfterBody)
            else
              .ok (Outcome.regular stateAfterCond, cursorAfterCond)
  termination_by fuel _cursor _state => (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.runWithGasOracle (program : Program) (ctx : Ctx)
      (oracle : Structured.GasOracle) :
      Nat → Stmt → Nat → RunState →
        Except EVMException (Outcome × Ctx × Nat)
    | _fuel, .expr expr, cursor, state => do
        let (state', cursor') ←
          Expr.runStateWithGasOracle ctx expr oracle cursor state
        .ok (Outcome.regular state', ctx, cursor')
    | _fuel, .exprs exprs, cursor, state => do
        let (evm, cursor') ←
          Expr.ExprSeq.runCodeWithGasOracle ctx 0 exprs oracle cursor state.evm
        .ok (Outcome.regular (state.withEVM evm), ctx, cursor')
    | _fuel, .let_ name value, cursor, state => do
        let (state', cursor') ←
          Expr.runStateWithGasOracle ctx value oracle cursor state
        .ok (Outcome.regular state', ctx.withLayout (name :: ctx.layout),
          cursor')
    | _fuel, .assign name value, cursor, state => do
        let depth ← (Layout.lookupDepth? name ctx.layout).elim invalid pure
        let swapOp ← (StackOp.swap? depth).elim invalid pure
        let (evmAfterValue, cursorAfterValue) ←
          Expr.runCodeWithGasOracle ctx 0 value oracle cursor state.evm
        let (evmAfterSwap, cursorAfterSwap) ←
          swapOp.stepWithGasOracle oracle cursorAfterValue evmAfterValue
        let (evmAfterPop, cursorAfterPop) ←
          Structured.BasicOp.pop.stepWithGasOracle oracle cursorAfterSwap
            evmAfterSwap
        .ok (Outcome.regular (state.withEVM evmAfterPop), ctx, cursorAfterPop)
    | _fuel, .assignTop name, cursor, state => do
        let depth ← (Layout.lookupDepth? name ctx.layout).elim invalid pure
        let swapOp ← (StackOp.swap? depth).elim invalid pure
        let (evmAfterSwap, cursorAfterSwap) ←
          swapOp.stepWithGasOracle oracle cursor state.evm
        let (evmAfterPop, cursorAfterPop) ←
          Structured.BasicOp.pop.stepWithGasOracle oracle cursorAfterSwap
            evmAfterSwap
        .ok (Outcome.regular (state.withEVM evmAfterPop), ctx, cursorAfterPop)
    | _fuel, .assignTopWithOffset offset name, cursor, state => do
        let depth ← (Layout.lookupDepth? name ctx.layout).elim invalid pure
        let swapOp ← (StackOp.swap? (offset + depth)).elim invalid pure
        let (evmAfterSwap, cursorAfterSwap) ←
          swapOp.stepWithGasOracle oracle cursor state.evm
        let (evmAfterPop, cursorAfterPop) ←
          Structured.BasicOp.pop.stepWithGasOracle oracle cursorAfterSwap
            evmAfterSwap
        .ok (Outcome.regular (state.withEVM evmAfterPop), ctx, cursorAfterPop)
    | _fuel, .block body, cursor, state => do
        let (outcome, cursor') ←
          Block.runScopedWithGasOracle program ctx body oracle _fuel cursor state
        .ok (outcome, ctx, cursor')
    | 0, .if_ _cond _body, _cursor, _state =>
        invalid
    | fuel + 1, .if_ cond body, cursor, state =>
        match Expr.runConditionWithGasOracle ctx cond oracle cursor state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue, cursorAfterCond) =>
            if condTrue then do
              let (outcome, cursor') ←
                Block.runScopedWithGasOracle program ctx body oracle fuel
                  cursorAfterCond stateAfterCond
              .ok (outcome, ctx, cursor')
            else
              .ok (Outcome.regular stateAfterCond, ctx, cursorAfterCond)
    | 0, .switch _scrutinee _cases _defaultBody, _cursor, _state =>
        invalid
    | fuel + 1, .switch scrutinee cases defaultBody, cursor, state => do
        let (stateAfterScrutinee, cursorAfterScrutinee) ←
          Expr.runStateWithGasOracle ctx scrutinee oracle cursor state
        match stateAfterScrutinee.evm.stack.pop with
        | none =>
            .error .StackUnderflow
        | some ⟨stack, value⟩ =>
            let stateAfterPop :=
              stateAfterScrutinee.withEVM
                { stateAfterScrutinee.evm with stack := stack }
            match Switch.select value cases defaultBody with
            | none =>
                .ok (Outcome.regular stateAfterPop, ctx, cursorAfterScrutinee)
            | some body => do
                let (outcome, cursor') ←
                  Block.runScopedWithGasOracle program ctx body oracle fuel
                    cursorAfterScrutinee stateAfterPop
                .ok (outcome, ctx, cursor')
    | 0, .for_ _init _cond _post _body, _cursor, _state =>
        invalid
    | fuel + 1, .for_ init cond post body, cursor, state => do
        let initBase := ctx.withoutLoopControl
        let (initOutcome, initCtx, cursorAfterInit) ←
          Block.runOpenWithGasOracle program initBase oracle fuel init cursor state
        match initOutcome.mode with
        | .regular =>
            let postBase := initCtx.withoutLoopControl
            let bodyBase := initCtx.withLoopControl initCtx.layout.length
            let (loopOutcome, cursorAfterLoop) ←
              Stmt.runForLoopWithGasOracle program initCtx cond postBase post
                bodyBase body oracle fuel cursorAfterInit initOutcome.state
            match loopOutcome.mode with
            | .regular =>
                let (state', cursor') ←
                  Ctx.runCleanupToWithGasOracle initCtx ctx.layout.length oracle
                    cursorAfterLoop loopOutcome.state
                .ok (Outcome.regular state', ctx, cursor')
            | .brk | .cont =>
                invalid
            | .leave | .halt _ =>
                .ok (loopOutcome, ctx, cursorAfterLoop)
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok (initOutcome, ctx, cursorAfterInit)
    | _fuel, .brk, cursor, state => do
        let target ← ctx.breakDepth?.elim invalid pure
        let (state', cursor') ←
          Ctx.runCleanupToWithGasOracle ctx target oracle cursor state
        .ok (Outcome.brk state', ctx, cursor')
    | _fuel, .cont, cursor, state => do
        let target ← ctx.continueDepth?.elim invalid pure
        let (state', cursor') ←
          Ctx.runCleanupToWithGasOracle ctx target oracle cursor state
        .ok (Outcome.cont state', ctx, cursor')
    | _fuel, .leave, cursor, state => do
        let target ← ctx.leaveDepth?.elim invalid pure
        let (state', cursor') ←
          Ctx.runCleanupToPreservingWithGasOracle ctx ctx.leaveRetc target oracle
            cursor state
        match state'.returns with
        | [] => invalid
        | _ :: _ => .ok (Outcome.leave state', ctx, cursor')
    | 0, .call _name, _cursor, _state =>
        invalid
    | fuel + 1, .call name, cursor, state =>
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
                match Block.runOpenWithGasOracle program
                    (Ctx.procEntryWithLayoutAndRetc
                      proc.entryLayout proc.retc) oracle fuel proc.body cursor
                    callState with
                | .error err => .error err
                | .ok (outcome, bodyCtx, cursorAfterBody) =>
                    match outcome.mode with
                    | .regular => do
                        let (bodyState, cursorAfterCleanup) ←
                          Ctx.runCleanupToPreservingWithGasOracle bodyCtx
                            proc.retc 0 oracle cursorAfterBody outcome.state
                        match bodyState.popReturn? with
                        | none => invalid
                        | some (frame, returned) =>
                            match Structured.StackFrame.attachReturns? frame
                                bodyState.evm.stack with
                            | none => invalid
                            | some stack =>
                                let evm := { bodyState.evm with stack := stack }
                                .ok (Outcome.regular (returned.withEVM evm), ctx,
                                  cursorAfterCleanup)
                    | .leave =>
                        match outcome.state.popReturn? with
                        | none => invalid
                        | some (frame, returned) =>
                            match Structured.StackFrame.attachReturns? frame
                                outcome.state.evm.stack with
                            | none => invalid
                            | some stack =>
                                let evm := { outcome.state.evm with stack := stack }
                                .ok (Outcome.regular (returned.withEVM evm), ctx,
                                  cursorAfterBody)
                    | .brk | .cont =>
                        invalid
                    | .halt kind =>
                        .ok (Outcome.halt kind outcome.state, ctx,
                          cursorAfterBody)
    | _fuel, .terminal kind, cursor, state => do
        let (stateAfterCleanup, cursorAfterCleanup) ←
          Ctx.runCleanupAllWithGasOracle ctx oracle cursor state
        let (evm, cursor') ←
          Structured.Terminal.stepWithGasOracle kind oracle cursorAfterCleanup
            stateAfterCleanup.evm
        .ok (Outcome.halt kind (stateAfterCleanup.withEVM evm), ctx, cursor')
    | _fuel, .terminalArgs kind args, cursor, state => do
        let (evmAfterArgs, cursorAfterArgs) ←
          Expr.ExprSeq.runCodeWithGasOracle ctx 0 args oracle cursor state.evm
        let (evm, cursor') ←
          Structured.Terminal.stepWithGasOracle kind oracle cursorAfterArgs
            evmAfterArgs
        .ok (Outcome.halt kind (state.withEVM evm), ctx, cursor')
  termination_by fuel stmt _cursor _state => (fuel, 3, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Block

/--
On regular exit, a scoped block has run its open body and then cleaned the stack
back to the incoming block layout depth.
-/
theorem runScoped_regular_cleanup {program : Program} {ctx : Ctx}
    {block : Block} {fuel : Nat} {state final : RunState}
    (hRun :
      runScoped program ctx block fuel state = .ok (Outcome.regular final)) :
    ∃ openFinal finalCtx,
      runOpen program ctx fuel block state =
        .ok (Outcome.regular openFinal, finalCtx) ∧
      Ctx.runCleanupTo finalCtx ctx.layout.length openFinal = .ok final ∧
      ctx.layout.length ≤ finalCtx.layout.length ∧
      final.evm.stack =
        openFinal.evm.stack.drop
          (finalCtx.layout.length - ctx.layout.length) ∧
      final.returns = openFinal.returns := by
  unfold runScoped at hRun
  cases hOpen : runOpen program ctx fuel block state with
  | error err =>
      simp [hOpen] at hRun
  | ok openResult =>
      rcases openResult with ⟨openOutcome, finalCtx⟩
      rcases openOutcome with ⟨openFinal, mode⟩
      cases mode <;> simp [hOpen, Outcome.regular] at hRun
      case regular =>
        cases hCleanup :
            Ctx.runCleanupTo finalCtx ctx.layout.length openFinal with
        | error err =>
            simp [hCleanup] at hRun
        | ok cleaned =>
            simp [hCleanup] at hRun
            cases hRun
            rcases Ctx.runCleanupTo_stack_drop hCleanup with
              ⟨hDepth, hStack, _hShared, hReturns⟩
            refine ⟨openFinal, finalCtx, ?_, hCleanup, hDepth, hStack,
              hReturns⟩
            rfl
      all_goals cases hRun

end Block

namespace Program

def runState (fuel : Nat) (program : Program) (state : RunState) :
    Except EVMException Outcome :=
  Block.runScoped program Ctx.initial program.body fuel state

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  runState fuel program (Structured.Program.initialState state)

def runStateWithGasOracle (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : RunState) :
    Except EVMException (Outcome × Nat) :=
  Block.runScopedWithGasOracle program Ctx.initial program.body oracle fuel
    cursor state

def runWithGasOracle (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (Outcome × Nat) :=
  runStateWithGasOracle fuel program oracle cursor
    (Structured.Program.initialState state)

inductive Eval :
    Nat → Program → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program} {initial : EVMState}
      {outcome : Outcome}
      (hRun : run fuel program initial = .ok outcome) :
      Eval fuel program initial outcome

end Program

end Direct

namespace Program

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  Direct.Program.run fuel program state

def runWithGasOracle (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (Outcome × Nat) :=
  Direct.Program.runWithGasOracle fuel program oracle cursor state

inductive Eval :
    Nat → Program → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program} {initial : EVMState}
      {outcome : Outcome}
      (hRun : run fuel program initial = .ok outcome) :
      Eval fuel program initial outcome

theorem eval_of_run {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hRun : run fuel program initial = .ok outcome) :
    Eval fuel program initial outcome := by
  exact Eval.ofRun hRun

end Program

end Locals
end EvmCompiler
