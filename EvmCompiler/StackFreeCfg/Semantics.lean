import EvmCompiler.StackFreeCfg.Syntax

namespace EvmCompiler
namespace StackFreeCfg

abbrev SharedState := EvmYul.SharedState .EVM
abbrev EVMState := Assembly.EVMState

namespace Store

abbrev T := Name → Option Word

def empty : T :=
  fun _ => none

def insert (store : T) (name : Name) (value : Word) : T :=
  fun key => if key = name then some value else store key

def contains (store : T) (name : Name) : Bool :=
  (store name).isSome

def restrictTo (scope : List Name) (store : T) : T :=
  fun key => if key ∈ scope then store key else none

def insertMany : List Name → List Word → T → Option T
  | [], [], store => some store
  | name :: names, value :: values, store =>
      insertMany names values (insert store name value)
  | _, _, _ => none

def assignMany : List Name → List Word → T → Option T
  | [], [], store => some store
  | name :: names, value :: values, store =>
      if contains store name then
        assignMany names values (insert store name value)
      else
        none
  | _, _, _ => none

def lookupMany : List Name → T → Option (List Word)
  | [], _store => some []
  | name :: names, store => do
      let value ← store name
      let values ← lookupMany names store
      some (value :: values)

end Store

structure State where
  shared : SharedState
  vars : Store.T := Store.empty

namespace State

def withShared (state : State) (shared : SharedState) : State :=
  { state with shared := shared }

def withVars (state : State) (vars : Store.T) : State :=
  { state with vars := vars }

def restrictTo (scope : List Name) (state : State) : State :=
  { state with vars := Store.restrictTo scope state.vars }

def insertMany? (state : State) (names : List Name) (values : List Word) :
    Option State := do
  let vars ← Store.insertMany names values state.vars
  some (state.withVars vars)

def assignMany? (state : State) (names : List Name) (values : List Word) :
    Option State := do
  let vars ← Store.assignMany names values state.vars
  some (state.withVars vars)

end State

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def zeros (n : Nat) : List Word :=
  List.replicate n zero

abbrev invalid {α : Type} : Except EVMException α :=
  .error .InvalidInstruction

/--
Shared value-level primitive semantics for StackFreeCfg.

The source language is stack-free; this adapter is the explicit boundary where
already-shared EVM/Yul primitive meaning is reused. It evaluates a primitive on
an isolated argument vector and projects only the shared EVM state plus result
values back to the source interpreter.
-/
structure PrimitiveSemantics where
  eval :
    Assembly.PrimOp → SharedState → List Word →
      Except EVMException (SharedState × List Word)
  terminal :
    Assembly.HaltKind → SharedState → List Word →
      Except EVMException SharedState

namespace PrimitiveSemantics

def isolatedState (shared : SharedState) (args : List Word) : EVMState :=
  { toSharedState := shared
    pc := EvmYul.UInt256.ofNat 0
    stack := args
    execLength := 0 }

def canonical : PrimitiveSemantics where
  eval op shared args := do
    if op.haltKind?.isSome then
      invalid
    else
      match op.stackEffect? with
      | none => invalid
      | some (inputArity, outputArity) =>
          if args.length = inputArity then
            let state' ← op.step (isolatedState shared args)
            if state'.stack.length = outputArity then
              .ok (state'.toSharedState, state'.stack)
            else
              invalid
          else
            .error .StackUnderflow
  terminal kind shared args := do
    if args.length = kind.argCount then
      let state' ← kind.toPrimOp.step (isolatedState shared args)
      .ok state'.toSharedState
    else
      .error .StackUnderflow

end PrimitiveSemantics

structure Ctx where
  scope : List Name := []
  canBreak : Bool := false
  canContinue : Bool := false
  canLeave : Bool := false

namespace Ctx

def initial : Ctx := {}

def withScope (ctx : Ctx) (scope : List Name) : Ctx :=
  { ctx with scope := scope }

def withoutLoopControl (ctx : Ctx) : Ctx :=
  { ctx with canBreak := false, canContinue := false }

def withLoopControl (ctx : Ctx) : Ctx :=
  { ctx with canBreak := true, canContinue := true }

def withLeave (ctx : Ctx) : Ctx :=
  { ctx with canLeave := true }

end Ctx

inductive Mode where
  | regular
  | brk
  | cont
  | leave
  | halt (kind : Assembly.HaltKind)
  | outOfFuel
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  scope : List Name
  mode : Mode

namespace Outcome

def regular (state : State) (scope : List Name) : Outcome :=
  { state, scope, mode := .regular }

def brk (state : State) (scope : List Name) : Outcome :=
  { state, scope, mode := .brk }

def cont (state : State) (scope : List Name) : Outcome :=
  { state, scope, mode := .cont }

def leave (state : State) (scope : List Name) : Outcome :=
  { state, scope, mode := .leave }

def halt (kind : Assembly.HaltKind) (state : State) (scope : List Name) :
    Outcome :=
  { state, scope, mode := .halt kind }

def outOfFuel (state : State) (scope : List Name) : Outcome :=
  { state, scope, mode := .outOfFuel }

def restrictTo (scope : List Name) (outcome : Outcome) : Outcome :=
  { outcome with
    state := outcome.state.restrictTo scope
    scope := scope }

end Outcome

namespace Expr

mutual
  def eval (prim : PrimitiveSemantics) (expr : Expr) (state : State) :
      Except EVMException (State × List Word) :=
    match expr with
    | .literal value =>
        .ok (state, [value])
    | .var name =>
        match state.vars name with
        | some value => .ok (state, [value])
        | none => invalid
    | .prim op args => do
        let (stateAfterArgs, values) ← evalArgs prim args state
        let (shared, out) ← prim.eval op stateAfterArgs.shared values
        .ok (stateAfterArgs.withShared shared, out)

  /--
  Evaluate arguments from right to left and return values in source order.
  This matches Yul's call-argument evaluation order while keeping this layer
  free of any stack discipline.
  -/
  def evalArgs (prim : PrimitiveSemantics) : List Expr → State →
      Except EVMException (State × List Word)
    | [], state => .ok (state, [])
    | arg :: rest, state => do
        let (stateAfterRest, restValues) ← evalArgs prim rest state
        let (stateAfterArg, values) ← eval prim arg stateAfterRest
        match values with
        | [value] => .ok (stateAfterArg, value :: restValues)
        | _ => invalid
end

def evalOne (prim : PrimitiveSemantics) (expr : Expr) (state : State) :
    Except EVMException (State × Word) := do
  let (state', values) ← eval prim expr state
  match values with
  | [value] => .ok (state', value)
  | _ => invalid

def evalZero (prim : PrimitiveSemantics) (expr : Expr) (state : State) :
    Except EVMException State := do
  let (state', values) ← eval prim expr state
  match values with
  | [] => .ok state'
  | _ => invalid

def evalCondition (prim : PrimitiveSemantics) (expr : Expr) (state : State) :
    Except EVMException (State × Bool) := do
  let (state', value) ← evalOne prim expr state
  .ok (state', value != zero)

end Expr

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

mutual
  def Block.run (fuel : Nat) (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) (block : Block) (state : State) :
      Except EVMException Outcome :=
    match fuel with
    | 0 => .ok (Outcome.outOfFuel state ctx.scope)
    | fuel' + 1 => do
        let outcome ←
          StmtList.run fuel' prim program ctx block.stmts state
        .ok (outcome.restrictTo ctx.scope)

  def StmtList.run (fuel : Nat) (prim : PrimitiveSemantics)
      (program : Program) (ctx : Ctx) (stmts : List Stmt) (state : State) :
      Except EVMException Outcome :=
    match fuel with
    | 0 => .ok (Outcome.outOfFuel state ctx.scope)
    | fuel' + 1 =>
        match stmts with
        | [] => .ok (Outcome.regular state ctx.scope)
        | stmt :: rest => do
            let head ← Stmt.run fuel' prim program ctx stmt state
            match head.mode with
            | .regular =>
                StmtList.run fuel' prim program (ctx.withScope head.scope)
                  rest head.state
            | .brk | .cont | .leave | .halt _ | .outOfFuel =>
                .ok head

  def Stmt.run (fuel : Nat) (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) (stmt : Stmt) (state : State) :
      Except EVMException Outcome :=
    match fuel with
    | 0 => .ok (Outcome.outOfFuel state ctx.scope)
    | fuel' + 1 =>
        match stmt with
        | .expr expr => do
            let state' ← Expr.evalZero prim expr state
            .ok (Outcome.regular state' ctx.scope)
        | .decl names value? => do
            let (stateAfterValue, values) ←
              match value? with
              | none => .ok (state, zeros names.length)
              | some value => do
                  let (stateAfterValue, out) ← Expr.eval prim value state
                  if out.length = names.length then
                    .ok (stateAfterValue, out)
                  else
                    invalid
            let state' ←
              match stateAfterValue.insertMany? names values with
              | some state' => .ok state'
              | none => invalid
            .ok (Outcome.regular state' (names.reverse ++ ctx.scope))
        | .assign names value => do
            let (stateAfterValue, out) ← Expr.eval prim value state
            if out.length = names.length then
              let state' ←
                match stateAfterValue.assignMany? names out with
                | some state' => .ok state'
                | none => invalid
              .ok (Outcome.regular state' ctx.scope)
            else
              invalid
        | .block body =>
            Block.run fuel' prim program ctx body state
        | .if_ cond body => do
            let (stateAfterCond, condValue) ← Expr.evalCondition prim cond state
            if condValue then
              Block.run fuel' prim program ctx body stateAfterCond
            else
              .ok (Outcome.regular stateAfterCond ctx.scope)
        | .switch scrutinee cases defaultBody => do
            let (stateAfterScrutinee, value) ← Expr.evalOne prim scrutinee state
            match Switch.select value cases defaultBody with
            | none => .ok (Outcome.regular stateAfterScrutinee ctx.scope)
            | some body => Block.run fuel' prim program ctx body stateAfterScrutinee
        | .for_ init cond post body => do
            let initCtx := ctx.withoutLoopControl
            let initOutcome ←
              StmtList.run fuel' prim program initCtx init.stmts state
            match initOutcome.mode with
            | .regular =>
                For.run fuel' prim program ctx.scope cond post body
                  (initCtx.withScope initOutcome.scope) initOutcome.state
            | .brk | .cont => invalid
            | .leave | .halt _ | .outOfFuel =>
                .ok (initOutcome.restrictTo ctx.scope)
        | .brk =>
            if ctx.canBreak then
              .ok (Outcome.brk state ctx.scope)
            else
              invalid
        | .cont =>
            if ctx.canContinue then
              .ok (Outcome.cont state ctx.scope)
            else
              invalid
        | .leave =>
            if ctx.canLeave then
              .ok (Outcome.leave state ctx.scope)
            else
              invalid
        | .call targets functionName args => do
            let (stateAfterArgs, argValues) ← Expr.evalArgs prim args state
            match program.findProc? functionName with
            | none => invalid
            | some proc =>
                if argValues.length = proc.params.length ∧
                    targets.length = proc.returns.length then
                  let returnVars ←
                    match
                        Store.insertMany proc.returns
                          (zeros proc.returns.length) Store.empty with
                    | some vars => .ok vars
                    | none => invalid
                  let calleeVars ←
                    match Store.insertMany proc.params argValues returnVars with
                    | some vars => .ok vars
                    | none => invalid
                  let calleeState : State :=
                    { shared := stateAfterArgs.shared, vars := calleeVars }
                  let calleeCtx : Ctx :=
                    { scope := proc.returns ++ proc.params
                      canBreak := false
                      canContinue := false
                      canLeave := true }
                  let outcome ←
                    Block.run fuel' prim program calleeCtx proc.body calleeState
                  match outcome.mode with
                  | .regular | .leave =>
                      match Store.lookupMany proc.returns outcome.state.vars with
                      | none => invalid
                      | some retValues =>
                          let callerState :=
                            { stateAfterArgs with shared := outcome.state.shared }
                          match callerState.assignMany? targets retValues with
                          | none => invalid
                          | some assigned =>
                              .ok (Outcome.regular assigned ctx.scope)
                  | .halt kind =>
                      .ok (Outcome.halt kind
                        { stateAfterArgs with shared := outcome.state.shared }
                        ctx.scope)
                  | .outOfFuel =>
                      .ok (Outcome.outOfFuel
                        { stateAfterArgs with shared := outcome.state.shared }
                        ctx.scope)
                  | .brk | .cont => invalid
                else
                  invalid
        | .terminal kind args => do
            let (stateAfterArgs, values) ← Expr.evalArgs prim args state
            let shared ← prim.terminal kind stateAfterArgs.shared values
            .ok (Outcome.halt kind (stateAfterArgs.withShared shared) ctx.scope)

  def For.run (fuel : Nat) (prim : PrimitiveSemantics) (program : Program)
      (outerScope : List Name) (cond : Expr) (post body : Block)
      (loopCtx : Ctx) (state : State) :
      Except EVMException Outcome :=
    match fuel with
    | 0 => .ok ((Outcome.outOfFuel state loopCtx.scope).restrictTo outerScope)
    | fuel' + 1 => do
        let (stateAfterCond, condValue) ← Expr.evalCondition prim cond state
        if condValue then
          let bodyOutcome ←
            Block.run fuel' prim program loopCtx.withLoopControl body
              stateAfterCond
          match bodyOutcome.mode with
          | .regular | .cont =>
              let postOutcome ←
                Block.run fuel' prim program loopCtx.withoutLoopControl post
                  bodyOutcome.state
              match postOutcome.mode with
              | .regular =>
                  For.run fuel' prim program outerScope cond post body loopCtx
                    postOutcome.state
              | .leave | .halt _ | .outOfFuel =>
                  .ok (postOutcome.restrictTo outerScope)
              | .brk | .cont => invalid
          | .brk =>
              .ok ((Outcome.regular bodyOutcome.state loopCtx.scope).restrictTo
                outerScope)
          | .leave | .halt _ | .outOfFuel =>
              .ok (bodyOutcome.restrictTo outerScope)
        else
          .ok ((Outcome.regular stateAfterCond loopCtx.scope).restrictTo
            outerScope)
end

namespace Program

def runState (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : State) : Except EVMException Outcome :=
  Block.run fuel prim program Ctx.initial program.body state

def run (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (shared : SharedState) : Except EVMException Outcome :=
  runState prim fuel program { shared := shared }

def runCanonical (fuel : Nat) (program : Program) (shared : SharedState) :
    Except EVMException Outcome :=
  runState PrimitiveSemantics.canonical fuel program { shared := shared }

end Program

end StackFreeCfg
end EvmCompiler
