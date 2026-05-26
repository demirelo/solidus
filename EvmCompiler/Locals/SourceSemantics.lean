import EvmCompiler.Locals.Syntax
import EvmCompiler.Structured.Semantics

namespace EvmCompiler
namespace Locals

/-
Stack-free source semantics for the locals abstraction.

This namespace is the source-side contract the layers above locals should
target. Stack slots, layout depths, and return-frame encodings belong in
compiler relations below this semantics, not in the meaning of the source
language.
-/
namespace Source

abbrev Store := Name → Option Word

namespace Store

def empty : Store :=
  fun _ => none

def insert (store : Store) (name : Name) (value : Word) : Store :=
  fun key => if key = name then some value else store key

def contains (store : Store) (name : Name) : Bool :=
  (store name).isSome

def restrictTo (scope : List Name) (store : Store) : Store :=
  fun key => if key ∈ scope then store key else none

@[simp] theorem empty_apply (name : Name) :
    empty name = none := rfl

@[simp] theorem insert_self (store : Store) (name : Name) (value : Word) :
    insert store name value name = some value := by
  simp [insert]

theorem insert_of_ne {store : Store} {name other : Name} {value : Word}
    (hNe : other ≠ name) :
    insert store name value other = store other := by
  simp [insert, hNe]

theorem restrictTo_mem {scope : List Name} {store : Store} {name : Name}
    (hMem : name ∈ scope) :
    restrictTo scope store name = store name := by
  simp [restrictTo, hMem]

theorem restrictTo_not_mem {scope : List Name} {store : Store} {name : Name}
    (hMem : name ∉ scope) :
    restrictTo scope store name = none := by
  simp [restrictTo, hMem]

end Store

structure State where
  shared : EvmYul.SharedState .EVM
  vars : Store

namespace State

def withShared (state : State) (shared : EvmYul.SharedState .EVM) :
    State :=
  { state with shared := shared }

def withVars (state : State) (vars : Store) : State :=
  { state with vars := vars }

def restrictTo (scope : List Name) (state : State) : State :=
  { state with vars := Store.restrictTo scope state.vars }

def insert (state : State) (name : Name) (value : Word) : State :=
  { state with vars := Store.insert state.vars name value }

@[simp] theorem restrictTo_shared (scope : List Name) (state : State) :
    (restrictTo scope state).shared = state.shared := rfl

@[simp] theorem insert_shared (state : State) (name : Name) (value : Word) :
    (insert state name value).shared = state.shared := rfl

end State

/--
Shared primitive semantics used by the stack-free locals interpreter.

Primitive operations may deliberately share their meaning with lower layers.
This record keeps that sharing explicit while avoiding any source-level mention
of the concrete EVM stack representation.
-/
structure PrimitiveSemantics where
  eval :
    Structured.BasicOp → EvmYul.SharedState .EVM → List Word →
      Except EVMException (EvmYul.SharedState .EVM × List Word)
  terminal :
    Assembly.HaltKind → EvmYul.SharedState .EVM → List Word →
      Except EVMException (EvmYul.SharedState .EVM)

namespace PrimitiveSemantics

/--
Continuing EVM primitives exposed at the source-primitive boundary.

Backend stack-shuffle instructions are deliberately not source primitives here:
they remain part of the lower stack-machine implementation and proofs. External
call/create and control/PC-dependent primitives are still rejected by
`continuingStep?` until their source-facing interaction semantics are wired in.
-/
def sourceContinuingStep? (op : Structured.BasicOp) :
    Option Assembly.PrimStep :=
  match op with
  | .dup1 | .dup2 | .dup3 | .dup4
  | .dup5 | .dup6 | .dup7 | .dup8
  | .dup9 | .dup10 | .dup11 | .dup12
  | .dup13 | .dup14 | .dup15 | .dup16
  | .swap1 | .swap2 | .swap3 | .swap4
  | .swap5 | .swap6 | .swap7 | .swap8
  | .swap9 | .swap10 | .swap11 | .swap12
  | .swap13 | .swap14 | .swap15 | .swap16 => none
  | op => op.toPrimOp.continuingStep?

/--
Canonical source primitive semantics for the compiler tower.

It runs the already-verified structured/EVM primitive on an isolated concrete
stack containing exactly the source arguments, then projects the resulting
shared state and produced stack values back to the stack-free locals source
interpreter. This definition is deliberately not a proof shortcut: the lowering
proof must still show that running the same primitive inside an arbitrary caller
stack/frame has the same projected behavior.
-/
def structured : PrimitiveSemantics where
  eval op shared values :=
    if values.length = Expressions.Structured.BasicOp.inputs op then
    let state : EVMState :=
      { toSharedState := shared,
        pc := EvmYul.UInt256.ofNat 0,
        stack := values.reverse,
        execLength := 0 }
    match sourceContinuingStep? op with
    | none => .error .InvalidInstruction
    | some step =>
    match step.run state with
    | .ok state' => .ok (state'.toSharedState, state'.stack.reverse)
    | .error err => .error err
    else
      .error .StackUnderflow
  terminal kind shared values :=
    let state : EVMState :=
      { toSharedState := shared,
        pc := EvmYul.UInt256.ofNat 0,
        stack := values.reverse,
        execLength := 0 }
    match Structured.Terminal.step kind state with
    | .ok state' => .ok state'.toSharedState
    | .error err => .error err

end PrimitiveSemantics

structure Ctx where
  scope : List Name := []
  breakScope? : Option (List Name) := none
  continueScope? : Option (List Name) := none
  leaveScope? : Option (List Name) := none

namespace Ctx

def initial : Ctx := {}

def withoutLoopControl (ctx : Ctx) : Ctx :=
  { ctx with breakScope? := none, continueScope? := none }

def withLoopControl (ctx : Ctx) (breakScope continueScope : List Name) :
    Ctx :=
  { scope := ctx.scope,
    breakScope? := some breakScope,
    continueScope? := some continueScope,
    leaveScope? := ctx.leaveScope? }

def withLeaveScope (ctx : Ctx) (leaveScope : List Name) : Ctx :=
  { ctx with leaveScope? := some leaveScope }

end Ctx

abbrev invalid {α : Type} : Except EVMException α :=
  EvmCompiler.Structured.invalid

inductive Mode where
  | regular
  | brk
  | cont
  | leave
  | halt (kind : Assembly.HaltKind)
  deriving DecidableEq

structure Outcome where
  state : State
  mode : Mode

namespace Outcome

def regular (state : State) : Outcome :=
  { state := state, mode := .regular }

def brk (state : State) : Outcome :=
  { state := state, mode := .brk }

def cont (state : State) : Outcome :=
  { state := state, mode := .cont }

def leave (state : State) : Outcome :=
  { state := state, mode := .leave }

def halt (kind : Assembly.HaltKind) (state : State) : Outcome :=
  { state := state, mode := .halt kind }

end Outcome

namespace Expr

mutual
  def eval {results : Nat} (prim : PrimitiveSemantics)
      (expr : Expr results) (state : State) :
      Except EVMException (State × List Word) :=
    match expr with
    | .lit value =>
        .ok (state, [value])
    | .var name =>
        match state.vars name with
        | some value => .ok (state, [value])
        | none => invalid
    | .code code =>
        invalid
    | .prim op args => do
        let (stateAfterArgs, values) ← ExprSeq.eval prim args state
        let (shared, values') ← prim.eval op stateAfterArgs.shared values
        .ok (stateAfterArgs.withShared shared, values')

  def ExprSeq.eval {results : Nat} (prim : PrimitiveSemantics)
      (exprs : ExprSeq results) (state : State) :
      Except EVMException (State × List Word) :=
    match exprs with
    | .nil => .ok (state, [])
    | .cons head tail => do
        let (stateAfterHead, headValues) ← eval prim head state
        let (stateAfterTail, tailValues) ← ExprSeq.eval prim tail stateAfterHead
        .ok (stateAfterTail, headValues ++ tailValues)
end

def evalOne {results : Nat} (prim : PrimitiveSemantics)
    (expr : Expr results) (state : State) :
    Except EVMException (State × Word) := do
  let (state', values) ← eval prim expr state
  match values with
  | [value] => .ok (state', value)
  | _ => invalid

def evalCondition (prim : PrimitiveSemantics) (expr : Expr 1)
    (state : State) :
    Except EVMException (State × Bool) := do
  let (state', value) ← evalOne prim expr state
  .ok (state', value != EvmYul.UInt256.ofNat 0)

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
  def Block.runOpen (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) : Nat → Block → State →
      Except EVMException (Outcome × Ctx)
    | 0, _block, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Outcome.regular state, ctx)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let (outcome, ctx') ← Stmt.run prim program ctx fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.runOpen prim program ctx' fuel { stmts := rest }
              outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, ctx)
  termination_by fuel block _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScoped (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) (block : Block) (fuel : Nat) (state : State) :
      Except EVMException Outcome := do
    let (outcome, _) ← Block.runOpen prim program ctx fuel block state
    match outcome.mode with
    | .regular =>
        .ok (Outcome.regular (outcome.state.restrictTo ctx.scope))
    | .brk | .cont | .leave | .halt _ =>
        .ok outcome
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def Stmt.runForLoop (prim : PrimitiveSemantics) (program : Program)
      (loopCtx : Ctx) (cond : Expr 1) (postBase : Ctx) (post : Block)
      (bodyBase : Ctx) (body : Block) :
      Nat → State → Except EVMException Outcome
    | 0, _state =>
        invalid
    | fuel + 1, state =>
        match Expr.evalCondition prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match Block.runScoped prim program bodyBase body fuel
                  stateAfterCond with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match Block.runScoped prim program postBase post fuel
                          bodyOutcome.state with
                      | .error err => .error err
                      | .ok postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop prim program loopCtx cond
                                postBase post bodyBase body fuel
                                postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok (Outcome.regular (stateAfterCond.restrictTo loopCtx.scope))
  termination_by fuel _state => (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run (prim : PrimitiveSemantics) (program : Program) (ctx : Ctx) :
      Nat → Stmt → State → Except EVMException (Outcome × Ctx)
    | _fuel, .expr expr, state => do
        let (state', _values) ← Expr.eval prim expr state
        .ok (Outcome.regular state', ctx)
    | _fuel, .exprs exprs, state => do
        let (state', _values) ← Expr.ExprSeq.eval prim exprs state
        .ok (Outcome.regular state', ctx)
    | _fuel, .let_ name value, state => do
        let (stateAfterValue, value') ← Expr.evalOne prim value state
        .ok (Outcome.regular (stateAfterValue.insert name value'),
          { ctx with scope := name :: ctx.scope })
    | _fuel, .assign name value, state => do
        if state.vars.contains name then
          let (stateAfterValue, value') ← Expr.evalOne prim value state
          .ok (Outcome.regular
            (stateAfterValue.withVars
              (Store.insert stateAfterValue.vars name value')), ctx)
        else
          invalid
    | _fuel, .assignTop _name, _state =>
        invalid
    | _fuel, .assignTopWithOffset _offset _name, _state =>
        invalid
    | fuel, .block body, state => do
        let outcome ← Block.runScoped prim program ctx body fuel state
        .ok (outcome, ctx)
    | 0, .if_ _cond _body, _state =>
        invalid
    | fuel + 1, .if_ cond body, state =>
        match Expr.evalCondition prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then do
              let outcome ← Block.runScoped prim program ctx body fuel
                stateAfterCond
              .ok (outcome, ctx)
            else
              .ok (Outcome.regular stateAfterCond, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        invalid
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let (stateAfterScrutinee, value) ← Expr.evalOne prim scrutinee state
        match Switch.select value cases defaultBody with
        | none => .ok (Outcome.regular stateAfterScrutinee, ctx)
        | some body =>
            let outcome ← Block.runScoped prim program ctx body fuel
              stateAfterScrutinee
            .ok (outcome, ctx)
    | 0, .for_ _init _cond _post _body, _state =>
        invalid
    | fuel + 1, .for_ init cond post body, state => do
        let initBase := ctx.withoutLoopControl
        let (initOutcome, initCtx) ←
          Block.runOpen prim program initBase fuel init state
        match initOutcome.mode with
        | .regular =>
            let loopCtx := initCtx
            let postBase := initCtx.withoutLoopControl
            let bodyBase := initCtx.withLoopControl initCtx.scope initCtx.scope
            let loopOutcome ←
              Stmt.runForLoop prim program loopCtx cond postBase post
                bodyBase body fuel initOutcome.state
            match loopOutcome.mode with
            | .regular =>
                .ok (Outcome.regular (loopOutcome.state.restrictTo ctx.scope),
                  ctx)
            | .brk | .cont =>
                invalid
            | .leave | .halt _ =>
                .ok (loopOutcome, ctx)
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok (initOutcome, ctx)
    | _fuel, .brk, state =>
        match ctx.breakScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.brk (state.restrictTo scope), ctx)
    | _fuel, .cont, state =>
        match ctx.continueScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.cont (state.restrictTo scope), ctx)
    | _fuel, .leave, state =>
        match ctx.leaveScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.leave (state.restrictTo scope), ctx)
    | _fuel, .call _name, _state =>
        invalid
    | _fuel, .terminal kind, state => do
        let shared ← prim.terminal kind state.shared []
        .ok (Outcome.halt kind (state.withShared shared), ctx)
    | _fuel, .terminalArgs kind args, state => do
        let (stateAfterArgs, values) ← Expr.ExprSeq.eval prim args state
        let shared ← prim.terminal kind stateAfterArgs.shared values
        .ok (Outcome.halt kind (stateAfterArgs.withShared shared), ctx)
  termination_by fuel stmt _state => (fuel, 3, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

def initialState (shared : EvmYul.SharedState .EVM) : State :=
  { shared := shared, vars := Store.empty }

def runState (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : State) : Except EVMException Outcome :=
  Block.runScoped prim program Ctx.initial program.body fuel state

def run (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : EVMState) : Except EVMException Outcome :=
  runState prim fuel program (initialState state.toSharedState)

inductive Eval (prim : PrimitiveSemantics) :
    Nat → Program → State → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program} {initial : State}
      {outcome : Outcome}
      (hRun : runState prim fuel program initial = .ok outcome) :
      Eval prim fuel program initial outcome

end Program

mutual
  def Expr.SourceOwned {results : Nat} (expr : Expr results) : Prop :=
    match expr with
    | .lit _value => True
    | .var _name => True
    | .code _code => False
    | .prim _op args => ExprSeq.SourceOwned args

  def ExprSeq.SourceOwned {results : Nat} (exprs : ExprSeq results) : Prop :=
    match exprs with
    | .nil => True
    | .cons head tail =>
        Expr.SourceOwned head ∧ ExprSeq.SourceOwned tail
end

mutual
  def Block.SourceOwned : Block → Prop
    | ⟨stmts⟩ => StmtList.SourceOwned stmts

  def Stmt.SourceOwned : Stmt → Prop
    | .expr (results := results) expr =>
        results = 0 ∧ Expr.SourceOwned expr
    | .exprs _exprs => False
    | .let_ _name value => Expr.SourceOwned value
    | .assign _name value => Expr.SourceOwned value
    | .assignTop _name => False
    | .assignTopWithOffset _offset _name => False
    | .block body => Block.SourceOwned body
    | .if_ cond body => Expr.SourceOwned cond ∧ Block.SourceOwned body
    | .switch scrutinee cases defaultBody =>
        Expr.SourceOwned scrutinee ∧ CaseList.SourceOwned cases ∧
          (match defaultBody with
          | none => True
          | some body => Block.SourceOwned body)
    | .for_ init cond post body =>
        Block.SourceOwned init ∧ Expr.SourceOwned cond ∧
          Block.SourceOwned post ∧ Block.SourceOwned body
    | .brk | .cont | .leave => True
    | .call _name => False
    | .terminal _kind => True
    | .terminalArgs _kind args => ExprSeq.SourceOwned args

  def StmtList.SourceOwned : List Stmt → Prop
    | [] => True
    | stmt :: rest => Stmt.SourceOwned stmt ∧ StmtList.SourceOwned rest

  def CaseList.SourceOwned : List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest => Block.SourceOwned body ∧
        CaseList.SourceOwned rest
end

def Program.SourceOwned (program : Program) : Prop :=
  program.procs = [] ∧ Block.SourceOwned program.body

def Expr.SourceWF {results : Nat} (env : List Name)
    (expr : Expr results) : Prop :=
  Expr.SourceOwned expr ∧ Lexical.ExprScoped env expr

def ExprSeq.SourceWF {results : Nat} (env : List Name)
    (exprs : ExprSeq results) : Prop :=
  ExprSeq.SourceOwned exprs ∧ Lexical.ExprSeqScoped env exprs

def Block.SourceWF (env : List Name) (block : Block) : Prop :=
  Block.SourceOwned block ∧ Lexical.BlockScoped env block

def Stmt.SourceWF (env : List Name) (stmt : Stmt) : Prop :=
  Stmt.SourceOwned stmt ∧ Lexical.StmtScoped env stmt

def StmtList.SourceWF (env : List Name) (stmts : List Stmt) : Prop :=
  StmtList.SourceOwned stmts ∧ Lexical.StmtListScoped env stmts

def Program.SourceWF (program : Program) : Prop :=
  program.procs = [] ∧ Block.SourceWF [] program.body

namespace Program

theorem sourceOwned_of_sourceWF {program : Program}
    (hWF : SourceWF program) :
    SourceOwned program := by
  rcases hWF with ⟨hProcs, hBody⟩
  exact ⟨hProcs, hBody.1⟩

theorem lexicalScoped_of_sourceWF {program : Program}
    (hWF : SourceWF program) :
    Lexical.ProgramScoped program := by
  exact hWF.2.2

end Program

end Source

end Locals
end EvmCompiler
