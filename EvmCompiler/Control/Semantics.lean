import EvmCompiler.Control.Syntax

namespace EvmCompiler
namespace Control

namespace Prim

def invalid {α : Type} : Except EVMException α :=
  .error .InvalidInstruction

def restoreStack (original : EvmYul.Stack Word) (state : EVMState) :
    EVMState :=
  { state with stack := original }

def runNonterminal (op : Assembly.PrimOp) (args : List Word)
    (state : EVMState) : Except EVMException (EVMState × List Word) := do
  if op.haltKind?.isSome then
    invalid
  else
    match op.stackEffect? with
    | none => invalid
    | some (inputArity, outputArity) =>
        if args.length = inputArity then
          let originalStack := state.stack
          let state' ← op.step { state with stack := args }
          if state'.stack.length = outputArity then
            .ok (restoreStack originalStack state', state'.stack)
          else
            invalid
        else
          .error .StackUnderflow

def runTerminal (kind : Assembly.HaltKind) (args : List Word)
    (state : EVMState) : Except EVMException EVMState := do
  if args.length = kind.argCount then
    let originalStack := state.stack
    let state' ← kind.toPrimOp.step { state with stack := args }
    .ok (restoreStack originalStack state')
  else
    .error .StackUnderflow

end Prim

mutual
  def Expr.eval (expr : Expr) (state : EVMState) :
      Except EVMException (EVMState × Word) :=
    match expr with
    | .literal value => .ok (state, value)
    | .prim op args => do
        let (state', values) ← Expr.evalArgs args state
        let (state'', out) ← Prim.runNonterminal op values state'
        match out with
        | [value] => .ok (state'', value)
        | _ => Prim.invalid

  /--
  Evaluate argument expressions from right to left, returning values in source
  order. This matches the direction the compiler uses to place arguments on the
  target stack while keeping the source semantics stack-free.
  -/
  def Expr.evalArgs : List Expr → EVMState →
      Except EVMException (EVMState × List Word)
    | [], state => .ok (state, [])
    | arg :: rest, state => do
        let (stateAfterRest, restValues) ← Expr.evalArgs rest state
        let (stateAfterArg, value) ← Expr.eval arg stateAfterRest
        .ok (stateAfterArg, value :: restValues)
end

def Expr.evalCondition (expr : Expr) (state : EVMState) :
    Except EVMException (EVMState × Bool) := do
  let (state', value) ← expr.eval state
  .ok (state', value != EvmYul.UInt256.ofNat 0)

inductive Mode where
  | regular
  | brk
  | cont
  | leave
  | halt (kind : Assembly.HaltKind)
  deriving DecidableEq, Repr

structure Outcome where
  state : EVMState
  mode : Mode

namespace Outcome

def regular (state : EVMState) : Outcome := { state, mode := .regular }
def brk (state : EVMState) : Outcome := { state, mode := .brk }
def cont (state : EVMState) : Outcome := { state, mode := .cont }
def leave (state : EVMState) : Outcome := { state, mode := .leave }
def halt (kind : Assembly.HaltKind) (state : EVMState) : Outcome :=
  { state, mode := .halt kind }

end Outcome

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
  def Block.run : Nat → Block → EVMState → Except EVMException Outcome
    | 0, _block, _state => Prim.invalid
    | fuel + 1, block, state =>
        match block with
        | ⟨[]⟩ => .ok (Outcome.regular state)
        | ⟨stmt :: rest⟩ => do
            let outcome ← Stmt.run fuel stmt state
            match outcome.mode with
            | .regular => Block.run fuel { stmts := rest } outcome.state
            | .brk | .cont | .leave | .halt _ => .ok outcome

  def Stmt.run : Nat → Stmt → EVMState → Except EVMException Outcome
    | 0, _stmt, _state => Prim.invalid
    | fuel + 1, stmt, state =>
        match stmt with
        | .prim op args => do
            let (state', values) ← Expr.evalArgs args state
            let (state'', out) ← Prim.runNonterminal op values state'
            match out with
            | [] => .ok (Outcome.regular state'')
            | _ => Prim.invalid
        | .if_ cond body => do
            let (stateAfterCond, condValue) ← cond.evalCondition state
            if condValue then
              Block.run fuel body stateAfterCond
            else
              .ok (Outcome.regular stateAfterCond)
        | .switch scrutinee cases defaultBody => do
            let (stateAfterScrutinee, value) ← scrutinee.eval state
            match Switch.select value cases defaultBody with
            | none => .ok (Outcome.regular stateAfterScrutinee)
            | some body => Block.run fuel body stateAfterScrutinee
        | .for_ init cond post body => do
            let initOutcome ← Block.run fuel init state
            match initOutcome.mode with
            | .regular =>
                For.run fuel cond post body initOutcome.state
            | .leave | .halt _ => .ok initOutcome
            | .brk | .cont => Prim.invalid
        | .brk => .ok (Outcome.brk state)
        | .cont => .ok (Outcome.cont state)
        | .leave => .ok (Outcome.leave state)
        | .terminal kind args => do
            let (state', values) ← Expr.evalArgs args state
            let state'' ← Prim.runTerminal kind values state'
            .ok (Outcome.halt kind state'')

  def For.run : Nat → Expr → Block → Block → EVMState →
      Except EVMException Outcome
    | 0, _cond, _post, _body, _state => Prim.invalid
    | fuel + 1, cond, post, body, state => do
        let (stateAfterCond, condValue) ← cond.evalCondition state
        if condValue then
          let bodyOutcome ← Block.run fuel body stateAfterCond
          match bodyOutcome.mode with
          | .regular | .cont =>
              let postOutcome ← Block.run fuel post bodyOutcome.state
              match postOutcome.mode with
              | .regular => For.run fuel cond post body postOutcome.state
              | .leave | .halt _ => .ok postOutcome
              | .brk | .cont => Prim.invalid
          | .brk => .ok (Outcome.regular bodyOutcome.state)
          | .leave | .halt _ => .ok bodyOutcome
        else
          .ok (Outcome.regular stateAfterCond)
end

namespace Program

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  program.body.run fuel state

end Program

end Control
end EvmCompiler
