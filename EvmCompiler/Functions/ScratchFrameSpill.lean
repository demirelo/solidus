import EvmCompiler.Functions.Compiler

/-!
Executable stack-too-deep fallback for imported function-layer programs.

This compiler is intentionally not part of the public preservation spine yet.
It keeps a hidden frame base on the EVM stack, stores source locals in a
compiler-managed memory frame, and uses ordinary `Expressions.Stmt.call`
splice points for internal function calls.  The route is for fail-closed
bytecode generation after the theorem-covered ordinary path and checked
call-aware spill path reject a program.
-/

namespace EvmCompiler
namespace Functions
namespace ScratchFrameSpill

abbrev SlotEnv := List (Name × Nat)

structure FunSlots where
  name : Name
  params : List (Name × Nat)
  returns : List (Name × Nat)

structure CompileState where
  env : SlotEnv
  nextSlot : Nat

structure CompileCtx where
  functions : List FunSlots
  frameWords : Nat

structure Plan where
  state : CompileState
  block : Expressions.Block

def word (n : Nat) : Word :=
  EvmYul.UInt256.ofNat n

def freePtrWord : Word :=
  word 64

def slotOffset (slot : Nat) : Word :=
  word (32 * slot)

def frameBytes (words : Nat) : Word :=
  word (32 * words)

namespace Block

def append (left right : Expressions.Block) : Expressions.Block :=
  { stmts := left.stmts ++ right.stmts }

def ofCode (code : Structured.Code) : Expressions.Block :=
  { stmts := [Expressions.Stmt.code code] }

def seqList : List Expressions.Block → Expressions.Block
  | [] => { stmts := [] }
  | head :: tail => append head (seqList tail)

end Block

def lookupSlot? (name : Name) : SlotEnv → Option Nat
  | [] => none
  | (candidate, slot) :: rest =>
      if candidate = name then some slot else lookupSlot? name rest

def lookupFun? (name : Name) : List FunSlots → Option FunSlots
  | [] => none
  | fn :: rest => if fn.name = name then some fn else lookupFun? name rest

def allocateName (name : Name) (state : CompileState) :
    Nat × CompileState :=
  (state.nextSlot,
    { env := (name, state.nextSlot) :: state.env
      nextSlot := state.nextSlot + 1 })

def allocateNames : List Name → CompileState →
    List (Name × Nat) × CompileState
  | [], state => ([], state)
  | name :: rest, state =>
      let (slot, state) := allocateName name state
      let (tail, state) := allocateNames rest state
      ((name, slot) :: tail, state)

def allocateFunctionSignatures : List FunDef → CompileState →
    List FunSlots × CompileState
  | [], state => ([], state)
  | fn :: rest, state =>
      let (params, state) := allocateNames fn.params state
      let (returns, state) := allocateNames fn.returns state
      let slots : FunSlots :=
        { name := fn.name, params := params, returns := returns }
      let (tail, state) := allocateFunctionSignatures rest state
      (slots :: tail, state)

def dupCode? (depth : Nat) : Option Structured.Code := do
  let op ← Locals.StackOp.dup? depth
  some [Structured.BasicInstr.op op]

def slotAddressCode? (valuesAboveBase slot : Nat) :
    Option Structured.Code := do
  let dup ← dupCode? (valuesAboveBase + 1)
  some
    (dup ++
      [ Structured.BasicInstr.push (slotOffset slot),
        Structured.BasicInstr.op .add ])

def loadSlotCode? (valuesAboveBase slot : Nat) :
    Option Structured.Code := do
  let addr ← slotAddressCode? valuesAboveBase slot
  some (addr ++ [Structured.BasicInstr.op .mload])

def storeTopSlotCode? (valuesAboveBase slot : Nat) :
    Option Structured.Code := do
  let addr ← slotAddressCode? valuesAboveBase slot
  some (addr ++ [Structured.BasicInstr.op .mstore])

def liftBuriedToTopCode? : Nat → Option Structured.Code
  | 0 => some []
  | depth + 1 => do
      let pref ← liftBuriedToTopCode? depth
      let op ← Locals.StackOp.swap? (depth + 1)
      some (pref ++ [Structured.BasicInstr.op op])

def removeBaseUnderCode? (valuesAboveBase : Nat) :
    Option Structured.Code := do
  let lift ← liftBuriedToTopCode? valuesAboveBase
  some (lift ++ [Structured.BasicInstr.op .pop])

mutual
  def compileExprCode? (env : SlotEnv) (valuesAboveBase : Nat)
      {results : Nat} (expr : Expr results) : Option Structured.Code :=
    match expr with
    | .lit value => some [Structured.BasicInstr.push value]
    | .var name => do
        let slot ← lookupSlot? name env
        loadSlotCode? valuesAboveBase slot
    | .code _code => none
    | .prim op args => do
        let argsCode ← compileExprSeqCode? env valuesAboveBase args
        some (argsCode ++ [Structured.BasicInstr.op op])

  def compileExprSeqCode? (env : SlotEnv) (valuesAboveBase : Nat)
      {results : Nat} (exprs : Locals.ExprSeq results) :
      Option Structured.Code :=
    match exprs with
    | .nil => some []
    | .cons (left := left) head tail => do
        let headCode ← compileExprCode? env valuesAboveBase head
        let tailCode ←
          compileExprSeqCode? env (valuesAboveBase + left) tail
        some (headCode ++ tailCode)
end

mutual
  def compileNoVarExprCode? {results : Nat}
      (expr : Expr results) : Option Structured.Code :=
    match expr with
    | .lit value => some [Structured.BasicInstr.push value]
    | .var _name => none
    | .code code => some code
    | .prim op args => do
        let argsCode ← compileNoVarExprSeqCode? args
        some (argsCode ++ [Structured.BasicInstr.op op])

  def compileNoVarExprSeqCode? {results : Nat}
      (exprs : Locals.ExprSeq results) : Option Structured.Code :=
    match exprs with
    | .nil => some []
    | .cons head tail => do
        let headCode ← compileNoVarExprCode? head
        let tailCode ← compileNoVarExprSeqCode? tail
        some (headCode ++ tailCode)
end

def compilePreludeStmt? : Stmt → Option Expressions.Stmt
  | .expr expr => do
      let code ← compileNoVarExprCode? expr
      some (Expressions.Stmt.code code)
  | _ => none

def splitPrelude : List Stmt → List Expressions.Stmt × List Stmt
  | [] => ([], [])
  | stmt :: rest =>
      match compilePreludeStmt? stmt with
      | some compiled =>
          let (pref, tail) := splitPrelude rest
          (compiled :: pref, tail)
      | none => ([], stmt :: rest)

def frameInitCode (words : Nat) : Structured.Code :=
  [ Structured.BasicInstr.push freePtrWord,
    Structured.BasicInstr.op .mload,
    Structured.BasicInstr.op .dup1,
    Structured.BasicInstr.push (frameBytes words),
    Structured.BasicInstr.op .add,
    Structured.BasicInstr.push freePtrWord,
    Structured.BasicInstr.op .mstore ]

def swapTopTwoCode? : Option Structured.Code := do
  let op ← Locals.StackOp.swap? 1
  some [Structured.BasicInstr.op op]

def slotList (entries : List (Name × Nat)) : List Nat :=
  entries.map Prod.snd

def compileStoreTopSlots? : Nat → List Nat → Option Structured.Code
  | _valuesAboveBase, [] => some []
  | valuesAboveBase, slot :: rest => do
      let head ← storeTopSlotCode? valuesAboveBase slot
      let tail ← compileStoreTopSlots? (valuesAboveBase - 1) rest
      some (head ++ tail)

def compileCallArgsToSlots? (env : SlotEnv) :
    List (Expr 1) → List (Name × Nat) → Option Structured.Code
  | [], [] => some []
  | arg :: args, (_name, slot) :: slots => do
      let argCode ← compileExprCode? env 0 arg
      let storeCode ← storeTopSlotCode? 2 slot
      let tail ← compileCallArgsToSlots? env args slots
      some (argCode ++ storeCode ++ tail)
  | _, _ => none

def compileReturnCode? (env : SlotEnv) (returns : List Name) :
    Option Structured.Code := do
  let rec loadReturns (valuesAboveBase : Nat) :
      List Name → Option Structured.Code
    | [] => some []
    | name :: rest => do
        let slot ← lookupSlot? name env
        let head ← loadSlotCode? valuesAboveBase slot
        let tail ← loadReturns (valuesAboveBase + 1) rest
        some (head ++ tail)
  let loads ← loadReturns 0 returns
  let removeBase ← removeBaseUnderCode? returns.length
  some (loads ++ removeBase)

mutual
  def compileBlockOpen? (ctx : CompileCtx) (returns : List Name)
      (state : CompileState) (block : Block) : Option Plan :=
    match block with
    | ⟨stmts⟩ => compileStmtList? ctx returns state stmts

  def compileBlockScoped? (ctx : CompileCtx) (returns : List Name)
      (state : CompileState) (block : Block) : Option Plan := do
    let plan ← compileBlockOpen? ctx returns state block
    some { state := { env := state.env, nextSlot := plan.state.nextSlot }
           block := plan.block }

  def compileStmtList? (ctx : CompileCtx) (returns : List Name)
      (state : CompileState) : List Stmt → Option Plan
    | [] => some { state := state, block := { stmts := [] } }
    | stmt :: rest => do
        let head ← compileStmt? ctx returns state stmt
        let tail ← compileStmtList? ctx returns head.state rest
        some { state := tail.state, block := Block.append head.block tail.block }

  def compileCases? (ctx : CompileCtx) (returns : List Name)
      (state : CompileState) :
      List (Word × Block) → Option (List (Word × Expressions.Block) ×
        CompileState)
    | [] => some ([], state)
    | (value, body) :: rest => do
        let bodyPlan ← compileBlockScoped? ctx returns state body
        let (tail, state) ← compileCases? ctx returns bodyPlan.state rest
        some ((value, bodyPlan.block) :: tail, state)

  def compileDefault? (ctx : CompileCtx) (returns : List Name)
      (state : CompileState) :
      Option Block → Option (Option Expressions.Block × CompileState)
    | none => some (none, state)
    | some body => do
        let plan ← compileBlockScoped? ctx returns state body
        some (some plan.block, plan.state)

  def compileStmt? (ctx : CompileCtx) (returns : List Name)
      (state : CompileState) : Stmt → Option Plan
    | .expr expr => do
        let code ← compileExprCode? state.env 0 expr
        some { state := state, block := Block.ofCode code }
    | .let_ name value => do
        let code ← compileExprCode? state.env 0 value
        let (slot, state') := allocateName name state
        let store ← storeTopSlotCode? 1 slot
        some { state := state', block := Block.ofCode (code ++ store) }
    | .assign name value => do
        let slot ← lookupSlot? name state.env
        let code ← compileExprCode? state.env 0 value
        let store ← storeTopSlotCode? 1 slot
        some { state := state, block := Block.ofCode (code ++ store) }
    | .block body =>
        compileBlockScoped? ctx returns state body
    | .if_ cond body => do
        let condCode ← compileExprCode? state.env 0 cond
        let bodyPlan ← compileBlockScoped? ctx returns state body
        some
          { state := bodyPlan.state
            block := { stmts := [Expressions.Stmt.if_ (.code condCode)
              bodyPlan.block] } }
    | .switch scrutinee cases defaultBody => do
        let scrutineeCode ← compileExprCode? state.env 0 scrutinee
        let (compiledCases, stateAfterCases) ←
          compileCases? ctx returns state cases
        let (compiledDefault, stateAfterDefault) ←
          compileDefault? ctx returns stateAfterCases defaultBody
        some
          { state := stateAfterDefault
            block :=
              { stmts :=
                  [Expressions.Stmt.switch (.code scrutineeCode)
                    compiledCases compiledDefault] } }
    | .for_ init cond post body => do
        let initPlan ← compileBlockOpen? ctx returns state init
        let loopState := initPlan.state
        let condCode ← compileExprCode? loopState.env 0 cond
        let postPlan ← compileBlockScoped? ctx returns loopState post
        let bodyPlan ← compileBlockScoped? ctx returns postPlan.state body
        some
          { state := { env := state.env, nextSlot := bodyPlan.state.nextSlot }
            block :=
              { stmts :=
                  [Expressions.Stmt.for_ initPlan.block (.code condCode)
                    postPlan.block bodyPlan.block] } }
    | .brk =>
        some { state := state, block := { stmts := [Expressions.Stmt.brk] } }
    | .cont =>
        some { state := state, block := { stmts := [Expressions.Stmt.cont] } }
    | .leave => do
        let code ← compileReturnCode? state.env returns
        some
          { state := { state with env := state.env }
            block := Block.seqList
              [ Block.ofCode code,
                { stmts := [Expressions.Stmt.leave] } ] }
    | .call targets functionName args => do
        let fn ← lookupFun? functionName ctx.functions
        if args.length = fn.params.length then pure () else none
        if targets.length = fn.returns.length then pure () else none
        if targets.Nodup then pure () else none
        let callerBaseTop ← swapTopTwoCode?
        let argCode ← compileCallArgsToSlots? state.env args fn.params
        let calleeBaseTop ← swapTopTwoCode?
        let targetSlots ← targets.mapM (fun name => lookupSlot? name state.env)
        let storeReturns ←
          compileStoreTopSlots? targets.length targetSlots.reverse
        some
          { state := state
            block := Block.seqList
              [ Block.ofCode (frameInitCode ctx.frameWords),
                Block.ofCode callerBaseTop,
                Block.ofCode argCode,
                Block.ofCode calleeBaseTop,
                { stmts := [Expressions.Stmt.call functionName] },
                Block.ofCode storeReturns ] }
    | .terminal kind =>
        some { state := state, block := { stmts := [Expressions.Stmt.terminal kind] } }
    | .terminalArgs kind args => do
        let code ← compileExprSeqCode? state.env 0 args
        some
          { state := state
            block := Block.seqList
              [ Block.ofCode code,
                { stmts := [Expressions.Stmt.terminal kind] } ] }
end

def functionEnv (slots : FunSlots) : SlotEnv :=
  slots.returns ++ slots.params

def compileFunction? (ctx : CompileCtx) (state : CompileState)
    (fn : FunDef) : Option (Expressions.Proc × CompileState) := do
  if (fn.returns ++ fn.params).Nodup then pure () else none
  if fn.returns.length < 16 then pure () else none
  let slots ← lookupFun? fn.name ctx.functions
  let bodyStart : CompileState :=
    { env := functionEnv slots, nextSlot := state.nextSlot }
  let bodyPlan ← compileBlockOpen? ctx fn.returns bodyStart fn.body
  let retCode ← compileReturnCode? bodyPlan.state.env fn.returns
  let fullBody :=
    Block.append bodyPlan.block (Block.ofCode retCode)
  some
    ({ name := fn.name
       argc := 1
       retc := fn.returns.length
       body := fullBody },
     { env := state.env, nextSlot := bodyPlan.state.nextSlot })

def compileFunctions? (ctx : CompileCtx) :
    CompileState → List FunDef → Option (List Expressions.Proc × CompileState)
  | state, [] => some ([], state)
  | state, fn :: rest => do
      let (proc, state) ← compileFunction? ctx state fn
      let (procs, state) ← compileFunctions? ctx state rest
      some (proc :: procs, state)

def compileMain? (ctx : CompileCtx) (frameWords : Nat)
    (state : CompileState) (body : Block) : Option Plan :=
  match body with
  | ⟨stmts⟩ => do
      let (prelude, rest) := splitPrelude stmts
      let plan ← compileStmtList? ctx [] state rest
      let init := Expressions.Stmt.code (frameInitCode frameWords)
      some
        { state := plan.state
          block := { stmts := prelude ++ init :: plan.block.stmts } }

def compileExpressionsProgram? (maxFrameWords : Nat)
    (program : Program) : Option Expressions.Program := do
  if (program.functions.map FunDef.name).Nodup then pure () else none
  let initial : CompileState := { env := [], nextSlot := 0 }
  let (functionSlots, stateAfterSignatures) ←
    some (allocateFunctionSignatures program.functions initial)
  let ctx : CompileCtx := { functions := functionSlots, frameWords := 0 }
  let (procs, stateAfterFunctions) ←
    compileFunctions? ctx stateAfterSignatures program.functions
  let mainStart : CompileState :=
    { env := [], nextSlot := stateAfterFunctions.nextSlot }
  let mainProbe ← compileMain? ctx 0 mainStart program.body
  if mainProbe.state.nextSlot ≤ maxFrameWords then
    let frameWords := mainProbe.state.nextSlot
    let ctx : CompileCtx := { functions := functionSlots, frameWords := frameWords }
    let (procs, _stateAfterFunctions) ←
      compileFunctions? ctx stateAfterSignatures program.functions
    let main ← compileMain? ctx frameWords mainStart program.body
    some { procs := procs, body := main.block }
  else
    none

def compileTarget? (maxFrameWords : Nat)
    (program : Program) : Option Assembly.TargetProgram := do
  let exprProgram ← compileExpressionsProgram? maxFrameWords program
  Expressions.Program.compile? exprProgram

end ScratchFrameSpill
end Functions
end EvmCompiler
