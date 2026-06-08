import EvmCompiler.Functions.Compiler
import EvmCompiler.Expressions.Preservation

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

def compileReturnLoadsCode? (env : SlotEnv) :
    Nat → List Name → Option Structured.Code
  | _valuesAboveBase, [] => some []
  | valuesAboveBase, name :: rest => do
      let slot ← lookupSlot? name env
      let head ← loadSlotCode? valuesAboveBase slot
      let tail ← compileReturnLoadsCode? env (valuesAboveBase + 1) rest
      some (head ++ tail)

def compileReturnCode? (env : SlotEnv) (returns : List Name) :
    Option Structured.Code := do
  let loads ← compileReturnLoadsCode? env 0 returns
  let removeBase ← removeBaseUnderCode? returns.length
  some (loads ++ removeBase)

theorem structuredCode_append_noCallCreate
    {left right : Structured.Code}
    (hLeft : left.usesCallCreate = false)
    (hRight : right.usesCallCreate = false) :
    (left ++ right).usesCallCreate = false :=
  Locals.CompilerFacts.Structured.Code.usesCallCreate_append_eq_false
    hLeft hRight

theorem generatedCode_noCallCreate
    (code : Structured.Code)
    (hAll : ∀ instr ∈ code, instr.usesCallCreate = false) :
    code.usesCallCreate = false := by
  simpa [Structured.Code.usesCallCreate] using hAll

theorem dupCode?_noCallCreate {depth : Nat} {code : Structured.Code}
    (hCode : dupCode? depth = some code) :
    code.usesCallCreate = false := by
  unfold dupCode? at hCode
  cases hOp : Locals.StackOp.dup? depth with
  | none =>
      simp [hOp] at hCode
  | some op =>
      simp [hOp] at hCode
      cases hCode
      have hOpNo :=
        Locals.CompilerFacts.StackOp.dup?_not_callCreate depth hOp
      simp [Structured.Code.usesCallCreate,
        Structured.BasicInstr.usesCallCreate, hOpNo]

theorem slotAddressCode?_noCallCreate {valuesAboveBase slot : Nat}
    {code : Structured.Code}
    (hCode : slotAddressCode? valuesAboveBase slot = some code) :
    code.usesCallCreate = false := by
  unfold slotAddressCode? at hCode
  cases hDup : dupCode? (valuesAboveBase + 1) with
  | none =>
      simp [hDup] at hCode
  | some dup =>
      simp [hDup] at hCode
      cases hCode
      exact
        structuredCode_append_noCallCreate
          (dupCode?_noCallCreate hDup)
          (by
            simp [Structured.Code.usesCallCreate,
              Structured.BasicInstr.usesCallCreate,
              Structured.BasicOp.toPrimOp, Assembly.PrimOp.isCallCreate])

theorem loadSlotCode?_noCallCreate {valuesAboveBase slot : Nat}
    {code : Structured.Code}
    (hCode : loadSlotCode? valuesAboveBase slot = some code) :
    code.usesCallCreate = false := by
  unfold loadSlotCode? at hCode
  cases hAddr : slotAddressCode? valuesAboveBase slot with
  | none =>
      simp [hAddr] at hCode
  | some addr =>
      simp [hAddr] at hCode
      cases hCode
      exact
        structuredCode_append_noCallCreate
          (slotAddressCode?_noCallCreate hAddr)
          (by
            simp [Structured.Code.usesCallCreate,
              Structured.BasicInstr.usesCallCreate,
              Structured.BasicOp.toPrimOp, Assembly.PrimOp.isCallCreate])

theorem storeTopSlotCode?_noCallCreate {valuesAboveBase slot : Nat}
    {code : Structured.Code}
    (hCode : storeTopSlotCode? valuesAboveBase slot = some code) :
    code.usesCallCreate = false := by
  unfold storeTopSlotCode? at hCode
  cases hAddr : slotAddressCode? valuesAboveBase slot with
  | none =>
      simp [hAddr] at hCode
  | some addr =>
      simp [hAddr] at hCode
      cases hCode
      exact
        structuredCode_append_noCallCreate
          (slotAddressCode?_noCallCreate hAddr)
          (by
            simp [Structured.Code.usesCallCreate,
              Structured.BasicInstr.usesCallCreate,
              Structured.BasicOp.toPrimOp, Assembly.PrimOp.isCallCreate])

theorem liftBuriedToTopCode?_noCallCreate :
    ∀ {depth : Nat} {code : Structured.Code},
      liftBuriedToTopCode? depth = some code →
        code.usesCallCreate = false
  | 0, code, hCode => by
      simp [liftBuriedToTopCode?] at hCode
      cases hCode
      rfl
  | depth + 1, code, hCode => by
      simp [liftBuriedToTopCode?] at hCode
      cases hPref : liftBuriedToTopCode? depth with
      | none =>
          simp [hPref] at hCode
      | some pref =>
          cases hOp : Locals.StackOp.swap? (depth + 1) with
          | none =>
              simp [hPref, hOp] at hCode
          | some op =>
              simp [hPref, hOp] at hCode
              cases hCode
              have hPrefNo :=
                liftBuriedToTopCode?_noCallCreate
                  (depth := depth) (code := pref) hPref
              have hOpNo :=
                Locals.CompilerFacts.StackOp.swap?_not_callCreate
                  (depth + 1) hOp
              exact
                structuredCode_append_noCallCreate hPrefNo
                  (by
                    simp [Structured.Code.usesCallCreate,
                      Structured.BasicInstr.usesCallCreate, hOpNo])

theorem removeBaseUnderCode?_noCallCreate {valuesAboveBase : Nat}
    {code : Structured.Code}
    (hCode : removeBaseUnderCode? valuesAboveBase = some code) :
    code.usesCallCreate = false := by
  unfold removeBaseUnderCode? at hCode
  cases hLift : liftBuriedToTopCode? valuesAboveBase with
  | none =>
      simp [hLift] at hCode
  | some lift =>
      simp [hLift] at hCode
      cases hCode
      exact
        structuredCode_append_noCallCreate
          (liftBuriedToTopCode?_noCallCreate hLift)
          (by
            simp [Structured.Code.usesCallCreate,
              Structured.BasicInstr.usesCallCreate,
              Structured.BasicOp.toPrimOp, Assembly.PrimOp.isCallCreate])

theorem frameInitCode_noCallCreate (words : Nat) :
    (frameInitCode words).usesCallCreate = false := by
  simp [frameInitCode, Structured.Code.usesCallCreate,
    Structured.BasicInstr.usesCallCreate, Structured.BasicOp.toPrimOp,
    Assembly.PrimOp.isCallCreate]

theorem swapTopTwoCode?_noCallCreate {code : Structured.Code}
    (hCode : swapTopTwoCode? = some code) :
    code.usesCallCreate = false := by
  unfold swapTopTwoCode? at hCode
  cases hOp : Locals.StackOp.swap? 1 with
  | none =>
      simp [hOp] at hCode
  | some op =>
      simp [hOp] at hCode
      cases hCode
      have hOpNo := Locals.CompilerFacts.StackOp.swap?_not_callCreate 1 hOp
      simp [Structured.Code.usesCallCreate,
        Structured.BasicInstr.usesCallCreate, hOpNo]

theorem compileStoreTopSlots?_noCallCreate :
    ∀ {valuesAboveBase : Nat} {slots : List Nat} {code : Structured.Code},
      compileStoreTopSlots? valuesAboveBase slots = some code →
        code.usesCallCreate = false
  | _valuesAboveBase, [], code, hCode => by
      simp [compileStoreTopSlots?] at hCode
      cases hCode
      rfl
  | valuesAboveBase, slot :: rest, code, hCode => by
      simp [compileStoreTopSlots?] at hCode
      cases hHead : storeTopSlotCode? valuesAboveBase slot with
      | none =>
          simp [hHead] at hCode
      | some head =>
          cases hTail :
              compileStoreTopSlots? (valuesAboveBase - 1) rest with
          | none =>
              simp [hHead, hTail] at hCode
          | some tail =>
              simp [hHead, hTail] at hCode
              cases hCode
              exact
                structuredCode_append_noCallCreate
                  (storeTopSlotCode?_noCallCreate hHead)
                  (compileStoreTopSlots?_noCallCreate hTail)

set_option linter.unusedSimpArgs false in
mutual
  theorem compileExprCode?_noCallCreate {env : SlotEnv}
      {valuesAboveBase results : Nat} {expr : Expr results}
      {code : Structured.Code}
      (hExpr : expr.usesCallCreate = false)
      (hCompile :
        compileExprCode? env valuesAboveBase expr = some code) :
      code.usesCallCreate = false := by
    cases expr with
    | lit value =>
        simp [compileExprCode?] at hCompile
        cases hCompile
        simp [Structured.Code.usesCallCreate,
          Structured.BasicInstr.usesCallCreate]
    | var name =>
        simp [compileExprCode?] at hCompile
        cases hSlot : lookupSlot? name env with
        | none =>
            simp [hSlot] at hCompile
        | some slot =>
            simp [hSlot] at hCompile
            exact loadSlotCode?_noCallCreate hCompile
    | code raw =>
        simp [compileExprCode?] at hCompile
    | prim op args =>
        have hParts :
            args.usesCallCreate = false ∧
              op.toPrimOp.isCallCreate = false := by
          simpa [Locals.Expr.usesCallCreate] using hExpr
        simp [compileExprCode?] at hCompile
        cases hArgs :
            compileExprSeqCode? env valuesAboveBase args with
        | none =>
            simp [hArgs] at hCompile
        | some argsCode =>
            simp [hArgs] at hCompile
            cases hCompile
            exact
              structuredCode_append_noCallCreate
                (compileExprSeqCode?_noCallCreate hParts.1 hArgs)
                (by
                  simp [Structured.Code.usesCallCreate,
                    Structured.BasicInstr.usesCallCreate, hParts.2])

  theorem compileExprSeqCode?_noCallCreate {env : SlotEnv}
      {valuesAboveBase results : Nat}
      {exprs : Locals.ExprSeq results} {code : Structured.Code}
      (hExprs : exprs.usesCallCreate = false)
      (hCompile :
        compileExprSeqCode? env valuesAboveBase exprs = some code) :
      code.usesCallCreate = false := by
    cases exprs with
    | nil =>
        simp [compileExprSeqCode?] at hCompile
        cases hCompile
        rfl
    | @cons left right head tail =>
        have hParts :
            head.usesCallCreate = false ∧ tail.usesCallCreate = false := by
          simpa [Locals.ExprSeq.usesCallCreate] using hExprs
        simp [compileExprSeqCode?] at hCompile
        cases hHead :
            compileExprCode? env valuesAboveBase head with
        | none =>
            simp [hHead] at hCompile
        | some headCode =>
            cases hTail :
                compileExprSeqCode? env (valuesAboveBase + left) tail with
            | none =>
                simp [hHead, hTail] at hCompile
            | some tailCode =>
                simp [hHead, hTail] at hCompile
                cases hCompile
                exact
                  structuredCode_append_noCallCreate
                    (compileExprCode?_noCallCreate hParts.1 hHead)
                    (compileExprSeqCode?_noCallCreate hParts.2 hTail)
end

set_option linter.unusedSimpArgs false in
mutual
  theorem compileNoVarExprCode?_noCallCreate {results : Nat}
      {expr : Expr results} {code : Structured.Code}
      (hExpr : expr.usesCallCreate = false)
      (hCompile : compileNoVarExprCode? expr = some code) :
      code.usesCallCreate = false := by
    cases expr with
    | lit value =>
        simp [compileNoVarExprCode?] at hCompile
        cases hCompile
        simp [Structured.Code.usesCallCreate,
          Structured.BasicInstr.usesCallCreate]
    | var name =>
        simp [compileNoVarExprCode?] at hCompile
    | code raw =>
        simp [compileNoVarExprCode?] at hCompile
        cases hCompile
        simpa [Locals.Expr.usesCallCreate] using hExpr
    | prim op args =>
        have hParts :
            args.usesCallCreate = false ∧
              op.toPrimOp.isCallCreate = false := by
          simpa [Locals.Expr.usesCallCreate] using hExpr
        simp [compileNoVarExprCode?] at hCompile
        cases hArgs : compileNoVarExprSeqCode? args with
        | none =>
            simp [hArgs] at hCompile
        | some argsCode =>
            simp [hArgs] at hCompile
            cases hCompile
            exact
              structuredCode_append_noCallCreate
                (compileNoVarExprSeqCode?_noCallCreate hParts.1 hArgs)
                (by
                  simp [Structured.Code.usesCallCreate,
                    Structured.BasicInstr.usesCallCreate, hParts.2])

  theorem compileNoVarExprSeqCode?_noCallCreate {results : Nat}
      {exprs : Locals.ExprSeq results} {code : Structured.Code}
      (hExprs : exprs.usesCallCreate = false)
      (hCompile : compileNoVarExprSeqCode? exprs = some code) :
      code.usesCallCreate = false := by
    cases exprs with
    | nil =>
        simp [compileNoVarExprSeqCode?] at hCompile
        cases hCompile
        rfl
    | @cons left right head tail =>
        have hParts :
            head.usesCallCreate = false ∧ tail.usesCallCreate = false := by
          simpa [Locals.ExprSeq.usesCallCreate] using hExprs
        simp [compileNoVarExprSeqCode?] at hCompile
        cases hHead : compileNoVarExprCode? head with
        | none =>
            simp [hHead] at hCompile
        | some headCode =>
            cases hTail : compileNoVarExprSeqCode? tail with
            | none =>
                simp [hHead, hTail] at hCompile
            | some tailCode =>
                simp [hHead, hTail] at hCompile
                cases hCompile
                exact
                  structuredCode_append_noCallCreate
                    (compileNoVarExprCode?_noCallCreate hParts.1 hHead)
                    (compileNoVarExprSeqCode?_noCallCreate hParts.2 hTail)
end

theorem compileCallArgsToSlots?_noCallCreate {env : SlotEnv} :
    ∀ {args : List (Expr 1)} {slots : List (Name × Nat)}
      {code : Structured.Code},
      ExprList.usesCallCreate args = false →
      compileCallArgsToSlots? env args slots = some code →
        code.usesCallCreate = false
  | [], [], code, _hArgs, hCode => by
      simp [compileCallArgsToSlots?] at hCode
      cases hCode
      rfl
  | [], (_name, slot) :: slots, code, _hArgs, hCode => by
      simp [compileCallArgsToSlots?] at hCode
  | arg :: args, [], code, _hArgs, hCode => by
      simp [compileCallArgsToSlots?] at hCode
  | arg :: args, (_name, slot) :: slots, code, hArgs, hCode => by
      have hParts :
          arg.usesCallCreate = false ∧
            ExprList.usesCallCreate args = false := by
        simpa [ExprList.usesCallCreate] using hArgs
      simp [compileCallArgsToSlots?] at hCode
      cases hArg : compileExprCode? env 0 arg with
      | none =>
          simp [hArg] at hCode
      | some argCode =>
          cases hStore : storeTopSlotCode? 2 slot with
          | none =>
              simp [hArg, hStore] at hCode
          | some storeCode =>
              cases hTail : compileCallArgsToSlots? env args slots with
              | none =>
                  simp [hArg, hStore, hTail] at hCode
              | some tailCode =>
                  simp [hArg, hStore, hTail] at hCode
                  cases hCode
                  exact
                    structuredCode_append_noCallCreate
                      (compileExprCode?_noCallCreate hParts.1 hArg)
                      (structuredCode_append_noCallCreate
                        (storeTopSlotCode?_noCallCreate hStore)
                        (compileCallArgsToSlots?_noCallCreate hParts.2 hTail))

theorem compileReturnLoadsCode?_noCallCreate :
    ∀ {env : SlotEnv} {valuesAboveBase : Nat} {returns : List Name}
      {code : Structured.Code},
      compileReturnLoadsCode? env valuesAboveBase returns = some code →
        code.usesCallCreate = false
  | env, valuesAboveBase, [], code, hCode => by
      simp [compileReturnLoadsCode?] at hCode
      cases hCode
      rfl
  | env, valuesAboveBase, name :: rest, code, hCode => by
      simp [compileReturnLoadsCode?] at hCode
      cases hSlot : lookupSlot? name env with
      | none =>
          simp [hSlot] at hCode
      | some slot =>
          cases hHead : loadSlotCode? valuesAboveBase slot with
          | none =>
              simp [hSlot, hHead] at hCode
          | some head =>
              cases hTail :
                  compileReturnLoadsCode? env (valuesAboveBase + 1) rest with
              | none =>
                  simp [hSlot, hHead, hTail] at hCode
              | some tail =>
                  simp [hSlot, hHead, hTail] at hCode
                  cases hCode
                  exact
                    structuredCode_append_noCallCreate
                      (loadSlotCode?_noCallCreate hHead)
                      (compileReturnLoadsCode?_noCallCreate hTail)

theorem compileReturnCode?_noCallCreate {env : SlotEnv}
    {returns : List Name} {code : Structured.Code}
    (hCode : compileReturnCode? env returns = some code) :
    code.usesCallCreate = false := by
  unfold compileReturnCode? at hCode
  cases hLoads : compileReturnLoadsCode? env 0 returns with
  | none =>
      simp [hLoads] at hCode
  | some loads =>
      cases hRemove : removeBaseUnderCode? returns.length with
      | none =>
          simp [hLoads, hRemove] at hCode
      | some removeBase =>
          simp [hLoads, hRemove] at hCode
          cases hCode
          exact
            structuredCode_append_noCallCreate
              (compileReturnLoadsCode?_noCallCreate hLoads)
              (removeBaseUnderCode?_noCallCreate hRemove)

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

theorem expressionsStmtList_append_noCallCreate
    {left right : List Expressions.Stmt}
    (hLeft : Expressions.StmtList.usesCallCreate left = false)
    (hRight : Expressions.StmtList.usesCallCreate right = false) :
    Expressions.StmtList.usesCallCreate (left ++ right) = false :=
  Locals.CompilerFacts.Expressions.StmtList.usesCallCreate_append_eq_false
    hLeft hRight

theorem block_append_noCallCreate {left right : Expressions.Block}
    (hLeft : left.usesCallCreate = false)
    (hRight : right.usesCallCreate = false) :
    (Block.append left right).usesCallCreate = false := by
  cases left
  cases right
  simpa [Block.append, Expressions.Block.usesCallCreate] using
    expressionsStmtList_append_noCallCreate hLeft hRight

theorem block_ofCode_noCallCreate {code : Structured.Code}
    (hCode : code.usesCallCreate = false) :
    (Block.ofCode code).usesCallCreate = false := by
  simpa [Block.ofCode, Expressions.Block.usesCallCreate,
    Expressions.StmtList.usesCallCreate, Expressions.Stmt.usesCallCreate]
    using hCode

theorem block_empty_noCallCreate :
    ({ stmts := [] } : Expressions.Block).usesCallCreate = false := by
  simp [Expressions.Block.usesCallCreate, Expressions.StmtList.usesCallCreate]

theorem block_seqList_noCallCreate :
    ∀ {blocks : List Expressions.Block},
      (∀ block, block ∈ blocks → block.usesCallCreate = false) →
      (Block.seqList blocks).usesCallCreate = false
  | [], _hBlocks => by
      simp [Block.seqList, Expressions.Block.usesCallCreate,
        Expressions.StmtList.usesCallCreate]
  | head :: tail, hBlocks => by
      apply block_append_noCallCreate
      · exact hBlocks head (by simp)
      · exact
          block_seqList_noCallCreate
            (by
              intro block hMem
              exact hBlocks block (by simp [hMem]))

theorem callBlock_noCallCreate {functionName : Name} :
    ({ stmts := [Expressions.Stmt.call functionName] } :
      Expressions.Block).usesCallCreate = false := by
  simp [Expressions.Block.usesCallCreate, Expressions.StmtList.usesCallCreate,
    Expressions.Stmt.usesCallCreate]

theorem terminalBlock_noCallCreate {kind : Assembly.HaltKind} :
    ({ stmts := [Expressions.Stmt.terminal kind] } :
      Expressions.Block).usesCallCreate = false := by
  simp [Expressions.Block.usesCallCreate, Expressions.StmtList.usesCallCreate,
    Expressions.Stmt.usesCallCreate]

theorem leaveBlock_noCallCreate :
    ({ stmts := [Expressions.Stmt.leave] } :
      Expressions.Block).usesCallCreate = false := by
  simp [Expressions.Block.usesCallCreate, Expressions.StmtList.usesCallCreate,
    Expressions.Stmt.usesCallCreate]

set_option linter.unusedSimpArgs false in
mutual
  theorem compileBlockOpen?_noCallCreate
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {block : Block} {plan : Plan}
      (hBlock : block.usesCallCreate = false)
      (hCompile :
        compileBlockOpen? ctx returns state block = some plan) :
      plan.block.usesCallCreate = false := by
    cases block with
    | mk stmts =>
        exact compileStmtList?_noCallCreate hBlock
          (by simpa [compileBlockOpen?] using hCompile)

  theorem compileBlockScoped?_noCallCreate
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {block : Block} {plan : Plan}
      (hBlock : block.usesCallCreate = false)
      (hCompile :
        compileBlockScoped? ctx returns state block = some plan) :
      plan.block.usesCallCreate = false := by
    unfold compileBlockScoped? at hCompile
    cases hOpen : compileBlockOpen? ctx returns state block with
    | none =>
        simp [hOpen] at hCompile
    | some openPlan =>
        simp [hOpen] at hCompile
        cases hCompile
        have hOpenNo := compileBlockOpen?_noCallCreate hBlock hOpen
        simpa using hOpenNo

  theorem compileStmtList?_noCallCreate
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {stmts : List Stmt} {plan : Plan},
        StmtList.usesCallCreate stmts = false →
        compileStmtList? ctx returns state stmts = some plan →
          plan.block.usesCallCreate = false
  | [], plan, _hStmts, hCompile => by
      simp [compileStmtList?] at hCompile
      cases hCompile
      simp [Expressions.Block.usesCallCreate,
        Expressions.StmtList.usesCallCreate]
  | stmt :: rest, plan, hStmts, hCompile => by
      have hParts :
          stmt.usesCallCreate = false ∧
            StmtList.usesCallCreate rest = false := by
        simpa [StmtList.usesCallCreate] using hStmts
      unfold compileStmtList? at hCompile
      cases hHead : compileStmt? ctx returns state stmt with
      | none =>
          simp [hHead] at hCompile
      | some head =>
          cases hTail :
              compileStmtList? ctx returns head.state rest with
          | none =>
              simp [hHead, hTail] at hCompile
          | some tail =>
              simp [hHead, hTail] at hCompile
              cases hCompile
              exact
                block_append_noCallCreate
                  (compileStmt?_noCallCreate hParts.1 hHead)
                  (compileStmtList?_noCallCreate hParts.2 hTail)

  theorem compileCases?_noCallCreate
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {cases : List (Word × Block)}
        {compiled : List (Word × Expressions.Block)}
        {state' : CompileState},
        CaseList.usesCallCreate cases = false →
        compileCases? ctx returns state cases = some (compiled, state') →
          Expressions.CaseList.usesCallCreate compiled = false
  | [], compiled, state', _hCases, hCompile => by
      simp [compileCases?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      rfl
  | (value, body) :: rest, compiled, state', hCases, hCompile => by
      have hParts :
          body.usesCallCreate = false ∧
            CaseList.usesCallCreate rest = false := by
        simpa [CaseList.usesCallCreate] using hCases
      unfold compileCases? at hCompile
      cases hBody : compileBlockScoped? ctx returns state body with
      | none =>
          simp [hBody] at hCompile
      | some bodyPlan =>
          cases hTail :
              compileCases? ctx returns bodyPlan.state rest with
          | none =>
              simp [hBody, hTail] at hCompile
          | some tail =>
              rcases tail with ⟨tailCases, tailState⟩
              simp [hBody, hTail] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              have hBodyNo :=
                compileBlockScoped?_noCallCreate hParts.1 hBody
              have hTailNo :=
                compileCases?_noCallCreate hParts.2 hTail
              simpa [Expressions.CaseList.usesCallCreate, hBodyNo, hTailNo]

  theorem compileDefault?_noCallCreate
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {defaultBody : Option Block}
        {compiled : Option Expressions.Block} {state' : CompileState},
        Default.usesCallCreate defaultBody = false →
        compileDefault? ctx returns state defaultBody =
            some (compiled, state') →
          Expressions.Default.usesCallCreate compiled = false
  | none, compiled, state', _hDefault, hCompile => by
      simp [compileDefault?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      rfl
  | some body, compiled, state', hDefault, hCompile => by
      have hBody : body.usesCallCreate = false := by
        simpa [Default.usesCallCreate] using hDefault
      unfold compileDefault? at hCompile
      cases hPlan : compileBlockScoped? ctx returns state body with
      | none =>
          simp [hPlan] at hCompile
      | some plan =>
          simp [hPlan] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          simpa [Expressions.Default.usesCallCreate] using
            compileBlockScoped?_noCallCreate hBody hPlan

  theorem compileStmt?_noCallCreate
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {stmt : Stmt} {plan : Plan}
      (hStmt : stmt.usesCallCreate = false)
      (hCompile :
        compileStmt? ctx returns state stmt = some plan) :
      plan.block.usesCallCreate = false := by
    cases stmt with
    | expr expr =>
        simp [compileStmt?] at hCompile
        cases hCode : compileExprCode? state.env 0 expr with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            exact block_ofCode_noCallCreate
              (compileExprCode?_noCallCreate
                (by simpa [Stmt.usesCallCreate] using hStmt) hCode)
    | let_ name value =>
        have hValue : value.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [compileStmt?] at hCompile
        cases hCode : compileExprCode? state.env 0 value with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            cases hAlloc : allocateName name state with
            | mk slot state' =>
                cases hStore : storeTopSlotCode? 1 slot with
                | none =>
                    simp [hCode, hAlloc, hStore] at hCompile
                | some store =>
                    simp [hCode, hAlloc, hStore] at hCompile
                    cases hCompile
                    exact
                      block_ofCode_noCallCreate
                        (structuredCode_append_noCallCreate
                          (compileExprCode?_noCallCreate hValue hCode)
                          (storeTopSlotCode?_noCallCreate hStore))
    | assign name value =>
        have hValue : value.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [compileStmt?] at hCompile
        cases hSlot : lookupSlot? name state.env with
        | none =>
            simp [hSlot] at hCompile
        | some slot =>
            cases hCode : compileExprCode? state.env 0 value with
            | none =>
                simp [hSlot, hCode] at hCompile
            | some code =>
                cases hStore : storeTopSlotCode? 1 slot with
                | none =>
                    simp [hSlot, hCode, hStore] at hCompile
                | some store =>
                    simp [hSlot, hCode, hStore] at hCompile
                    cases hCompile
                    exact
                      block_ofCode_noCallCreate
                        (structuredCode_append_noCallCreate
                          (compileExprCode?_noCallCreate hValue hCode)
                          (storeTopSlotCode?_noCallCreate hStore))
    | block body =>
        exact
          compileBlockScoped?_noCallCreate
            (by simpa [Stmt.usesCallCreate] using hStmt)
            (by simpa [compileStmt?] using hCompile)
    | if_ cond body =>
        have hParts :
            cond.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [compileStmt?] at hCompile
        cases hCond : compileExprCode? state.env 0 cond with
        | none =>
            simp [hCond] at hCompile
        | some condCode =>
            cases hBody : compileBlockScoped? ctx returns state body with
            | none =>
                simp [hCond, hBody] at hCompile
            | some bodyPlan =>
                simp [hCond, hBody] at hCompile
                cases hCompile
                have hCondNo :=
                  compileExprCode?_noCallCreate hParts.1 hCond
                have hBodyNo :=
                  compileBlockScoped?_noCallCreate hParts.2 hBody
                simp [Expressions.Block.usesCallCreate,
                  Expressions.StmtList.usesCallCreate,
                  Expressions.Stmt.usesCallCreate,
                  Expressions.Expr.usesCallCreate, hCondNo, hBodyNo]
    | switch scrutinee cases defaultBody =>
        have hParts :
            scrutinee.usesCallCreate = false ∧
              CaseList.usesCallCreate cases = false ∧
                Default.usesCallCreate defaultBody = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        simp [compileStmt?] at hCompile
        cases hScrutinee : compileExprCode? state.env 0 scrutinee with
        | none =>
            simp [hScrutinee] at hCompile
        | some scrutineeCode =>
            cases hCases : compileCases? ctx returns state cases with
            | none =>
                simp [hScrutinee, hCases] at hCompile
            | some casesResult =>
                rcases casesResult with ⟨compiledCases, stateAfterCases⟩
                cases hDefault :
                    compileDefault? ctx returns stateAfterCases defaultBody with
                | none =>
                    simp [hScrutinee, hCases, hDefault] at hCompile
                | some defaultResult =>
                    rcases defaultResult with
                      ⟨compiledDefault, stateAfterDefault⟩
                    simp [hScrutinee, hCases, hDefault] at hCompile
                    cases hCompile
                    have hScrutineeNo :=
                      compileExprCode?_noCallCreate hParts.1 hScrutinee
                    have hCasesNo :=
                      compileCases?_noCallCreate hParts.2.1 hCases
                    have hDefaultNo :=
                      compileDefault?_noCallCreate hParts.2.2 hDefault
                    simp [Expressions.Block.usesCallCreate,
                      Expressions.StmtList.usesCallCreate,
                      Expressions.Stmt.usesCallCreate,
                      Expressions.Expr.usesCallCreate, hScrutineeNo,
                      hCasesNo, hDefaultNo]
    | for_ init cond post body =>
        have hParts :
            init.usesCallCreate = false ∧ cond.usesCallCreate = false ∧
              post.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        simp [compileStmt?] at hCompile
        cases hInit : compileBlockOpen? ctx returns state init with
        | none =>
            simp [hInit] at hCompile
        | some initPlan =>
            cases hCond :
                compileExprCode? initPlan.state.env 0 cond with
            | none =>
                simp [hInit, hCond] at hCompile
            | some condCode =>
                cases hPost :
                    compileBlockScoped? ctx returns initPlan.state post with
                | none =>
                    simp [hInit, hCond, hPost] at hCompile
                | some postPlan =>
                    cases hBody :
                        compileBlockScoped? ctx returns postPlan.state body with
                    | none =>
                        simp [hInit, hCond, hPost, hBody] at hCompile
                    | some bodyPlan =>
                        simp [hInit, hCond, hPost, hBody] at hCompile
                        cases hCompile
                        have hInitNo :=
                          compileBlockOpen?_noCallCreate hParts.1 hInit
                        have hCondNo :=
                          compileExprCode?_noCallCreate hParts.2.1 hCond
                        have hPostNo :=
                          compileBlockScoped?_noCallCreate hParts.2.2.1 hPost
                        have hBodyNo :=
                          compileBlockScoped?_noCallCreate hParts.2.2.2 hBody
                        simp [Expressions.Block.usesCallCreate,
                          Expressions.StmtList.usesCallCreate,
                          Expressions.Stmt.usesCallCreate,
                          Expressions.Expr.usesCallCreate, hInitNo, hCondNo,
                          hPostNo, hBodyNo]
    | brk =>
        simp [compileStmt?] at hCompile
        cases hCompile
        simp [Expressions.Block.usesCallCreate,
          Expressions.StmtList.usesCallCreate, Expressions.Stmt.usesCallCreate]
    | cont =>
        simp [compileStmt?] at hCompile
        cases hCompile
        simp [Expressions.Block.usesCallCreate,
          Expressions.StmtList.usesCallCreate, Expressions.Stmt.usesCallCreate]
    | leave =>
        simp [compileStmt?] at hCompile
        cases hCode : compileReturnCode? state.env returns with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            exact
              block_seqList_noCallCreate
                (by
                  intro block hMem
                  simp only [List.mem_cons, List.not_mem_nil] at hMem
                  rcases hMem with hMem | hMem
                  · subst block
                    exact block_ofCode_noCallCreate
                      (compileReturnCode?_noCallCreate hCode)
                  · rcases hMem with hMem | hMem
                    · subst block
                      exact leaveBlock_noCallCreate
                    · contradiction)
    | call targets functionName args =>
        have hArgs : ExprList.usesCallCreate args = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [compileStmt?] at hCompile
        cases hFn : lookupFun? functionName ctx.functions with
        | none =>
            simp [hFn] at hCompile
        | some fn =>
            by_cases hArgsLen : args.length = fn.params.length
            · simp [hFn, hArgsLen] at hCompile
              by_cases hTargetsLen : targets.length = fn.returns.length
              · simp [hTargetsLen] at hCompile
                by_cases hTargetsNodup : targets.Nodup
                · simp [hTargetsNodup] at hCompile
                  cases hCallerBase : swapTopTwoCode? with
                  | none =>
                      simp [hCallerBase] at hCompile
                  | some callerBaseTop =>
                      cases hArgsCode :
                          compileCallArgsToSlots? state.env args fn.params with
                      | none =>
                          simp [hCallerBase, hArgsCode] at hCompile
                      | some argCode =>
                          cases hCalleeBase : swapTopTwoCode? with
                          | none =>
                              simp [hCallerBase] at hCalleeBase
                          | some calleeBaseTop =>
                              cases hTargetSlots :
                                  targets.mapM
                                    (fun name => lookupSlot? name state.env) with
                              | none =>
                                  simp [hCallerBase, hArgsCode, hCalleeBase,
                                    hTargetSlots] at hCompile
                              | some targetSlots =>
                                  cases hStoreReturns :
                                      compileStoreTopSlots? fn.returns.length
                                        targetSlots.reverse with
                                  | none =>
                                      simp [hCallerBase, hArgsCode,
                                        hCalleeBase, hTargetSlots,
                                        hStoreReturns] at hCompile
                                  | some storeReturns =>
                                      simp [hCallerBase, hArgsCode,
                                        hCalleeBase, hTargetSlots,
                                        hStoreReturns] at hCompile
                                      cases hCompile
                                      exact
                                        block_seqList_noCallCreate
                                          (by
                                            intro block hMem
                                            simp only [List.mem_cons,
                                              List.not_mem_nil] at hMem
                                            rcases hMem with hMem | hMem
                                            · subst block
                                              exact block_ofCode_noCallCreate
                                                (frameInitCode_noCallCreate
                                                  ctx.frameWords)
                                            · rcases hMem with hMem | hMem
                                              · subst block
                                                exact
                                                  block_ofCode_noCallCreate
                                                    (swapTopTwoCode?_noCallCreate
                                                      hCallerBase)
                                              · rcases hMem with hMem | hMem
                                                · subst block
                                                  exact
                                                    block_ofCode_noCallCreate
                                                      (compileCallArgsToSlots?_noCallCreate
                                                        hArgs hArgsCode)
                                                · rcases hMem with hMem | hMem
                                                  · subst block
                                                    exact
                                                      block_ofCode_noCallCreate
                                                        (swapTopTwoCode?_noCallCreate
                                                          hCallerBase)
                                                  · rcases hMem with hMem | hMem
                                                    · subst block
                                                      exact callBlock_noCallCreate
                                                    · rcases hMem with hMem | hMem
                                                      · subst block
                                                        exact
                                                          block_ofCode_noCallCreate
                                                            (compileStoreTopSlots?_noCallCreate
                                                              hStoreReturns)
                                                      · contradiction)
                · simp [hFn, hArgsLen, hTargetsLen, hTargetsNodup]
                    at hCompile
              · simp [hFn, hArgsLen, hTargetsLen] at hCompile
            · simp [hFn, hArgsLen] at hCompile
    | terminal kind =>
        simp [compileStmt?] at hCompile
        cases hCompile
        exact terminalBlock_noCallCreate
    | terminalArgs kind args =>
        have hArgs : args.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp [compileStmt?] at hCompile
        cases hCode : compileExprSeqCode? state.env 0 args with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            exact
              block_seqList_noCallCreate
                (by
                  intro block hMem
                  simp only [List.mem_cons, List.not_mem_nil] at hMem
                  rcases hMem with hMem | hMem
                  · subst block
                    exact block_ofCode_noCallCreate
                      (compileExprSeqCode?_noCallCreate hArgs hCode)
                  · rcases hMem with hMem | hMem
                    · subst block
                      exact terminalBlock_noCallCreate
                    · contradiction)
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

theorem compilePreludeStmt?_noCallCreate {stmt : Stmt}
    {compiled : Expressions.Stmt}
    (hStmt : stmt.usesCallCreate = false)
    (hCompile : compilePreludeStmt? stmt = some compiled) :
    compiled.usesCallCreate = false := by
  cases stmt with
  | expr expr =>
      simp [compilePreludeStmt?] at hCompile
      cases hCode : compileNoVarExprCode? expr with
      | none =>
          simp [hCode] at hCompile
      | some code =>
          simp [hCode] at hCompile
          cases hCompile
          exact compileNoVarExprCode?_noCallCreate
            (by simpa [Stmt.usesCallCreate] using hStmt) hCode
  | let_ name value =>
      simp [compilePreludeStmt?] at hCompile
  | assign name value =>
      simp [compilePreludeStmt?] at hCompile
  | block body =>
      simp [compilePreludeStmt?] at hCompile
  | if_ cond body =>
      simp [compilePreludeStmt?] at hCompile
  | switch scrutinee cases defaultBody =>
      simp [compilePreludeStmt?] at hCompile
  | for_ init cond post body =>
      simp [compilePreludeStmt?] at hCompile
  | brk =>
      simp [compilePreludeStmt?] at hCompile
  | cont =>
      simp [compilePreludeStmt?] at hCompile
  | leave =>
      simp [compilePreludeStmt?] at hCompile
  | call targets functionName args =>
      simp [compilePreludeStmt?] at hCompile
  | terminal kind =>
      simp [compilePreludeStmt?] at hCompile
  | terminalArgs kind args =>
      simp [compilePreludeStmt?] at hCompile

theorem splitPrelude_noCallCreate :
    ∀ {stmts : List Stmt} {prelude : List Expressions.Stmt}
      {rest : List Stmt},
      StmtList.usesCallCreate stmts = false →
      splitPrelude stmts = (prelude, rest) →
        Expressions.StmtList.usesCallCreate prelude = false ∧
          StmtList.usesCallCreate rest = false
  | [], prelude, rest, _hStmts, hSplit => by
      simp [splitPrelude] at hSplit
      rcases hSplit with ⟨rfl, rfl⟩
      simp [Expressions.StmtList.usesCallCreate, StmtList.usesCallCreate]
  | stmt :: stmts, prelude, rest, hStmts, hSplit => by
      have hParts :
          stmt.usesCallCreate = false ∧
            StmtList.usesCallCreate stmts = false := by
        simpa [StmtList.usesCallCreate] using hStmts
      unfold splitPrelude at hSplit
      cases hPrelude : compilePreludeStmt? stmt with
      | none =>
          simp [hPrelude] at hSplit
          rcases hSplit with ⟨rfl, rfl⟩
          exact ⟨rfl, hStmts⟩
      | some compiled =>
          cases hTail : splitPrelude stmts with
          | mk tailPrelude tailRest =>
              simp [hPrelude, hTail] at hSplit
              rcases hSplit with ⟨rfl, rfl⟩
              rcases splitPrelude_noCallCreate hParts.2 hTail with
                ⟨hTailPrelude, hTailRest⟩
              have hCompiled :=
                compilePreludeStmt?_noCallCreate hParts.1 hPrelude
              exact
                ⟨by
                  simp [Expressions.StmtList.usesCallCreate, hCompiled,
                    hTailPrelude],
                 hTailRest⟩

theorem compileFunction?_noCallCreate {ctx : CompileCtx}
    {state : CompileState} {fn : FunDef}
    {proc : Expressions.Proc} {state' : CompileState}
    (hFn : fn.usesCallCreate = false)
    (hCompile : compileFunction? ctx state fn = some (proc, state')) :
    proc.usesCallCreate = false := by
  have hBody : fn.body.usesCallCreate = false := by
    simpa [FunDef.usesCallCreate] using hFn
  unfold compileFunction? at hCompile
  by_cases hSigNodup : (fn.returns ++ fn.params).Nodup
  · simp [hSigNodup] at hCompile
    by_cases hRetBound : fn.returns.length < 16
    · simp [hRetBound] at hCompile
      cases hSlots : lookupFun? fn.name ctx.functions with
      | none =>
          simp [hSlots] at hCompile
      | some slots =>
          simp [hSlots] at hCompile
          let bodyStart : CompileState :=
            { env := functionEnv slots, nextSlot := state.nextSlot }
          cases hBodyPlan :
              compileBlockOpen? ctx fn.returns bodyStart fn.body with
          | none =>
              simp [bodyStart, hBodyPlan] at hCompile
          | some bodyPlan =>
              cases hRetCode :
                  compileReturnCode? bodyPlan.state.env fn.returns with
              | none =>
                  simp [bodyStart, hBodyPlan, hRetCode] at hCompile
              | some retCode =>
                  simp [bodyStart, hBodyPlan, hRetCode] at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  have hBodyNo :=
                    compileBlockOpen?_noCallCreate hBody hBodyPlan
                  have hRetNo :=
                    block_ofCode_noCallCreate
                      (compileReturnCode?_noCallCreate hRetCode)
                  simpa [Expressions.Proc.usesCallCreate] using
                    block_append_noCallCreate hBodyNo hRetNo
    · simp [hRetBound] at hCompile
  · simp [hSigNodup] at hCompile

theorem compileFunctions?_noCallCreate {ctx : CompileCtx} :
    ∀ {state : CompileState} {fns : List FunDef}
      {procs : List Expressions.Proc} {state' : CompileState},
      FunList.usesCallCreate fns = false →
      compileFunctions? ctx state fns = some (procs, state') →
        Expressions.ProcList.usesCallCreate procs = false
  | state, [], procs, state', _hFns, hCompile => by
      simp [compileFunctions?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      rfl
  | state, fn :: rest, procs, state', hFns, hCompile => by
      have hParts :
          fn.usesCallCreate = false ∧
            FunList.usesCallCreate rest = false := by
        simpa [FunList.usesCallCreate] using hFns
      unfold compileFunctions? at hCompile
      cases hHead : compileFunction? ctx state fn with
      | none =>
          simp [hHead] at hCompile
      | some headResult =>
          rcases headResult with ⟨proc, stateAfterHead⟩
          cases hTail :
              compileFunctions? ctx stateAfterHead rest with
          | none =>
              simp [hHead, hTail] at hCompile
          | some tailResult =>
              rcases tailResult with ⟨tailProcs, tailState⟩
              simp [hHead, hTail] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              have hHeadNo := compileFunction?_noCallCreate hParts.1 hHead
              have hTailNo := compileFunctions?_noCallCreate hParts.2 hTail
              simp [Expressions.ProcList.usesCallCreate, hHeadNo, hTailNo]

theorem compileMain?_noCallCreate {ctx : CompileCtx}
    {frameWords : Nat} {state : CompileState} {body : Block}
    {plan : Plan}
    (hBody : body.usesCallCreate = false)
    (hCompile : compileMain? ctx frameWords state body = some plan) :
    plan.block.usesCallCreate = false := by
  cases body with
  | mk stmts =>
      unfold compileMain? at hCompile
      cases hSplit : splitPrelude stmts with
      | mk prelude rest =>
          simp [hSplit] at hCompile
          cases hPlan : compileStmtList? ctx [] state rest with
          | none =>
              simp [hPlan] at hCompile
          | some bodyPlan =>
              simp [hPlan] at hCompile
              cases hCompile
              rcases
                  splitPrelude_noCallCreate
                    (by simpa [Block.usesCallCreate] using hBody) hSplit with
                ⟨hPrelude, hRest⟩
              have hPlanNo :=
                compileStmtList?_noCallCreate hRest hPlan
              let init := Expressions.Stmt.code (frameInitCode frameWords)
              have hPlanStmts :
                  Expressions.StmtList.usesCallCreate
                    bodyPlan.block.stmts = false := by
                cases hBlock : bodyPlan.block with
                | mk bodyStmts =>
                    simpa [hBlock, Expressions.Block.usesCallCreate]
                      using hPlanNo
              have hInitTail :
                  Expressions.StmtList.usesCallCreate
                    (init :: bodyPlan.block.stmts) = false := by
                simp [init, Expressions.StmtList.usesCallCreate,
                  Expressions.Stmt.usesCallCreate,
                  frameInitCode_noCallCreate, hPlanStmts]
              simpa [Expressions.Block.usesCallCreate] using
                expressionsStmtList_append_noCallCreate hPrelude hInitTail

theorem compileExpressionsProgram?_noCallCreate
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile :
      compileExpressionsProgram? maxFrameWords program = some exprProgram) :
    exprProgram.usesCallCreate = false := by
  have hParts :
      FunList.usesCallCreate program.functions = false ∧
        program.body.usesCallCreate = false := by
    simpa [Program.usesCallCreate] using hProgram
  unfold compileExpressionsProgram? at hCompile
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · simp [hNames] at hCompile
    let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        simp [initial, hSignatures] at hCompile
        let ctx0 : CompileCtx := { functions := functionSlots, frameWords := 0 }
        cases hProbeFunctions :
            compileFunctions? ctx0 stateAfterSignatures program.functions with
        | none =>
            simp [ctx0, hProbeFunctions] at hCompile
        | some probeResult =>
            rcases probeResult with ⟨_probeProcs, stateAfterFunctions⟩
            let mainStart : CompileState :=
              { env := [], nextSlot := stateAfterFunctions.nextSlot }
            cases hMainProbe :
                compileMain? ctx0 0 mainStart program.body with
            | none =>
                simp [ctx0, mainStart, hProbeFunctions, hMainProbe]
                  at hCompile
            | some mainProbe =>
                by_cases hBound : mainProbe.state.nextSlot ≤ maxFrameWords
                · simp [ctx0, mainStart, hProbeFunctions, hMainProbe,
                    hBound] at hCompile
                  let frameWords := mainProbe.state.nextSlot
                  let ctxFinal : CompileCtx :=
                    { functions := functionSlots, frameWords := frameWords }
                  cases hFinalFunctions :
                      compileFunctions? ctxFinal stateAfterSignatures
                        program.functions with
                  | none =>
                      have hFinalFunctions' :
                          compileFunctions?
                              { functions := functionSlots,
                                frameWords := mainProbe.state.nextSlot }
                              stateAfterSignatures program.functions =
                            none := by
                        simpa [frameWords, ctxFinal] using hFinalFunctions
                      simp [hFinalFunctions'] at hCompile
                  | some finalResult =>
                      rcases finalResult with ⟨procs, _stateAfterFunctions⟩
                      have hFinalFunctions' :
                          compileFunctions?
                              { functions := functionSlots,
                                frameWords := mainProbe.state.nextSlot }
                              stateAfterSignatures program.functions =
                            some (procs, _stateAfterFunctions) := by
                        simpa [frameWords, ctxFinal] using hFinalFunctions
                      cases hMain :
                          compileMain? ctxFinal frameWords mainStart
                            program.body with
                      | none =>
                          have hMain' :
                              compileMain?
                                  { functions := functionSlots,
                                    frameWords := mainProbe.state.nextSlot }
                                  mainProbe.state.nextSlot
                                  { env := [],
                                    nextSlot := stateAfterFunctions.nextSlot }
                                  program.body = none := by
                            simpa [frameWords, ctxFinal, mainStart] using hMain
                          simp [hFinalFunctions', hMain'] at hCompile
                      | some main =>
                          have hMain' :
                              compileMain?
                                  { functions := functionSlots,
                                    frameWords := mainProbe.state.nextSlot }
                                  mainProbe.state.nextSlot
                                  { env := [],
                                    nextSlot := stateAfterFunctions.nextSlot }
                                  program.body = some main := by
                            simpa [frameWords, ctxFinal, mainStart] using hMain
                          simp [hFinalFunctions', hMain'] at hCompile
                          cases hCompile
                          have hProcsNo :=
                            compileFunctions?_noCallCreate hParts.1
                              hFinalFunctions
                          have hMainNo :=
                            compileMain?_noCallCreate hParts.2 hMain
                          simp [Expressions.Program.usesCallCreate,
                            hProcsNo, hMainNo]
                · simp [ctx0, mainStart, hProbeFunctions, hMainProbe,
                    hBound] at hCompile
  · simp [hNames] at hCompile

noncomputable def compileChecked? (maxFrameWords : Nat)
    (program : Program) : Option (Expressions.Program × Assembly.Program) := do
  let exprProgram ← compileExpressionsProgram? maxFrameWords program
  let asm ← Expressions.Program.compileChecked? exprProgram
  some (exprProgram, asm)

theorem compileChecked?_eq_some
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileChecked? maxFrameWords program = some (exprProgram, asm)) :
    compileExpressionsProgram? maxFrameWords program = some exprProgram ∧
      Expressions.Program.compileChecked? exprProgram = some asm := by
  unfold compileChecked? at hCompile
  cases hExpr : compileExpressionsProgram? maxFrameWords program with
  | none =>
      simp [hExpr] at hCompile
  | some exprProgram' =>
      simp [hExpr] at hCompile
      cases hAsm : Expressions.Program.compileChecked? exprProgram' with
      | none =>
          simp [hAsm] at hCompile
      | some asm' =>
          simp [hAsm] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact ⟨rfl, hAsm⟩

theorem compileChecked?_noCallCreate
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hExprNo : exprProgram.usesCallCreate = false)
    (hCompile :
      compileChecked? maxFrameWords program = some (exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false := by
  exact
    Expressions.Program.compileChecked?_noCallCreate hExprNo
      (compileChecked?_eq_some hCompile).2

theorem compileChecked?_noCallCreate_of_source
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile :
      compileChecked? maxFrameWords program = some (exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  compileChecked?_noCallCreate
    (compileExpressionsProgram?_noCallCreate hProgram
      (compileChecked?_eq_some hCompile).1)
    hCompile

noncomputable def compileCheckedAssembly? (maxFrameWords : Nat)
    (program : Program) : Option Assembly.Program := do
  let (_exprProgram, asm) ← compileChecked? maxFrameWords program
  some asm

theorem compileCheckedAssembly?_eq_some
    {maxFrameWords : Nat} {program : Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedAssembly? maxFrameWords program = some asm) :
    ∃ exprProgram : Expressions.Program,
      compileExpressionsProgram? maxFrameWords program = some exprProgram ∧
        Expressions.Program.compileChecked? exprProgram = some asm := by
  unfold compileCheckedAssembly? at hCompile
  cases hChecked : compileChecked? maxFrameWords program with
  | none =>
      simp [hChecked] at hCompile
  | some result =>
      rcases result with ⟨exprProgram, asm'⟩
      simp [hChecked] at hCompile
      cases hCompile
      exact ⟨exprProgram, compileChecked?_eq_some hChecked⟩

theorem compileCheckedAssembly?_noCallCreate
    {maxFrameWords : Nat} {program : Program} {asm : Assembly.Program}
    (hExprNo :
      ∀ exprProgram : Expressions.Program,
        compileExpressionsProgram? maxFrameWords program = some exprProgram →
          exprProgram.usesCallCreate = false)
    (hCompile :
      compileCheckedAssembly? maxFrameWords program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileCheckedAssembly?_eq_some hCompile with
    ⟨exprProgram, hExpr, hAsm⟩
  exact Expressions.Program.compileChecked?_noCallCreate
    (hExprNo exprProgram hExpr) hAsm

theorem compileCheckedAssembly?_noCallCreate_of_source
    {maxFrameWords : Nat} {program : Program} {asm : Assembly.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile :
      compileCheckedAssembly? maxFrameWords program = some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  compileCheckedAssembly?_noCallCreate
    (fun exprProgram hExpr =>
      compileExpressionsProgram?_noCallCreate hProgram hExpr)
    hCompile

def compileTarget? (maxFrameWords : Nat)
    (program : Program) : Option Assembly.TargetProgram := do
  let exprProgram ← compileExpressionsProgram? maxFrameWords program
  Expressions.Program.compileExecutable? exprProgram

theorem compileTarget?_eq_standard (maxFrameWords : Nat)
    (program : Program) :
    compileTarget? maxFrameWords program =
      (do
        let exprProgram ← compileExpressionsProgram? maxFrameWords program
        Expressions.Program.compile? exprProgram) := by
  unfold compileTarget?
  cases hExpr : compileExpressionsProgram? maxFrameWords program with
  | none =>
      simp [hExpr]
  | some exprProgram =>
      simp [hExpr, Expressions.Program.compileExecutable?_eq_compile?]

end ScratchFrameSpill
end Functions
end EvmCompiler
