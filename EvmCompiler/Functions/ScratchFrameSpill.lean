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

def slotList (entries : List (Name × Nat)) : List Nat :=
  entries.map Prod.snd

def functionEnv (slots : FunSlots) : SlotEnv :=
  slots.returns ++ slots.params

def EnvSlotsBounded (env : SlotEnv) (limit : Nat) : Prop :=
  ∀ entry, entry ∈ env → entry.2 < limit

def StateSlotsBounded (state : CompileState) : Prop :=
  EnvSlotsBounded state.env state.nextSlot

def FunSlotsBounded (slots : FunSlots) (limit : Nat) : Prop :=
  EnvSlotsBounded (functionEnv slots) limit

def FunSlotListBounded (functions : List FunSlots) (limit : Nat) : Prop :=
  ∀ slots, slots ∈ functions → FunSlotsBounded slots limit

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

theorem lookupSlot?_some_mem {name : Name} {slot : Nat}
    {env : SlotEnv}
    (hLookup : lookupSlot? name env = some slot) :
    (name, slot) ∈ env := by
  induction env with
  | nil =>
      simp [lookupSlot?] at hLookup
  | cons head rest ih =>
      rcases head with ⟨candidate, candidateSlot⟩
      by_cases hName : candidate = name
      · simp [lookupSlot?, hName] at hLookup
        cases hLookup
        simp [hName]
      · simp [lookupSlot?, hName] at hLookup
        exact List.mem_cons_of_mem _ (ih hLookup)

theorem lookupSlot?_lt_of_bounded {name : Name} {slot limit : Nat}
    {env : SlotEnv}
    (hBound : EnvSlotsBounded env limit)
    (hLookup : lookupSlot? name env = some slot) :
    slot < limit := by
  exact hBound (name, slot) (lookupSlot?_some_mem hLookup)

theorem lookupFun?_some_mem {name : Name} {slots : FunSlots}
    {functions : List FunSlots}
    (hLookup : lookupFun? name functions = some slots) :
    slots ∈ functions := by
  induction functions with
  | nil =>
      simp [lookupFun?] at hLookup
  | cons head rest ih =>
      by_cases hName : head.name = name
      · simp [lookupFun?, hName] at hLookup
        cases hLookup
        simp
      · simp [lookupFun?, hName] at hLookup
        exact List.mem_cons_of_mem _ (ih hLookup)

theorem lookupFun?_bounded {name : Name} {slots : FunSlots}
    {functions : List FunSlots} {limit : Nat}
    (hBound : FunSlotListBounded functions limit)
    (hLookup : lookupFun? name functions = some slots) :
    FunSlotsBounded slots limit :=
  hBound slots (lookupFun?_some_mem hLookup)

theorem funSlotListBounded_mono {functions : List FunSlots}
    {limit limit' : Nat}
    (hBound : FunSlotListBounded functions limit)
    (hLe : limit ≤ limit') :
    FunSlotListBounded functions limit' := by
  intro slots hMem entry hEntry
  exact Nat.lt_of_lt_of_le (hBound slots hMem entry hEntry) hLe

theorem allocateName_nextSlot (name : Name) (state : CompileState) :
    (allocateName name state).2.nextSlot = state.nextSlot + 1 := by
  simp [allocateName]

theorem allocateName_env (name : Name) (state : CompileState) :
    (allocateName name state).2.env =
      (name, state.nextSlot) :: state.env := by
  simp [allocateName]

theorem allocateName_stateSlotsBounded (name : Name)
    (state : CompileState)
    (hBound : StateSlotsBounded state) :
    StateSlotsBounded (allocateName name state).2 := by
  intro entry hMem
  simp [allocateName] at hMem ⊢
  rcases hMem with hHead | hTail
  · cases hHead
    omega
  · exact Nat.lt_trans (hBound entry hTail) (Nat.lt_succ_self _)

theorem allocateNames_nextSlot :
    ∀ (names : List Name) (state : CompileState),
      (allocateNames names state).2.nextSlot =
        state.nextSlot + names.length
  | [], state => by
      simp [allocateNames]
  | name :: rest, state => by
      let state1 : CompileState :=
        { env := (name, state.nextSlot) :: state.env,
          nextSlot := state.nextSlot + 1 }
      have hTail := allocateNames_nextSlot rest state1
      simp [state1] at hTail
      simp [allocateNames, allocateName]
      omega

theorem allocateNames_nextSlot_mono (names : List Name)
    (state : CompileState) :
    state.nextSlot ≤ (allocateNames names state).2.nextSlot := by
  rw [allocateNames_nextSlot]
  omega

theorem allocateNames_stateSlotsBounded :
    ∀ (names : List Name) (state : CompileState),
      StateSlotsBounded state →
        StateSlotsBounded (allocateNames names state).2
  | [], state, hBound => by
      simpa [allocateNames] using hBound
  | name :: rest, state, hBound => by
      cases hAlloc : allocateName name state with
      | mk slot stateAfterHead =>
          have hHeadBound :
              StateSlotsBounded stateAfterHead := by
            simpa [hAlloc] using
              allocateName_stateSlotsBounded name state hBound
          simpa [allocateNames, hAlloc] using
            allocateNames_stateSlotsBounded rest stateAfterHead hHeadBound

theorem allocateNames_entries_length :
    ∀ (names : List Name) (state : CompileState),
      (allocateNames names state).1.length = names.length
  | [], state => by
      simp [allocateNames]
  | name :: rest, state => by
      let state1 : CompileState :=
        { env := (name, state.nextSlot) :: state.env,
          nextSlot := state.nextSlot + 1 }
      have hTail := allocateNames_entries_length rest state1
      simpa [allocateNames, allocateName, state1] using hTail

theorem allocateNames_entries_names :
    ∀ (names : List Name) (state : CompileState),
      (allocateNames names state).1.map Prod.fst = names
  | [], state => by
      simp [allocateNames]
  | name :: rest, state => by
      let state1 : CompileState :=
        { env := (name, state.nextSlot) :: state.env,
          nextSlot := state.nextSlot + 1 }
      have hTail := allocateNames_entries_names rest state1
      simpa [allocateNames, allocateName, state1] using hTail

theorem allocateNames_slots_ge_start :
    ∀ {names : List Name} {state : CompileState}
      {entry : Name × Nat},
      entry ∈ (allocateNames names state).1 →
        state.nextSlot ≤ entry.2
  | [], state, entry, hMem => by
      simp [allocateNames] at hMem
  | name :: rest, state, entry, hMem => by
      let state1 : CompileState :=
        { env := (name, state.nextSlot) :: state.env,
          nextSlot := state.nextSlot + 1 }
      simp [allocateNames, allocateName, state1] at hMem
      rcases hMem with hHead | hTail
      · cases hHead
        omega
      · have hGe :=
          allocateNames_slots_ge_start
            (names := rest) (state := state1) hTail
        have hState1Next : state1.nextSlot = state.nextSlot + 1 := rfl
        omega

theorem allocateNames_slots_lt_final :
    ∀ {names : List Name} {state : CompileState}
      {entry : Name × Nat},
      entry ∈ (allocateNames names state).1 →
        entry.2 < (allocateNames names state).2.nextSlot
  | [], state, entry, hMem => by
      simp [allocateNames] at hMem
  | name :: rest, state, entry, hMem => by
      let state1 : CompileState :=
        { env := (name, state.nextSlot) :: state.env,
          nextSlot := state.nextSlot + 1 }
      simp [allocateNames, allocateName, state1] at hMem
      rcases hMem with hHead | hTail
      · cases hHead
        have hNext := allocateNames_nextSlot rest state1
        simp [state1] at hNext
        simp [allocateNames, allocateName]
        omega
      · have hTailLt :=
          allocateNames_slots_lt_final
            (names := rest) (state := state1) hTail
        simpa [allocateNames, allocateName, state1] using hTailLt

theorem allocateNames_slotList_nodup :
    ∀ (names : List Name) (state : CompileState),
      (slotList (allocateNames names state).1).Nodup
  | [], state => by
      simp [allocateNames, slotList]
  | name :: rest, state => by
      let state1 : CompileState :=
        { env := (name, state.nextSlot) :: state.env,
          nextSlot := state.nextSlot + 1 }
      have hTail := allocateNames_slotList_nodup rest state1
      simp [allocateNames, allocateName, state1, slotList]
      constructor
      · intro other hEntry
        have hGe :=
          allocateNames_slots_ge_start
            (names := rest) (state := state1)
            (entry := (other, state.nextSlot)) hEntry
        have hState1Next : state1.nextSlot = state.nextSlot + 1 := rfl
        omega
      · exact hTail

theorem allocateFunctionSignatures_names :
    ∀ (fns : List FunDef) (state : CompileState),
      (allocateFunctionSignatures fns state).1.map FunSlots.name =
        fns.map FunDef.name
  | [], state => by
      simp [allocateFunctionSignatures]
  | fn :: rest, state => by
      cases hParams : allocateNames fn.params state with
      | mk params stateAfterParams =>
          cases hReturns : allocateNames fn.returns stateAfterParams with
          | mk returns stateAfterReturns =>
              have hTail :=
                allocateFunctionSignatures_names rest stateAfterReturns
              simp [allocateFunctionSignatures, hParams, hReturns, hTail]

theorem allocateFunctionSignatures_nextSlot_mono :
    ∀ (fns : List FunDef) (state : CompileState),
      state.nextSlot ≤ (allocateFunctionSignatures fns state).2.nextSlot
  | [], state => by
      simp [allocateFunctionSignatures]
  | fn :: rest, state => by
      cases hParams : allocateNames fn.params state with
      | mk params stateAfterParams =>
          cases hReturns : allocateNames fn.returns stateAfterParams with
          | mk returns stateAfterReturns =>
              cases hTail :
                  allocateFunctionSignatures rest stateAfterReturns with
              | mk tailSlots stateAfterTail =>
                  have hParamsLe :
                      state.nextSlot ≤ stateAfterParams.nextSlot := by
                    simpa [hParams] using
                      allocateNames_nextSlot_mono fn.params state
                  have hReturnsLe :
                      stateAfterParams.nextSlot ≤
                        stateAfterReturns.nextSlot := by
                    simpa [hReturns] using
                      allocateNames_nextSlot_mono fn.returns
                        stateAfterParams
                  have hTailLe :
                      stateAfterReturns.nextSlot ≤
                        stateAfterTail.nextSlot := by
                    simpa [hTail] using
                      allocateFunctionSignatures_nextSlot_mono rest
                        stateAfterReturns
                  simp [allocateFunctionSignatures, hParams, hReturns, hTail]
                  exact Nat.le_trans hParamsLe
                    (Nat.le_trans hReturnsLe hTailLe)

theorem allocateFunctionSignatures_stateSlotsBounded :
    ∀ (fns : List FunDef) (state : CompileState),
      StateSlotsBounded state →
        StateSlotsBounded (allocateFunctionSignatures fns state).2
  | [], state, hBound => by
      simpa [allocateFunctionSignatures] using hBound
  | fn :: rest, state, hBound => by
      cases hParams : allocateNames fn.params state with
      | mk params stateAfterParams =>
          have hParamsBound :
              StateSlotsBounded stateAfterParams := by
            simpa [hParams] using
              allocateNames_stateSlotsBounded fn.params state hBound
          cases hReturns : allocateNames fn.returns stateAfterParams with
          | mk returns stateAfterReturns =>
              have hReturnsBound :
                  StateSlotsBounded stateAfterReturns := by
                simpa [hReturns] using
                  allocateNames_stateSlotsBounded fn.returns
                    stateAfterParams hParamsBound
              cases hTail :
                  allocateFunctionSignatures rest stateAfterReturns with
              | mk tailSlots stateAfterTail =>
                  simp [allocateFunctionSignatures, hParams, hReturns, hTail]
                  simpa [hTail] using
                    allocateFunctionSignatures_stateSlotsBounded rest
                      stateAfterReturns hReturnsBound

theorem allocateFunctionSignatures_slots_lt_final :
    ∀ {fns : List FunDef} {state : CompileState}
      {functionSlots : List FunSlots} {finalState : CompileState}
      {slots : FunSlots} {entry : Name × Nat},
      allocateFunctionSignatures fns state =
          (functionSlots, finalState) →
      slots ∈ functionSlots →
      entry ∈ slots.params ++ slots.returns →
        entry.2 < finalState.nextSlot
  | [], state, functionSlots, finalState, slots, entry,
      hAlloc, hSlots, _hEntry => by
      simp [allocateFunctionSignatures] at hAlloc
      rcases hAlloc with ⟨rfl, rfl⟩
      simp at hSlots
  | fn :: rest, state, functionSlots, finalState, slots, entry,
      hAlloc, hSlots, hEntry => by
      cases hParams : allocateNames fn.params state with
      | mk params stateAfterParams =>
          cases hReturns : allocateNames fn.returns stateAfterParams with
          | mk returns stateAfterReturns =>
              cases hTail :
                  allocateFunctionSignatures rest stateAfterReturns with
              | mk tailSlots stateAfterTail =>
                  simp [allocateFunctionSignatures, hParams, hReturns, hTail]
                    at hAlloc
                  rcases hAlloc with ⟨rfl, rfl⟩
                  simp at hSlots
                  rcases hSlots with hHead | hTailMem
                  · cases hHead
                    have hReturnsLe :
                        stateAfterParams.nextSlot ≤
                          stateAfterReturns.nextSlot := by
                      simpa [hReturns] using
                        allocateNames_nextSlot_mono fn.returns
                          stateAfterParams
                    have hTailLe :
                        stateAfterReturns.nextSlot ≤
                          stateAfterTail.nextSlot := by
                      simpa [hTail] using
                        allocateFunctionSignatures_nextSlot_mono rest
                          stateAfterReturns
                    have hAppend := List.mem_append.mp hEntry
                    rcases hAppend with hParamEntry | hReturnEntry
                    · have hParamLt :
                          entry.2 < stateAfterParams.nextSlot := by
                        have hParamEntry' :
                            entry ∈ (allocateNames fn.params state).1 := by
                          simpa [hParams] using hParamEntry
                        simpa [hParams] using
                          allocateNames_slots_lt_final
                            (names := fn.params) (state := state)
                            (entry := entry) hParamEntry'
                      exact Nat.lt_of_lt_of_le hParamLt
                        (Nat.le_trans hReturnsLe hTailLe)
                    · have hReturnLt :
                          entry.2 < stateAfterReturns.nextSlot := by
                        have hReturnEntry' :
                            entry ∈
                              (allocateNames fn.returns stateAfterParams).1 := by
                          simpa [hReturns] using hReturnEntry
                        simpa [hReturns] using
                          allocateNames_slots_lt_final
                            (names := fn.returns)
                            (state := stateAfterParams)
                            (entry := entry) hReturnEntry'
                      exact Nat.lt_of_lt_of_le hReturnLt hTailLe
                  · exact
                      allocateFunctionSignatures_slots_lt_final
                        (fns := rest) (state := stateAfterReturns)
                        (functionSlots := tailSlots)
                        (finalState := stateAfterTail)
                        (slots := slots) (entry := entry)
                        hTail hTailMem hEntry

theorem allocateFunctionSignatures_funSlotListBounded_final
    {fns : List FunDef} {state : CompileState}
    {functionSlots : List FunSlots} {finalState : CompileState}
    (hAlloc :
      allocateFunctionSignatures fns state =
        (functionSlots, finalState)) :
    FunSlotListBounded functionSlots finalState.nextSlot := by
  intro slots hSlots entry hEntry
  have hEntry' : entry ∈ slots.params ++ slots.returns := by
    have hAppend := List.mem_append.mp hEntry
    rcases hAppend with hReturn | hParam
    · exact List.mem_append_right slots.params hReturn
    · exact List.mem_append_left slots.returns hParam
  exact
    allocateFunctionSignatures_slots_lt_final
      (fns := fns) (state := state)
      (functionSlots := functionSlots) (finalState := finalState)
      (slots := slots) (entry := entry) hAlloc hSlots hEntry'

theorem allocateFunctionSignatures_lookup_of_find? :
    ∀ {fns : List FunDef} {state : CompileState}
      {name : Name} {fn : FunDef},
      FunList.find? name fns = some fn →
        ∃ slots,
          lookupFun? name (allocateFunctionSignatures fns state).1 =
            some slots ∧
          slots.name = fn.name ∧
          slots.params.map Prod.fst = fn.params ∧
          slots.returns.map Prod.fst = fn.returns
  | [], state, name, fn, hFind => by
      simp [FunList.find?] at hFind
  | head :: rest, state, name, fn, hFind => by
      cases hParams : allocateNames head.params state with
      | mk params stateAfterParams =>
          cases hReturns : allocateNames head.returns stateAfterParams with
          | mk returns stateAfterReturns =>
              cases hTail :
                  allocateFunctionSignatures rest stateAfterReturns with
              | mk tailSlots stateAfterTail =>
                  by_cases hName : head.name = name
                  · simp [FunList.find?, hName] at hFind
                    cases hFind
                    have hParamsNames :
                        params.map Prod.fst = head.params := by
                      simpa [hParams] using
                        allocateNames_entries_names head.params state
                    have hReturnsNames :
                        returns.map Prod.fst = head.returns := by
                      simpa [hReturns] using
                        allocateNames_entries_names head.returns
                          stateAfterParams
                    refine
                      ⟨{ name := head.name, params := params,
                          returns := returns }, ?_, rfl,
                        hParamsNames, hReturnsNames⟩
                    simp [allocateFunctionSignatures, lookupFun?, hParams,
                      hReturns, hTail, hName]
                  · have hTailFind :
                        FunList.find? name rest = some fn := by
                      simpa [FunList.find?, hName] using hFind
                    rcases
                        allocateFunctionSignatures_lookup_of_find?
                          (state := stateAfterReturns) hTailFind with
                      ⟨slots, hLookup, hSlotName, hParamsNames,
                        hReturnsNames⟩
                    refine
                      ⟨slots, ?_, hSlotName, hParamsNames, hReturnsNames⟩
                    simp [allocateFunctionSignatures, lookupFun?, hParams,
                      hReturns, hTail, hName]
                    simpa [hTail] using hLookup

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

set_option linter.unusedSimpArgs false in
mutual
  theorem compileBlockOpen?_nextSlot_mono
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {block : Block} {plan : Plan}
      (hCompile :
        compileBlockOpen? ctx returns state block = some plan) :
      state.nextSlot ≤ plan.state.nextSlot := by
    cases block with
    | mk stmts =>
        exact compileStmtList?_nextSlot_mono
          (by simpa [compileBlockOpen?] using hCompile)

  theorem compileBlockScoped?_nextSlot_mono
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {block : Block} {plan : Plan}
      (hCompile :
        compileBlockScoped? ctx returns state block = some plan) :
      state.nextSlot ≤ plan.state.nextSlot := by
    unfold compileBlockScoped? at hCompile
    cases hOpen : compileBlockOpen? ctx returns state block with
    | none =>
        simp [hOpen] at hCompile
    | some openPlan =>
        simp [hOpen] at hCompile
        cases hCompile
        exact (compileBlockOpen?_nextSlot_mono (plan := openPlan) hOpen)

  theorem compileStmtList?_nextSlot_mono
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {stmts : List Stmt} {plan : Plan},
        compileStmtList? ctx returns state stmts = some plan →
          state.nextSlot ≤ plan.state.nextSlot
  | [], plan, hCompile => by
      simp [compileStmtList?] at hCompile
      cases hCompile
      rfl
  | stmt :: rest, plan, hCompile => by
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
              exact Nat.le_trans
                (compileStmt?_nextSlot_mono (plan := head) hHead)
                (compileStmtList?_nextSlot_mono
                  (stmts := rest) (plan := tail) hTail)

  theorem compileCases?_nextSlot_mono
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {cases : List (Word × Block)}
        {compiled : List (Word × Expressions.Block)}
        {state' : CompileState},
        compileCases? ctx returns state cases = some (compiled, state') →
          state.nextSlot ≤ state'.nextSlot
  | [], compiled, state', hCompile => by
      simp [compileCases?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      rfl
  | (value, body) :: rest, compiled, state', hCompile => by
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
              exact Nat.le_trans
                (compileBlockScoped?_nextSlot_mono (plan := bodyPlan) hBody)
                (compileCases?_nextSlot_mono
                  (cases := rest) (compiled := tailCases)
                  (state' := tailState) hTail)

  theorem compileDefault?_nextSlot_mono
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {defaultBody : Option Block}
        {compiled : Option Expressions.Block} {state' : CompileState},
        compileDefault? ctx returns state defaultBody =
            some (compiled, state') →
          state.nextSlot ≤ state'.nextSlot
  | none, compiled, state', hCompile => by
      simp [compileDefault?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      rfl
  | some body, compiled, state', hCompile => by
      unfold compileDefault? at hCompile
      cases hPlan : compileBlockScoped? ctx returns state body with
      | none =>
          simp [hPlan] at hCompile
      | some plan =>
          simp [hPlan] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact (compileBlockScoped?_nextSlot_mono (plan := plan) hPlan)

  theorem compileStmt?_nextSlot_mono
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {stmt : Stmt} {plan : Plan}
      (hCompile :
        compileStmt? ctx returns state stmt = some plan) :
      state.nextSlot ≤ plan.state.nextSlot := by
    cases stmt with
    | expr expr =>
        simp [compileStmt?] at hCompile
        cases hCode : compileExprCode? state.env 0 expr with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            rfl
    | let_ name value =>
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
                    have hNext :
                        state'.nextSlot = state.nextSlot + 1 := by
                      simpa [hAlloc] using
                        allocateName_nextSlot name state
                    simp [hNext]
    | assign name value =>
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
                    rfl
    | block body =>
        exact
          compileBlockScoped?_nextSlot_mono
            (plan := plan)
            (by simpa [compileStmt?] using hCompile)
    | if_ cond body =>
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
                exact (compileBlockScoped?_nextSlot_mono
                  (plan := bodyPlan) hBody)
    | switch scrutinee cases defaultBody =>
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
                    exact Nat.le_trans
                      (compileCases?_nextSlot_mono
                        (cases := cases) (compiled := compiledCases)
                        (state' := stateAfterCases) hCases)
                      (compileDefault?_nextSlot_mono
                        (defaultBody := defaultBody)
                        (compiled := compiledDefault)
                        (state' := stateAfterDefault) hDefault)
    | for_ init cond post body =>
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
                        exact Nat.le_trans
                          (compileBlockOpen?_nextSlot_mono
                            (plan := initPlan) hInit)
                          (Nat.le_trans
                            (compileBlockScoped?_nextSlot_mono
                              (plan := postPlan) hPost)
                            (compileBlockScoped?_nextSlot_mono
                              (plan := bodyPlan) hBody))
    | brk =>
        simp [compileStmt?] at hCompile
        cases hCompile
        rfl
    | cont =>
        simp [compileStmt?] at hCompile
        cases hCompile
        rfl
    | leave =>
        simp [compileStmt?] at hCompile
        cases hCode : compileReturnCode? state.env returns with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            rfl
    | call targets functionName args =>
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
                                      rfl
                · simp [hFn, hArgsLen, hTargetsLen, hTargetsNodup]
                    at hCompile
              · simp [hFn, hArgsLen, hTargetsLen] at hCompile
            · simp [hFn, hArgsLen] at hCompile
    | terminal kind =>
        simp [compileStmt?] at hCompile
        cases hCompile
        rfl
    | terminalArgs kind args =>
        simp [compileStmt?] at hCompile
        cases hCode : compileExprSeqCode? state.env 0 args with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            rfl
end

set_option linter.unusedSimpArgs false in
mutual
  theorem compileBlockOpen?_stateSlotsBounded
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {block : Block} {plan : Plan}
      (hBound : StateSlotsBounded state)
      (hCompile :
        compileBlockOpen? ctx returns state block = some plan) :
      StateSlotsBounded plan.state := by
    cases block with
    | mk stmts =>
        exact compileStmtList?_stateSlotsBounded hBound
          (by simpa [compileBlockOpen?] using hCompile)

  theorem compileBlockScoped?_stateSlotsBounded
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {block : Block} {plan : Plan}
      (hBound : StateSlotsBounded state)
      (hCompile :
        compileBlockScoped? ctx returns state block = some plan) :
      StateSlotsBounded plan.state := by
    unfold compileBlockScoped? at hCompile
    cases hOpen : compileBlockOpen? ctx returns state block with
    | none =>
        simp [hOpen] at hCompile
    | some openPlan =>
        simp [hOpen] at hCompile
        cases hCompile
        intro entry hMem
        exact Nat.lt_of_lt_of_le
          (hBound entry hMem)
          (compileBlockOpen?_nextSlot_mono (plan := openPlan) hOpen)

  theorem compileStmtList?_stateSlotsBounded
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {stmts : List Stmt} {plan : Plan},
        StateSlotsBounded state →
        compileStmtList? ctx returns state stmts = some plan →
          StateSlotsBounded plan.state
  | [], plan, hBound, hCompile => by
      simp [compileStmtList?] at hCompile
      cases hCompile
      exact hBound
  | stmt :: rest, plan, hBound, hCompile => by
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
                compileStmtList?_stateSlotsBounded
                  (stmts := rest) (plan := tail)
                  (compileStmt?_stateSlotsBounded
                    (plan := head) hBound hHead)
                  hTail

  theorem compileCases?_stateSlotsBounded
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {cases : List (Word × Block)}
        {compiled : List (Word × Expressions.Block)}
        {state' : CompileState},
        StateSlotsBounded state →
        compileCases? ctx returns state cases = some (compiled, state') →
          StateSlotsBounded state'
  | [], compiled, state', hBound, hCompile => by
      simp [compileCases?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact hBound
  | (value, body) :: rest, compiled, state', hBound, hCompile => by
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
              exact
                compileCases?_stateSlotsBounded
                  (cases := rest) (compiled := tailCases)
                  (state' := tailState)
                  (compileBlockScoped?_stateSlotsBounded
                    (plan := bodyPlan) hBound hBody)
                  hTail

  theorem compileDefault?_stateSlotsBounded
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} :
      ∀ {defaultBody : Option Block}
        {compiled : Option Expressions.Block} {state' : CompileState},
        StateSlotsBounded state →
        compileDefault? ctx returns state defaultBody =
            some (compiled, state') →
          StateSlotsBounded state'
  | none, compiled, state', hBound, hCompile => by
      simp [compileDefault?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact hBound
  | some body, compiled, state', hBound, hCompile => by
      unfold compileDefault? at hCompile
      cases hPlan : compileBlockScoped? ctx returns state body with
      | none =>
          simp [hPlan] at hCompile
      | some plan =>
          simp [hPlan] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact compileBlockScoped?_stateSlotsBounded
            (plan := plan) hBound hPlan

  theorem compileStmt?_stateSlotsBounded
      {ctx : CompileCtx} {returns : List Name}
      {state : CompileState} {stmt : Stmt} {plan : Plan}
      (hBound : StateSlotsBounded state)
      (hCompile :
        compileStmt? ctx returns state stmt = some plan) :
      StateSlotsBounded plan.state := by
    cases stmt with
    | expr expr =>
        simp [compileStmt?] at hCompile
        cases hCode : compileExprCode? state.env 0 expr with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            exact hBound
    | let_ name value =>
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
                    simpa [hAlloc] using
                      allocateName_stateSlotsBounded name state hBound
    | assign name value =>
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
                    exact hBound
    | block body =>
        exact
          compileBlockScoped?_stateSlotsBounded
            (plan := plan) hBound
            (by simpa [compileStmt?] using hCompile)
    | if_ cond body =>
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
                exact compileBlockScoped?_stateSlotsBounded
                  (plan := bodyPlan) hBound hBody
    | switch scrutinee cases defaultBody =>
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
                    exact compileDefault?_stateSlotsBounded
                      (defaultBody := defaultBody)
                      (compiled := compiledDefault)
                      (state' := stateAfterDefault)
                      (compileCases?_stateSlotsBounded
                        (cases := cases) (compiled := compiledCases)
                        (state' := stateAfterCases) hBound hCases)
                      hDefault
    | for_ init cond post body =>
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
                        intro entry hMem
                        have hLe :
                            state.nextSlot ≤ bodyPlan.state.nextSlot :=
                          Nat.le_trans
                            (compileBlockOpen?_nextSlot_mono
                              (plan := initPlan) hInit)
                            (Nat.le_trans
                              (compileBlockScoped?_nextSlot_mono
                                (plan := postPlan) hPost)
                              (compileBlockScoped?_nextSlot_mono
                                (plan := bodyPlan) hBody))
                        exact Nat.lt_of_lt_of_le (hBound entry hMem) hLe
    | brk =>
        simp [compileStmt?] at hCompile
        cases hCompile
        exact hBound
    | cont =>
        simp [compileStmt?] at hCompile
        cases hCompile
        exact hBound
    | leave =>
        simp [compileStmt?] at hCompile
        cases hCode : compileReturnCode? state.env returns with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            exact hBound
    | call targets functionName args =>
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
                                      exact hBound
                · simp [hFn, hArgsLen, hTargetsLen, hTargetsNodup]
                    at hCompile
              · simp [hFn, hArgsLen, hTargetsLen] at hCompile
            · simp [hFn, hArgsLen] at hCompile
    | terminal kind =>
        simp [compileStmt?] at hCompile
        cases hCompile
        exact hBound
    | terminalArgs kind args =>
        simp [compileStmt?] at hCompile
        cases hCode : compileExprSeqCode? state.env 0 args with
        | none =>
            simp [hCode] at hCompile
        | some code =>
            simp [hCode] at hCompile
            cases hCompile
            exact hBound
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

theorem compileFunction?_nextSlot_mono {ctx : CompileCtx}
    {state : CompileState} {fn : FunDef}
    {proc : Expressions.Proc} {state' : CompileState}
    (hCompile : compileFunction? ctx state fn = some (proc, state')) :
    state.nextSlot ≤ state'.nextSlot := by
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
                  exact
                    compileBlockOpen?_nextSlot_mono
                      (state := bodyStart) (plan := bodyPlan) hBodyPlan
    · simp [hRetBound] at hCompile
  · simp [hSigNodup] at hCompile

theorem compileFunction?_stateSlotsBounded {ctx : CompileCtx}
    {state : CompileState} {fn : FunDef}
    {proc : Expressions.Proc} {state' : CompileState}
    (hStateBound : StateSlotsBounded state)
    (hFunctionBound :
      FunSlotListBounded ctx.functions state.nextSlot)
    (hCompile : compileFunction? ctx state fn = some (proc, state')) :
    StateSlotsBounded state' := by
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
          have hBodyStartBound : StateSlotsBounded bodyStart := by
            simpa [bodyStart, StateSlotsBounded] using
              lookupFun?_bounded hFunctionBound hSlots
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
                  intro entry hMem
                  exact Nat.lt_of_lt_of_le
                    (hStateBound entry hMem)
                    (compileBlockOpen?_nextSlot_mono
                      (state := bodyStart) (plan := bodyPlan) hBodyPlan)
    · simp [hRetBound] at hCompile
  · simp [hSigNodup] at hCompile

theorem compileFunction?_bodyPlan_stateSlotsBounded {ctx : CompileCtx}
    {state : CompileState} {fn : FunDef}
    {proc : Expressions.Proc} {state' : CompileState}
    (hFunctionBound :
      FunSlotListBounded ctx.functions state.nextSlot)
    (hCompile : compileFunction? ctx state fn = some (proc, state')) :
    ∃ slots bodyPlan retCode,
      lookupFun? fn.name ctx.functions = some slots ∧
        compileBlockOpen? ctx fn.returns
          { env := functionEnv slots, nextSlot := state.nextSlot }
          fn.body = some bodyPlan ∧
        compileReturnCode? bodyPlan.state.env fn.returns = some retCode ∧
        StateSlotsBounded bodyPlan.state := by
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
          have hBodyStartBound : StateSlotsBounded bodyStart := by
            simpa [bodyStart, StateSlotsBounded] using
              lookupFun?_bounded hFunctionBound hSlots
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
                  refine ⟨slots, bodyPlan, retCode, rfl, ?_, hRetCode, ?_⟩
                  · simpa [bodyStart] using hBodyPlan
                  · exact
                      compileBlockOpen?_stateSlotsBounded
                        (state := bodyStart) (plan := bodyPlan)
                        hBodyStartBound hBodyPlan
    · simp [hRetBound] at hCompile
  · simp [hSigNodup] at hCompile

theorem compileFunctions?_nextSlot_mono {ctx : CompileCtx} :
    ∀ {state : CompileState} {fns : List FunDef}
      {procs : List Expressions.Proc} {state' : CompileState},
      compileFunctions? ctx state fns = some (procs, state') →
        state.nextSlot ≤ state'.nextSlot
  | state, [], procs, state', hCompile => by
      simp [compileFunctions?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      rfl
  | state, fn :: rest, procs, state', hCompile => by
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
              exact Nat.le_trans
                (compileFunction?_nextSlot_mono hHead)
                (compileFunctions?_nextSlot_mono hTail)

theorem compileFunctions?_stateSlotsBounded {ctx : CompileCtx} :
    ∀ {state : CompileState} {fns : List FunDef}
      {procs : List Expressions.Proc} {state' : CompileState},
      StateSlotsBounded state →
      FunSlotListBounded ctx.functions state.nextSlot →
      compileFunctions? ctx state fns = some (procs, state') →
        StateSlotsBounded state'
  | state, [], procs, state', hStateBound, _hFunctionBound,
      hCompile => by
      simp [compileFunctions?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact hStateBound
  | state, fn :: rest, procs, state', hStateBound, hFunctionBound,
      hCompile => by
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
              have hHeadBound :
                  StateSlotsBounded stateAfterHead :=
                compileFunction?_stateSlotsBounded
                  hStateBound hFunctionBound hHead
              have hFunctionBoundTail :
                  FunSlotListBounded ctx.functions
                    stateAfterHead.nextSlot :=
                funSlotListBounded_mono hFunctionBound
                  (compileFunction?_nextSlot_mono hHead)
              exact
                compileFunctions?_stateSlotsBounded
                  (fns := rest) (procs := tailProcs)
                  (state' := tailState)
                  hHeadBound hFunctionBoundTail hTail

theorem compileMain?_nextSlot_mono {ctx : CompileCtx}
    {frameWords : Nat} {state : CompileState} {body : Block}
    {plan : Plan}
    (hCompile : compileMain? ctx frameWords state body = some plan) :
    state.nextSlot ≤ plan.state.nextSlot := by
  unfold compileMain? at hCompile
  cases body with
  | mk stmts =>
      simp at hCompile
      cases hList :
          compileStmtList? ctx [] state (splitPrelude stmts).2 with
      | none =>
          simp [hList] at hCompile
      | some listPlan =>
          simp [hList] at hCompile
          cases hCompile
          exact
            compileStmtList?_nextSlot_mono
              (stmts := (splitPrelude stmts).2)
              (plan := listPlan) hList

theorem compileMain?_stateSlotsBounded {ctx : CompileCtx}
    {frameWords : Nat} {state : CompileState} {body : Block}
    {plan : Plan}
    (hStateBound : StateSlotsBounded state)
    (hCompile : compileMain? ctx frameWords state body = some plan) :
    StateSlotsBounded plan.state := by
  unfold compileMain? at hCompile
  cases body with
  | mk stmts =>
      simp at hCompile
      cases hList :
          compileStmtList? ctx [] state (splitPrelude stmts).2 with
      | none =>
          simp [hList] at hCompile
      | some listPlan =>
          simp [hList] at hCompile
          cases hCompile
          exact
            compileStmtList?_stateSlotsBounded
              (stmts := (splitPrelude stmts).2)
              (plan := listPlan) hStateBound hList

theorem compileExpressionsProgram?_signatures_nextSlot_le_maxFrameWords
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program}
    {functionSlots : List FunSlots}
    {stateAfterSignatures : CompileState}
    (hSignatures :
      allocateFunctionSignatures program.functions
        ({ env := [], nextSlot := 0 } : CompileState) =
          (functionSlots, stateAfterSignatures))
    (hCompile :
      compileExpressionsProgram? maxFrameWords program = some exprProgram) :
    stateAfterSignatures.nextSlot ≤ maxFrameWords := by
  unfold compileExpressionsProgram? at hCompile
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · simp [hNames, hSignatures] at hCompile
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
            simp [ctx0, mainStart, hProbeFunctions, hMainProbe] at hCompile
        | some mainProbe =>
            by_cases hBound : mainProbe.state.nextSlot ≤ maxFrameWords
            · have hFunctionsLe :
                  stateAfterSignatures.nextSlot ≤
                    stateAfterFunctions.nextSlot :=
                compileFunctions?_nextSlot_mono
                  (ctx := ctx0) (state := stateAfterSignatures)
                  (fns := program.functions) hProbeFunctions
              have hMainLe :
                  stateAfterFunctions.nextSlot ≤
                    mainProbe.state.nextSlot := by
                simpa [mainStart] using
                  compileMain?_nextSlot_mono
                    (ctx := ctx0) (frameWords := 0)
                    (state := mainStart) (body := program.body)
                    (plan := mainProbe) hMainProbe
              exact Nat.le_trans hFunctionsLe
                (Nat.le_trans hMainLe hBound)
            · simp [ctx0, mainStart, hProbeFunctions, hMainProbe,
                hBound] at hCompile
  · simp [hNames] at hCompile

theorem compileExpressionsProgram?_signature_slot_lt_maxFrameWords
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program}
    {functionSlots : List FunSlots}
    {stateAfterSignatures : CompileState}
    {functionName : Name} {slots : FunSlots} {entry : Name × Nat}
    (hSignatures :
      allocateFunctionSignatures program.functions
        ({ env := [], nextSlot := 0 } : CompileState) =
          (functionSlots, stateAfterSignatures))
    (hCompile :
      compileExpressionsProgram? maxFrameWords program = some exprProgram)
    (hLookup : lookupFun? functionName functionSlots = some slots)
    (hEntry : entry ∈ slots.params ++ slots.returns) :
    entry.2 < maxFrameWords := by
  have hSlotLt :
      entry.2 < stateAfterSignatures.nextSlot :=
    allocateFunctionSignatures_slots_lt_final
      (fns := program.functions)
      (state := ({ env := [], nextSlot := 0 } : CompileState))
      (functionSlots := functionSlots)
      (finalState := stateAfterSignatures)
      (slots := slots) (entry := entry)
      hSignatures (lookupFun?_some_mem hLookup) hEntry
  have hFrameLe :
      stateAfterSignatures.nextSlot ≤ maxFrameWords :=
    compileExpressionsProgram?_signatures_nextSlot_le_maxFrameWords
      hSignatures hCompile
  exact Nat.lt_of_lt_of_le hSlotLt hFrameLe

theorem compileExpressionsProgram?_functionSlotListBounded
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program}
    {functionSlots : List FunSlots}
    {stateAfterSignatures : CompileState}
    (hSignatures :
      allocateFunctionSignatures program.functions
        ({ env := [], nextSlot := 0 } : CompileState) =
          (functionSlots, stateAfterSignatures))
    (hCompile :
      compileExpressionsProgram? maxFrameWords program = some exprProgram) :
    FunSlotListBounded functionSlots maxFrameWords :=
  funSlotListBounded_mono
    (allocateFunctionSignatures_funSlotListBounded_final hSignatures)
    (compileExpressionsProgram?_signatures_nextSlot_le_maxFrameWords
      hSignatures hCompile)

theorem compileExpressionsProgram?_bounded_passes
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program}
    (hCompile :
      compileExpressionsProgram? maxFrameWords program = some exprProgram) :
    ∃ functionSlots stateAfterSignatures probeProcs
        stateAfterFunctions mainProbe procs stateAfterFunctionsFinal main,
      allocateFunctionSignatures program.functions
        ({ env := [], nextSlot := 0 } : CompileState) =
          (functionSlots, stateAfterSignatures) ∧
      FunSlotListBounded functionSlots maxFrameWords ∧
      StateSlotsBounded stateAfterSignatures ∧
      compileFunctions?
          { functions := functionSlots, frameWords := 0 }
          stateAfterSignatures program.functions =
            some (probeProcs, stateAfterFunctions) ∧
      StateSlotsBounded stateAfterFunctions ∧
      compileMain?
          { functions := functionSlots, frameWords := 0 }
          0 { env := [], nextSlot := stateAfterFunctions.nextSlot }
          program.body = some mainProbe ∧
      StateSlotsBounded mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      compileFunctions?
          { functions := functionSlots,
            frameWords := mainProbe.state.nextSlot }
          stateAfterSignatures program.functions =
            some (procs, stateAfterFunctionsFinal) ∧
      StateSlotsBounded stateAfterFunctionsFinal ∧
      compileMain?
          { functions := functionSlots,
            frameWords := mainProbe.state.nextSlot }
          mainProbe.state.nextSlot
          { env := [], nextSlot := stateAfterFunctions.nextSlot }
          program.body = some main ∧
      StateSlotsBounded main.state ∧
      exprProgram = { procs := procs, body := main.block } := by
  unfold compileExpressionsProgram? at hCompile
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · simp [hNames] at hCompile
    let initial : CompileState := { env := [], nextSlot := 0 }
    have hInitialBound : StateSlotsBounded initial := by
      intro entry hMem
      simp [initial] at hMem
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        simp [initial, hSignatures] at hCompile
        have hSignatures' :
            allocateFunctionSignatures program.functions
              ({ env := [], nextSlot := 0 } : CompileState) =
                (functionSlots, stateAfterSignatures) := by
          simpa [initial] using hSignatures
        have hSignatureStateBound :
            StateSlotsBounded stateAfterSignatures := by
          simpa [hSignatures] using
            allocateFunctionSignatures_stateSlotsBounded
              program.functions initial hInitialBound
        have hFunctionBoundSig :
            FunSlotListBounded functionSlots
              stateAfterSignatures.nextSlot := by
          exact
            allocateFunctionSignatures_funSlotListBounded_final
              hSignatures'
        let ctx0 : CompileCtx := { functions := functionSlots, frameWords := 0 }
        cases hProbeFunctions :
            compileFunctions? ctx0 stateAfterSignatures
              program.functions with
        | none =>
            simp [ctx0, hProbeFunctions] at hCompile
        | some probeResult =>
            rcases probeResult with ⟨probeProcs, stateAfterFunctions⟩
            have hProbeFunctionsBound :
                StateSlotsBounded stateAfterFunctions :=
              compileFunctions?_stateSlotsBounded
                (ctx := ctx0) (state := stateAfterSignatures)
                (fns := program.functions)
                hSignatureStateBound hFunctionBoundSig hProbeFunctions
            let mainStart : CompileState :=
              { env := [], nextSlot := stateAfterFunctions.nextSlot }
            have hMainStartBound : StateSlotsBounded mainStart := by
              intro entry hMem
              simp [mainStart] at hMem
            cases hMainProbe :
                compileMain? ctx0 0 mainStart program.body with
            | none =>
                simp [ctx0, mainStart, hProbeFunctions, hMainProbe]
                  at hCompile
            | some mainProbe =>
                have hMainProbeBound : StateSlotsBounded mainProbe.state :=
                  compileMain?_stateSlotsBounded
                    (ctx := ctx0) (frameWords := 0)
                    (state := mainStart) (body := program.body)
                    (plan := mainProbe) hMainStartBound hMainProbe
                by_cases hBound :
                    mainProbe.state.nextSlot ≤ maxFrameWords
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
                      rcases finalResult with
                        ⟨procs, stateAfterFunctionsFinal⟩
                      have hFinalFunctions' :
                          compileFunctions?
                              { functions := functionSlots,
                                frameWords := mainProbe.state.nextSlot }
                              stateAfterSignatures program.functions =
                            some (procs, stateAfterFunctionsFinal) := by
                        simpa [frameWords, ctxFinal] using hFinalFunctions
                      have hFinalFunctionsBound :
                          StateSlotsBounded stateAfterFunctionsFinal :=
                        compileFunctions?_stateSlotsBounded
                          (ctx := ctxFinal) (state := stateAfterSignatures)
                          (fns := program.functions)
                          hSignatureStateBound hFunctionBoundSig
                          hFinalFunctions
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
                          have hMainBound : StateSlotsBounded main.state :=
                            compileMain?_stateSlotsBounded
                              (ctx := ctxFinal) (frameWords := frameWords)
                              (state := mainStart) (body := program.body)
                              (plan := main) hMainStartBound hMain
                          simp [hFinalFunctions', hMain'] at hCompile
                          cases hCompile
                          have hFunctionsLe :
                              stateAfterSignatures.nextSlot ≤
                                stateAfterFunctions.nextSlot :=
                            compileFunctions?_nextSlot_mono
                              (ctx := ctx0)
                              (state := stateAfterSignatures)
                              (fns := program.functions)
                              hProbeFunctions
                          have hMainLe :
                              stateAfterFunctions.nextSlot ≤
                                mainProbe.state.nextSlot := by
                            simpa [mainStart] using
                              compileMain?_nextSlot_mono
                                (ctx := ctx0) (frameWords := 0)
                                (state := mainStart)
                                (body := program.body)
                                (plan := mainProbe) hMainProbe
                          have hSignaturesLeMax :
                              stateAfterSignatures.nextSlot ≤
                                maxFrameWords :=
                            Nat.le_trans hFunctionsLe
                              (Nat.le_trans hMainLe hBound)
                          refine
                            ⟨functionSlots, stateAfterSignatures,
                              probeProcs, stateAfterFunctions, mainProbe,
                              procs, stateAfterFunctionsFinal, main,
                              rfl, ?_, hSignatureStateBound,
                              ?_, hProbeFunctionsBound, ?_,
                              hMainProbeBound, hBound, hFinalFunctions',
                              hFinalFunctionsBound, hMain', hMainBound,
                              rfl⟩
                          · exact
                              funSlotListBounded_mono
                                hFunctionBoundSig hSignaturesLeMax
                          · simpa [ctx0] using hProbeFunctions
                          · simpa [ctx0, mainStart] using hMainProbe
                · simp [ctx0, mainStart, hProbeFunctions, hMainProbe,
                    hBound] at hCompile
  · simp [hNames] at hCompile

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

theorem compileFunction?_eq_some_header {ctx : CompileCtx}
    {state : CompileState} {fn : FunDef}
    {proc : Expressions.Proc} {state' : CompileState}
    (hCompile : compileFunction? ctx state fn = some (proc, state')) :
    proc.name = fn.name ∧ proc.argc = 1 ∧
      proc.retc = fn.returns.length := by
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
                  simp
    · simp [hRetBound] at hCompile
  · simp [hSigNodup] at hCompile

theorem compileFunctions?_eq_some_headers {ctx : CompileCtx} :
    ∀ {state : CompileState} {fns : List FunDef}
      {procs : List Expressions.Proc} {state' : CompileState},
      compileFunctions? ctx state fns = some (procs, state') →
        procs.map (fun proc => proc.name) =
            fns.map (fun fn => fn.name) ∧
          procs.map (fun proc => proc.argc) =
            fns.map (fun _fn => 1) ∧
          procs.map (fun proc => proc.retc) =
            fns.map (fun fn => fn.returns.length)
  | state, [], procs, state', hCompile => by
      simp [compileFunctions?] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      simp
  | state, fn :: rest, procs, state', hCompile => by
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
              rcases compileFunction?_eq_some_header hHead with
                ⟨hName, hArgc, hRetc⟩
              rcases compileFunctions?_eq_some_headers hTail with
                ⟨hNames, hArgcs, hRetcs⟩
              simp [hName, hArgc, hRetc, hNames, hArgcs, hRetcs]

theorem compileFunctions?_lookup_of_find? {ctx : CompileCtx} :
    ∀ {state : CompileState} {fns : List FunDef}
      {procs : List Expressions.Proc} {state' : CompileState}
      {name : Name} {fn : FunDef},
      compileFunctions? ctx state fns = some (procs, state') →
      FunList.find? name fns = some fn →
        ∃ proc,
          Expressions.ProcList.lookup? name procs = some proc ∧
            proc.name = fn.name ∧ proc.argc = 1 ∧
              proc.retc = fn.returns.length
  | state, [], procs, state', name, fn, hCompile, hFind => by
      simp [FunList.find?] at hFind
  | state, head :: rest, procs, state', name, fn, hCompile, hFind => by
      unfold compileFunctions? at hCompile
      cases hHeadCompile : compileFunction? ctx state head with
      | none =>
          simp [hHeadCompile] at hCompile
      | some headResult =>
          rcases headResult with ⟨headProc, stateAfterHead⟩
          cases hTailCompile :
              compileFunctions? ctx stateAfterHead rest with
          | none =>
              simp [hHeadCompile, hTailCompile] at hCompile
          | some tailResult =>
              rcases tailResult with ⟨tailProcs, tailState⟩
              simp [hHeadCompile, hTailCompile] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              rcases compileFunction?_eq_some_header hHeadCompile with
                ⟨hHeadName, hHeadArgc, hHeadRetc⟩
              by_cases hName : head.name = name
              · simp [FunList.find?, hName] at hFind
                cases hFind
                have hLookupName : headProc.name = name := by
                  simpa [hName] using hHeadName
                exact
                  ⟨headProc,
                    by simp [Expressions.ProcList.lookup?, hLookupName],
                    hHeadName, hHeadArgc, hHeadRetc⟩
              · have hTailFind : FunList.find? name rest = some fn := by
                  simpa [FunList.find?, hName] using hFind
                rcases compileFunctions?_lookup_of_find?
                    hTailCompile hTailFind with
                  ⟨proc, hLookup, hProcName, hArgc, hRetc⟩
                have hHeadProcNameNe : headProc.name ≠ name := by
                  intro hEq
                  exact hName (by simpa [hHeadName] using hEq)
                exact
                  ⟨proc,
                    by
                      simp [Expressions.ProcList.lookup?,
                        hHeadProcNameNe, hLookup],
                    hProcName, hArgc, hRetc⟩

theorem compileFunctions?_lookup_of_find?_with_compile
    {ctx : CompileCtx} :
    ∀ {state : CompileState} {fns : List FunDef}
      {procs : List Expressions.Proc} {state' : CompileState}
      {name : Name} {fn : FunDef},
      compileFunctions? ctx state fns = some (procs, state') →
      FunList.find? name fns = some fn →
        ∃ proc fnState fnState',
          Expressions.ProcList.lookup? name procs = some proc ∧
            compileFunction? ctx fnState fn = some (proc, fnState') ∧
            proc.name = fn.name ∧ proc.argc = 1 ∧
              proc.retc = fn.returns.length
  | state, [], procs, state', name, fn, hCompile, hFind => by
      simp [FunList.find?] at hFind
  | state, head :: rest, procs, state', name, fn, hCompile, hFind => by
      unfold compileFunctions? at hCompile
      cases hHeadCompile : compileFunction? ctx state head with
      | none =>
          simp [hHeadCompile] at hCompile
      | some headResult =>
          rcases headResult with ⟨headProc, stateAfterHead⟩
          cases hTailCompile :
              compileFunctions? ctx stateAfterHead rest with
          | none =>
              simp [hHeadCompile, hTailCompile] at hCompile
          | some tailResult =>
              rcases tailResult with ⟨tailProcs, tailState⟩
              simp [hHeadCompile, hTailCompile] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              rcases compileFunction?_eq_some_header hHeadCompile with
                ⟨hHeadName, hHeadArgc, hHeadRetc⟩
              by_cases hName : head.name = name
              · simp [FunList.find?, hName] at hFind
                cases hFind
                have hLookupName : headProc.name = name := by
                  simpa [hName] using hHeadName
                exact
                  ⟨headProc, state, stateAfterHead,
                    by simp [Expressions.ProcList.lookup?, hLookupName],
                    hHeadCompile, hHeadName, hHeadArgc, hHeadRetc⟩
              · have hTailFind : FunList.find? name rest = some fn := by
                  simpa [FunList.find?, hName] using hFind
                rcases compileFunctions?_lookup_of_find?_with_compile
                    hTailCompile hTailFind with
                  ⟨proc, fnState, fnState', hLookup, hProcCompile,
                    hProcName, hArgc, hRetc⟩
                have hHeadProcNameNe : headProc.name ≠ name := by
                  intro hEq
                  exact hName (by simpa [hHeadName] using hEq)
                exact
                  ⟨proc, fnState, fnState',
                    by
                      simp [Expressions.ProcList.lookup?,
                        hHeadProcNameNe, hLookup],
                    hProcCompile, hProcName, hArgc, hRetc⟩

theorem compileExpressionsProgram?_lookup_of_find?
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program} {name : Name} {fn : FunDef}
    (hCompile :
      compileExpressionsProgram? maxFrameWords program = some exprProgram)
    (hFind : FunList.find? name program.functions = some fn) :
    ∃ proc,
      Expressions.ProcList.lookup? name exprProgram.procs = some proc ∧
        proc.name = fn.name ∧ proc.argc = 1 ∧
          proc.retc = fn.returns.length := by
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
                      rcases finalResult with
                        ⟨procs, stateAfterFunctionsFinal⟩
                      have hFinalFunctions' :
                          compileFunctions?
                              { functions := functionSlots,
                                frameWords := mainProbe.state.nextSlot }
                              stateAfterSignatures program.functions =
                            some (procs, stateAfterFunctionsFinal) := by
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
                          exact
                            compileFunctions?_lookup_of_find?
                              hFinalFunctions hFind
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

theorem compileChecked?_lookup_of_find?
    {maxFrameWords : Nat} {program : Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    {name : Name} {fn : FunDef}
    (hCompile :
      compileChecked? maxFrameWords program = some (exprProgram, asm))
    (hFind : FunList.find? name program.functions = some fn) :
    ∃ proc,
      Expressions.ProcList.lookup? name exprProgram.procs = some proc ∧
        proc.name = fn.name ∧ proc.argc = 1 ∧
          proc.retc = fn.returns.length :=
  compileExpressionsProgram?_lookup_of_find?
    (compileChecked?_eq_some hCompile).1 hFind

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
