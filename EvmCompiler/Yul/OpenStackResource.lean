import EvmCompiler.Yul.OpenGasAware
import EvmCompiler.Structured.StackResource

namespace EvmCompiler
namespace Yul
namespace OpenAssemblyStackBounds

open Structured.StackResource

abbrev EVMState := EvmYul.EVM.State
abbrev Word := EvmYul.UInt256
abbrev Effect := Structured.StackResource.Effect
abbrev BoundTable :=
  Structured.StackResource.AssemblyBounds.BoundTable

def lookupBound? : BoundTable → Word → Option Nat :=
  Structured.StackResource.AssemblyBounds.lookupBound?

def fallthroughPc (pc : Nat) (delta : Nat) : Word :=
  Structured.StackResource.AssemblyBounds.fallthroughPc pc delta

def jumpiFallthroughPc (pc : Nat) : Word :=
  Structured.StackResource.AssemblyBounds.jumpiFallthroughPc pc

def SourceStackBoundPoint (program : Assembly.Program) (table : BoundTable)
    (reserved maxStack : Nat) (state : EVMState) : Prop :=
  Structured.StackResource.AssemblyBounds.SourceStackBoundPoint
    program table reserved maxStack state

def callKindEffect (kind : OpenExternal.CallKind) : Effect :=
  { input := kind.inputArity, output := 1 }

def runningEffect? : Assembly.Instr → Option Effect
  | .label _ => some { input := 0, output := 0 }
  | .push _ => some { input := 0, output := 1 }
  | .jump _ => some { input := 0, output := 0 }
  | .jumpi _ => some { input := 1, output := 0 }
  | .prim op =>
      match OpenExternal.CallKind.ofEVMOperation? op.toEVM with
      | some kind => some (callKindEffect kind)
      | none =>
          match op.haltKind? with
          | some _ => none
          | none =>
              match op.continuingStep? with
              | some step =>
                  some
                    { input := Assembly.PrimStep.inputArity step
                      output := Assembly.PrimStep.outputArity step }
              | none => none

def runningSuccessors? (program : Assembly.Program) (pc : Nat) :
    Assembly.Instr → Option (List Word)
  | .label _ => some [fallthroughPc pc 1]
  | .push _ => some [fallthroughPc pc Assembly.Instr.push32Size]
  | .jump target => do
      let dest ← Assembly.Program.labelPc program target
      some [EvmYul.UInt256.ofNat dest]
  | .jumpi target => do
      let dest ← Assembly.Program.labelPc program target
      some [EvmYul.UInt256.ofNat dest, jumpiFallthroughPc pc]
  | .prim op =>
      match OpenExternal.CallKind.ofEVMOperation? op.toEVM with
      | some _ => some [fallthroughPc pc 1]
      | none =>
          match op.haltKind? with
          | some _ => some []
          | none =>
              match op.continuingStep? with
              | some _ => some [fallthroughPc pc 1]
              | none => none

def successorBoundOk? (table : BoundTable) (height reserved maxStack : Nat)
    (pc : Word) : Bool :=
  Structured.StackResource.AssemblyBounds.successorBoundOk?
    table height reserved maxStack pc

def successorsBoundOk? (table : BoundTable) (height reserved maxStack : Nat) :
    List Word → Bool :=
  Structured.StackResource.AssemblyBounds.successorsBoundOk?
    table height reserved maxStack

def instructionBoundOk? (program : Assembly.Program) (table : BoundTable)
    (reserved maxStack pc : Nat) (instr : Assembly.Instr) : Bool :=
  match lookupBound? table (EvmYul.UInt256.ofNat pc),
      runningEffect? instr,
      runningSuccessors? program pc instr with
  | some bound, some effect, some successors =>
      decide (bound + reserved ≤ maxStack) &&
        successorsBoundOk? table
          (bound - effect.input + effect.output)
          reserved maxStack successors
  | some bound, none, some [] =>
      decide (bound + reserved ≤ maxStack)
  | _, _, _ => false

def programBoundOkFrom? (program : Assembly.Program) (table : BoundTable)
    (reserved maxStack : Nat) : Assembly.Program → Nat → Bool
  | [], _pc => true
  | instr :: rest, pc =>
      instructionBoundOk? program table reserved maxStack pc instr &&
        programBoundOkFrom? program table reserved maxStack
          rest (pc + instr.byteSize)

def programBoundOk? (program : Assembly.Program) (table : BoundTable)
    (reserved maxStack : Nat) : Bool :=
  programBoundOkFrom? program table reserved maxStack program 0

structure ProgramBoundCheckResult (program : Assembly.Program)
    (reserved maxStack : Nat) where
  table : BoundTable
  checked : programBoundOk? program table reserved maxStack = true

def checkProgramBoundCheckResult? (program : Assembly.Program)
    (table : BoundTable) (reserved maxStack : Nat) :
    Option (ProgramBoundCheckResult program reserved maxStack) :=
  if h : programBoundOk? program table reserved maxStack = true then
    some { table := table, checked := h }
  else
    none

theorem checkProgramBoundCheckResult?_eq_some
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat}
    {check : ProgramBoundCheckResult program reserved maxStack}
    (hCheck :
      checkProgramBoundCheckResult? program table reserved maxStack =
        some check) :
    programBoundOk? program table reserved maxStack = true := by
  unfold checkProgramBoundCheckResult? at hCheck
  by_cases h : programBoundOk? program table reserved maxStack = true
  · exact h
  · simp [h] at hCheck

theorem checkProgramBoundCheckResult?_table
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat}
    {check : ProgramBoundCheckResult program reserved maxStack}
    (hCheck :
      checkProgramBoundCheckResult? program table reserved maxStack =
        some check) :
    check.table = table := by
  unfold checkProgramBoundCheckResult? at hCheck
  by_cases h : programBoundOk? program table reserved maxStack = true
  · simp [h] at hCheck
    cases hCheck
    rfl
  · simp [h] at hCheck

def seedProgramBounds (program : Assembly.Program) : BoundTable :=
  Structured.StackResource.AssemblyBounds.seedProgramBounds program

def relaxSuccessors? (table : BoundTable) (height reserved maxStack : Nat) :
    List Word → Option (BoundTable × Bool) :=
  Structured.StackResource.AssemblyBounds.relaxSuccessors?
    table height reserved maxStack

def relaxInstruction? (program : Assembly.Program) (table : BoundTable)
    (reserved maxStack pc : Nat) (instr : Assembly.Instr) :
    Option (BoundTable × Bool) := do
  let bound ← lookupBound? table (EvmYul.UInt256.ofNat pc)
  if _hBound : bound + reserved ≤ maxStack then
    match runningEffect? instr, runningSuccessors? program pc instr with
    | some effect, some successors =>
        relaxSuccessors? table
          (bound - effect.input + effect.output)
          reserved maxStack successors
    | none, some [] => some (table, false)
    | _, _ => none
  else
    none

def relaxProgramFrom? (whole : Assembly.Program) (reserved maxStack : Nat) :
    Assembly.Program → Nat → BoundTable → Option (BoundTable × Bool)
  | [], _pc, table => some (table, false)
  | instr :: rest, pc, table => do
      let (table', changedHere) ←
        relaxInstruction? whole table reserved maxStack pc instr
      let (table'', changedRest) ←
        relaxProgramFrom? whole reserved maxStack rest
          (pc + instr.byteSize) table'
      some (table'', changedHere || changedRest)

def inferProgramBoundTableLoop? (fuel : Nat) (program : Assembly.Program)
    (table : BoundTable) (reserved maxStack : Nat) : Option BoundTable :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match relaxProgramFrom? program reserved maxStack program 0 table with
      | none => none
      | some (table', false) => some table'
      | some (table', true) =>
          inferProgramBoundTableLoop? fuel program table' reserved maxStack

def inferProgramBoundTable? (program : Assembly.Program)
    (reserved maxStack : Nat) : Option BoundTable :=
  if _hLimit : reserved ≤ maxStack then
    let limit := maxStack - reserved
    let fuel := (program.length * 3 + 1) * (limit + 1) + 1
    inferProgramBoundTableLoop? fuel program (seedProgramBounds program)
      reserved maxStack
  else
    none

def inferProgramBoundCheckResult? (program : Assembly.Program)
    (reserved maxStack : Nat) :
    Option (ProgramBoundCheckResult program reserved maxStack) := do
  let table ← inferProgramBoundTable? program reserved maxStack
  checkProgramBoundCheckResult? program table reserved maxStack

theorem programBoundOkFrom?_sound
    {program suffix : Assembly.Program} {table : BoundTable}
    {reserved maxStack base query pc : Nat} {instr : Assembly.Instr}
    (hCheck :
      programBoundOkFrom? program table reserved maxStack suffix base = true)
    (hAt :
      Assembly.Program.instrAtPcFrom suffix base query = some (pc, instr)) :
    instructionBoundOk? program table reserved maxStack pc instr = true := by
  induction suffix generalizing base with
  | nil =>
      simp [Assembly.Program.instrAtPcFrom] at hAt
  | cons head tail ih =>
      simp [programBoundOkFrom?] at hCheck
      by_cases hEq : query = base
      · simp [Assembly.Program.instrAtPcFrom, hEq] at hAt
        rcases hAt with ⟨rfl, rfl⟩
        exact hCheck.1
      · simp [Assembly.Program.instrAtPcFrom, hEq] at hAt
        exact ih hCheck.2 hAt

theorem programBoundOk?_instructionBoundOk
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack query pc : Nat} {instr : Assembly.Instr}
    (hCheck : programBoundOk? program table reserved maxStack = true)
    (hAt : Assembly.Program.instrAtPc program query = some (pc, instr)) :
    instructionBoundOk? program table reserved maxStack pc instr = true :=
  programBoundOkFrom?_sound (program := program) hCheck hAt

theorem instructionBoundOk?_lookup
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack pc : Nat} {instr : Assembly.Instr}
    (hCheck :
      instructionBoundOk? program table reserved maxStack pc instr = true) :
    ∃ bound,
      lookupBound? table (EvmYul.UInt256.ofNat pc) = some bound ∧
        bound + reserved ≤ maxStack := by
  unfold instructionBoundOk? at hCheck
  cases hLookup : lookupBound? table (EvmYul.UInt256.ofNat pc) with
  | none =>
      simp [hLookup] at hCheck
  | some bound =>
      refine ⟨bound, rfl, ?_⟩
      cases hEffect : runningEffect? instr with
      | none =>
          cases hSuccessors : runningSuccessors? program pc instr with
          | none =>
              simp [hLookup, hEffect, hSuccessors] at hCheck
          | some successors =>
              cases successors with
              | nil =>
                  simp [hLookup, hEffect, hSuccessors] at hCheck
                  exact hCheck
              | cons head tail =>
                  simp [hLookup, hEffect, hSuccessors] at hCheck
      | some effect =>
          cases hSuccessors : runningSuccessors? program pc instr with
          | none =>
              simp [hLookup, hEffect, hSuccessors] at hCheck
          | some successors =>
              simp [hLookup, hEffect, hSuccessors] at hCheck
              exact hCheck.1

theorem sourceStackBoundPoint_initial_of_programBoundOk?
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat} {state : EVMState}
    (hCheck : programBoundOk? program table reserved maxStack = true)
    (hReserved : reserved ≤ maxStack) :
    SourceStackBoundPoint program table reserved maxStack
      { state with pc := Assembly.Program.pcAfter [], stack := [] } := by
  constructor
  · simpa [SourceStackBoundPoint] using hReserved
  · intro pc instr hAt
    have hInstrCheck :
        instructionBoundOk? program table reserved maxStack pc instr = true :=
      programBoundOk?_instructionBoundOk hCheck hAt
    rcases instructionBoundOk?_lookup hInstrCheck with
      ⟨bound, hLookup, hBound⟩
    refine ⟨bound, ?_, by simp, hBound⟩
    have hPc :=
      Structured.StackResource.AssemblyBounds.instrAtPc_eq_query hAt
    simpa [SourceStackBoundPoint, Assembly.Program.pcAfter_nil, hPc]
      using hLookup

theorem ProgramBoundCheckResult.initialSourceStackBoundPoint
    {program : Assembly.Program} {reserved maxStack : Nat}
    (check : ProgramBoundCheckResult program reserved maxStack)
    {state : EVMState}
    (hReserved : reserved ≤ maxStack) :
    SourceStackBoundPoint program check.table reserved maxStack
      { state with pc := Assembly.Program.pcAfter [], stack := [] } :=
  sourceStackBoundPoint_initial_of_programBoundOk? check.checked hReserved

theorem successorsBoundOk?_sound
    {table : BoundTable} {height reserved maxStack : Nat}
    {successors : List Word} {pc : Word}
    (hCheck :
      successorsBoundOk? table height reserved maxStack successors = true)
    (hMem : pc ∈ successors) :
    ∃ bound,
      lookupBound? table pc = some bound ∧
        height ≤ bound ∧
          bound + reserved ≤ maxStack := by
  simpa [successorsBoundOk?, lookupBound?] using
    (AssemblyBounds.successorsBoundOk?_sound
      (table := table) (height := height) (reserved := reserved)
      (maxStack := maxStack) (successors := successors) (pc := pc)
      hCheck hMem)

theorem length_of_pop7_some {α : Type} {stack rest : EvmYul.Stack α}
    {a b c d e f g : α}
    (h :
      EvmYul.Stack.pop7 stack =
        some (rest, a, b, c, d, e, f, g)) :
    stack.length = rest.length + 7 := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop7] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop7] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop7] at h
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop7] at h
              | cons w ws =>
                  cases ws with
                  | nil => simp [EvmYul.Stack.pop7] at h
                  | cons v vs =>
                      cases vs with
                      | nil => simp [EvmYul.Stack.pop7] at h
                      | cons u us =>
                          cases us with
                          | nil => simp [EvmYul.Stack.pop7] at h
                          | cons t ts =>
                              simp [EvmYul.Stack.pop7] at h
                              rcases h with
                                ⟨hRest, hA, hB, hC, hD, hE, hF, hG⟩
                              subst rest
                              simp

theorem call_resume_stack_length_of_evmOpenCall?
    {state : EVMState} {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    (call.resume response).stack.length =
      state.stack.length - kind.inputArity + 1 := by
  unfold OpenExternal.CallKind.evmOpenCall? at hCall
  cases hSite : OpenExternal.CallKind.evmCallSite? state kind with
  | none =>
      simp [hSite] at hCall
  | some pair =>
      rcases pair with ⟨rest, site⟩
      simp [hSite] at hCall
      cases hCall
      unfold OpenExternal.CallKind.evmCallSite? at hSite
      cases kind with
      | call =>
          cases hPop : state.stack.pop7 with
          | none =>
              simp [OpenExternal.CallKind.evmOperands?, hPop] at hSite
          | some popped =>
              rcases popped with
                ⟨rest', gas, address, value, inOffset, inSize, outOffset,
                  outSize⟩
              simp [OpenExternal.CallKind.evmOperands?, hPop] at hSite
              rcases hSite with ⟨rfl, rfl⟩
              have hLen :=
                length_of_pop7_some
                  (stack := state.stack) (rest := rest') hPop
              rw [hLen]
              simp [OpenExternal.CallKind.inputArity]
      | callcode =>
          cases hPop : state.stack.pop7 with
          | none =>
              simp [OpenExternal.CallKind.evmOperands?, hPop] at hSite
          | some popped =>
              rcases popped with
                ⟨rest', gas, address, value, inOffset, inSize, outOffset,
                  outSize⟩
              simp [OpenExternal.CallKind.evmOperands?, hPop] at hSite
              rcases hSite with ⟨rfl, rfl⟩
              have hLen :=
                length_of_pop7_some
                  (stack := state.stack) (rest := rest') hPop
              rw [hLen]
              simp [OpenExternal.CallKind.inputArity]
      | delegatecall =>
          cases hPop : state.stack.pop6 with
          | none =>
              simp [OpenExternal.CallKind.evmOperands?, hPop] at hSite
          | some popped =>
              rcases popped with
                ⟨rest', gas, address, inOffset, inSize, outOffset, outSize⟩
              simp [OpenExternal.CallKind.evmOperands?, hPop] at hSite
              rcases hSite with ⟨rfl, rfl⟩
              have hLen :=
                Assembly.PrimStep.Stack.length_of_pop6_some
                  (stack := state.stack) (rest := rest') hPop
              rw [hLen]
              simp [OpenExternal.CallKind.inputArity]
      | staticcall =>
          cases hPop : state.stack.pop6 with
          | none =>
              simp [OpenExternal.CallKind.evmOperands?, hPop] at hSite
          | some popped =>
              rcases popped with
                ⟨rest', gas, address, inOffset, inSize, outOffset, outSize⟩
              simp [OpenExternal.CallKind.evmOperands?, hPop] at hSite
              rcases hSite with ⟨rfl, rfl⟩
              have hLen :=
                Assembly.PrimStep.Stack.length_of_pop6_some
                  (stack := state.stack) (rest := rest') hPop
              rw [hLen]
              simp [OpenExternal.CallKind.inputArity]

theorem call_resume_pc_of_evmOpenCall?
    {state : EVMState} {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    (call.resume response).pc = state.pc := by
  unfold OpenExternal.CallKind.evmOpenCall? at hCall
  cases hSite : OpenExternal.CallKind.evmCallSite? state kind with
  | none =>
      simp [hSite] at hCall
  | some pair =>
      rcases pair with ⟨rest, site⟩
      simp [hSite] at hCall
      cases hCall
      simp

theorem incrPC_call_resume_stack_length_of_evmOpenCall?
    {state : EVMState} {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    (EvmYul.EVM.State.incrPC (call.resume response)).stack.length =
      state.stack.length - kind.inputArity + 1 := by
  simpa [EvmYul.EVM.State.incrPC] using
    call_resume_stack_length_of_evmOpenCall? hCall response

theorem incrPC_call_resume_pc_of_evmOpenCall?
    {state : EVMState} {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    (EvmYul.EVM.State.incrPC (call.resume response)).pc =
      state.pc + EvmYul.UInt256.ofNat 1 := by
  simp [EvmYul.EVM.State.incrPC,
    call_resume_pc_of_evmOpenCall? hCall response]

theorem openRunListResult_emitInstr_prim_call_running_stack_length
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {emitted : List Assembly.LocatedTarget} {state mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {kind : OpenExternal.CallKind}
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        trace (.ok (.running mid))) :
    mid.stack.length =
      state.stack.length - kind.inputArity + 1 := by
  cases hCall : OpenExternal.CallKind.evmOpenCall? state kind with
  | none =>
      have hEmit' := hEmit
      simp [Assembly.emitInstr?] at hEmit'
      subst emitted
      change
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            [Assembly.TargetInstr.prim op] state)
          trace (.ok (.running mid)) at hRun
      rw [OpenAssembly.Target.openRunListResult_cons] at hRun
      unfold OpenAssembly.Target.openStepInstrResult at hRun
      rw [OpenAssembly.Target.openStepInstr_of_prim_callKind_no_call
        hKind hCall] at hRun
      simp only [OpenExternal.OpenResult.bind_done_error] at hRun
      cases hRun
  | some call =>
      rcases
          _root_.EvmCompiler.Yul.OpenGasAware.OpenXBlockTraceRelReady.openRunListResult_emitInstr_prim_call_running_inv
            hEmit hKind hCall hRun with
        ⟨response, _hTrace, hMid⟩
      subst mid
      exact incrPC_call_resume_stack_length_of_evmOpenCall?
        hCall response

theorem openRunListResult_emitInstr_prim_call_running_pc_mem
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {emitted : List Assembly.LocatedTarget} {state mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {kind : OpenExternal.CallKind}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        trace (.ok (.running mid))) :
    mid.pc ∈ [fallthroughPc pc 1] := by
  cases hCall : OpenExternal.CallKind.evmOpenCall? state kind with
  | none =>
      have hEmit' := hEmit
      simp [Assembly.emitInstr?] at hEmit'
      subst emitted
      change
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            [Assembly.TargetInstr.prim op] state)
          trace (.ok (.running mid)) at hRun
      rw [OpenAssembly.Target.openRunListResult_cons] at hRun
      unfold OpenAssembly.Target.openStepInstrResult at hRun
      rw [OpenAssembly.Target.openStepInstr_of_prim_callKind_no_call
        hKind hCall] at hRun
      simp only [OpenExternal.OpenResult.bind_done_error] at hRun
      cases hRun
  | some call =>
      rcases
          _root_.EvmCompiler.Yul.OpenGasAware.OpenXBlockTraceRelReady.openRunListResult_emitInstr_prim_call_running_inv
            hEmit hKind hCall hRun with
        ⟨response, _hTrace, hMid⟩
      subst mid
      have hPc :=
        AssemblyBounds.state_pc_eq_of_instrAtPc hAt
      simp [fallthroughPc, AssemblyBounds.fallthroughPc, hPc,
        incrPC_call_resume_pc_of_evmOpenCall? hCall response]

theorem closed_stepAtResult_running_of_open_emit_no_callCreate
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget} {state mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        trace (.ok (.running mid))) :
    Assembly.Source.stepAtResult program pc instr state =
      .ok (.running mid) := by
  rcases
      _root_.EvmCompiler.Yul.OpenGasAware.OpenXBlockTraceRelReady.openRunListResult_emitInstr_no_call_inv
        hNoInstr hEmit hRun with
    ⟨_hTrace, hClosedRun⟩
  exact
    AssemblyInstr.stepAtResult_running_of_emit_runListResult
      hEmit hClosedRun

theorem prim_usesCallCreate_true_of_callKind
    {op : Assembly.PrimOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind) :
    Assembly.Instr.usesCallCreate (.prim op) = true := by
  cases op <;>
    simp [Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
      Assembly.PrimOp.toEVM, OpenExternal.CallKind.ofEVMOperation?]
      at hKind ⊢

theorem prim_usesCallCreate_false_of_runningEffect?_some_no_callKind
    {op : Assembly.PrimOp} {effect : Effect}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hEffect : runningEffect? (.prim op) = some effect) :
    Assembly.Instr.usesCallCreate (.prim op) = false := by
  cases op <;>
    simp [runningEffect?, Assembly.Instr.usesCallCreate,
      Assembly.PrimOp.isCallCreate, Assembly.PrimOp.toEVM,
      Assembly.PrimOp.haltKind?, Assembly.PrimOp.continuingStep?,
      OpenExternal.CallKind.ofEVMOperation?] at hKind hEffect ⊢

theorem prim_usesCallCreate_false_of_runningSuccessors?_some_no_callKind
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {successors : List Word}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hSuccessors :
      runningSuccessors? program pc (.prim op) = some successors) :
    Assembly.Instr.usesCallCreate (.prim op) = false := by
  cases op <;>
    simp [runningSuccessors?, fallthroughPc, AssemblyBounds.fallthroughPc,
      Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate,
      Assembly.PrimOp.toEVM, Assembly.PrimOp.haltKind?,
      Assembly.PrimOp.continuingStep?,
      OpenExternal.CallKind.ofEVMOperation?]
      at hKind hSuccessors ⊢

theorem runningEffect?_closed_of_no_callCreate
    {instr : Assembly.Instr} {effect : Effect}
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEffect : runningEffect? instr = some effect) :
    AssemblyInstr.runningEffect? instr = some effect := by
  cases instr with
  | label name =>
      simpa [runningEffect?, AssemblyInstr.runningEffect?] using hEffect
  | push value =>
      simpa [runningEffect?, AssemblyInstr.runningEffect?] using hEffect
  | jump target =>
      simpa [runningEffect?, AssemblyInstr.runningEffect?] using hEffect
  | jumpi target =>
      simpa [runningEffect?, AssemblyInstr.runningEffect?] using hEffect
  | prim op =>
      unfold runningEffect? at hEffect
      cases hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM with
      | some kind =>
          have hUse :=
            prim_usesCallCreate_true_of_callKind hKind
          rw [hUse] at hNoInstr
          contradiction
      | none =>
          simp [hKind] at hEffect
          unfold AssemblyInstr.runningEffect?
          exact hEffect

theorem runningSuccessors?_closed_of_no_callCreate
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {successors : List Word}
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hSuccessors : runningSuccessors? program pc instr = some successors) :
    AssemblyBounds.runningSuccessors? program pc instr = some successors := by
  cases instr with
  | label name =>
      simpa [runningSuccessors?, AssemblyBounds.runningSuccessors?,
        fallthroughPc, AssemblyBounds.fallthroughPc] using hSuccessors
  | push value =>
      simpa [runningSuccessors?, AssemblyBounds.runningSuccessors?,
        fallthroughPc, AssemblyBounds.fallthroughPc] using hSuccessors
  | jump target =>
      simpa [runningSuccessors?, AssemblyBounds.runningSuccessors?]
        using hSuccessors
  | jumpi target =>
      simpa [runningSuccessors?, AssemblyBounds.runningSuccessors?,
        jumpiFallthroughPc, AssemblyBounds.jumpiFallthroughPc]
        using hSuccessors
  | prim op =>
      unfold runningSuccessors? at hSuccessors
      cases hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM with
      | some kind =>
          have hUse :=
            prim_usesCallCreate_true_of_callKind hKind
          rw [hUse] at hNoInstr
          contradiction
      | none =>
          simp [hKind, fallthroughPc,
            AssemblyBounds.fallthroughPc] at hSuccessors
          unfold AssemblyBounds.runningSuccessors?
          simpa [fallthroughPc, AssemblyBounds.fallthroughPc]
            using hSuccessors

theorem instructionBoundOk?_preserves_openTargetBlock_sourceStackBoundPoint
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {target : Assembly.TargetProgram}
    {state mid : EVMState} {trace : OpenExternal.OpenTrace}
    (hCheck :
      instructionBoundOk? program table reserved maxStack pc instr = true)
    (hPoint :
      SourceStackBoundPoint program table reserved maxStack state)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (_hTargetBlock : target.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        trace (.ok (.running mid))) :
    SourceStackBoundPoint program table reserved maxStack mid := by
  have hPc := AssemblyBounds.state_pc_eq_of_instrAtPc hAt
  rcases hPoint.2 hAt with
    ⟨bound, hLookupState, hStack, _hCurrentHeadroom⟩
  have hLookupPc :
      lookupBound? table (EvmYul.UInt256.ofNat pc) = some bound := by
    simpa [lookupBound?, hPc] using hLookupState
  unfold instructionBoundOk? at hCheck
  rw [hLookupPc] at hCheck
  cases hEffect : runningEffect? instr with
  | none =>
      cases hSuccs : runningSuccessors? program pc instr with
      | none =>
          simp [hEffect, hSuccs] at hCheck
      | some successors =>
          cases successors with
          | nil =>
              have hMem : mid.pc ∈ ([] : List Word) := by
                cases instr with
                | label name =>
                    simp [runningSuccessors?] at hSuccs
                | push value =>
                    simp [runningSuccessors?] at hSuccs
                | jump targetLabel =>
                    cases hDest :
                        Assembly.Program.labelPc program targetLabel with
                    | none =>
                        simp [runningSuccessors?, hDest] at hSuccs
                    | some dest =>
                        simp [runningSuccessors?, hDest] at hSuccs
                | jumpi targetLabel =>
                    cases hDest :
                        Assembly.Program.labelPc program targetLabel with
                    | none =>
                        simp [runningSuccessors?, hDest] at hSuccs
                    | some dest =>
                        simp [runningSuccessors?, hDest] at hSuccs
                | prim op =>
                    cases hKind :
                        OpenExternal.CallKind.ofEVMOperation? op.toEVM with
                    | some kind =>
                        simp [runningSuccessors?, hKind] at hSuccs
                    | none =>
                        have hNoInstr :
                            Assembly.Instr.usesCallCreate (.prim op) =
                              false :=
                          prim_usesCallCreate_false_of_runningSuccessors?_some_no_callKind
                            hKind hSuccs
                        have hStep :=
                          closed_stepAtResult_running_of_open_emit_no_callCreate
                            hNoInstr hEmit hRun
                        have hSuccClosed :=
                          runningSuccessors?_closed_of_no_callCreate
                            hNoInstr hSuccs
                        exact
                          AssemblyBounds.stepAtResult_running_pc_mem_successors?
                            hSuccClosed hPc hStep
              simp at hMem
          | cons head tail =>
              simp [hEffect, hSuccs] at hCheck
  | some effect =>
      cases hSuccs : runningSuccessors? program pc instr with
      | none =>
          simp [hEffect, hSuccs] at hCheck
      | some successors =>
          simp [hEffect, hSuccs] at hCheck
          have hMem : mid.pc ∈ successors := by
            cases instr with
            | label name =>
                have hNoInstr :
                    Assembly.Instr.usesCallCreate (.label name) = false := by
                  simp [Assembly.Instr.usesCallCreate]
                have hStep :=
                  closed_stepAtResult_running_of_open_emit_no_callCreate
                    hNoInstr hEmit hRun
                have hSuccClosed :=
                  runningSuccessors?_closed_of_no_callCreate
                    hNoInstr hSuccs
                exact
                  AssemblyBounds.stepAtResult_running_pc_mem_successors?
                    hSuccClosed hPc hStep
            | push value =>
                have hNoInstr :
                    Assembly.Instr.usesCallCreate (.push value) = false := by
                  simp [Assembly.Instr.usesCallCreate]
                have hStep :=
                  closed_stepAtResult_running_of_open_emit_no_callCreate
                    hNoInstr hEmit hRun
                have hSuccClosed :=
                  runningSuccessors?_closed_of_no_callCreate
                    hNoInstr hSuccs
                exact
                  AssemblyBounds.stepAtResult_running_pc_mem_successors?
                    hSuccClosed hPc hStep
            | jump targetLabel =>
                have hNoInstr :
                    Assembly.Instr.usesCallCreate (.jump targetLabel) =
                      false := by
                  simp [Assembly.Instr.usesCallCreate]
                have hStep :=
                  closed_stepAtResult_running_of_open_emit_no_callCreate
                    hNoInstr hEmit hRun
                have hSuccClosed :=
                  runningSuccessors?_closed_of_no_callCreate
                    hNoInstr hSuccs
                exact
                  AssemblyBounds.stepAtResult_running_pc_mem_successors?
                    hSuccClosed hPc hStep
            | jumpi targetLabel =>
                have hNoInstr :
                    Assembly.Instr.usesCallCreate (.jumpi targetLabel) =
                      false := by
                  simp [Assembly.Instr.usesCallCreate]
                have hStep :=
                  closed_stepAtResult_running_of_open_emit_no_callCreate
                    hNoInstr hEmit hRun
                have hSuccClosed :=
                  runningSuccessors?_closed_of_no_callCreate
                    hNoInstr hSuccs
                exact
                  AssemblyBounds.stepAtResult_running_pc_mem_successors?
                    hSuccClosed hPc hStep
            | prim op =>
                cases hKind :
                    OpenExternal.CallKind.ofEVMOperation? op.toEVM with
                | some kind =>
                    have hMemCall :=
                      openRunListResult_emitInstr_prim_call_running_pc_mem
                        (program := program) (pc := pc) (op := op)
                        hAt hEmit hKind hRun
                    simp [runningSuccessors?, hKind] at hSuccs
                    cases hSuccs
                    exact hMemCall
                | none =>
                    have hNoInstr :
                        Assembly.Instr.usesCallCreate (.prim op) = false :=
                      prim_usesCallCreate_false_of_runningEffect?_some_no_callKind
                        hKind hEffect
                    have hStep :=
                      closed_stepAtResult_running_of_open_emit_no_callCreate
                        hNoInstr hEmit hRun
                    have hSuccClosed :=
                      runningSuccessors?_closed_of_no_callCreate
                        hNoInstr hSuccs
                    exact
                      AssemblyBounds.stepAtResult_running_pc_mem_successors?
                        hSuccClosed hPc hStep
          rcases successorsBoundOk?_sound hCheck.2 hMem with
            ⟨nextBound, hLookupNext, hNextHeight, hNextHeadroom⟩
          have hMidStack : mid.stack.length ≤ nextBound := by
            cases instr with
            | label name =>
                have hNoInstr :
                    Assembly.Instr.usesCallCreate (.label name) = false := by
                  simp [Assembly.Instr.usesCallCreate]
                have hEffectClosed :=
                  runningEffect?_closed_of_no_callCreate hNoInstr hEffect
                have hStep :=
                  closed_stepAtResult_running_of_open_emit_no_callCreate
                    hNoInstr hEmit hRun
                exact
                  AssemblyInstr.stepAtResult_running_stack_le_of_effect?
                    hEffectClosed hStack hNextHeight hStep
            | push value =>
                have hNoInstr :
                    Assembly.Instr.usesCallCreate (.push value) = false := by
                  simp [Assembly.Instr.usesCallCreate]
                have hEffectClosed :=
                  runningEffect?_closed_of_no_callCreate hNoInstr hEffect
                have hStep :=
                  closed_stepAtResult_running_of_open_emit_no_callCreate
                    hNoInstr hEmit hRun
                exact
                  AssemblyInstr.stepAtResult_running_stack_le_of_effect?
                    hEffectClosed hStack hNextHeight hStep
            | jump targetLabel =>
                have hNoInstr :
                    Assembly.Instr.usesCallCreate (.jump targetLabel) =
                      false := by
                  simp [Assembly.Instr.usesCallCreate]
                have hEffectClosed :=
                  runningEffect?_closed_of_no_callCreate hNoInstr hEffect
                have hStep :=
                  closed_stepAtResult_running_of_open_emit_no_callCreate
                    hNoInstr hEmit hRun
                exact
                  AssemblyInstr.stepAtResult_running_stack_le_of_effect?
                    hEffectClosed hStack hNextHeight hStep
            | jumpi targetLabel =>
                have hNoInstr :
                    Assembly.Instr.usesCallCreate (.jumpi targetLabel) =
                      false := by
                  simp [Assembly.Instr.usesCallCreate]
                have hEffectClosed :=
                  runningEffect?_closed_of_no_callCreate hNoInstr hEffect
                have hStep :=
                  closed_stepAtResult_running_of_open_emit_no_callCreate
                    hNoInstr hEmit hRun
                exact
                  AssemblyInstr.stepAtResult_running_stack_le_of_effect?
                    hEffectClosed hStack hNextHeight hStep
            | prim op =>
                cases hKind :
                    OpenExternal.CallKind.ofEVMOperation? op.toEVM with
                | some kind =>
                    have hLen :=
                      openRunListResult_emitInstr_prim_call_running_stack_length
                        (program := program) (pc := pc) (op := op)
                        hEmit hKind hRun
                    simp [runningEffect?, hKind, callKindEffect] at hEffect
                    cases hEffect
                    rw [hLen]
                    have hMono :
                        state.stack.length - kind.inputArity + 1 ≤
                          bound - kind.inputArity + 1 := by
                      exact Nat.add_le_add_right
                        (Nat.sub_le_sub_right hStack kind.inputArity) 1
                    exact le_trans hMono hNextHeight
                | none =>
                    have hNoInstr :
                        Assembly.Instr.usesCallCreate (.prim op) = false :=
                      prim_usesCallCreate_false_of_runningEffect?_some_no_callKind
                        hKind hEffect
                    have hEffectClosed :=
                      runningEffect?_closed_of_no_callCreate hNoInstr hEffect
                    have hStep :=
                      closed_stepAtResult_running_of_open_emit_no_callCreate
                        hNoInstr hEmit hRun
                    exact
                      AssemblyInstr.stepAtResult_running_stack_le_of_effect?
                        hEffectClosed hStack hNextHeight hStep
          constructor
          · omega
          · intro _pc' _instr' _hAt
            exact
              ⟨nextBound, hLookupNext, hMidStack, hNextHeadroom⟩

def StepResultHeadroom (reserved maxStack : Nat) :
    Assembly.StepResult → Prop
  | .running state => state.stack.length + reserved ≤ maxStack
  | .halted _halt => True

theorem openBlockTraceResult_headroom_of_programBoundOk?
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hInitial :
      SourceStackBoundPoint program table reserved maxStack initial)
    (hCheck : programBoundOk? program table reserved maxStack = true)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program target fuel initial trace
        result) :
    StepResultHeadroom reserved maxStack result := by
  induction hTrace with
  | done state =>
      exact AssemblyBounds.SourceStackBoundPoint.headroom hInitial
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      have hInstrCheck :
          instructionBoundOk? program table reserved maxStack _ _ = true :=
        programBoundOk?_instructionBoundOk hCheck hAt
      have hMidPoint :=
        instructionBoundOk?_preserves_openTargetBlock_sourceStackBoundPoint
          hInstrCheck hInitial hAt hEmit hTargetBlock hRun
      exact ih hMidPoint
  | stepHalted hAt hEmit hTargetBlock hRun =>
      trivial

theorem openBlockTraceResult_headroom_of_check
    {program : Assembly.Program} {reserved maxStack : Nat}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (check : ProgramBoundCheckResult program reserved maxStack)
    (hInitial :
      SourceStackBoundPoint program check.table reserved maxStack initial)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program target fuel initial trace
        result) :
    StepResultHeadroom reserved maxStack result :=
  openBlockTraceResult_headroom_of_programBoundOk?
    hInitial check.checked hTrace

theorem openBlockTraceResult_running_stack_le_of_programBoundOk?
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial finalState : EVMState} {trace : OpenExternal.OpenTrace}
    (hInitial :
      SourceStackBoundPoint program table reserved maxStack initial)
    (hCheck : programBoundOk? program table reserved maxStack = true)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program target fuel initial trace
        (.running finalState)) :
    finalState.stack.length ≤ maxStack := by
  have hHeadroom :=
    openBlockTraceResult_headroom_of_programBoundOk?
      hInitial hCheck hTrace
  simp [StepResultHeadroom] at hHeadroom
  omega

theorem openBlockTraceResult_running_stack_le_of_check
    {program : Assembly.Program} {reserved maxStack : Nat}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial finalState : EVMState} {trace : OpenExternal.OpenTrace}
    (check : ProgramBoundCheckResult program reserved maxStack)
    (hInitial :
      SourceStackBoundPoint program check.table reserved maxStack initial)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program target fuel initial trace
        (.running finalState)) :
    finalState.stack.length ≤ maxStack :=
  openBlockTraceResult_running_stack_le_of_programBoundOk?
    hInitial check.checked hTrace

inductive CurrentInstrPrimitiveStaticTraceReadyFor
    {program : Assembly.Program} (targetProgram : Assembly.TargetProgram) :
    {targetFuel : Nat} → {state : EVMState} →
      {trace : OpenExternal.OpenTrace} →
        {targetResult : Assembly.StepResult} →
          OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
            state trace targetResult → Prop where
  | done (state : EVMState) :
      CurrentInstrPrimitiveStaticTraceReadyFor targetProgram
        (OpenAssembly.OpenBlockTraceResult.done
          (program := program) (target := targetProgram) state)
  | stepRunning
      {fuel : Nat} {state mid : EVMState}
      {trace tailTrace : OpenExternal.OpenTrace}
      {result : Assembly.StepResult}
      {pc : Nat} {instr : Assembly.Instr}
      {emitted before after : List Assembly.LocatedTarget}
      (hAt :
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr))
      (hEmit : Assembly.emitInstr? program pc instr = some emitted)
      (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
      (hRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)))
      {hRest :
        OpenAssembly.OpenBlockTraceResult program targetProgram fuel mid
          tailTrace result}
      (hStatic :
        Assembly.GasAware.XStepTrace.InstrPrimitiveStaticInputsReady
          targetProgram instr state)
      (hRestReady :
        CurrentInstrPrimitiveStaticTraceReadyFor targetProgram hRest) :
      CurrentInstrPrimitiveStaticTraceReadyFor targetProgram
        (OpenAssembly.OpenBlockTraceResult.stepRunning
          hAt hEmit hTargetBlock hRun hRest)
  | stepHalted
      {fuel : Nat} {state : EVMState}
      {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
      {pc : Nat} {instr : Assembly.Instr}
      {emitted before after : List Assembly.LocatedTarget}
      (hAt :
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr))
      (hEmit : Assembly.emitInstr? program pc instr = some emitted)
      (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
      (hRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)))
      (hStatic :
        Assembly.GasAware.XStepTrace.InstrPrimitiveStaticInputsReady
          targetProgram instr state) :
      CurrentInstrPrimitiveStaticTraceReadyFor targetProgram
        (OpenAssembly.OpenBlockTraceResult.stepHalted
          hAt hEmit hTargetBlock hRun)

theorem currentNoCallInstrCoreResidualTraceReadyFor_of_stack_bound_static_trace
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        initial trace targetResult}
    (check : ProgramBoundCheckResult program 17 1024)
    (hInitial :
      SourceStackBoundPoint program check.table 17 1024 initial)
    (hStaticReady :
      CurrentInstrPrimitiveStaticTraceReadyFor targetProgram hTrace) :
    OpenGasAware.OpenXBlockTraceRelReady.CurrentNoCallInstrCoreResidualTraceReadyFor
      targetProgram hTrace := by
  induction hStaticReady with
  | done state =>
      exact
        OpenGasAware.OpenXBlockTraceRelReady.CurrentNoCallInstrCoreResidualTraceReadyFor.done
          state
  | stepRunning hAt hEmit hTargetBlock hRun hStatic _hRestReady ih =>
      have hInstrCheck :
          instructionBoundOk? program check.table 17 1024 _ _ = true :=
        programBoundOk?_instructionBoundOk check.checked hAt
      have hMidPoint :
          SourceStackBoundPoint program check.table 17 1024 _ :=
        instructionBoundOk?_preserves_openTargetBlock_sourceStackBoundPoint
          hInstrCheck hInitial hAt hEmit hTargetBlock hRun
      have hCurrentHeadroom :
          _ ≤ _ := hInitial.1
      exact
        OpenGasAware.OpenXBlockTraceRelReady.CurrentNoCallInstrCoreResidualTraceReadyFor.stepRunning
          hAt hEmit hTargetBlock hRun
          (fun _hNoCall =>
            Assembly.GasAware.XStepTrace.InstrCoreResidualInputsReady.of_stack_headroom17_static
              hCurrentHeadroom hStatic)
          (ih hMidPoint)
  | stepHalted hAt hEmit hTargetBlock hRun hStatic =>
      rename_i _targetFuel0 fuel0 state0 trace0 halt0 pc0 instr0 emitted0
        before0 after0
      have hCurrentHeadroom :
          _ ≤ _ := hInitial.1
      exact
        OpenGasAware.OpenXBlockTraceRelReady.CurrentNoCallInstrCoreResidualTraceReadyFor.stepHalted
          (fuel := fuel0)
          hAt hEmit hTargetBlock hRun
          (fun _hNoCall =>
            Assembly.GasAware.XStepTrace.InstrCoreResidualInputsReady.of_stack_headroom17_static
              hCurrentHeadroom hStatic)

end OpenAssemblyStackBounds
end Yul
end EvmCompiler
