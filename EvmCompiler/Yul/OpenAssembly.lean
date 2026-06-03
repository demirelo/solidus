import EvmCompiler.Yul.OpenExternal
import EvmCompiler.Assembly.Semantics

/-!
Open external-call adapters for the gasless Assembly/EVM target layer.

The source-side CALL proof already uses `OpenExternal` at the compiler-source
primitive boundary.  This file starts the corresponding target-side vocabulary
without changing the closed Assembly interpreter: non-CALL primitives embed as
closed results, while CALL-family primitives suspend at the abstract external
request extracted from the EVM state.
-/

namespace EvmCompiler
namespace Yul
namespace OpenAssembly

abbrev EVMState := EvmYul.EVM.State
abbrev EVMException := EvmYul.EVM.ExecutionException

def evmCallResult (call : OpenExternal.OpenCall EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  .call
    { site := call.site
      resume := fun response => .done (.ok (call.resume response)) }

theorem evmCallResult_resolves
    (call : OpenExternal.OpenCall EVMState)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (evmCallResult call)
      [{ site := call.site, response := response }]
      (.ok (call.resume response)) := by
  unfold evmCallResult
  exact OpenExternal.OpenResultResolves.call
    OpenExternal.OpenResultResolves.done

def evmInstructionCallResult (call : OpenExternal.OpenCall EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  .call
    { site := call.site
      resume := fun response =>
        .done (.ok (EvmYul.EVM.State.incrPC (call.resume response))) }

theorem evmInstructionCallResult_resolves
    (call : OpenExternal.OpenCall EVMState)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (evmInstructionCallResult call)
      [{ site := call.site, response := response }]
      (.ok (EvmYul.EVM.State.incrPC (call.resume response))) := by
  unfold evmInstructionCallResult
  exact OpenExternal.OpenResultResolves.call
    OpenExternal.OpenResultResolves.done

namespace PrimOp

def openStep (op : Assembly.PrimOp) (state : EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  match OpenExternal.CallKind.ofEVMOperation? op.toEVM with
  | some kind =>
      match OpenExternal.CallKind.evmOpenCall? state kind with
      | some call => evmCallResult call
      | none => .done (op.step state)
  | none => .done (op.step state)

theorem openStep_of_not_callKind
    {op : Assembly.PrimOp} {state : EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none) :
    openStep op state = .done (op.step state) := by
  simp [openStep, hKind]

theorem openStep_of_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call) :
    openStep op state = evmCallResult call := by
  simp [openStep, hKind, hCall]

theorem openStep_of_callKind_no_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = none) :
    openStep op state = .done (op.step state) := by
  simp [openStep, hKind, hCall]

theorem openStep_resolves_closed_of_not_callKind
    {op : Assembly.PrimOp} {state state' : EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hStep : op.step state = .ok state') :
    OpenExternal.OpenResultResolves (openStep op state) [] (.ok state') := by
  rw [openStep_of_not_callKind hKind, hStep]
  exact OpenExternal.OpenResultResolves.done

theorem openStep_resolves_closed_of_callKind_no_call
    {op : Assembly.PrimOp} {state state' : EVMState}
    {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = none)
    (hStep : op.step state = .ok state') :
    OpenExternal.OpenResultResolves (openStep op state) [] (.ok state') := by
  rw [openStep_of_callKind_no_call hKind hCall, hStep]
  exact OpenExternal.OpenResultResolves.done

theorem openStep_resolves_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStep op state)
      [{ site := call.site, response := response }]
      (.ok (call.resume response)) := by
  rw [openStep_of_call hKind hCall]
  exact evmCallResult_resolves call response

end PrimOp

namespace Target

def openStepInstr (instr : Assembly.TargetInstr) (state : EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  match instr with
  | .prim op =>
      match OpenExternal.CallKind.ofEVMOperation? op.toEVM with
      | some kind =>
          match OpenExternal.CallKind.evmOpenCall? state kind with
          | some call => evmInstructionCallResult call
          | none => .done (Assembly.Target.stepInstr instr state)
      | none => .done (Assembly.Target.stepInstr instr state)
  | _ => .done (Assembly.Target.stepInstr instr state)

theorem openStepInstr_of_non_prim
    {instr : Assembly.TargetInstr} {state : EVMState}
    (hInstr : ∀ op, instr ≠ .prim op) :
    openStepInstr instr state = .done (Assembly.Target.stepInstr instr state) := by
  cases instr <;> simp [openStepInstr]
  exact False.elim (hInstr _ rfl)

theorem openStepInstr_of_prim_not_callKind
    {op : Assembly.PrimOp} {state : EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none) :
    openStepInstr (.prim op) state =
      .done (Assembly.Target.stepInstr (.prim op) state) := by
  simp [openStepInstr, hKind]

theorem openStepInstr_of_prim_callKind_no_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = none) :
    openStepInstr (.prim op) state =
      .done (Assembly.Target.stepInstr (.prim op) state) := by
  simp [openStepInstr, hKind, hCall]

theorem openStepInstr_of_prim_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call) :
    openStepInstr (.prim op) state = evmInstructionCallResult call := by
  simp [openStepInstr, hKind, hCall]

theorem openStepInstr_resolves_closed_of_prim_not_callKind
    {op : Assembly.PrimOp} {state state' : EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = none)
    (hStep : Assembly.Target.stepInstr (.prim op) state = .ok state') :
    OpenExternal.OpenResultResolves
      (openStepInstr (.prim op) state) [] (.ok state') := by
  rw [openStepInstr_of_prim_not_callKind hKind, hStep]
  exact OpenExternal.OpenResultResolves.done

theorem openStepInstr_resolves_closed_of_prim_callKind_no_call
    {op : Assembly.PrimOp} {state state' : EVMState}
    {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = none)
    (hStep : Assembly.Target.stepInstr (.prim op) state = .ok state') :
    OpenExternal.OpenResultResolves
      (openStepInstr (.prim op) state) [] (.ok state') := by
  rw [openStepInstr_of_prim_callKind_no_call hKind hCall, hStep]
  exact OpenExternal.OpenResultResolves.done

theorem openStepInstr_resolves_prim_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepInstr (.prim op) state)
      [{ site := call.site, response := response }]
      (.ok (EvmYul.EVM.State.incrPC (call.resume response))) := by
  rw [openStepInstr_of_prim_call hKind hCall]
  exact evmInstructionCallResult_resolves call response

end Target

end OpenAssembly
end Yul
end EvmCompiler
