import EvmCompiler.Yul.OpenExternal
import EvmCompiler.Assembly.Accepted
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

def instrUsesCallCreate : Assembly.TargetInstr → Bool
  | .prim op => op.isCallCreate
  | _ => false

def codeUsesCallCreate (code : List Assembly.TargetInstr) : Bool :=
  code.any instrUsesCallCreate

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

theorem prim_haltKind?_none_of_callKind
    {op : Assembly.PrimOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind) :
    op.haltKind? = none := by
  cases op <;>
    simp [Assembly.PrimOp.toEVM, OpenExternal.CallKind.ofEVMOperation?,
      Assembly.PrimOp.haltKind?] at hKind ⊢

theorem callKind_none_of_not_isCallCreate
    {op : Assembly.PrimOp} (hNo : op.isCallCreate = false) :
    OpenExternal.CallKind.ofEVMOperation? op.toEVM = none := by
  cases op <;>
    simp [Assembly.PrimOp.isCallCreate, Assembly.PrimOp.toEVM,
      OpenExternal.CallKind.ofEVMOperation?] at hNo ⊢

def stepResultAfter (instr : Assembly.TargetInstr) (state : EVMState) :
    Assembly.StepResult :=
  match instr.haltKind? with
  | some kind =>
      .halted { kind := kind, state := state, output := kind.output state }
  | none =>
      .running state

def openStepInstrResult (instr : Assembly.TargetInstr) (state : EVMState) :
    OpenExternal.OpenResult EVMException Assembly.StepResult :=
  OpenExternal.OpenResult.bind (openStepInstr instr state)
    (fun state' => .done (.ok (stepResultAfter instr state')))

theorem openStepInstr_of_no_callCreate
    {instr : Assembly.TargetInstr} {state : EVMState}
    (hNo : instrUsesCallCreate instr = false) :
    openStepInstr instr state = .done (Assembly.Target.stepInstr instr state) := by
  cases instr with
  | prim op =>
      simp [instrUsesCallCreate] at hNo
      have hKind := callKind_none_of_not_isCallCreate hNo
      simp [openStepInstr, hKind]
  | push32 value =>
      simp [openStepInstr]
  | jump =>
      simp [openStepInstr]
  | jumpi =>
      simp [openStepInstr]
  | jumpdest =>
      simp [openStepInstr]

theorem openStepInstrResult_resolves_closed_of_openStepInstr_done
    {instr : Assembly.TargetInstr} {state : EVMState}
    {result : Assembly.StepResult}
    (hOpen :
      openStepInstr instr state = .done (Assembly.Target.stepInstr instr state))
    (hStep : Assembly.Target.stepInstrResult instr state = .ok result) :
    OpenExternal.OpenResultResolves
      (openStepInstrResult instr state) [] (.ok result) := by
  unfold openStepInstrResult
  rw [hOpen]
  unfold Assembly.Target.stepInstrResult at hStep
  cases hRaw : Assembly.Target.stepInstr instr state with
  | error err =>
      rw [hRaw] at hStep
      cases hStep
  | ok state' =>
      rw [hRaw] at hStep
      have hResult : stepResultAfter instr state' = result := by
        cases hKind : instr.haltKind? with
        | none =>
            simpa [stepResultAfter, hKind] using hStep
        | some kind =>
            simpa [stepResultAfter, hKind] using hStep
      simpa [OpenExternal.OpenResult.bind, hResult] using
        (OpenExternal.OpenResultResolves.done :
          OpenExternal.OpenResultResolves
            ((.done (.ok result)) :
              OpenExternal.OpenResult EVMException Assembly.StepResult)
            [] (.ok result))

theorem openStepInstrResult_resolves_closed_of_no_callCreate
    {instr : Assembly.TargetInstr} {state : EVMState}
    {result : Assembly.StepResult}
    (hNo : instrUsesCallCreate instr = false)
    (hStep : Assembly.Target.stepInstrResult instr state = .ok result) :
    OpenExternal.OpenResultResolves
      (openStepInstrResult instr state) [] (.ok result) := by
  exact
    openStepInstrResult_resolves_closed_of_openStepInstr_done
      (openStepInstr_of_no_callCreate hNo) hStep

theorem openStepInstrResult_resolves_prim_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepInstrResult (.prim op) state)
      [{ site := call.site, response := response }]
    (.ok (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  unfold openStepInstrResult
  rw [openStepInstr_of_prim_call hKind hCall]
  unfold evmInstructionCallResult
  have hHalt : (Assembly.TargetInstr.prim op).haltKind? = none := by
    simpa [Assembly.TargetInstr.haltKind?] using
      prim_haltKind?_none_of_callKind hKind
  refine OpenExternal.OpenResultResolves.call ?_
  simpa [OpenExternal.OpenResult.bind, stepResultAfter, hHalt] using
    (OpenExternal.OpenResultResolves.done :
      OpenExternal.OpenResultResolves
        (.done
          (.ok
            (Assembly.StepResult.running
              (EvmYul.EVM.State.incrPC (call.resume response)))))
        []
        (.ok
          (Assembly.StepResult.running
            (EvmYul.EVM.State.incrPC (call.resume response)))))

def openRunListResult : List Assembly.TargetInstr → EVMState →
    OpenExternal.OpenResult EVMException Assembly.StepResult
  | [], state => .done (.ok (.running state))
  | instr :: rest, state =>
      OpenExternal.OpenResult.bind (openStepInstrResult instr state)
        (fun result =>
          match result with
          | .running state' => openRunListResult rest state'
          | .halted halt => .done (.ok (.halted halt)))

theorem openRunListResult_nil (state : EVMState) :
    openRunListResult [] state = .done (.ok (.running state)) := by
  rfl

theorem openRunListResult_cons
    (instr : Assembly.TargetInstr) (rest : List Assembly.TargetInstr)
    (state : EVMState) :
    openRunListResult (instr :: rest) state =
      OpenExternal.OpenResult.bind (openStepInstrResult instr state)
        (fun result =>
          match result with
          | .running state' => openRunListResult rest state'
          | .halted halt => .done (.ok (.halted halt))) := by
  rfl

theorem all_false_of_codeUsesCallCreate_false
    {code : List Assembly.TargetInstr}
    (hCode : codeUsesCallCreate code = false) :
    ∀ instr ∈ code, instrUsesCallCreate instr = false := by
  simpa [codeUsesCallCreate] using hCode

theorem openRunListResult_resolves_closed_of_forall_no_callCreate :
    ∀ {code : List Assembly.TargetInstr} {state : EVMState}
      {result : Assembly.StepResult},
      (∀ instr ∈ code, instrUsesCallCreate instr = false) →
      Assembly.Target.runListResult code state = .ok result →
      OpenExternal.OpenResultResolves (openRunListResult code state)
        [] (.ok result) := by
  intro code
  induction code with
  | nil =>
      intro state result _hNo hRun
      simp [Assembly.Target.runListResult] at hRun
      subst result
      exact OpenExternal.OpenResultResolves.done
  | cons instr rest ih =>
      intro state result hNo hRun
      have hInstrNo : instrUsesCallCreate instr = false := hNo instr (by simp)
      have hRestNo :
          ∀ restInstr ∈ rest, instrUsesCallCreate restInstr = false := by
        intro restInstr hMem
        exact hNo restInstr (by simp [hMem])
      rw [openRunListResult_cons]
      cases hStep : Assembly.Target.stepInstrResult instr state with
      | error err =>
          rw [Assembly.Target.runListResult, hStep] at hRun
          cases hRun
      | ok stepResult =>
          rw [Assembly.Target.runListResult, hStep] at hRun
          have hOpenStep :=
            openStepInstrResult_resolves_closed_of_no_callCreate
              hInstrNo hStep
          cases stepResult with
          | running mid =>
              have hRest := ih hRestNo hRun
              simpa using
                OpenExternal.OpenResultResolves.bind_ok
                  hOpenStep hRest
          | halted halt =>
              cases hRun
              have hDone :
                  OpenExternal.OpenResultResolves
                    ((.done (.ok (Assembly.StepResult.halted halt))) :
                      OpenExternal.OpenResult EVMException Assembly.StepResult)
                    [] (.ok (Assembly.StepResult.halted halt)) :=
                OpenExternal.OpenResultResolves.done
              simpa using
                OpenExternal.OpenResultResolves.bind_ok
                  hOpenStep hDone

theorem openRunListResult_resolves_closed_of_no_callCreate
    {code : List Assembly.TargetInstr} {state : EVMState}
    {result : Assembly.StepResult}
    (hCode : codeUsesCallCreate code = false)
    (hRun : Assembly.Target.runListResult code state = .ok result) :
    OpenExternal.OpenResultResolves (openRunListResult code state)
      [] (.ok result) := by
  exact
    openRunListResult_resolves_closed_of_forall_no_callCreate
      (all_false_of_codeUsesCallCreate_false hCode) hRun

theorem openRunListResult_single_prim_call
    {op : Assembly.PrimOp} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves
      (openRunListResult [Assembly.TargetInstr.prim op] state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  rw [openRunListResult_cons]
  have hStep :=
    openStepInstrResult_resolves_prim_call hKind hCall response
  have hRest :
      OpenExternal.OpenResultResolves
        (openRunListResult []
          (EvmYul.EVM.State.incrPC (call.resume response)))
        []
        (.ok
          (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
    exact OpenExternal.OpenResultResolves.done
  simpa [openRunListResult_nil] using
    OpenExternal.OpenResultResolves.bind_ok hStep hRest

def openStep (target : Assembly.TargetProgram) (state : EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  match target.fetch state.pc.toNat with
  | some instr => openStepInstr instr state
  | none => .done (.error .InvalidInstruction)

def openStepResult (target : Assembly.TargetProgram) (state : EVMState) :
    OpenExternal.OpenResult EVMException Assembly.StepResult :=
  match target.fetch state.pc.toNat with
  | some instr => openStepInstrResult instr state
  | none => .done (.error .InvalidInstruction)

def openRunNResult (target : Assembly.TargetProgram) :
    Nat → EVMState → OpenExternal.OpenResult EVMException Assembly.StepResult
  | 0, state => .done (.ok (.running state))
  | fuel + 1, state =>
      OpenExternal.OpenResult.bind (openStepResult target state)
        (fun result =>
          match result with
          | .running state' => openRunNResult target fuel state'
          | .halted halt => .done (.ok (.halted halt)))

end Target

namespace Compiled

def openStepResult (program : Assembly.Program) (state : EVMState) :
    OpenExternal.OpenResult EVMException Assembly.StepResult :=
  match Assembly.emitCurrent? program state with
  | some code => Target.openRunListResult code state
  | none => .done (.error .InvalidInstruction)

def openRunNResult (program : Assembly.Program) :
    Nat → EVMState → OpenExternal.OpenResult EVMException Assembly.StepResult
  | 0, state => .done (.ok (.running state))
  | fuel + 1, state =>
      OpenExternal.OpenResult.bind (openStepResult program state)
        (fun result =>
          match result with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt)))

end Compiled

end OpenAssembly
end Yul
end EvmCompiler
