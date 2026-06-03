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

theorem codeUsesCallCreate_false_of_emitInstr_no_call
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEmit : Assembly.emitInstr? program pc instr = some emitted) :
    codeUsesCallCreate (emitted.map Assembly.LocatedTarget.instr) = false := by
  cases instr with
  | label name =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      simp [codeUsesCallCreate, instrUsesCallCreate]
  | prim op =>
      simp [Assembly.emitInstr?, Assembly.Instr.usesCallCreate] at hEmit hNoInstr
      subst emitted
      simp [codeUsesCallCreate, instrUsesCallCreate, hNoInstr]
  | push value =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      simp [codeUsesCallCreate, instrUsesCallCreate]
  | jump target =>
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.emitInstr?, hDest] at hEmit
      | some dest =>
          simp [Assembly.emitInstr?, hDest] at hEmit
          subst emitted
          simp [codeUsesCallCreate, instrUsesCallCreate]
  | jumpi target =>
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.emitInstr?, hDest] at hEmit
      | some dest =>
          simp [Assembly.emitInstr?, hDest] at hEmit
          subst emitted
          simp [codeUsesCallCreate, instrUsesCallCreate]

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

theorem openRunListResult_emitInstr_prim_call
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {emitted : List Assembly.LocatedTarget} {state : EVMState}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEmit : Assembly.emitInstr? program pc (.prim op) = some emitted)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves
      (openRunListResult (emitted.map Assembly.LocatedTarget.instr) state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  simp [Assembly.emitInstr?] at hEmit
  subst emitted
  simpa using openRunListResult_single_prim_call hKind hCall response

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

theorem openRunNResult_zero (program : Assembly.Program) (state : EVMState) :
    openRunNResult program 0 state =
      .done (.ok (.running state)) := by
  rfl

theorem openRunNResult_succ
    (program : Assembly.Program) (fuel : Nat) (state : EVMState) :
    openRunNResult program (fuel + 1) state =
      OpenExternal.OpenResult.bind (openStepResult program state)
        (fun result =>
          match result with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt))) := by
  rfl

theorem openRunNResult_resolves_step_running
    {program : Assembly.Program} {fuel : Nat} {state mid : EVMState}
    {headTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hStep :
      OpenExternal.OpenResultResolves (openStepResult program state)
        headTrace (.ok (.running mid)))
    (hRest :
      OpenExternal.OpenResultResolves (openRunNResult program fuel mid)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      (headTrace ++ tailTrace) result := by
  rw [openRunNResult_succ]
  exact OpenExternal.OpenResultResolves.bind_ok hStep hRest

theorem openRunNResult_resolves_step_halted
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {headTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    (hStep :
      OpenExternal.OpenResultResolves (openStepResult program state)
        headTrace (.ok (.halted halt))) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      headTrace (.ok (.halted halt)) := by
  rw [openRunNResult_succ]
  have hDone :
      OpenExternal.OpenResultResolves
        ((match Assembly.StepResult.halted halt with
          | .running state' => openRunNResult program fuel state'
          | .halted halt => .done (.ok (.halted halt))) :
          OpenExternal.OpenResult EVMException Assembly.StepResult)
        [] (.ok (.halted halt)) :=
    OpenExternal.OpenResultResolves.done
  simpa using
    (OpenExternal.OpenResultResolves.bind_ok
      (source := openStepResult program state)
      (next := fun stepResult =>
        match stepResult with
        | .running state' => openRunNResult program fuel state'
        | .halted halt => .done (.ok (.halted halt)))
      (left := headTrace) (right := [])
      (value := Assembly.StepResult.halted halt)
      (result := (.ok (.halted halt) :
        Except EVMException Assembly.StepResult))
      hStep hDone)

theorem openStepResult_resolves_closed_of_emitCurrent_no_callCreate
    {program : Assembly.Program} {state : EVMState}
    {code : List Assembly.TargetInstr} {result : Assembly.StepResult}
    (hEmit : Assembly.emitCurrent? program state = some code)
    (hCode : Target.codeUsesCallCreate code = false)
    (hStep : Assembly.Compiled.stepResult program state = .ok result) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [] (.ok result) := by
  unfold openStepResult
  rw [hEmit]
  unfold Assembly.Compiled.stepResult at hStep
  rw [hEmit] at hStep
  exact Target.openRunListResult_resolves_closed_of_no_callCreate hCode hStep

theorem codeUsesCallCreate_false_of_current_no_call
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr} {code : List Assembly.TargetInstr}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEmit : Assembly.emitCurrent? program state = some code) :
    Target.codeUsesCallCreate code = false := by
  unfold Assembly.emitCurrent? at hEmit
  rw [hAt] at hEmit
  cases hEmitInstr : Assembly.emitInstr? program pc instr with
  | none =>
      simp [hEmitInstr] at hEmit
  | some emitted =>
      simp [hEmitInstr] at hEmit
      subst code
      exact
        Target.codeUsesCallCreate_false_of_emitInstr_no_call
          hNoInstr hEmitInstr

theorem openStepResult_emitCurrent_single_prim_call
    {program : Assembly.Program} {state : EVMState} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEmit : Assembly.emitCurrent? program state =
      some [Assembly.TargetInstr.prim op])
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  unfold openStepResult
  rw [hEmit]
  exact Target.openRunListResult_single_prim_call hKind hCall response

theorem openStepResult_current_prim_call
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (openStepResult program state)
      [{ site := call.site, response := response }]
      (.ok
        (.running (EvmYul.EVM.State.incrPC (call.resume response)))) := by
  have hEmit :
      Assembly.emitCurrent? program state =
        some [Assembly.TargetInstr.prim op] := by
    simp [Assembly.emitCurrent?, hAt, Assembly.emitInstr?]
  exact
    openStepResult_emitCurrent_single_prim_call
      (op := op) hEmit hKind hCall response

theorem openRunNResult_current_prim_call_continue
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse)
    (hRest :
      OpenExternal.OpenResultResolves
        (openRunNResult program fuel
          (EvmYul.EVM.State.incrPC (call.resume response)))
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (openRunNResult program (fuel + 1) state)
      ({ site := call.site, response := response } :: tailTrace) result := by
  have hStep :=
    openStepResult_current_prim_call hAt hKind hCall response
  simpa using
    openRunNResult_resolves_step_running
      (fuel := fuel) hStep hRest

inductive OpenTraceResult (program : Assembly.Program) :
    Nat → EVMState → OpenExternal.OpenTrace → Assembly.StepResult → Prop where
  | done (state : EVMState) :
      OpenTraceResult program 0 state [] (.running state)
  | stepRunning
      {fuel : Nat} {state mid : EVMState}
      {headTrace tailTrace : OpenExternal.OpenTrace}
      {result : Assembly.StepResult}
      (hStep :
        OpenExternal.OpenResultResolves (openStepResult program state)
          headTrace (.ok (.running mid)))
      (hRest : OpenTraceResult program fuel mid tailTrace result) :
      OpenTraceResult program (fuel + 1) state
        (headTrace ++ tailTrace) result
  | stepHalted
      {fuel : Nat} {state : EVMState}
      {headTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
      (hStep :
        OpenExternal.OpenResultResolves (openStepResult program state)
          headTrace (.ok (.halted halt))) :
      OpenTraceResult program (fuel + 1) state headTrace (.halted halt)

namespace OpenTraceResult

theorem resolves
    {program : Assembly.Program} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hTrace : OpenTraceResult program fuel state trace result) :
    OpenExternal.OpenResultResolves (openRunNResult program fuel state)
      trace (.ok result) := by
  induction hTrace with
  | done state =>
      exact OpenExternal.OpenResultResolves.done
  | stepRunning hStep _hRest ih =>
      exact openRunNResult_resolves_step_running hStep ih
  | stepHalted hStep =>
      exact openRunNResult_resolves_step_halted hStep

theorem current_prim_call_continue
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {op : Assembly.PrimOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse)
    (hRest :
      OpenTraceResult program fuel
        (EvmYul.EVM.State.incrPC (call.resume response))
        tailTrace result) :
    OpenTraceResult program (fuel + 1) state
      ({ site := call.site, response := response } :: tailTrace) result := by
  have hStep :=
    openStepResult_current_prim_call hAt hKind hCall response
  simpa using OpenTraceResult.stepRunning hStep hRest

theorem current_no_call_running_continue
    {program : Assembly.Program} {state mid : EVMState}
    {fuel : Nat} {code : List Assembly.TargetInstr}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hEmit : Assembly.emitCurrent? program state = some code)
    (hCode : Target.codeUsesCallCreate code = false)
    (hStep :
      Assembly.Compiled.stepResult program state = .ok (.running mid))
    (hRest : OpenTraceResult program fuel mid tailTrace result) :
    OpenTraceResult program (fuel + 1) state tailTrace result := by
  have hOpenStep :=
    openStepResult_resolves_closed_of_emitCurrent_no_callCreate
      hEmit hCode hStep
  simpa using OpenTraceResult.stepRunning hOpenStep hRest

theorem current_no_call_halted
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {code : List Assembly.TargetInstr} {halt : Assembly.Halt}
    (hEmit : Assembly.emitCurrent? program state = some code)
    (hCode : Target.codeUsesCallCreate code = false)
    (hStep :
      Assembly.Compiled.stepResult program state = .ok (.halted halt)) :
    OpenTraceResult program (fuel + 1) state [] (.halted halt) := by
  have hOpenStep :=
    openStepResult_resolves_closed_of_emitCurrent_no_callCreate
      hEmit hCode hStep
  exact OpenTraceResult.stepHalted hOpenStep

theorem current_no_call_running_continue_of_current_instr
    {program : Assembly.Program} {state mid : EVMState}
    {fuel : Nat} {pc : Nat} {instr : Assembly.Instr}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hStep :
      Assembly.Compiled.stepResult program state = .ok (.running mid))
    (hRest : OpenTraceResult program fuel mid tailTrace result) :
    OpenTraceResult program (fuel + 1) state tailTrace result := by
  cases hEmit : Assembly.emitCurrent? program state with
  | none =>
      unfold Assembly.Compiled.stepResult at hStep
      rw [hEmit] at hStep
      cases hStep
  | some code =>
      have hCode :
          Target.codeUsesCallCreate code = false :=
        codeUsesCallCreate_false_of_current_no_call hAt hNoInstr hEmit
      exact
        current_no_call_running_continue hEmit hCode hStep hRest

theorem current_no_call_halted_of_current_instr
    {program : Assembly.Program} {state : EVMState}
    {fuel : Nat} {pc : Nat} {instr : Assembly.Instr} {halt : Assembly.Halt}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hStep :
      Assembly.Compiled.stepResult program state = .ok (.halted halt)) :
    OpenTraceResult program (fuel + 1) state [] (.halted halt) := by
  cases hEmit : Assembly.emitCurrent? program state with
  | none =>
      unfold Assembly.Compiled.stepResult at hStep
      rw [hEmit] at hStep
      cases hStep
  | some code =>
      have hCode :
          Target.codeUsesCallCreate code = false :=
        codeUsesCallCreate_false_of_current_no_call hAt hNoInstr hEmit
      exact current_no_call_halted hEmit hCode hStep

end OpenTraceResult

end Compiled

inductive OpenBlockTraceResult
    (program : Assembly.Program) (target : Assembly.TargetProgram) :
    Nat → EVMState → OpenExternal.OpenTrace → Assembly.StepResult → Prop where
  | done (state : EVMState) :
      OpenBlockTraceResult program target 0 state [] (.running state)
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
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        OpenExternal.OpenResultResolves
          (Target.openRunListResult (emitted.map Assembly.LocatedTarget.instr)
            state)
          trace (.ok (.running mid)))
      (hRest : OpenBlockTraceResult program target fuel mid tailTrace result) :
      OpenBlockTraceResult program target (fuel + 1) state
        (trace ++ tailTrace) result
  | stepHalted
      {fuel : Nat} {state : EVMState}
      {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
      {pc : Nat} {instr : Assembly.Instr}
      {emitted before after : List Assembly.LocatedTarget}
      (hAt :
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr))
      (hEmit : Assembly.emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        OpenExternal.OpenResultResolves
          (Target.openRunListResult (emitted.map Assembly.LocatedTarget.instr)
            state)
          trace (.ok (.halted halt))) :
      OpenBlockTraceResult program target (fuel + 1) state trace
        (.halted halt)

namespace OpenBlockTraceResult

theorem emitCurrent?_of_instrAt_emit
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted) :
    Assembly.emitCurrent? program state =
      some (emitted.map Assembly.LocatedTarget.instr) := by
  simp [Assembly.emitCurrent?, hAt, hEmit]

theorem openStepResult_resolves_of_emit
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hRun :
      OpenExternal.OpenResultResolves
        (Target.openRunListResult (emitted.map Assembly.LocatedTarget.instr)
          state)
        trace (.ok result)) :
    OpenExternal.OpenResultResolves
      (Compiled.openStepResult program state) trace (.ok result) := by
  have hCurrent := emitCurrent?_of_instrAt_emit hAt hEmit
  unfold Compiled.openStepResult
  rw [hCurrent]
  exact hRun

theorem to_compiled_trace
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hTrace : OpenBlockTraceResult program target fuel state trace result) :
    Compiled.OpenTraceResult program fuel state trace result := by
  induction hTrace with
  | done state =>
      exact Compiled.OpenTraceResult.done state
  | stepRunning hAt hEmit _hTargetBlock hRun _hRest ih =>
      exact
        Compiled.OpenTraceResult.stepRunning
          (openStepResult_resolves_of_emit hAt hEmit hRun) ih
  | stepHalted hAt hEmit _hTargetBlock hRun =>
      exact
        Compiled.OpenTraceResult.stepHalted
          (openStepResult_resolves_of_emit hAt hEmit hRun)

theorem resolves_compiled
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {state : EVMState} {trace : OpenExternal.OpenTrace}
    {result : Assembly.StepResult}
    (hTrace : OpenBlockTraceResult program target fuel state trace result) :
    OpenExternal.OpenResultResolves
      (Compiled.openRunNResult program fuel state)
      trace (.ok result) :=
  (to_compiled_trace hTrace).resolves

theorem current_prim_call_continue
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {state : EVMState} {fuel : Nat}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit : Assembly.emitInstr? program pc (.prim op) = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse)
    (hRest :
      OpenBlockTraceResult program target fuel
        (EvmYul.EVM.State.incrPC (call.resume response))
        tailTrace result) :
    OpenBlockTraceResult program target (fuel + 1) state
      ({ site := call.site, response := response } :: tailTrace) result := by
  have hRun :
      OpenExternal.OpenResultResolves
        (Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        [{ site := call.site, response := response }]
        (.ok (.running
          (EvmYul.EVM.State.incrPC (call.resume response)))) :=
    Target.openRunListResult_emitInstr_prim_call
      hEmit hKind hCall response
  simpa using
    OpenBlockTraceResult.stepRunning hAt hEmit hTargetBlock hRun hRest

theorem current_no_call_running_continue
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {state mid : EVMState} {fuel : Nat}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {tailTrace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hRun :
      Assembly.Target.runListResult
        (emitted.map Assembly.LocatedTarget.instr) state =
        .ok (.running mid))
    (hRest : OpenBlockTraceResult program target fuel mid tailTrace result) :
    OpenBlockTraceResult program target (fuel + 1) state tailTrace result := by
  have hCode :
      Target.codeUsesCallCreate
        (emitted.map Assembly.LocatedTarget.instr) = false :=
    Target.codeUsesCallCreate_false_of_emitInstr_no_call hNoInstr hEmit
  have hOpenRun :
      OpenExternal.OpenResultResolves
        (Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        [] (.ok (.running mid)) :=
    Target.openRunListResult_resolves_closed_of_no_callCreate hCode hRun
  simpa using
    OpenBlockTraceResult.stepRunning hAt hEmit hTargetBlock hOpenRun hRest

theorem current_no_call_halted
    {program : Assembly.Program} {target : Assembly.TargetProgram}
    {state : EVMState} {fuel : Nat}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {halt : Assembly.Halt}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hRun :
      Assembly.Target.runListResult
        (emitted.map Assembly.LocatedTarget.instr) state =
        .ok (.halted halt)) :
    OpenBlockTraceResult program target (fuel + 1) state [] (.halted halt) := by
  have hCode :
      Target.codeUsesCallCreate
        (emitted.map Assembly.LocatedTarget.instr) = false :=
    Target.codeUsesCallCreate_false_of_emitInstr_no_call hNoInstr hEmit
  have hOpenRun :
      OpenExternal.OpenResultResolves
        (Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        [] (.ok (.halted halt)) :=
    Target.openRunListResult_resolves_closed_of_no_callCreate hCode hRun
  exact
    OpenBlockTraceResult.stepHalted hAt hEmit hTargetBlock hOpenRun

end OpenBlockTraceResult

end OpenAssembly
end Yul
end EvmCompiler
