import EvmCompiler.Yul.OpenAssembly
import EvmCompiler.Assembly.GasAware

/-!
Open gas-aware EVM execution for external CALL-family traces.

`Assembly.GasAware` proves the no-internal-CALL public spine against the closed
`EvmYul.EVM.X` runner.  For the CALL route we need the same gas/check/final
result shape, but CALL-family opcodes must suspend at the abstract
`OpenExternal.CallSite` boundary instead of entering the concrete EVM world.
-/

namespace EvmCompiler
namespace Yul
namespace OpenGasAware

abbrev Word := EvmYul.UInt256
abbrev EVMOp := EvmYul.Operation .EVM
abbrev EVMState := EvmYul.EVM.State
abbrev EVMException := EvmYul.EVM.ExecutionException
abbrev EVMResult := EvmYul.EVM.ExecutionResult EVMState

def gasChargedState (state : EVMState) (op : EVMOp) : EVMState :=
  let memoryState := Assembly.GasAware.memoryGasState state op
  { memoryState with
    gasAvailable :=
      memoryState.gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.C' memoryState op)
    execLength := memoryState.execLength + 1 }

def finishGasAwareCall
    (call : OpenExternal.OpenCall EVMState)
    (response : OpenExternal.CallResponse) : EVMState :=
  let resumed := call.resume response
  { resumed with gasAvailable := resumed.gasAvailable + response.returnedGas }

theorem uint256_add_toNat_of_lt_size {left right : Word}
    (hNoOverflow : left.toNat + right.toNat < EvmYul.UInt256.size) :
    (left + right).toNat = left.toNat + right.toNat := by
  cases left with
  | mk leftVal =>
      cases right with
      | mk rightVal =>
          unfold EvmYul.UInt256.toNat EvmYul.UInt256.size at hNoOverflow
          change
            (EvmYul.UInt256.add { val := leftVal } { val := rightVal }).toNat =
              leftVal.val + rightVal.val
          unfold EvmYul.UInt256.toNat EvmYul.UInt256.add
            EvmYul.UInt256.size
          simpa [Fin.val_add, Nat.mod_eq_of_lt hNoOverflow]

theorem finishGasAwareCall_incrPC_gasAvailable_toNat_of_no_overflow
    (call : OpenExternal.OpenCall EVMState)
    (response : OpenExternal.CallResponse)
    (hNoOverflow :
      (call.resume response).gasAvailable.toNat +
          response.returnedGas.toNat < EvmYul.UInt256.size) :
    (EvmYul.EVM.State.incrPC
        (finishGasAwareCall call response)).gasAvailable.toNat =
      (call.resume response).gasAvailable.toNat +
        response.returnedGas.toNat := by
  simp [finishGasAwareCall, EvmYul.EVM.State.incrPC,
    uint256_add_toNat_of_lt_size hNoOverflow]

theorem finishGasAwareCall_incrPC_tail_budget_of_no_overflow
    {tailGasBound : Nat}
    (call : OpenExternal.OpenCall EVMState)
    (response : OpenExternal.CallResponse)
    (hNoOverflow :
      (call.resume response).gasAvailable.toNat +
          response.returnedGas.toNat < EvmYul.UInt256.size)
    (hTail :
      tailGasBound ≤
        (call.resume response).gasAvailable.toNat +
          response.returnedGas.toNat) :
    tailGasBound ≤
      (EvmYul.EVM.State.incrPC
        (finishGasAwareCall call response)).gasAvailable.toNat := by
  rw [finishGasAwareCall_incrPC_gasAvailable_toNat_of_no_overflow
    call response hNoOverflow]
  exact hTail

theorem evmCallSite?_gasChargedState
    (state : EVMState) (op : EVMOp) (kind : OpenExternal.CallKind) :
    OpenExternal.CallKind.evmCallSite? (gasChargedState state op) kind =
      OpenExternal.CallKind.evmCallSite? state kind := by
  cases hOperands : kind.evmOperands? state.stack with
  | none =>
      simp [OpenExternal.CallKind.evmCallSite?, gasChargedState,
        Assembly.GasAware.memoryGasState, hOperands]
  | some pair =>
      rcases pair with ⟨rest, operands⟩
      simp [OpenExternal.CallKind.evmCallSite?, gasChargedState,
        Assembly.GasAware.memoryGasState, hOperands,
        OpenExternal.CallContext.ofEVMState,
        OpenExternal.CallContext.callSite,
        OpenExternal.CallContext.calldata,
        OpenExternal.CallContext.caller,
        OpenExternal.CallContext.recipient,
        OpenExternal.CallContext.transferValue,
        OpenExternal.CallContext.apparentValue,
        OpenExternal.CallContext.effectivePermission]

theorem evmCallSite?_of_gasExecRel
    {full target : EVMState}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (kind : OpenExternal.CallKind) :
    OpenExternal.CallKind.evmCallSite? full kind =
      OpenExternal.CallKind.evmCallSite? target kind := by
  rw [hRel]
  cases hOperands : kind.evmOperands? target.stack with
  | none =>
      simp [OpenExternal.CallKind.evmCallSite?, hOperands]
  | some pair =>
      rcases pair with ⟨rest, operands⟩
      simp [OpenExternal.CallKind.evmCallSite?, hOperands,
        OpenExternal.CallContext.ofEVMState,
        OpenExternal.CallContext.callSite,
        OpenExternal.CallContext.calldata,
        OpenExternal.CallContext.caller,
        OpenExternal.CallContext.recipient,
        OpenExternal.CallContext.transferValue,
        OpenExternal.CallContext.apparentValue,
        OpenExternal.CallContext.effectivePermission]

theorem evmCallSite?_gasChargedState_of_gasExecRel
    {full target : EVMState}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (op : EVMOp) (kind : OpenExternal.CallKind) :
    OpenExternal.CallKind.evmCallSite? (gasChargedState full op) kind =
      OpenExternal.CallKind.evmCallSite? target kind := by
  rw [evmCallSite?_gasChargedState]
  exact evmCallSite?_of_gasExecRel hRel kind

theorem evmOpenCall?_gasChargedState_site
    {state : EVMState} {op : EVMOp} {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call) :
    ∃ gasCall : OpenExternal.OpenCall EVMState,
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        some gasCall ∧
      gasCall.site = call.site := by
  unfold OpenExternal.CallKind.evmOpenCall? at hCall ⊢
  rw [evmCallSite?_gasChargedState]
  cases hSite : OpenExternal.CallKind.evmCallSite? state kind with
  | none =>
      simp [hSite] at hCall
  | some siteData =>
      rcases siteData with ⟨rest, site⟩
      simp [hSite] at hCall ⊢
      cases hCall
      rfl

theorem evmOpenCall?_gasChargedState_resume_gasExecRel
    {state : EVMState} {op : EVMOp} {kind : OpenExternal.CallKind}
    {call gasCall : OpenExternal.OpenCall EVMState}
    (hCall : OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (hGasCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        some gasCall)
    (response : OpenExternal.CallResponse) :
    Assembly.GasAware.GasExecRel
      (EvmYul.EVM.State.incrPC
        (finishGasAwareCall gasCall response))
      (EvmYul.EVM.State.incrPC (call.resume response)) := by
  unfold OpenExternal.CallKind.evmOpenCall? at hCall hGasCall
  rw [evmCallSite?_gasChargedState] at hGasCall
  cases hSite : OpenExternal.CallKind.evmCallSite? state kind with
  | none =>
      simp [hSite] at hCall
  | some siteData =>
      rcases siteData with ⟨rest, site⟩
      simp [hSite] at hCall hGasCall
      cases hCall
      cases hGasCall
      simp [finishGasAwareCall, gasChargedState,
        Assembly.GasAware.memoryGasState,
        OpenExternal.CallSite.finishShared,
        OpenExternal.ReturnWindow.finishMachine,
        EvmYul.MachineState.finishExternalCall,
        EvmYul.writeBytes,
        EvmYul.EVM.State.incrPC,
        Assembly.GasAware.GasExecRel]

theorem evmOpenCall?_gasChargedState_site_of_gasExecRel
    {full target : EVMState} {op : EVMOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hCall : OpenExternal.CallKind.evmOpenCall? target kind = some call) :
    ∃ gasCall : OpenExternal.OpenCall EVMState,
      OpenExternal.CallKind.evmOpenCall? (gasChargedState full op) kind =
        some gasCall ∧
      gasCall.site = call.site := by
  unfold OpenExternal.CallKind.evmOpenCall? at hCall ⊢
  rw [evmCallSite?_gasChargedState_of_gasExecRel hRel op]
  cases hSite : OpenExternal.CallKind.evmCallSite? target kind with
  | none =>
      simp [hSite] at hCall
  | some siteData =>
      rcases siteData with ⟨rest, site⟩
      simp [hSite] at hCall ⊢
      cases hCall
      rfl

theorem evmOpenCall?_gasChargedState_of_gasExecRel
    {full target : EVMState} {op : EVMOp}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hCall : OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (response : OpenExternal.CallResponse) :
    ∃ gasCall : OpenExternal.OpenCall EVMState,
      OpenExternal.CallKind.evmOpenCall? (gasChargedState full op) kind =
        some gasCall ∧
      gasCall.site = call.site ∧
      Assembly.GasAware.GasExecRel
        (EvmYul.EVM.State.incrPC
          (finishGasAwareCall gasCall response))
        (EvmYul.EVM.State.incrPC (call.resume response)) := by
  unfold OpenExternal.CallKind.evmOpenCall? at hCall ⊢
  rw [evmCallSite?_gasChargedState_of_gasExecRel hRel op]
  cases hSite : OpenExternal.CallKind.evmCallSite? target kind with
  | none =>
      simp [hSite] at hCall
  | some siteData =>
      rcases siteData with ⟨rest, site⟩
      simp [hSite] at hCall ⊢
      cases hCall
      constructor
      · rfl
      · rw [hRel]
        simp [finishGasAwareCall, gasChargedState,
          Assembly.GasAware.memoryGasState,
          OpenExternal.CallSite.finishShared,
          OpenExternal.ReturnWindow.finishMachine,
          EvmYul.MachineState.finishExternalCall,
          EvmYul.writeBytes,
          EvmYul.EVM.State.incrPC,
          Assembly.GasAware.GasExecRel]

theorem evmOpenCall?_gasChargedState_resume_gasExecRel_of_gasExecRel
    {full target : EVMState} {op : EVMOp}
    {kind : OpenExternal.CallKind}
    {call gasCall : OpenExternal.OpenCall EVMState}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hCall : OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hGasCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState full op) kind =
        some gasCall)
    (response : OpenExternal.CallResponse) :
    Assembly.GasAware.GasExecRel
      (EvmYul.EVM.State.incrPC
        (finishGasAwareCall gasCall response))
      (EvmYul.EVM.State.incrPC (call.resume response)) := by
  obtain ⟨gasCall', hGasCall', _hSite, hPostRel⟩ :=
    evmOpenCall?_gasChargedState_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall response
  rw [hGasCall] at hGasCall'
  cases hGasCall'
  exact hPostRel

def evmGasAwareCallResult
    (call : OpenExternal.OpenCall EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  .call
    { site := call.site
      resume := fun response =>
        .done
          (.ok
            (EvmYul.EVM.State.incrPC
              (finishGasAwareCall call response))) }

theorem evmGasAwareCallResult_resolves
    (call : OpenExternal.OpenCall EVMState)
    (response : OpenExternal.CallResponse) :
    OpenExternal.OpenResultResolves (evmGasAwareCallResult call)
      [OpenExternal.OpenEvent.call call.site response]
      (.ok
        (EvmYul.EVM.State.incrPC
          (finishGasAwareCall call response))) := by
  unfold evmGasAwareCallResult
  exact OpenExternal.OpenResultResolves.call
    OpenExternal.OpenResultResolves.done

def staticWriteSensitive? (op : EVMOp) (stack : EvmYul.Stack Word) : Bool :=
  op == EvmYul.Operation.CREATE ||
    op == EvmYul.Operation.CREATE2 ||
    op == EvmYul.Operation.SSTORE ||
    op == EvmYul.Operation.SELFDESTRUCT ||
    op == EvmYul.Operation.LOG0 ||
    op == EvmYul.Operation.LOG1 ||
    op == EvmYul.Operation.LOG2 ||
    op == EvmYul.Operation.LOG3 ||
    op == EvmYul.Operation.LOG4 ||
    op == EvmYul.Operation.TSTORE ||
    (op == EvmYul.Operation.CALL &&
      stack[2]? != some (⟨0⟩ : Word))

theorem uint256_beq_eq_true_iff_eq (left right : Word) :
    (left == right) = true ↔ left = right := by
  cases left with
  | mk leftVal =>
      cases right with
      | mk rightVal =>
          constructor
          · intro hEq
            have hVal : leftVal = rightVal := eq_of_beq hEq
            cases hVal
            rfl
          · intro hEq
            cases hEq
            change (leftVal == leftVal) = true
            exact BEq.rfl

theorem optionWord_bne_zero_true_iff_ne
    (value : Option Word) :
    (value != some (⟨0⟩ : Word)) = true ↔
      value ≠ some (⟨0⟩ : Word) := by
  cases value with
  | none =>
      constructor
      · intro _ hEq
        cases hEq
      · intro _
        rfl
  | some word =>
      constructor
      · intro hNe hEq
        cases hEq
        change (! ((⟨0⟩ : Word) == (⟨0⟩ : Word))) = true at hNe
        have hSelf :
            ((⟨0⟩ : Word) == (⟨0⟩ : Word)) = true :=
          (uint256_beq_eq_true_iff_eq
            (⟨0⟩ : Word) (⟨0⟩ : Word)).2 rfl
        rw [hSelf] at hNe
        cases hNe
      · intro hNe
        change (! (word == (⟨0⟩ : Word))) = true
        cases hBeq : (word == (⟨0⟩ : Word))
        · rfl
        · have hEq :=
            (uint256_beq_eq_true_iff_eq word (⟨0⟩ : Word)).1 hBeq
          exact False.elim (hNe (by cases hEq; rfl))

theorem staticWriteSensitive?_true
    {op : EVMOp} {stack : EvmYul.Stack Word}
    (hStatic : staticWriteSensitive? op stack = true) :
    Assembly.GasAware.staticWriteSensitive op stack := by
  simpa [staticWriteSensitive?, Assembly.GasAware.staticWriteSensitive,
    or_assoc, optionWord_bne_zero_true_iff_ne]
    using hStatic

def xStepException?
    (validJumps : Array Word) (state : EVMState) (op : EVMOp) :
    Option EVMException :=
  if state.gasAvailable.toNat <
      EvmYul.EVM.memoryExpansionCost state op then
    some (.OutOfGass : EVMException)
  else
    let memoryState := Assembly.GasAware.memoryGasState state op
    let cost := EvmYul.EVM.C' memoryState op
    if memoryState.gasAvailable.toNat < cost then
      some (.OutOfGass : EVMException)
    else if EvmYul.EVM.δ op = none then
      some (.InvalidInstruction : EVMException)
    else if memoryState.stack.length < (EvmYul.EVM.δ op).getD 0 then
      some (.StackUnderflow : EVMException)
    else if op = EvmYul.Operation.JUMP ∧
        EvmYul.EVM.X.notIn memoryState.stack[0]? validJumps = true then
      some (.BadJumpDestination : EVMException)
    else if op = EvmYul.Operation.JUMPI ∧
        memoryState.stack[1]? ≠ some (⟨0⟩ : Word) ∧
          EvmYul.EVM.X.notIn memoryState.stack[0]? validJumps = true then
      some (.BadJumpDestination : EVMException)
    else if op = EvmYul.Operation.RETURNDATACOPY ∧
        memoryState.returnData.size <
          (memoryState.stack.getD 1 (⟨0⟩ : Word)).toNat +
            (memoryState.stack.getD 2 (⟨0⟩ : Word)).toNat then
      some (.InvalidMemoryAccess : EVMException)
    else if 1024 <
        memoryState.stack.length - (EvmYul.EVM.δ op).getD 0 +
          (EvmYul.EVM.α op).getD 0 then
      some (.StackOverflow : EVMException)
    else if memoryState.executionEnv.perm = false ∧
        staticWriteSensitive? op memoryState.stack = true then
      some (.StaticModeViolation : EVMException)
    else if op = EvmYul.Operation.SSTORE ∧
        memoryState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
      some (.OutOfGass : EVMException)
    else if op.isCreate = true ∧
        (⟨49152⟩ : Word) < memoryState.stack.getD 2 (⟨0⟩ : Word) then
      some (.OutOfGass : EVMException)
    else
      none

theorem xStepException?_none_of_raw_checks
    {validJumps : Array Word} {state : EVMState} {op : EVMOp}
    (hChecks :
      Assembly.GasAware.XStepRawChecksPass validJumps state op) :
    xStepException? validJumps state op = none := by
  let memoryState := Assembly.GasAware.memoryGasState state op
  have hReturnData :
      ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
        memoryState.returnData.size <
          (memoryState.stack[1]?.getD (⟨0⟩ : Word)).toNat +
            (memoryState.stack[2]?.getD (⟨0⟩ : Word)).toNat) := by
    intro hBad
    exact hChecks.returnData (by
      simpa [memoryState] using hBad)
  have hStatic :
      ¬ (memoryState.executionEnv.perm = false ∧
        staticWriteSensitive? op memoryState.stack = true) := by
    intro hBad
    exact hChecks.staticMode
      ⟨(by
          rw [hBad.1]
          simp),
        (by
          simpa [Assembly.GasAware.staticWriteSensitive, or_assoc,
            memoryState] using
            staticWriteSensitive?_true hBad.2)⟩
  have hCreate :
      ¬ (op.isCreate = true ∧
        (⟨49152⟩ : Word) <
          memoryState.stack[2]?.getD (⟨0⟩ : Word)) := by
    intro hBad
    exact hChecks.createSize (by
      simpa [memoryState] using hBad)
  simp [xStepException?, memoryState, hChecks.memoryGas,
    hChecks.dynamicGas, hChecks.delta, hChecks.stack, hChecks.jump,
    hChecks.jumpi, hReturnData, hChecks.stackOverflow, hStatic,
    hChecks.sstoreStipend, hCreate]

theorem xStepException?_none_of_step_checks
    {validJumps : Array Word} {state : EVMState} {op : EVMOp}
    (hChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op) :
    xStepException? validJumps state op = none :=
  xStepException?_none_of_raw_checks
    (Assembly.GasAware.XStepRawChecksPass.of_step_checks hChecks)

theorem xStepException?_none_or_outOfGas_of_nonGas_checks
    {validJumps : Array Word} {state : EVMState} {op : EVMOp}
    (hNonGas :
      Assembly.GasAware.XNonGasChecksPass validJumps state op) :
    xStepException? validJumps state op = none ∨
      xStepException? validJumps state op =
        some (.OutOfGass : EVMException) := by
  let memoryState := Assembly.GasAware.memoryGasState state op
  rcases hNonGas with
    ⟨hDelta, hStack, hJump, hJumpi, hReturnData, hOverflow, hStatic,
      hCreate⟩
  have hStackBad :
      ¬ (memoryState.stack.length < (EvmYul.EVM.δ op).getD 0) := by
    simpa [memoryState, Assembly.GasAware.memoryGasState] using
      (not_lt_of_ge hStack)
  have hJumpBad :
      ¬ (op = EvmYul.Operation.JUMP ∧
        EvmYul.EVM.X.notIn memoryState.stack[0]? validJumps = true) := by
    intro hBad
    rcases hBad with ⟨hOp, hBad⟩
    have hAllowed := hJump hOp
    unfold Assembly.GasAware.jumpTargetAllowed at hAllowed
    subst op
    cases hTarget : state.stack[0]? with
    | none =>
        simp [hTarget] at hAllowed
    | some target =>
        simp [hTarget] at hAllowed
        simp [memoryState, Assembly.GasAware.memoryGasState,
          EvmYul.EVM.X.notIn, EvmYul.EVM.X.belongs, hTarget, hAllowed]
          at hBad
  have hJumpiBad :
      ¬ (op = EvmYul.Operation.JUMPI ∧
        memoryState.stack[1]? ≠ some (⟨0⟩ : Word) ∧
          EvmYul.EVM.X.notIn memoryState.stack[0]? validJumps = true) := by
    intro hBad
    rcases hBad with ⟨hOp, hCond, hBad⟩
    have hCond' : state.stack[1]? ≠ some (⟨0⟩ : Word) := by
      simpa [memoryState, Assembly.GasAware.memoryGasState] using hCond
    have hAllowed := hJumpi hOp hCond'
    unfold Assembly.GasAware.jumpTargetAllowed at hAllowed
    subst op
    cases hTarget : state.stack[0]? with
    | none =>
        simp [hTarget] at hAllowed
    | some target =>
        simp [hTarget] at hAllowed
        simp [memoryState, Assembly.GasAware.memoryGasState,
          EvmYul.EVM.X.notIn, EvmYul.EVM.X.belongs, hTarget, hAllowed]
          at hBad
  have hReturnDataBad :
      ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
        memoryState.returnData.size <
          (memoryState.stack.getD 1 (⟨0⟩ : Word)).toNat +
            (memoryState.stack.getD 2 (⟨0⟩ : Word)).toNat) := by
    intro hBad
    exact (not_lt_of_ge (hReturnData hBad.1)) (by
      simpa [memoryState, Assembly.GasAware.memoryGasState] using hBad.2)
  have hOverflowBad :
      ¬ (1024 <
        memoryState.stack.length - (EvmYul.EVM.δ op).getD 0 +
          (EvmYul.EVM.α op).getD 0) := by
    simpa [memoryState, Assembly.GasAware.memoryGasState] using
      (not_lt_of_ge hOverflow)
  have hStaticBad :
      ¬ (memoryState.executionEnv.perm = false ∧
        staticWriteSensitive? op memoryState.stack = true) := by
    intro hBad
    rcases hBad with ⟨hPerm, hWrite⟩
    have hPermFalse : state.executionEnv.perm = false := by
      simpa [memoryState, Assembly.GasAware.memoryGasState] using hPerm
    exact (hStatic hPermFalse) (by
      simpa [memoryState, Assembly.GasAware.memoryGasState] using
        staticWriteSensitive?_true hWrite)
  have hCreateBad :
      ¬ (op.isCreate = true ∧
        (⟨49152⟩ : Word) <
          memoryState.stack.getD 2 (⟨0⟩ : Word)) := by
    intro hBad
    have hCreateLe :
        state.stack.getD 2 (⟨0⟩ : Word) ≤ (⟨49152⟩ : Word) :=
      hCreate hBad.1
    have hTooLarge0 := hBad.2
    simp [memoryState, Assembly.GasAware.memoryGasState] at hTooLarge0
    have hTooLarge :
        (⟨49152⟩ : Word).val <
          (state.stack[2]?.getD (⟨0⟩ : Word)).val := by
      change (⟨49152⟩ : Word).val <
        (state.stack[2]?.getD (⟨0⟩ : Word)).val at hTooLarge0
      exact hTooLarge0
    have hCreateLe0 := hCreateLe
    have hCreateVal :
        (state.stack[2]?.getD (⟨0⟩ : Word)).val ≤
          (⟨49152⟩ : Word).val := by
      change (state.stack[2]?.getD (⟨0⟩ : Word)).val ≤
        (⟨49152⟩ : Word).val at hCreateLe0
      exact hCreateLe0
    exact (not_lt_of_ge hCreateVal) hTooLarge
  by_cases hMemory :
      state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state op
  · exact Or.inr (by simp [xStepException?, hMemory])
  · by_cases hDynamic :
        memoryState.gasAvailable.toNat <
          EvmYul.EVM.C' memoryState op
    · exact Or.inr (by
        simp [xStepException?, memoryState, hMemory, hDynamic])
    · have hDynamic' :
          ¬ ((Assembly.GasAware.memoryGasState state op).gasAvailable.toNat <
            EvmYul.EVM.C' (Assembly.GasAware.memoryGasState state op) op) := by
        simpa [memoryState] using hDynamic
      have hStackBad' :
          ¬ ((Assembly.GasAware.memoryGasState state op).stack.length <
            (EvmYul.EVM.δ op).getD 0) := by
        simpa [memoryState] using hStackBad
      have hJumpBad' :
          ¬ (op = EvmYul.Operation.JUMP ∧
            EvmYul.EVM.X.notIn
              (Assembly.GasAware.memoryGasState state op).stack[0]?
              validJumps = true) := by
        simpa [memoryState] using hJumpBad
      have hJumpiBad' :
          ¬ (op = EvmYul.Operation.JUMPI ∧
            (Assembly.GasAware.memoryGasState state op).stack[1]? ≠
              some (⟨0⟩ : Word) ∧
              EvmYul.EVM.X.notIn
                (Assembly.GasAware.memoryGasState state op).stack[0]?
                validJumps = true) := by
        simpa [memoryState] using hJumpiBad
      have hReturnDataBad' :
          ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
            (Assembly.GasAware.memoryGasState state op).returnData.size <
              ((Assembly.GasAware.memoryGasState state op).stack.getD 1
                  (⟨0⟩ : Word)).toNat +
                ((Assembly.GasAware.memoryGasState state op).stack.getD 2
                    (⟨0⟩ : Word)).toNat) := by
        simpa [memoryState] using hReturnDataBad
      have hReturnDataBadGet' :
          ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
            (Assembly.GasAware.memoryGasState state op).returnData.size <
              (((Assembly.GasAware.memoryGasState state op).stack[1]?).getD
                  (⟨0⟩ : Word)).toNat +
                (((Assembly.GasAware.memoryGasState state op).stack[2]?).getD
                    (⟨0⟩ : Word)).toNat) := by
        simpa [List.getD] using hReturnDataBad'
      have hOverflowBad' :
          ¬ (1024 <
            (Assembly.GasAware.memoryGasState state op).stack.length -
                (EvmYul.EVM.δ op).getD 0 +
              (EvmYul.EVM.α op).getD 0) := by
        simpa [memoryState] using hOverflowBad
      have hStaticBad' :
          ¬ ((Assembly.GasAware.memoryGasState state op).executionEnv.perm =
              false ∧
            staticWriteSensitive? op
                (Assembly.GasAware.memoryGasState state op).stack =
              true) := by
        simpa [memoryState] using hStaticBad
      have hCreateBad' :
          ¬ (op.isCreate = true ∧
            (⟨49152⟩ : Word) <
              (Assembly.GasAware.memoryGasState state op).stack.getD 2
                (⟨0⟩ : Word)) := by
        simpa [memoryState] using hCreateBad
      have hCreateBadGet' :
          ¬ (op.isCreate = true ∧
            (⟨49152⟩ : Word) <
              ((Assembly.GasAware.memoryGasState state op).stack[2]?).getD
                (⟨0⟩ : Word)) := by
        simpa [List.getD] using hCreateBad'
      by_cases hSstore :
        op = EvmYul.Operation.SSTORE ∧
          memoryState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
      · exact Or.inr (by
          rcases hSstore with ⟨hOp, hStipend⟩
          subst op
          have hDeltaS :
              ¬ EvmYul.EVM.δ EvmYul.Operation.SSTORE = none := by
            simpa using hDelta
          have hDynamicS :
              ¬ ((Assembly.GasAware.memoryGasState state
                    EvmYul.Operation.SSTORE).gasAvailable.toNat <
                EvmYul.EVM.C'
                  (Assembly.GasAware.memoryGasState state
                    EvmYul.Operation.SSTORE)
                  EvmYul.Operation.SSTORE) := by
            simpa using hDynamic'
          have hStackBadS :
              ¬ ((Assembly.GasAware.memoryGasState state
                    EvmYul.Operation.SSTORE).stack.length <
                (EvmYul.EVM.δ EvmYul.Operation.SSTORE).getD 0) := by
            simpa using hStackBad'
          have hOverflowBadS :
              ¬ (1024 <
                (Assembly.GasAware.memoryGasState state
                    EvmYul.Operation.SSTORE).stack.length -
                    (EvmYul.EVM.δ EvmYul.Operation.SSTORE).getD 0 +
                  (EvmYul.EVM.α EvmYul.Operation.SSTORE).getD 0) := by
            simpa using hOverflowBad'
          have hStaticBadS :
              ¬ ((Assembly.GasAware.memoryGasState state
                    EvmYul.Operation.SSTORE).executionEnv.perm = false ∧
                staticWriteSensitive? EvmYul.Operation.SSTORE
                    (Assembly.GasAware.memoryGasState state
                      EvmYul.Operation.SSTORE).stack =
                  true) := by
            simpa using hStaticBad'
          have hStipendS :
              (Assembly.GasAware.memoryGasState state
                EvmYul.Operation.SSTORE).gasAvailable.toNat ≤
                GasConstants.Gcallstipend := by
            simpa [memoryState] using hStipend
          simp [xStepException?, hMemory, hDynamicS, hDeltaS, hStackBadS,
            hOverflowBadS, hStaticBadS, hStipendS])
      · exact Or.inl (by
          have hSstore' :
              ¬ (op = EvmYul.Operation.SSTORE ∧
                (Assembly.GasAware.memoryGasState state op).gasAvailable.toNat ≤
                  GasConstants.Gcallstipend) := by
            simpa [memoryState] using hSstore
          simp [xStepException?, hMemory, hDynamic', hDelta, hStackBad',
            hJumpBad', hJumpiBad', hReturnDataBadGet', hOverflowBad',
            hStaticBad', hSstore', hCreateBadGet'])

theorem xStepException?_eq_outOfGas_of_nonGas_checks_of_some
    {validJumps : Array Word} {state : EVMState} {op : EVMOp}
    {err : EVMException}
    (hNonGas :
      Assembly.GasAware.XNonGasChecksPass validJumps state op)
    (hException :
      xStepException? validJumps state op = some err) :
    err = .OutOfGass := by
  rcases xStepException?_none_or_outOfGas_of_nonGas_checks hNonGas with
    hNone | hOutOfGas
  · rw [hException] at hNone
    cases hNone
  · rw [hException] at hOutOfGas
    cases hOutOfGas
    rfl

def openStepAfterChecks
    (fuel : Nat) (op : EVMOp) (arg : Option (Word × Nat))
    (state : EVMState) :
    OpenExternal.OpenResult EVMException EVMState :=
  match OpenExternal.CallKind.ofEVMOperation? op with
  | some kind =>
      let charged := gasChargedState state op
      match OpenExternal.CallKind.evmOpenCall? charged kind with
      | some call => evmGasAwareCallResult call
      | none =>
          .done
            (EvmYul.EVM.step fuel
              (EvmYul.EVM.C'
                (Assembly.GasAware.memoryGasState state op) op)
              (some (op, arg))
              (Assembly.GasAware.memoryGasState state op))
  | none =>
      .done
        (EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op))

theorem openStepAfterChecks_call
    {fuel : Nat} {op : EVMOp} {arg : Option (Word × Nat)}
    {state : EVMState} {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        some call) :
    openStepAfterChecks fuel op arg state = evmGasAwareCallResult call := by
  simp [openStepAfterChecks, hKind, hCall]

def continueAfterStep
    (openXNext : EVMState → OpenExternal.OpenResult EVMException EVMResult)
    (op : EVMOp) (post : EVMState) :
    OpenExternal.OpenResult EVMException EVMResult :=
  match Assembly.GasAware.XStepHaltOutput? op post with
  | none => openXNext post
  | some output =>
      if op = EvmYul.Operation.REVERT then
        .done (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output))
      else
        .done (.ok (EvmYul.EVM.ExecutionResult.success post output))

def openX :
    Nat → Array Word → EVMState →
      OpenExternal.OpenResult EVMException EVMResult
  | 0, _validJumps, _state => .done (.error (.OutOfFuel : EVMException))
  | fuel + 1, validJumps, state =>
      let (op, arg) :=
        (EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)
      match xStepException? validJumps state op with
      | some err => .done (.error err)
      | none =>
          OpenExternal.OpenResult.bind
            (openStepAfterChecks fuel op arg state)
            (continueAfterStep (openX fuel validJumps) op)

theorem openX_zero (validJumps : Array Word) (state : EVMState) :
    openX 0 validJumps state =
      .done (.error (.OutOfFuel : EVMException)) := by
  rfl

theorem openX_succ
    (fuel : Nat) (validJumps : Array Word) (state : EVMState) :
    openX (fuel + 1) validJumps state =
      (let (op, arg) :=
        (EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)
      match xStepException? validJumps state op with
      | some err => .done (.error err)
      | none =>
          OpenExternal.OpenResult.bind
            (openStepAfterChecks fuel op arg state)
            (continueAfterStep (openX fuel validJumps) op)) := by
  rfl

theorem XStepHaltOutput?_none_of_callKind
    {op : EVMOp} {kind : OpenExternal.CallKind} {state : EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind) :
    Assembly.GasAware.XStepHaltOutput? op state = none := by
  cases kind <;> cases op <;>
    simp [OpenExternal.CallKind.ofEVMOperation?,
      Assembly.GasAware.XStepHaltOutput?] at hKind ⊢
  all_goals
    try rename_i subop
    try cases subop <;>
      simp at hKind ⊢

theorem openX_current_call_continue
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {result : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : xStepException? validJumps state op = none)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        some call)
    (hRest :
      OpenExternal.OpenResultResolves
        (openX fuel validJumps
          (EvmYul.EVM.State.incrPC
            (finishGasAwareCall call response)))
        tailTrace (.ok result)) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state)
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      (.ok result) := by
  rw [openX_succ]
  simp [hDecode, hChecks]
  rw [openStepAfterChecks_call (fuel := fuel) (arg := arg)
    (state := state) hKind hCall]
  have hNoHalt :
      Assembly.GasAware.XStepHaltOutput? op
        (EvmYul.EVM.State.incrPC
          (finishGasAwareCall call response)) = none :=
    XStepHaltOutput?_none_of_callKind hKind
  have hStep :=
    evmGasAwareCallResult_resolves call response
  have hRest' :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps) op
          (EvmYul.EVM.State.incrPC
            (finishGasAwareCall call response)))
        tailTrace (.ok result) := by
    simpa [continueAfterStep, hNoHalt] using hRest
  exact OpenExternal.OpenResultResolves.bind_ok hStep hRest'

theorem openX_current_call_continue_outcome
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : xStepException? validJumps state op = none)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        some call)
    (hRest :
      OpenExternal.OpenResultResolves
        (openX fuel validJumps
          (EvmYul.EVM.State.incrPC
            (finishGasAwareCall call response)))
        tailTrace outcome) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state)
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      outcome := by
  rw [openX_succ]
  simp [hDecode, hChecks]
  rw [openStepAfterChecks_call (fuel := fuel) (arg := arg)
    (state := state) hKind hCall]
  have hNoHalt :
      Assembly.GasAware.XStepHaltOutput? op
        (EvmYul.EVM.State.incrPC
          (finishGasAwareCall call response)) = none :=
    XStepHaltOutput?_none_of_callKind hKind
  have hStep :=
    evmGasAwareCallResult_resolves call response
  have hRest' :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps) op
          (EvmYul.EVM.State.incrPC
            (finishGasAwareCall call response)))
        tailTrace outcome := by
    simpa [continueAfterStep, hNoHalt] using hRest
  exact OpenExternal.OpenResultResolves.bind_ok hStep hRest'

theorem openX_current_call_continue_outcome_inv
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : xStepException? validJumps state op = none)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        some call)
    (hTrace :
      OpenExternal.OpenResultResolves
        (openX (fuel + 1) validJumps state)
        (OpenExternal.OpenEvent.call call.site response :: tailTrace)
        outcome) :
    OpenExternal.OpenResultResolves
      (openX fuel validJumps
        (EvmYul.EVM.State.incrPC
          (finishGasAwareCall call response)))
      tailTrace outcome := by
  have hTrace' :
      OpenExternal.OpenResultResolves
        (OpenExternal.OpenResult.bind (evmGasAwareCallResult call)
          (continueAfterStep (openX fuel validJumps) op))
        (OpenExternal.OpenEvent.call call.site response :: tailTrace)
        outcome := by
    rw [openX_succ] at hTrace
    simp [hDecode, hChecks] at hTrace
    rw [openStepAfterChecks_call (fuel := fuel) (arg := arg)
      (state := state) hKind hCall] at hTrace
    exact hTrace
  rcases OpenExternal.OpenResultResolves.bind_inv hTrace' with
    hError | hOk
  · rcases hError with ⟨err, hSource, hOutcome⟩
    unfold evmGasAwareCallResult at hSource
    cases hSource with
    | call hTail =>
        cases hTail
  · rcases hOk with
      ⟨left, right, value, hTraceEq, hSource, hSuffix⟩
    unfold evmGasAwareCallResult at hSource
    cases hSource with
    | call hTail =>
        cases hTail
        simp at hTraceEq
        rcases hTraceEq with ⟨hResponse, hRight⟩
        cases hResponse
        cases hRight
        have hNoHalt :
            Assembly.GasAware.XStepHaltOutput? op
              (EvmYul.EVM.State.incrPC
                (finishGasAwareCall call response)) = none :=
          XStepHaltOutput?_none_of_callKind hKind
        simpa [continueAfterStep, hNoHalt] using hSuffix

theorem openX_current_call_continue_outcome_safelyTracks_of_tail_inv
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : xStepException? validJumps state op = none)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        some call)
    (hTail :
      ∀ tailTrace outcome,
        OpenExternal.OpenResultResolves
          (openX fuel validJumps
            (EvmYul.EVM.State.incrPC
              (finishGasAwareCall call response)))
          tailTrace outcome →
        Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference))
    (hTrace :
      OpenExternal.OpenResultResolves
        (openX (fuel + 1) validJumps state)
        (OpenExternal.OpenEvent.call call.site response :: tailTrace)
        outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  exact hTail tailTrace outcome
    (openX_current_call_continue_outcome_inv
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (op := op) (arg := arg) (kind := kind) (call := call)
      (response := response) (tailTrace := tailTrace)
      (outcome := outcome)
      hDecode hChecks hKind hCall hTrace)

theorem openStepAfterChecks_of_not_callKind
    {fuel : Nat} {op : EVMOp} {arg : Option (Word × Nat)}
    {state : EVMState}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = none) :
    openStepAfterChecks fuel op arg state =
      .done
        (EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op)) := by
  simp [openStepAfterChecks, hKind]

theorem openStepAfterChecks_of_callKind_no_call
    {fuel : Nat} {op : EVMOp} {arg : Option (Word × Nat)}
    {state : EVMState} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall?
        (gasChargedState state op) kind = none) :
    openStepAfterChecks fuel op arg state =
      .done
        (EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op)) := by
  simp [openStepAfterChecks, hKind, hCall]

theorem openStepAfterChecks_of_targetInstr_no_callCreate
    {fuel : Nat} {instr : Assembly.TargetInstr} {state : EVMState}
    (hNoCallCreate :
      Assembly.GasAware.targetInstrUsesCallCreate instr = false) :
    openStepAfterChecks fuel instr.op instr.arg state =
      .done
        (EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state instr.op) instr.op)
          (some (instr.op, instr.arg))
          (Assembly.GasAware.memoryGasState state instr.op)) := by
  cases instr with
  | push32 value =>
      rfl
  | jump =>
      rfl
  | jumpi =>
      rfl
  | jumpdest =>
      rfl
  | prim op =>
      cases op <;>
        simp [Assembly.GasAware.targetInstrUsesCallCreate,
          Assembly.PrimOp.isCallCreate, Assembly.TargetInstr.op,
          Assembly.TargetInstr.arg, Assembly.PrimOp.toEVM,
          OpenExternal.CallKind.ofEVMOperation?, openStepAfterChecks]
        at hNoCallCreate ⊢

theorem openX_current_running_continue_of_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {tailTrace : OpenExternal.OpenTrace} {result : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hOpenStep :
      openStepAfterChecks fuel op arg state =
        .done
          (EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              (Assembly.GasAware.memoryGasState state op) op)
            (some (op, arg))
            (Assembly.GasAware.memoryGasState state op)))
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hNoHalt :
      Assembly.GasAware.XStepHaltOutput? op post = none)
    (hRest :
      OpenExternal.OpenResultResolves
        (openX fuel validJumps post) tailTrace (.ok result)) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) tailTrace (.ok result) := by
  rw [openX_succ]
  simp [hDecode, xStepException?_none_of_step_checks hStepChecks]
  rw [hOpenStep, hStep]
  have hRest' :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps) op post)
        tailTrace (.ok result) := by
    simpa [continueAfterStep, hNoHalt] using hRest
  exact
    OpenExternal.OpenResultResolves.bind_ok
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done (.ok post)) :
            OpenExternal.OpenResult EVMException EVMState)
          [] (.ok post))
      hRest'

theorem openX_current_running_continue_outcome_of_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {tailTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException : xStepException? validJumps state op = none)
    (hOpenStep :
      openStepAfterChecks fuel op arg state =
        .done
          (EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              (Assembly.GasAware.memoryGasState state op) op)
            (some (op, arg))
            (Assembly.GasAware.memoryGasState state op)))
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hNoHalt :
      Assembly.GasAware.XStepHaltOutput? op post = none)
    (hRest :
      OpenExternal.OpenResultResolves
        (openX fuel validJumps post) tailTrace outcome) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) tailTrace outcome := by
  rw [openX_succ]
  simp [hDecode, hException]
  rw [hOpenStep, hStep]
  have hRest' :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps) op post)
        tailTrace outcome := by
    simpa [continueAfterStep, hNoHalt] using hRest
  exact
    OpenExternal.OpenResultResolves.bind_ok
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done (.ok post)) :
            OpenExternal.OpenResult EVMException EVMState)
          [] (.ok post))
      hRest'

theorem openX_current_running_continue_of_not_callKind
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {tailTrace : OpenExternal.OpenTrace} {result : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hNoHalt :
      Assembly.GasAware.XStepHaltOutput? op post = none)
    (hRest :
      OpenExternal.OpenResultResolves
        (openX fuel validJumps post) tailTrace (.ok result)) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) tailTrace (.ok result) :=
  openX_current_running_continue_of_openStepAfterChecks_done
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (post := post) (op := op) (arg := arg)
    (tailTrace := tailTrace) (result := result)
    hDecode hStepChecks
    (openStepAfterChecks_of_not_callKind hKind)
    hStep hNoHalt hRest

theorem openX_current_running_continue_of_callKind_no_call
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {tailTrace : OpenExternal.OpenTrace} {result : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall?
        (gasChargedState state op) kind = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hNoHalt :
      Assembly.GasAware.XStepHaltOutput? op post = none)
    (hRest :
      OpenExternal.OpenResultResolves
        (openX fuel validJumps post) tailTrace (.ok result)) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) tailTrace (.ok result) :=
  openX_current_running_continue_of_openStepAfterChecks_done
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (post := post) (op := op) (arg := arg)
    (tailTrace := tailTrace) (result := result)
    hDecode hStepChecks
    (openStepAfterChecks_of_callKind_no_call hKind hCall)
    hStep hNoHalt hRest

theorem openX_current_success_of_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hOpenStep :
      openStepAfterChecks fuel op arg state =
        .done
          (EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              (Assembly.GasAware.memoryGasState state op) op)
            (some (op, arg))
            (Assembly.GasAware.memoryGasState state op)))
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
  rw [openX_succ]
  simp [hDecode, xStepException?_none_of_step_checks hStepChecks]
  rw [hOpenStep, hStep]
  have hDone :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps) op post)
        [] (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
    simpa [continueAfterStep, hHalt, hNotRevert] using
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done
            (.ok
              (EvmYul.EVM.ExecutionResult.success post output))) :
            OpenExternal.OpenResult EVMException EVMResult)
          [] (.ok (EvmYul.EVM.ExecutionResult.success post output)))
  exact
    OpenExternal.OpenResultResolves.bind_ok
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done (.ok post)) :
            OpenExternal.OpenResult EVMException EVMState)
          [] (.ok post))
      hDone

theorem openX_current_success_of_openStepAfterChecks_done_of_exception_none
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException : xStepException? validJumps state op = none)
    (hOpenStep :
      openStepAfterChecks fuel op arg state =
        .done
          (EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              (Assembly.GasAware.memoryGasState state op) op)
            (some (op, arg))
            (Assembly.GasAware.memoryGasState state op)))
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
  rw [openX_succ]
  simp [hDecode, hException]
  rw [hOpenStep, hStep]
  have hDone :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps) op post)
        [] (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
    simpa [continueAfterStep, hHalt, hNotRevert] using
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done
            (.ok
              (EvmYul.EVM.ExecutionResult.success post output))) :
            OpenExternal.OpenResult EVMException EVMResult)
          [] (.ok (EvmYul.EVM.ExecutionResult.success post output)))
  exact
    OpenExternal.OpenResultResolves.bind_ok
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done (.ok post)) :
            OpenExternal.OpenResult EVMException EVMState)
          [] (.ok post))
      hDone

theorem openX_fallthrough_stop_success_of_checks
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {output : ByteArray}
    (hDecodeNone :
      EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state
        EvmYul.Operation.STOP)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state EvmYul.Operation.STOP)
            EvmYul.Operation.STOP)
          (some (EvmYul.Operation.STOP, none))
          (Assembly.GasAware.memoryGasState state EvmYul.Operation.STOP) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XHaltOutput? EvmYul.Operation.STOP post =
        some output) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
  rw [openX_succ]
  simp [hDecodeNone, xStepException?_none_of_step_checks hStepChecks]
  have hKind :
      OpenExternal.CallKind.ofEVMOperation? EvmYul.Operation.STOP = none := by
    rfl
  have hStepHalt :
      Assembly.GasAware.XStepHaltOutput? EvmYul.Operation.STOP post =
        some output := by
    simpa [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?] using hHalt
  rw [openStepAfterChecks_of_not_callKind
    (fuel := fuel) (op := EvmYul.Operation.STOP) (arg := none)
    (state := state) hKind, hStep]
  have hDone :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps)
          EvmYul.Operation.STOP post)
        [] (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
    simpa [continueAfterStep, hStepHalt] using
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done
            (.ok
              (EvmYul.EVM.ExecutionResult.success post output))) :
            OpenExternal.OpenResult EVMException EVMResult)
          [] (.ok (EvmYul.EVM.ExecutionResult.success post output)))
  exact
    OpenExternal.OpenResultResolves.bind_ok
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done (.ok post)) :
            OpenExternal.OpenResult EVMException EVMState)
          [] (.ok post))
      hDone

theorem openX_fallthrough_stop_success_of_exception_none
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {output : ByteArray}
    (hDecodeNone :
      EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hException :
      xStepException? validJumps state EvmYul.Operation.STOP = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state EvmYul.Operation.STOP)
            EvmYul.Operation.STOP)
          (some (EvmYul.Operation.STOP, none))
          (Assembly.GasAware.memoryGasState state EvmYul.Operation.STOP) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? EvmYul.Operation.STOP post =
        some output) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
  rw [openX_succ]
  simp [hDecodeNone, hException]
  have hKind :
      OpenExternal.CallKind.ofEVMOperation? EvmYul.Operation.STOP = none := by
    rfl
  have hStepHalt :
      Assembly.GasAware.XStepHaltOutput? EvmYul.Operation.STOP post =
        some output := by
    simpa [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?] using hHalt
  rw [openStepAfterChecks_of_not_callKind
    (fuel := fuel) (op := EvmYul.Operation.STOP) (arg := none)
    (state := state) hKind, hStep]
  have hDone :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps)
          EvmYul.Operation.STOP post)
        [] (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
    simpa [continueAfterStep, hStepHalt] using
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done
            (.ok
              (EvmYul.EVM.ExecutionResult.success post output))) :
            OpenExternal.OpenResult EVMException EVMResult)
          [] (.ok (EvmYul.EVM.ExecutionResult.success post output)))
  exact
    OpenExternal.OpenResultResolves.bind_ok
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done (.ok post)) :
            OpenExternal.OpenResult EVMException EVMState)
          [] (.ok post))
      hDone

theorem openX_current_revert_of_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hOpenStep :
      openStepAfterChecks fuel op arg state =
        .done
          (EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              (Assembly.GasAware.memoryGasState state op) op)
            (some (op, arg))
            (Assembly.GasAware.memoryGasState state op)))
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) := by
  rw [openX_succ]
  simp [hDecode, xStepException?_none_of_step_checks hStepChecks]
  rw [hOpenStep, hStep]
  have hDone :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps) op post)
        [] (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) := by
    have hHaltRevert :
        Assembly.GasAware.XStepHaltOutput?
            EvmYul.Operation.REVERT post = some output := by
      simpa [hRevert] using hHalt
    simpa [continueAfterStep, hHalt, hHaltRevert, hRevert] using
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done
            (.ok
              (EvmYul.EVM.ExecutionResult.revert post.gasAvailable
                output))) :
            OpenExternal.OpenResult EVMException EVMResult)
          [] (.ok
            (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)))
  exact
    OpenExternal.OpenResultResolves.bind_ok
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done (.ok post)) :
            OpenExternal.OpenResult EVMException EVMState)
          [] (.ok post))
      hDone

theorem openX_current_revert_of_openStepAfterChecks_done_of_exception_none
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException : xStepException? validJumps state op = none)
    (hOpenStep :
      openStepAfterChecks fuel op arg state =
        .done
          (EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              (Assembly.GasAware.memoryGasState state op) op)
            (some (op, arg))
            (Assembly.GasAware.memoryGasState state op)))
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) := by
  rw [openX_succ]
  simp [hDecode, hException]
  rw [hOpenStep, hStep]
  have hDone :
      OpenExternal.OpenResultResolves
        (continueAfterStep (openX fuel validJumps) op post)
        [] (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) := by
    have hHaltRevert :
        Assembly.GasAware.XStepHaltOutput?
            EvmYul.Operation.REVERT post = some output := by
      simpa [hRevert] using hHalt
    simpa [continueAfterStep, hHalt, hHaltRevert, hRevert] using
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done
            (.ok
              (EvmYul.EVM.ExecutionResult.revert post.gasAvailable
                output))) :
            OpenExternal.OpenResult EVMException EVMResult)
          [] (.ok
            (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)))
  exact
    OpenExternal.OpenResultResolves.bind_ok
      (OpenExternal.OpenResultResolves.done :
        OpenExternal.OpenResultResolves
          ((.done (.ok post)) :
            OpenExternal.OpenResult EVMException EVMState)
          [] (.ok post))
      hDone

theorem openX_current_success_of_not_callKind
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) :=
  openX_current_success_of_openStepAfterChecks_done
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (post := post) (op := op) (arg := arg) (output := output)
    hDecode hStepChecks
    (openStepAfterChecks_of_not_callKind hKind)
    hStep hHalt hNotRevert

theorem openX_current_success_of_callKind_no_call
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind} {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall?
        (gasChargedState state op) kind = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) :=
  openX_current_success_of_openStepAfterChecks_done
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (post := post) (op := op) (arg := arg) (output := output)
    hDecode hStepChecks
    (openStepAfterChecks_of_callKind_no_call hKind hCall)
    hStep hHalt hNotRevert

theorem openX_current_revert_of_not_callKind
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) :=
  openX_current_revert_of_openStepAfterChecks_done
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (post := post) (op := op) (arg := arg) (output := output)
    hDecode hStepChecks
    (openStepAfterChecks_of_not_callKind hKind)
    hStep hHalt hRevert

theorem openX_current_revert_of_callKind_no_call
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind} {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall?
        (gasChargedState state op) kind = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt :
      Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps state) []
      (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) :=
  openX_current_revert_of_openStepAfterChecks_done
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (post := post) (op := op) (arg := arg) (output := output)
    hDecode hStepChecks
    (openStepAfterChecks_of_callKind_no_call hKind hCall)
    hStep hHalt hRevert

theorem openX_current_gasless_call_continue
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {result : EVMResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hChecks : xStepException? validJumps full op = none)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hRest :
      ∀ {gasPost : EVMState},
        Assembly.GasAware.GasExecRel gasPost
          (EvmYul.EVM.State.incrPC (call.resume response)) →
        OpenExternal.OpenResultResolves
          (openX fuel validJumps gasPost) tailTrace (.ok result)) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps full)
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      (.ok result) := by
  obtain ⟨gasCall, hGasCall, hSite, hPostRel⟩ :=
    evmOpenCall?_gasChargedState_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall response
  have hRest' :
      OpenExternal.OpenResultResolves
        (openX fuel validJumps
          (EvmYul.EVM.State.incrPC
            (finishGasAwareCall gasCall response)))
        tailTrace (.ok result) :=
    hRest hPostRel
  have hStep :=
    openX_current_call_continue
      (fuel := fuel) (validJumps := validJumps) (state := full)
      (op := op) (arg := arg) (kind := kind) (call := gasCall)
      (response := response) (tailTrace := tailTrace) (result := result)
      hDecode hChecks hKind hGasCall hRest'
  simpa [hSite] using hStep

theorem openX_current_gasless_call_continue_of_step_checks
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {result : EVMResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hRest :
      ∀ {gasPost : EVMState},
        Assembly.GasAware.GasExecRel gasPost
          (EvmYul.EVM.State.incrPC (call.resume response)) →
        OpenExternal.OpenResultResolves
          (openX fuel validJumps gasPost) tailTrace (.ok result)) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps full)
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      (.ok result) :=
  openX_current_gasless_call_continue
    (fuel := fuel) (validJumps := validJumps)
    (full := full) (target := target) (op := op) (arg := arg)
    (kind := kind) (call := call) (response := response)
    (tailTrace := tailTrace) (result := result)
    hRel hDecode (xStepException?_none_of_step_checks hStepChecks)
    hKind hCall hRest

theorem openX_current_emitted_prim_call_continue_of_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {result : EVMResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program target.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hRest :
      ∀ {gasPost : EVMState},
        Assembly.GasAware.GasExecRel gasPost
          (EvmYul.EVM.State.incrPC (call.resume response)) →
        OpenExternal.OpenResultResolves
          (openX fuel validJumps gasPost) tailTrace (.ok result)) :
    OpenExternal.OpenResultResolves
      (openX (fuel + 1) validJumps full)
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      (.ok result) := by
  have hEmit' := hEmit
  simp [Assembly.emitInstr?] at hEmit'
  subst emitted
  have hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (op.toEVM, none) := by
    have hDecodeLocated :=
      Assembly.GasAware.decode_of_gasExecRel_instrAt_mem_emitted_of_safety
        (program := program) (target := targetProgram)
        (targetState := target) (fullState := full)
        (pc := pc) (instr := Assembly.Instr.prim op)
        (located := { pc := pc, instr := Assembly.TargetInstr.prim op })
        (before := before)
        (emitted := [{ pc := pc, instr := Assembly.TargetInstr.prim op }])
        (after := after)
        hEncoding hSafety hAt hTargetBlock (by simp) (by rfl)
        hRel hCode
    simpa [Assembly.TargetInstr.op, Assembly.TargetInstr.arg] using
      hDecodeLocated
  exact
    openX_current_gasless_call_continue_of_step_checks
      (fuel := fuel) (validJumps := validJumps)
      (full := full) (target := target) (op := op.toEVM)
      (arg := none) (kind := kind) (call := call)
      (response := response) (tailTrace := tailTrace)
      (result := result)
      hRel hDecode hStepChecks hKind hCall hRest

abbrev OpenXTraceResult
    (validJumps : Array Word) (fuel : Nat) (state : EVMState)
    (trace : OpenExternal.OpenTrace) (result : EVMResult) : Prop :=
  OpenExternal.OpenResultResolves
    (openX fuel validJumps state) trace (.ok result)

theorem OpenXTraceResult.resolves
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : EVMResult}
    (hTrace :
      OpenXTraceResult validJumps fuel state trace result) :
    OpenExternal.OpenResultResolves
      (openX fuel validJumps state) trace (.ok result) :=
  hTrace

theorem OpenXTraceResult.zero_false
    {validJumps : Array Word} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : EVMResult}
    (hTrace : OpenXTraceResult validJumps 0 state trace result) :
    False := by
  unfold OpenXTraceResult at hTrace
  rw [openX_zero] at hTrace
  cases hTrace

def clearReturnBuffers (state : EVMState) : EVMState :=
  { state with
    toMachineState :=
      (state.toMachineState.setReturnData ByteArray.empty).setHReturn
        ByteArray.empty }

def OpenXClearedRunningResultAgrees (targetResult : Assembly.StepResult)
    (result : EVMResult) : Prop :=
  match targetResult, result with
  | .running state, .success evmFinal output =>
      Assembly.eraseGas evmFinal =
          Assembly.eraseGas (clearReturnBuffers state) ∧
        output = ByteArray.empty
  | _, _ => False

def OpenXResultAgrees (targetResult : Assembly.StepResult)
    (result : EVMResult) : Prop :=
  Assembly.GasAware.XResultAgrees targetResult result ∨
    OpenXClearedRunningResultAgrees targetResult result

namespace OpenXResultAgrees

theorem of_assembly
    {targetResult : Assembly.StepResult} {result : EVMResult}
    (hAgree :
      Assembly.GasAware.XResultAgrees targetResult result) :
    OpenXResultAgrees targetResult result :=
  Or.inl hAgree

theorem running_success_of_gasExecRel_clear_return_buffers
    {full target : EVMState}
    (hRel : Assembly.GasAware.GasExecRel full target) :
    OpenXResultAgrees (.running target)
      (.success (clearReturnBuffers full) ByteArray.empty) := by
  refine Or.inr ⟨?_, rfl⟩
  rw [hRel]
  simp [clearReturnBuffers, Assembly.eraseGas,
    EvmYul.MachineState.setReturnData, EvmYul.MachineState.setHReturn]

theorem clearReturnBuffers_toState (state : EVMState) :
    (clearReturnBuffers state).toState = state.toState := by
  rfl

theorem committedObservation
    {targetResult : Assembly.StepResult} {result : EVMResult}
    (hAgree : OpenXResultAgrees targetResult result) :
    Assembly.GasAware.XResultCommittedObservation result =
      Assembly.GasAware.XTargetCommittedObservation targetResult := by
  rcases hAgree with hAssembly | hCleared
  · exact hAssembly.committedObservation
  · cases targetResult with
    | running state =>
        cases result with
        | success evmFinal output =>
            rcases hCleared with ⟨hState, hOutput⟩
            cases hOutput
            have hToState :
                evmFinal.toState = state.toState := by
              calc
                evmFinal.toState = (Assembly.eraseGas evmFinal).toState := by
                  rw [Assembly.GasAware.eraseGas_toState]
                _ = (Assembly.eraseGas (clearReturnBuffers state)).toState := by
                  rw [hState]
                _ = (clearReturnBuffers state).toState :=
                  Assembly.GasAware.eraseGas_toState (clearReturnBuffers state)
                _ = state.toState := clearReturnBuffers_toState state
            simp [Assembly.GasAware.XResultCommittedObservation,
              Assembly.GasAware.XTargetCommittedObservation, hToState]
        | revert gas output =>
            cases hCleared
    | halted halt =>
        cases result <;> cases hCleared

theorem outcomeSafelyMatches
    {targetResult : Assembly.StepResult} {result : EVMResult}
    (hAgree : OpenXResultAgrees targetResult result) :
    Assembly.GasAware.XRunOutcomeSafelyMatches targetResult (.ok result) :=
  Or.inl ⟨result, rfl, hAgree.committedObservation⟩

end OpenXResultAgrees

abbrev OpenXOutcomeTraceResult
    (validJumps : Array Word) (fuel : Nat) (state : EVMState)
    (trace : OpenExternal.OpenTrace)
    (outcome : Except EVMException EVMResult) : Prop :=
  OpenExternal.OpenResultResolves
    (openX fuel validJumps state) trace outcome

def OpenXOutcomeResult
    (validJumps : Array Word) (fuel : Nat) (state : EVMState)
    (outcome : Except EVMException EVMResult) : Prop :=
  ∃ trace : OpenExternal.OpenTrace,
    OpenXOutcomeTraceResult validJumps fuel state trace outcome

def OpenXOutcomeTraceSafelyTracksResult
    (validJumps : Array Word) (fuel : Nat) (state : EVMState)
    (trace : OpenExternal.OpenTrace) (reference : EVMResult) : Prop :=
  ∃ outcome,
    OpenXOutcomeTraceResult validJumps fuel state trace outcome ∧
      Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference)

def OpenXStateAllOutcomeTracesSafelyTrackResult
    (validJumps : Array Word) (fuel : Nat) (state : EVMState)
    (reference : EVMResult) : Prop :=
  ∀ trace outcome,
    OpenXOutcomeTraceResult validJumps fuel state trace outcome →
      Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference)

def OpenXStateAllOutcomeTracesSafelyMatchTarget
    (validJumps : Array Word) (fuel : Nat) (state : EVMState)
    (targetResult : Assembly.StepResult) : Prop :=
  ∀ trace outcome,
    OpenXOutcomeTraceResult validJumps fuel state trace outcome →
      Assembly.GasAware.XRunOutcomeSafelyMatches targetResult outcome

def OpenXGasRelStateAllOutcomeTracesSafelyTrackResult
    (validJumps : Array Word) (fuel : Nat) (targetState : EVMState)
    (reference : EVMResult) : Prop :=
  ∀ fullState,
    Assembly.GasAware.GasExecRel fullState targetState →
      OpenXStateAllOutcomeTracesSafelyTrackResult validJumps fuel
        fullState reference

def OpenXGasRelStateAllOutcomeTracesSafelyMatchTarget
    (validJumps : Array Word) (fuel : Nat) (targetState : EVMState)
    (targetResult : Assembly.StepResult) : Prop :=
  ∀ fullState,
    Assembly.GasAware.GasExecRel fullState targetState →
      OpenXStateAllOutcomeTracesSafelyMatchTarget validJumps fuel
        fullState targetResult

def OpenXTraceObservationOrFailure
    (validJumps : Array Word) (fuel : Nat) (state : EVMState)
    (trace : OpenExternal.OpenTrace)
    (targetResult : Assembly.StepResult) : Prop :=
  (∃ result : EVMResult,
    OpenXTraceResult validJumps fuel state trace result ∧
      Assembly.GasAware.XResultCommittedObservation result =
        Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
  (∃ outcome : Except EVMException EVMResult,
    OpenXOutcomeTraceResult validJumps fuel state trace outcome ∧
      Assembly.GasAware.XRunOutcomeFails outcome)

def OpenXCommittedSafeAt
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gas : Nat) : Prop :=
  gas < EvmYul.UInt256.size ∧
    ∃ outcome,
      OpenXOutcomeResult (Assembly.GasAware.validJumps target) evmFuel
        (Assembly.GasAware.installCodeAndGas target gas initial) outcome ∧
      Assembly.GasAware.XRunOutcomeSafelyMatches targetResult outcome

def OpenXCommittedSafeAbove
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      gas < EvmYul.UInt256.size →
        OpenXCommittedSafeAt target initial targetResult evmFuel gas

def OpenXCommittedSafeForAllGas
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel : Nat) : Prop :=
  ∀ gas,
    gas < EvmYul.UInt256.size →
      OpenXCommittedSafeAt target initial targetResult evmFuel gas

/--
Low-gas side condition for committed-result safety.

`OpenXReplayAbove` already proves committed safety at and above the generated
gas bound.  The difficult theorem-boundary work is below that bound, where an
external CALL may observe a different gas budget and therefore needs the
stronger external-world safety premise discussed in the CALL gas model.
-/
def OpenXCommittedSafeBelow
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gas < gasBound →
      gas < EvmYul.UInt256.size →
        OpenXCommittedSafeAt target initial targetResult evmFuel gas

def OpenXOutcomeTraceExistsAt
    (target : Assembly.TargetProgram) (initial : EVMState)
    (evmFuel gas : Nat) : Prop :=
  gas < EvmYul.UInt256.size →
    ∃ trace,
    ∃ outcome,
      OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target) evmFuel
        (Assembly.GasAware.installCodeAndGas target gas initial)
        trace outcome

def OpenXOutcomeTraceExistsBelow
    (target : Assembly.TargetProgram) (initial : EVMState)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gas < gasBound →
      OpenXOutcomeTraceExistsAt target initial evmFuel gas

def OpenXOutcomeTraceExistsForAllGas
    (target : Assembly.TargetProgram) (initial : EVMState)
    (evmFuel : Nat) : Prop :=
  ∀ gas,
    OpenXOutcomeTraceExistsAt target initial evmFuel gas

def OpenXAllOutcomeTracesSafelyMatchAt
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gas : Nat) : Prop :=
  gas < EvmYul.UInt256.size →
    ∀ trace outcome,
      OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target) evmFuel
        (Assembly.GasAware.installCodeAndGas target gas initial)
        trace outcome →
      Assembly.GasAware.XRunOutcomeSafelyMatches targetResult outcome

def OpenXAllOutcomeTracesSafelyMatchBelow
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gas < gasBound →
      OpenXAllOutcomeTracesSafelyMatchAt target initial targetResult evmFuel gas

def OpenXAllOutcomeTracesSafelyMatchAbove
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      OpenXAllOutcomeTracesSafelyMatchAt target initial targetResult evmFuel gas

def OpenXAllOutcomeTracesSafelyMatchForAllGas
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel : Nat) : Prop :=
  ∀ gas,
    OpenXAllOutcomeTracesSafelyMatchAt target initial targetResult evmFuel gas

def OpenXOutcomeSafelyTracksResult
    (validJumps : Array Word) (fuel : Nat) (state : EVMState)
    (reference : EVMResult) : Prop :=
  ∃ outcome,
    OpenXOutcomeResult validJumps fuel state outcome ∧
      Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference)

namespace OpenXTraceObservationOrFailure

theorem of_trace_target_observation
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {result : EVMResult}
    (hTrace : OpenXTraceResult validJumps fuel state trace result)
    (hObservation :
      Assembly.GasAware.XResultCommittedObservation result =
        Assembly.GasAware.XTargetCommittedObservation targetResult) :
    OpenXTraceObservationOrFailure validJumps fuel state trace
      targetResult :=
  Or.inl ⟨result, hTrace, hObservation⟩

theorem of_failure_trace
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {outcome : Except EVMException EVMResult}
    (hTrace : OpenXOutcomeTraceResult validJumps fuel state trace outcome)
    (hFails : Assembly.GasAware.XRunOutcomeFails outcome) :
    OpenXTraceObservationOrFailure validJumps fuel state trace
      targetResult :=
  Or.inr ⟨outcome, hTrace, hFails⟩

theorem to_outcomeSafelyMatches
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hClassified :
      OpenXTraceObservationOrFailure validJumps fuel state trace
        targetResult) :
    ∃ outcome : Except EVMException EVMResult,
      OpenXOutcomeTraceResult validJumps fuel state trace outcome ∧
        Assembly.GasAware.XRunOutcomeSafelyMatches targetResult outcome := by
  rcases hClassified with
    ⟨result, hTrace, hObservation⟩ |
    ⟨outcome, hTrace, hFails⟩
  · exact ⟨.ok result, hTrace, Or.inl ⟨result, rfl, hObservation⟩⟩
  · exact ⟨outcome, hTrace, Or.inr hFails⟩

theorem zero_false
    {validJumps : Array Word} {state : EVMState}
    {trace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    (hClassified :
      OpenXTraceObservationOrFailure validJumps 0 state trace
        targetResult) :
    False := by
  rcases hClassified with
    ⟨result, hTrace, _hObservation⟩ |
    ⟨outcome, hTrace, hFails⟩
  · exact OpenXTraceResult.zero_false hTrace
  · unfold OpenXOutcomeTraceResult at hTrace
    rw [openX_zero] at hTrace
    cases hTrace
    simp [Assembly.GasAware.XRunOutcomeFails] at hFails

theorem of_current_outOfGas_exception
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {targetResult : Assembly.StepResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException :
      xStepException? validJumps state op =
        some (.OutOfGass : EVMException)) :
    OpenXTraceObservationOrFailure validJumps (fuel + 1) state []
      targetResult := by
  have hDone :
      OpenExternal.OpenResultResolves
        (.done
          ((.error (.OutOfGass : EVMException)) :
            Except EVMException EVMResult))
        ([] : OpenExternal.OpenTrace)
        ((.error (.OutOfGass : EVMException)) :
          Except EVMException EVMResult) :=
    OpenExternal.OpenResultResolves.done
  have hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state []
        (.error (.OutOfGass : EVMException)) := by
    simpa [OpenXOutcomeTraceResult, openX_succ, hDecode, hException]
      using hDone
  exact of_failure_trace hTrace (by simp [Assembly.GasAware.XRunOutcomeFails])

theorem of_fallthrough_stop_outOfGas_exception
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {targetResult : Assembly.StepResult}
    (hDecodeNone :
      EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hException :
      xStepException? validJumps state EvmYul.Operation.STOP =
        some (.OutOfGass : EVMException)) :
    OpenXTraceObservationOrFailure validJumps (fuel + 1) state []
      targetResult := by
  have hDone :
      OpenExternal.OpenResultResolves
        (.done
          ((.error (.OutOfGass : EVMException)) :
            Except EVMException EVMResult))
        ([] : OpenExternal.OpenTrace)
        ((.error (.OutOfGass : EVMException)) :
          Except EVMException EVMResult) :=
    OpenExternal.OpenResultResolves.done
  have hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state []
        (.error (.OutOfGass : EVMException)) := by
    simpa [OpenXOutcomeTraceResult, openX_succ, hDecodeNone, hException]
      using hDone
  exact of_failure_trace hTrace (by simp [Assembly.GasAware.XRunOutcomeFails])

theorem of_current_nonGas_exception
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {err : EVMException} {targetResult : Assembly.StepResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hNonGas :
      Assembly.GasAware.XNonGasChecksPass validJumps state op)
    (hException :
      xStepException? validJumps state op = some err) :
    OpenXTraceObservationOrFailure validJumps (fuel + 1) state []
      targetResult := by
  have hErr :
      err = .OutOfGass :=
    xStepException?_eq_outOfGas_of_nonGas_checks_of_some
      hNonGas hException
  subst err
  exact of_current_outOfGas_exception hDecode hException

end OpenXTraceObservationOrFailure

namespace OpenXStateAllOutcomeTracesSafelyTrackResult

theorem to_matchTarget
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {targetResult : Assembly.StepResult} {reference : EVMResult}
    (hAgree : OpenXResultAgrees targetResult reference)
    (hAll :
      OpenXStateAllOutcomeTracesSafelyTrackResult validJumps fuel state
        reference) :
    OpenXStateAllOutcomeTracesSafelyMatchTarget validJumps fuel state
      targetResult := by
  intro trace outcome hOutcome
  exact
    Assembly.GasAware.XRunOutcomeSafelyTracks.outcomeSafelyMatches_of_result
      (hAll trace outcome hOutcome) hAgree.committedObservation

end OpenXStateAllOutcomeTracesSafelyTrackResult

namespace OpenXGasRelStateAllOutcomeTracesSafelyTrackResult

theorem to_matchTarget
    {validJumps : Array Word} {fuel : Nat} {targetState : EVMState}
    {targetResult : Assembly.StepResult} {reference : EVMResult}
    (hAgree : OpenXResultAgrees targetResult reference)
    (hAll :
      OpenXGasRelStateAllOutcomeTracesSafelyTrackResult validJumps fuel
        targetState reference) :
    OpenXGasRelStateAllOutcomeTracesSafelyMatchTarget validJumps fuel
      targetState targetResult := by
  intro fullState hRel
  exact
    OpenXStateAllOutcomeTracesSafelyTrackResult.to_matchTarget
      hAgree (hAll fullState hRel)

end OpenXGasRelStateAllOutcomeTracesSafelyTrackResult

theorem openX_current_running_all_outcomes_safelyTracks_of_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException : xStepException? validJumps state op = none)
    (hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post))
    (hNoHalt : Assembly.GasAware.XStepHaltOutput? op post = none)
    (hTail :
      OpenXStateAllOutcomeTracesSafelyTrackResult validJumps fuel post
        reference)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  apply hTail trace outcome
  unfold OpenXOutcomeTraceResult at hTrace ⊢
  rw [openX_succ] at hTrace
  simp [hDecode, hException] at hTrace
  rw [hOpenStep] at hTrace
  simpa [continueAfterStep, hNoHalt] using hTrace

theorem openX_current_running_all_outcomes_safelyTracks_of_not_callKind
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hNoHalt : Assembly.GasAware.XStepHaltOutput? op post = none)
    (hTail :
      OpenXStateAllOutcomeTracesSafelyTrackResult validJumps fuel post
        reference)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  have hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post) := by
    rw [openStepAfterChecks_of_not_callKind hKind, hStep]
  exact
    openX_current_running_all_outcomes_safelyTracks_of_openStepAfterChecks_done
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (post := post) (op := op) (arg := arg) (trace := trace)
      (outcome := outcome) (reference := reference)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hOpenStep hNoHalt hTail hTrace

theorem openX_current_running_all_outcomes_safelyTracks_of_callKind_no_call
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hNoHalt : Assembly.GasAware.XStepHaltOutput? op post = none)
    (hTail :
      OpenXStateAllOutcomeTracesSafelyTrackResult validJumps fuel post
        reference)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  have hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post) := by
    rw [openStepAfterChecks_of_callKind_no_call hKind hCall, hStep]
  exact
    openX_current_running_all_outcomes_safelyTracks_of_openStepAfterChecks_done
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (post := post) (op := op) (arg := arg) (trace := trace)
      (outcome := outcome) (reference := reference)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hOpenStep hNoHalt hTail hTrace

theorem openX_current_success_all_outcomes_safelyTracks_of_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException : xStepException? validJumps state op = none)
    (hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post))
    (hHalt : Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
  have hTraceDone :
      OpenExternal.OpenResultResolves
        ((.done
          (.ok (EvmYul.EVM.ExecutionResult.success post output))) :
          OpenExternal.OpenResult EVMException EVMResult)
        trace outcome := by
    unfold OpenXOutcomeTraceResult at hTrace
    rw [openX_succ] at hTrace
    simp [hDecode, hException] at hTrace
    rw [hOpenStep] at hTrace
    simpa [continueAfterStep, hHalt, hNotRevert] using hTrace
  cases hTraceDone
  exact
    Assembly.GasAware.XRunOutcomeSafelyTracks.ok_refl
      (EvmYul.EVM.ExecutionResult.success post output)

theorem openX_current_revert_all_outcomes_safelyTracks_of_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException : xStepException? validJumps state op = none)
    (hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post))
    (hHalt : Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome
      (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) := by
  have hTraceDone :
      OpenExternal.OpenResultResolves
        ((.done
          (.ok
            (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output))) :
          OpenExternal.OpenResult EVMException EVMResult)
        trace outcome := by
    unfold OpenXOutcomeTraceResult at hTrace
    rw [openX_succ] at hTrace
    simp [hDecode, hException] at hTrace
    rw [hOpenStep] at hTrace
    have hHaltRevert :
        Assembly.GasAware.XStepHaltOutput?
            EvmYul.Operation.REVERT post = some output := by
      simpa [hRevert] using hHalt
    simpa [continueAfterStep, hHalt, hHaltRevert, hRevert] using hTrace
  cases hTraceDone
  exact
    Assembly.GasAware.XRunOutcomeSafelyTracks.ok_refl
      (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)

theorem openX_current_success_all_outcomes_safelyTracks_of_not_callKind
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt : Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
  have hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post) := by
    rw [openStepAfterChecks_of_not_callKind hKind, hStep]
  exact
    openX_current_success_all_outcomes_safelyTracks_of_openStepAfterChecks_done
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (post := post) (op := op) (arg := arg) (trace := trace)
      (outcome := outcome) (output := output)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hOpenStep hHalt hNotRevert hTrace

theorem openX_current_success_all_outcomes_safelyTracks_of_callKind_no_call
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt : Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome
      (.ok (EvmYul.EVM.ExecutionResult.success post output)) := by
  have hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post) := by
    rw [openStepAfterChecks_of_callKind_no_call hKind hCall, hStep]
  exact
    openX_current_success_all_outcomes_safelyTracks_of_openStepAfterChecks_done
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (post := post) (op := op) (arg := arg) (trace := trace)
      (outcome := outcome) (output := output)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hOpenStep hHalt hNotRevert hTrace

theorem openX_current_revert_all_outcomes_safelyTracks_of_not_callKind
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt : Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome
      (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) := by
  have hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post) := by
    rw [openStepAfterChecks_of_not_callKind hKind, hStep]
  exact
    openX_current_revert_all_outcomes_safelyTracks_of_openStepAfterChecks_done
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (post := post) (op := op) (arg := arg) (trace := trace)
      (outcome := outcome) (output := output)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hOpenStep hHalt hRevert hTrace

theorem openX_current_revert_all_outcomes_safelyTracks_of_callKind_no_call
    {fuel : Nat} {validJumps : Array Word} {state post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {output : ByteArray}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps state op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? (gasChargedState state op) kind =
        none)
    (hStep :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (Assembly.GasAware.memoryGasState state op) op)
          (some (op, arg))
          (Assembly.GasAware.memoryGasState state op) =
        .ok post)
    (hHalt : Assembly.GasAware.XStepHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome
      (.ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)) := by
  have hOpenStep :
      openStepAfterChecks fuel op arg state = .done (.ok post) := by
    rw [openStepAfterChecks_of_callKind_no_call hKind hCall, hStep]
  exact
    openX_current_revert_all_outcomes_safelyTracks_of_openStepAfterChecks_done
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (post := post) (op := op) (arg := arg) (trace := trace)
      (outcome := outcome) (output := output)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hOpenStep hHalt hRevert hTrace

theorem openX_current_exception_all_outcomes_safelyTracks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult} {err : EVMException}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException : xStepException? validJumps state op = some err)
    (hFails :
      Assembly.GasAware.XRunOutcomeFails
        (((.error err) : Except EVMException EVMResult)))
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  have hTraceDone :
      OpenExternal.OpenResultResolves
        ((.done (((.error err) : Except EVMException EVMResult))) :
          OpenExternal.OpenResult EVMException EVMResult)
        trace outcome := by
    unfold OpenXOutcomeTraceResult at hTrace
    rw [openX_succ] at hTrace
    simpa [hDecode, hException] using hTrace
  cases hTraceDone
  exact Assembly.GasAware.XRunOutcomeSafelyTracks.of_candidate_fails hFails

theorem openX_current_outOfGas_exception_all_outcomes_safelyTracks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hException :
      xStepException? validJumps state op =
        some (.OutOfGass : EVMException))
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) :=
  openX_current_exception_all_outcomes_safelyTracks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (op := op) (arg := arg) (trace := trace) (outcome := outcome)
    (reference := reference) (err := (.OutOfGass : EVMException))
    hDecode hException (by simp [Assembly.GasAware.XRunOutcomeFails])
    hTrace

theorem openX_current_nonGas_exception_all_outcomes_safelyTracks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult} {err : EVMException}
    (hDecode :
      EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hNonGas :
      Assembly.GasAware.XNonGasChecksPass validJumps state op)
    (hException : xStepException? validJumps state op = some err)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  have hErr :
      err = .OutOfGass :=
    xStepException?_eq_outOfGas_of_nonGas_checks_of_some
      hNonGas hException
  subst err
  exact
    openX_current_outOfGas_exception_all_outcomes_safelyTracks
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (op := op) (arg := arg) (trace := trace) (outcome := outcome)
      (reference := reference)
      hDecode hException hTrace

theorem openX_fallthrough_stop_exception_all_outcomes_safelyTracks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult} {err : EVMException}
    (hDecodeNone :
      EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hException :
      xStepException? validJumps state EvmYul.Operation.STOP = some err)
    (hFails :
      Assembly.GasAware.XRunOutcomeFails
        (((.error err) : Except EVMException EVMResult)))
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  have hTraceDone :
      OpenExternal.OpenResultResolves
        ((.done (((.error err) : Except EVMException EVMResult))) :
          OpenExternal.OpenResult EVMException EVMResult)
        trace outcome := by
    unfold OpenXOutcomeTraceResult at hTrace
    rw [openX_succ] at hTrace
    simpa [hDecodeNone, hException] using hTrace
  cases hTraceDone
  exact Assembly.GasAware.XRunOutcomeSafelyTracks.of_candidate_fails hFails

theorem openX_fallthrough_stop_outOfGas_exception_all_outcomes_safelyTracks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {trace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hDecodeNone :
      EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hException :
      xStepException? validJumps state EvmYul.Operation.STOP =
        some (.OutOfGass : EVMException))
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) state trace outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) :=
  openX_fallthrough_stop_exception_all_outcomes_safelyTracks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (trace := trace) (outcome := outcome) (reference := reference)
    (err := (.OutOfGass : EVMException))
    hDecodeNone hException (by simp [Assembly.GasAware.XRunOutcomeFails])
    hTrace

theorem openX_gasrel_current_running_all_outcomes_safelyTracks_of_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {initial post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {reference : EVMResult}
    (hDecode :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hException :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          xStepException? validJumps full op = none)
    (hStep :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          ∃ gasPost : EVMState,
            openStepAfterChecks fuel op arg full = .done (.ok gasPost) ∧
              Assembly.GasAware.GasExecRel gasPost post ∧
                Assembly.GasAware.XStepHaltOutput? op gasPost = none)
    (hTail :
      OpenXGasRelStateAllOutcomeTracesSafelyTrackResult validJumps fuel post
        reference) :
    OpenXGasRelStateAllOutcomeTracesSafelyTrackResult validJumps
      (fuel + 1) initial reference := by
  intro full hRel trace outcome hTrace
  obtain ⟨gasPost, hOpenStep, hRelPost, hNoHalt⟩ := hStep hRel
  exact
    openX_current_running_all_outcomes_safelyTracks_of_openStepAfterChecks_done
      (fuel := fuel) (validJumps := validJumps) (state := full)
      (post := gasPost) (op := op) (arg := arg) (trace := trace)
      (outcome := outcome) (reference := reference)
      (hDecode hRel) (hException hRel) hOpenStep hNoHalt
      (hTail gasPost hRelPost) hTrace

theorem openX_gasrel_current_running_all_outcomes_safelyTracks_of_nonGas_openStepAfterChecks_done
    {fuel : Nat} {validJumps : Array Word} {initial post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {reference : EVMResult}
    (hDecode :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hNonGas :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XNonGasChecksPass validJumps full op)
    (hStep :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          xStepException? validJumps full op = none →
            ∃ gasPost : EVMState,
              openStepAfterChecks fuel op arg full = .done (.ok gasPost) ∧
                Assembly.GasAware.GasExecRel gasPost post ∧
                  Assembly.GasAware.XStepHaltOutput? op gasPost = none)
    (hTail :
      OpenXGasRelStateAllOutcomeTracesSafelyTrackResult validJumps fuel post
        reference) :
    OpenXGasRelStateAllOutcomeTracesSafelyTrackResult validJumps
      (fuel + 1) initial reference := by
  intro full hRel trace outcome hTrace
  rcases xStepException?_none_or_outOfGas_of_nonGas_checks
      (hNonGas hRel) with hException | hException
  · obtain ⟨gasPost, hOpenStep, hRelPost, hNoHalt⟩ :=
      hStep hRel hException
    exact
      openX_current_running_all_outcomes_safelyTracks_of_openStepAfterChecks_done
        (fuel := fuel) (validJumps := validJumps) (state := full)
        (post := gasPost) (op := op) (arg := arg) (trace := trace)
        (outcome := outcome) (reference := reference)
        (hDecode hRel) hException hOpenStep hNoHalt
        (hTail gasPost hRelPost) hTrace
  · exact
      openX_current_outOfGas_exception_all_outcomes_safelyTracks
        (fuel := fuel) (validJumps := validJumps) (state := full)
        (op := op) (arg := arg) (trace := trace) (outcome := outcome)
        (reference := reference)
        (hDecode hRel) hException hTrace

namespace OpenXOutcomeTraceSafelyTracksResult

theorem of_trace_observation_eq
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result reference : EVMResult}
    (hTrace : OpenXTraceResult validJumps fuel state trace result)
    (hObservation :
      Assembly.GasAware.XResultCommittedObservation result =
        Assembly.GasAware.XResultCommittedObservation reference) :
    OpenXOutcomeTraceSafelyTracksResult validJumps fuel state trace
      reference := by
  refine ⟨.ok result, hTrace, ?_⟩
  cases result with
  | success state output =>
      cases reference with
      | success refState refOutput =>
          exact
            Or.inl
              ⟨.committed state.toState output,
                by simp [Assembly.GasAware.XRunOutcomeCommitsTo],
                by
                  simpa [Assembly.GasAware.XRunOutcomeCommitsTo,
                    Assembly.GasAware.XResultCommittedObservation]
                    using hObservation⟩
      | revert gas output =>
          cases hObservation
  | revert gas output =>
      exact Or.inr (by simp [Assembly.GasAware.XRunOutcomeFails])

theorem of_trace_agrees
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {result reference : EVMResult}
    (hTrace : OpenXTraceResult validJumps fuel state trace result)
    (hResult : OpenXResultAgrees targetResult result)
    (hReference : OpenXResultAgrees targetResult reference) :
    OpenXOutcomeTraceSafelyTracksResult validJumps fuel state trace
      reference :=
  of_trace_observation_eq hTrace
    (hResult.committedObservation.trans hReference.committedObservation.symm)

theorem of_trace_target_observation
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {result reference : EVMResult}
    (hTrace : OpenXTraceResult validJumps fuel state trace result)
    (hObservation :
      Assembly.GasAware.XResultCommittedObservation result =
        Assembly.GasAware.XTargetCommittedObservation targetResult)
    (hReference : OpenXResultAgrees targetResult reference) :
    OpenXOutcomeTraceSafelyTracksResult validJumps fuel state trace
      reference :=
  of_trace_observation_eq hTrace
    (hObservation.trans hReference.committedObservation.symm)

theorem of_failure_trace
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hTrace : OpenXOutcomeTraceResult validJumps fuel state trace outcome)
    (hFails : Assembly.GasAware.XRunOutcomeFails outcome) :
    OpenXOutcomeTraceSafelyTracksResult validJumps fuel state trace
      reference :=
  ⟨outcome, hTrace,
    Assembly.GasAware.XRunOutcomeSafelyTracks.of_candidate_fails hFails⟩

theorem traceObservation_or_failure
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {reference : EVMResult}
    (hTracks :
      OpenXOutcomeTraceSafelyTracksResult validJumps fuel state trace
        reference)
    (hReference : OpenXResultAgrees targetResult reference) :
    (∃ result : EVMResult,
      OpenXTraceResult validJumps fuel state trace result ∧
        Assembly.GasAware.XResultCommittedObservation result =
          Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
    (∃ outcome : Except EVMException EVMResult,
      OpenXOutcomeTraceResult validJumps fuel state trace outcome ∧
        Assembly.GasAware.XRunOutcomeFails outcome) := by
  rcases hTracks with ⟨outcome, hTrace, hTracksOutcome⟩
  rcases hTracksOutcome with hCommit | hFails
  · rcases hCommit with ⟨observation, hCandidate, hReferenceCommit⟩
    cases outcome with
    | ok result =>
        cases result with
        | success state output =>
            have hCandidateObservation :
                observation =
                  Assembly.GasAware.XResultCommittedObservation
                    (.success state output : EVMResult) :=
              Assembly.GasAware.XRunOutcomeCommitsTo.ok_result_observation
                hCandidate
            have hReferenceObservation :
                observation =
                  Assembly.GasAware.XResultCommittedObservation reference :=
              Assembly.GasAware.XRunOutcomeCommitsTo.ok_result_observation
                hReferenceCommit
            exact
              Or.inl
                ⟨.success state output, hTrace,
                  hCandidateObservation.symm.trans
                    (hReferenceObservation.trans
                      hReference.committedObservation)⟩
        | revert gas output =>
            simp [Assembly.GasAware.XRunOutcomeCommitsTo] at hCandidate
    | error err =>
        simp [Assembly.GasAware.XRunOutcomeCommitsTo] at hCandidate
  · exact Or.inr ⟨outcome, hTrace, hFails⟩

theorem to_result
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {reference : EVMResult}
    (hTracks :
      OpenXOutcomeTraceSafelyTracksResult validJumps fuel state trace
        reference) :
    OpenXOutcomeSafelyTracksResult validJumps fuel state reference := by
  rcases hTracks with ⟨outcome, hTrace, hTracksOutcome⟩
  exact ⟨outcome, ⟨trace, hTrace⟩, hTracksOutcome⟩

end OpenXOutcomeTraceSafelyTracksResult

namespace OpenXOutcomeSafelyTracksResult

theorem of_trace
    {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : EVMResult}
    (hTrace : OpenXTraceResult validJumps fuel state trace result) :
    OpenXOutcomeSafelyTracksResult validJumps fuel state result :=
  ⟨.ok result, ⟨trace, hTrace⟩,
    Assembly.GasAware.XRunOutcomeSafelyTracks.ok_refl result⟩

end OpenXOutcomeSafelyTracksResult

/--
Directional tracking form of the low-gas side condition.

Below the replay bound, a future induction may choose any reference EVM result
that agrees with the gas-erased assembly result. The low-gas run is safe when
it either fails or commits to the same observation as that reference.
-/
def OpenXCommittedSafeBelowTracksResult
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gas < gasBound →
      gas < EvmYul.UInt256.size →
        ∃ reference : EVMResult,
          OpenXResultAgrees targetResult reference ∧
            OpenXOutcomeSafelyTracksResult
              (Assembly.GasAware.validJumps target) evmFuel
              (Assembly.GasAware.installCodeAndGas target gas initial)
              reference

/--
Fixed-reference version of the low-gas tracking frontier.

This is the shape an induction usually wants: choose one reference result that
agrees with the gas-erased target result, then prove every low-gas execution
either fails or tracks that same committed observation.
-/
def OpenXCommittedSafeBelowTracksFixedResult
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) (reference : EVMResult) : Prop :=
  OpenXResultAgrees targetResult reference ∧
    ∀ gas,
      gas < gasBound →
        gas < EvmYul.UInt256.size →
          OpenXOutcomeSafelyTracksResult
            (Assembly.GasAware.validJumps target) evmFuel
            (Assembly.GasAware.installCodeAndGas target gas initial)
            reference

/--
Trace-indexed fixed-reference low-gas frontier.

Compared with `OpenXCommittedSafeBelowTracksFixedResult`, this keeps the
candidate low-gas trace visible. That is the shape needed by an induction that
compares a fixed reference trace against each low-gas candidate trace.
-/
def OpenXCommittedSafeBelowTracksFixedTraceResult
    (target : Assembly.TargetProgram) (initial : EVMState)
    (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) (reference : EVMResult) : Prop :=
  OpenXResultAgrees targetResult reference ∧
    ∀ gas,
      gas < gasBound →
        gas < EvmYul.UInt256.size →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXOutcomeTraceSafelyTracksResult
              (Assembly.GasAware.validJumps target) evmFuel
              (Assembly.GasAware.installCodeAndGas target gas initial)
              candidateTrace reference

namespace OpenXCommittedSafeBelowTracksResult

theorem mono
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBoundSmall gasBoundLarge : Nat}
    (hLe : gasBoundSmall ≤ gasBoundLarge)
    (hTracks :
      OpenXCommittedSafeBelowTracksResult target initial targetResult evmFuel
        gasBoundLarge) :
    OpenXCommittedSafeBelowTracksResult target initial targetResult evmFuel
      gasBoundSmall := by
  intro gas hLow hGasFits
  exact hTracks gas (Nat.lt_of_lt_of_le hLow hLe) hGasFits

theorem of_fixedResult
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat} {reference : EVMResult}
    (hFixed :
      OpenXCommittedSafeBelowTracksFixedResult target initial targetResult
        evmFuel gasBound reference) :
    OpenXCommittedSafeBelowTracksResult target initial targetResult evmFuel
      gasBound := by
  intro gas hLow hGasFits
  exact ⟨reference, hFixed.1, hFixed.2 gas hLow hGasFits⟩

end OpenXCommittedSafeBelowTracksResult

namespace OpenXCommittedSafeBelowTracksFixedResult

theorem mono
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBoundSmall gasBoundLarge : Nat} {reference : EVMResult}
    (hLe : gasBoundSmall ≤ gasBoundLarge)
    (hFixed :
      OpenXCommittedSafeBelowTracksFixedResult target initial targetResult
        evmFuel gasBoundLarge reference) :
    OpenXCommittedSafeBelowTracksFixedResult target initial targetResult
      evmFuel gasBoundSmall reference := by
  refine ⟨hFixed.1, ?_⟩
  intro gas hLow hGasFits
  exact hFixed.2 gas (Nat.lt_of_lt_of_le hLow hLe) hGasFits

theorem of_traceResult
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat} {reference : EVMResult}
    (hTrace :
      OpenXCommittedSafeBelowTracksFixedTraceResult target initial
        targetResult evmFuel gasBound reference) :
    OpenXCommittedSafeBelowTracksFixedResult target initial targetResult
      evmFuel gasBound reference := by
  refine ⟨hTrace.1, ?_⟩
  intro gas hLow hGasFits
  rcases hTrace.2 gas hLow hGasFits with ⟨candidateTrace, hTracks⟩
  exact OpenXOutcomeTraceSafelyTracksResult.to_result hTracks

end OpenXCommittedSafeBelowTracksFixedResult

namespace OpenXCommittedSafeBelowTracksFixedTraceResult

theorem mono
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBoundSmall gasBoundLarge : Nat} {reference : EVMResult}
    (hLe : gasBoundSmall ≤ gasBoundLarge)
    (hTrace :
      OpenXCommittedSafeBelowTracksFixedTraceResult target initial
        targetResult evmFuel gasBoundLarge reference) :
    OpenXCommittedSafeBelowTracksFixedTraceResult target initial targetResult
      evmFuel gasBoundSmall reference := by
  refine ⟨hTrace.1, ?_⟩
  intro gas hLow hGasFits
  exact hTrace.2 gas (Nat.lt_of_lt_of_le hLow hLe) hGasFits

theorem succ_of_at
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat} {reference : EVMResult}
    (hTrace :
      OpenXCommittedSafeBelowTracksFixedTraceResult target initial
        targetResult evmFuel gasBound reference)
    (hAt :
      gasBound < EvmYul.UInt256.size →
        ∃ candidateTrace : OpenExternal.OpenTrace,
          OpenXOutcomeTraceSafelyTracksResult
            (Assembly.GasAware.validJumps target) evmFuel
            (Assembly.GasAware.installCodeAndGas target gasBound initial)
            candidateTrace reference) :
    OpenXCommittedSafeBelowTracksFixedTraceResult target initial targetResult
      evmFuel gasBound.succ reference := by
  refine ⟨hTrace.1, ?_⟩
  intro gas hLow hGasFits
  by_cases hBefore : gas < gasBound
  · exact hTrace.2 gas hBefore hGasFits
  · have hLe : gas ≤ gasBound := Nat.lt_succ_iff.mp hLow
    have hGe : gasBound ≤ gas := Nat.le_of_not_gt hBefore
    have hEq : gas = gasBound := Nat.le_antisymm hLe hGe
    subst gas
    exact hAt hGasFits

theorem succ_of_trace_or_failure_at
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat} {reference : EVMResult}
    (hTrace :
      OpenXCommittedSafeBelowTracksFixedTraceResult target initial
        targetResult evmFuel gasBound reference)
    (hAt :
      gasBound < EvmYul.UInt256.size →
        (∃ candidateTrace : OpenExternal.OpenTrace,
          ∃ result : EVMResult,
            OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
              (Assembly.GasAware.installCodeAndGas target gasBound initial)
              candidateTrace result ∧
              OpenXResultAgrees targetResult result) ∨
        (∃ candidateTrace : OpenExternal.OpenTrace,
          ∃ outcome : Except EVMException EVMResult,
            OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
              evmFuel
              (Assembly.GasAware.installCodeAndGas target gasBound initial)
              candidateTrace outcome ∧
              Assembly.GasAware.XRunOutcomeFails outcome)) :
    OpenXCommittedSafeBelowTracksFixedTraceResult target initial targetResult
      evmFuel gasBound.succ reference := by
  exact
    succ_of_at hTrace (fun hGasFits => by
      rcases hAt hGasFits with
        ⟨candidateTrace, result, hCandidateTrace, hAgree⟩ |
        ⟨candidateTrace, outcome, hCandidateTrace, hFails⟩
      · exact
          ⟨candidateTrace,
            OpenXOutcomeTraceSafelyTracksResult.of_trace_agrees
              hCandidateTrace hAgree hTrace.1⟩
      · exact
        ⟨candidateTrace,
          OpenXOutcomeTraceSafelyTracksResult.of_failure_trace
            hCandidateTrace hFails⟩)

theorem succ_of_trace_observation_or_failure_at
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat} {reference : EVMResult}
    (hTrace :
      OpenXCommittedSafeBelowTracksFixedTraceResult target initial
        targetResult evmFuel gasBound reference)
    (hAt :
      gasBound < EvmYul.UInt256.size →
        (∃ candidateTrace : OpenExternal.OpenTrace,
          ∃ result : EVMResult,
            OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
              (Assembly.GasAware.installCodeAndGas target gasBound initial)
              candidateTrace result ∧
              Assembly.GasAware.XResultCommittedObservation result =
                Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
        (∃ candidateTrace : OpenExternal.OpenTrace,
          ∃ outcome : Except EVMException EVMResult,
            OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
              evmFuel
              (Assembly.GasAware.installCodeAndGas target gasBound initial)
              candidateTrace outcome ∧
              Assembly.GasAware.XRunOutcomeFails outcome)) :
    OpenXCommittedSafeBelowTracksFixedTraceResult target initial targetResult
      evmFuel gasBound.succ reference := by
  exact
    succ_of_at hTrace (fun hGasFits => by
      rcases hAt hGasFits with
        ⟨candidateTrace, result, hCandidateTrace, hObservation⟩ |
        ⟨candidateTrace, outcome, hCandidateTrace, hFails⟩
      · exact
          ⟨candidateTrace,
            OpenXOutcomeTraceSafelyTracksResult.of_trace_target_observation
              hCandidateTrace hObservation hTrace.1⟩
      · exact
          ⟨candidateTrace,
            OpenXOutcomeTraceSafelyTracksResult.of_failure_trace
              hCandidateTrace hFails⟩)

theorem zero_bound
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult} {evmFuel : Nat}
    {reference : EVMResult}
    (hAgree : OpenXResultAgrees targetResult reference) :
    OpenXCommittedSafeBelowTracksFixedTraceResult target initial targetResult
      evmFuel 0 reference := by
  refine ⟨hAgree, ?_⟩
  intro gas hLow _hGasFits
  exact False.elim (Nat.not_lt_zero gas hLow)

theorem of_trace_or_failure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat} {reference : EVMResult}
    (hAgree : OpenXResultAgrees targetResult reference)
    (hAt :
      ∀ gas,
        gas < gasBound →
          gas < EvmYul.UInt256.size →
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ result : EVMResult,
                OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace result ∧
                  OpenXResultAgrees targetResult result) ∨
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ outcome : Except EVMException EVMResult,
                OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
                  evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace outcome ∧
                  Assembly.GasAware.XRunOutcomeFails outcome)) :
    OpenXCommittedSafeBelowTracksFixedTraceResult target initial targetResult
      evmFuel gasBound reference := by
  induction gasBound with
  | zero =>
      exact zero_bound hAgree
  | succ gasBound ih =>
      exact
        succ_of_trace_or_failure_at
          (ih (fun gas hLow hGasFits =>
            hAt gas (Nat.lt_trans hLow (Nat.lt_succ_self gasBound))
              hGasFits))
          (fun hGasFits =>
            hAt gasBound (Nat.lt_succ_self gasBound) hGasFits)

theorem of_trace_observation_or_failure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat} {reference : EVMResult}
    (hAgree : OpenXResultAgrees targetResult reference)
    (hAt :
      ∀ gas,
        gas < gasBound →
          gas < EvmYul.UInt256.size →
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ result : EVMResult,
                OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace result ∧
                  Assembly.GasAware.XResultCommittedObservation result =
                    Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ outcome : Except EVMException EVMResult,
                OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
                  evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace outcome ∧
                  Assembly.GasAware.XRunOutcomeFails outcome)) :
    OpenXCommittedSafeBelowTracksFixedTraceResult target initial targetResult
      evmFuel gasBound reference := by
  induction gasBound with
  | zero =>
      exact zero_bound hAgree
  | succ gasBound ih =>
      exact
        succ_of_trace_observation_or_failure_at
          (ih (fun gas hLow hGasFits =>
            hAt gas (Nat.lt_trans hLow (Nat.lt_succ_self gasBound))
              hGasFits))
          (fun hGasFits =>
            hAt gasBound (Nat.lt_succ_self gasBound) hGasFits)

theorem traceObservation_or_failure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat} {reference : EVMResult}
    (hTrace :
      OpenXCommittedSafeBelowTracksFixedTraceResult target initial targetResult
        evmFuel gasBound reference) :
    ∀ gas,
      gas < gasBound →
        gas < EvmYul.UInt256.size →
          (∃ candidateTrace : OpenExternal.OpenTrace,
            ∃ result : EVMResult,
              OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
                (Assembly.GasAware.installCodeAndGas target gas initial)
                candidateTrace result ∧
                Assembly.GasAware.XResultCommittedObservation result =
                  Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
          (∃ candidateTrace : OpenExternal.OpenTrace,
            ∃ outcome : Except EVMException EVMResult,
              OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
                evmFuel
                (Assembly.GasAware.installCodeAndGas target gas initial)
                candidateTrace outcome ∧
                Assembly.GasAware.XRunOutcomeFails outcome) := by
  intro gas hLow hGasFits
  rcases hTrace.2 gas hLow hGasFits with ⟨candidateTrace, hTracks⟩
  rcases
      OpenXOutcomeTraceSafelyTracksResult.traceObservation_or_failure
        hTracks hTrace.1 with
    ⟨result, hCandidateTrace, hObservation⟩ |
    ⟨outcome, hCandidateTrace, hFails⟩
  · exact Or.inl ⟨candidateTrace, result, hCandidateTrace, hObservation⟩
  · exact Or.inr ⟨candidateTrace, outcome, hCandidateTrace, hFails⟩

end OpenXCommittedSafeBelowTracksFixedTraceResult

namespace OpenXCommittedSafeAt

theorem to_outcome_safety
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gas : Nat}
    (hSafe :
      OpenXCommittedSafeAt target initial targetResult evmFuel gas) :
    ∃ outcome : Except EVMException EVMResult,
      OpenXOutcomeResult (Assembly.GasAware.validJumps target) evmFuel
        (Assembly.GasAware.installCodeAndGas target gas initial)
        outcome ∧
      Assembly.GasAware.XRunOutcomeSafelyMatches targetResult outcome := by
  rcases hSafe with ⟨_hGasFits, outcome, hOutcome, hMatches⟩
  exact ⟨outcome, hOutcome, hMatches⟩

theorem to_result_or_failure
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gas : Nat}
    (hSafe :
      OpenXCommittedSafeAt target initial targetResult evmFuel gas) :
    (∃ result : EVMResult,
      OpenXOutcomeResult (Assembly.GasAware.validJumps target) evmFuel
        (Assembly.GasAware.installCodeAndGas target gas initial)
        (.ok result) ∧
        Assembly.GasAware.XResultCommittedObservation result =
          Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
      (∃ outcome : Except EVMException EVMResult,
        OpenXOutcomeResult (Assembly.GasAware.validJumps target) evmFuel
          (Assembly.GasAware.installCodeAndGas target gas initial)
          outcome ∧
          Assembly.GasAware.XRunOutcomeFails outcome) := by
  rcases hSafe with ⟨_hGasFits, outcome, hOutcome, hMatches⟩
  rcases hMatches with ⟨result, hOutcomeEq, hObservation⟩ | hFails
  · subst outcome
    exact Or.inl ⟨result, hOutcome, hObservation⟩
  · exact Or.inr ⟨outcome, hOutcome, hFails⟩

theorem of_outcomeSafelyTracksResult
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gas : Nat} {reference : EVMResult}
    (hGasFits : gas < EvmYul.UInt256.size)
    (hTracks :
      OpenXOutcomeSafelyTracksResult
        (Assembly.GasAware.validJumps target) evmFuel
        (Assembly.GasAware.installCodeAndGas target gas initial) reference)
    (hAgree : OpenXResultAgrees targetResult reference) :
    OpenXCommittedSafeAt target initial targetResult evmFuel gas := by
  rcases hTracks with ⟨outcome, hOutcome, hTracksOutcome⟩
  exact
    ⟨hGasFits, outcome, hOutcome,
      Assembly.GasAware.XRunOutcomeSafelyTracks.outcomeSafelyMatches_of_result
        hTracksOutcome hAgree.committedObservation⟩

end OpenXCommittedSafeAt

namespace OpenXCommittedSafeBelow

theorem mono
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBoundSmall gasBoundLarge : Nat}
    (hLe : gasBoundSmall ≤ gasBoundLarge)
    (hBelow :
      OpenXCommittedSafeBelow target initial targetResult evmFuel
        gasBoundLarge) :
    OpenXCommittedSafeBelow target initial targetResult evmFuel
      gasBoundSmall := by
  intro gas hLow hGasFits
  exact hBelow gas (Nat.lt_of_lt_of_le hLow hLe) hGasFits

theorem of_tracksResult
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hTracks :
      OpenXCommittedSafeBelowTracksResult target initial targetResult evmFuel
        gasBound) :
    OpenXCommittedSafeBelow target initial targetResult evmFuel gasBound := by
  intro gas hLow hGasFits
  rcases hTracks gas hLow hGasFits with
    ⟨reference, hAgree, hTracksResult⟩
  exact
    OpenXCommittedSafeAt.of_outcomeSafelyTracksResult hGasFits
      hTracksResult hAgree

theorem of_trace_or_failure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hAt :
      ∀ gas,
        gas < gasBound →
          gas < EvmYul.UInt256.size →
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ result : EVMResult,
                OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace result ∧
                  OpenXResultAgrees targetResult result) ∨
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ outcome : Except EVMException EVMResult,
                OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
                  evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace outcome ∧
                  Assembly.GasAware.XRunOutcomeFails outcome)) :
    OpenXCommittedSafeBelow target initial targetResult evmFuel gasBound := by
  intro gas hLow hGasFits
  rcases hAt gas hLow hGasFits with
    ⟨candidateTrace, result, hTrace, hAgree⟩ |
    ⟨candidateTrace, outcome, hTrace, hFails⟩
  · exact
      ⟨hGasFits, .ok result, ⟨candidateTrace, hTrace⟩,
        hAgree.outcomeSafelyMatches⟩
  · exact
      ⟨hGasFits, outcome, ⟨candidateTrace, hTrace⟩, Or.inr hFails⟩

theorem of_trace_observation_or_failure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hAt :
      ∀ gas,
        gas < gasBound →
          gas < EvmYul.UInt256.size →
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ result : EVMResult,
                OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace result ∧
                  Assembly.GasAware.XResultCommittedObservation result =
                    Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ outcome : Except EVMException EVMResult,
                OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
                  evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace outcome ∧
                  Assembly.GasAware.XRunOutcomeFails outcome)) :
    OpenXCommittedSafeBelow target initial targetResult evmFuel gasBound := by
  intro gas hLow hGasFits
  rcases hAt gas hLow hGasFits with
    ⟨candidateTrace, result, hTrace, hObservation⟩ |
    ⟨candidateTrace, outcome, hTrace, hFails⟩
  · exact
      ⟨hGasFits, .ok result, ⟨candidateTrace, hTrace⟩,
        Or.inl ⟨result, rfl, hObservation⟩⟩
  · exact
      ⟨hGasFits, outcome, ⟨candidateTrace, hTrace⟩, Or.inr hFails⟩

theorem of_traceObservationOrFailure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hAt :
      ∀ gas,
        gas < gasBound →
          gas < EvmYul.UInt256.size →
            ∃ candidateTrace : OpenExternal.OpenTrace,
              OpenXTraceObservationOrFailure
                (Assembly.GasAware.validJumps target) evmFuel
                (Assembly.GasAware.installCodeAndGas target gas initial)
                candidateTrace targetResult) :
    OpenXCommittedSafeBelow target initial targetResult evmFuel gasBound := by
  intro gas hLow hGasFits
  rcases hAt gas hLow hGasFits with
    ⟨candidateTrace, hClassified⟩
  rcases
      OpenXTraceObservationOrFailure.to_outcomeSafelyMatches
        hClassified with
    ⟨outcome, hTrace, hMatches⟩
  exact ⟨hGasFits, outcome, ⟨candidateTrace, hTrace⟩, hMatches⟩

theorem of_traceObservationOrFailure_exists
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget target)
    (hClassified :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps target) evmFuel full
              candidateTrace targetResult) :
    OpenXCommittedSafeBelow target initial targetResult evmFuel gasBound :=
  of_traceObservationOrFailure_below
    (target := target) (initial := initial) (targetResult := targetResult)
    (evmFuel := evmFuel) (gasBound := gasBound)
    (fun gas _hLow hGasFits =>
      hClassified
        (Assembly.GasAware.GasExecRel.installCodeAndGas_of_code_eq
          (target := target) (gas := gas) (initial := initial)
          hInitialCode))

end OpenXCommittedSafeBelow

namespace OpenXOutcomeTraceExistsBelow

theorem mono
    {target : Assembly.TargetProgram} {initial : EVMState}
    {evmFuel gasBoundSmall gasBoundLarge : Nat}
    (hLe : gasBoundSmall ≤ gasBoundLarge)
    (hExists :
      OpenXOutcomeTraceExistsBelow target initial evmFuel gasBoundLarge) :
    OpenXOutcomeTraceExistsBelow target initial evmFuel gasBoundSmall := by
  intro gas hLow hGasFits
  exact hExists gas (Nat.lt_of_lt_of_le hLow hLe) hGasFits

theorem zero_bound
    {target : Assembly.TargetProgram} {initial : EVMState}
    {evmFuel : Nat} :
    OpenXOutcomeTraceExistsBelow target initial evmFuel 0 := by
  intro gas hLow hGasFits
  exact (Nat.not_lt_zero gas hLow).elim

theorem succ_of_at
    {target : Assembly.TargetProgram} {initial : EVMState}
    {evmFuel gasBound : Nat}
    (hBelow :
      OpenXOutcomeTraceExistsBelow target initial evmFuel gasBound)
    (hAt : OpenXOutcomeTraceExistsAt target initial evmFuel gasBound) :
    OpenXOutcomeTraceExistsBelow target initial evmFuel gasBound.succ := by
  intro gas hLow hGasFits
  by_cases hEq : gas = gasBound
  · subst gas
    exact hAt hGasFits
  · have hLe : gas ≤ gasBound := Nat.le_of_lt_succ hLow
    have hLt : gas < gasBound := Nat.lt_of_le_of_ne hLe hEq
    exact hBelow gas hLt hGasFits

end OpenXOutcomeTraceExistsBelow

namespace OpenXOutcomeTraceExistsForAllGas

theorem of_openResult
    {target : Assembly.TargetProgram} {initial : EVMState}
    {evmFuel : Nat} :
    OpenXOutcomeTraceExistsForAllGas target initial evmFuel := by
  intro gas _hGasFits
  rcases
      OpenExternal.OpenResultResolves.exists_trace
        (openX evmFuel (Assembly.GasAware.validJumps target)
          (Assembly.GasAware.installCodeAndGas target gas initial)) with
    ⟨trace, outcome, hOutcome⟩
  exact ⟨trace, outcome, hOutcome⟩

theorem below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {evmFuel gasBound : Nat}
    (hExists : OpenXOutcomeTraceExistsForAllGas target initial evmFuel) :
    OpenXOutcomeTraceExistsBelow target initial evmFuel gasBound := by
  intro gas _hLow hGasFits
  exact hExists gas hGasFits

theorem below_of_openResult
    {target : Assembly.TargetProgram} {initial : EVMState}
    {evmFuel gasBound : Nat} :
    OpenXOutcomeTraceExistsBelow target initial evmFuel gasBound :=
  below of_openResult

end OpenXOutcomeTraceExistsForAllGas

namespace OpenXAllOutcomeTracesSafelyMatchAt

theorem to_committedSafeAt
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gas : Nat}
    (hExists : OpenXOutcomeTraceExistsAt target initial evmFuel gas)
    (hAll :
      OpenXAllOutcomeTracesSafelyMatchAt target initial targetResult
        evmFuel gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    OpenXCommittedSafeAt target initial targetResult evmFuel gas := by
  rcases hExists hGasFits with ⟨trace, outcome, hOutcome⟩
  exact
    ⟨hGasFits, outcome, ⟨trace, hOutcome⟩,
      hAll hGasFits trace outcome hOutcome⟩

end OpenXAllOutcomeTracesSafelyMatchAt

namespace OpenXAllOutcomeTracesSafelyMatchBelow

theorem mono
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBoundSmall gasBoundLarge : Nat}
    (hLe : gasBoundSmall ≤ gasBoundLarge)
    (hAll :
      OpenXAllOutcomeTracesSafelyMatchBelow target initial targetResult
        evmFuel gasBoundLarge) :
    OpenXAllOutcomeTracesSafelyMatchBelow target initial targetResult evmFuel
      gasBoundSmall := by
  intro gas hLow hGasFits trace outcome hOutcome
  exact hAll gas (Nat.lt_of_lt_of_le hLow hLe) hGasFits trace outcome
    hOutcome

theorem zero_bound
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult} {evmFuel : Nat} :
    OpenXAllOutcomeTracesSafelyMatchBelow target initial targetResult evmFuel
      0 := by
  intro gas hLow hGasFits trace outcome hOutcome
  exact (Nat.not_lt_zero gas hLow).elim

theorem succ_of_at
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult} {evmFuel gasBound : Nat}
    (hBelow :
      OpenXAllOutcomeTracesSafelyMatchBelow target initial targetResult
        evmFuel gasBound)
    (hAt :
      OpenXAllOutcomeTracesSafelyMatchAt target initial targetResult
        evmFuel gasBound) :
    OpenXAllOutcomeTracesSafelyMatchBelow target initial targetResult evmFuel
      gasBound.succ := by
  intro gas hLow hGasFits trace outcome hOutcome
  by_cases hEq : gas = gasBound
  · subst gas
    exact hAt hGasFits trace outcome hOutcome
  · have hLe : gas ≤ gasBound := Nat.le_of_lt_succ hLow
    have hLt : gas < gasBound := Nat.lt_of_le_of_ne hLe hEq
    exact hBelow gas hLt hGasFits trace outcome hOutcome

theorem to_committedSafeBelow
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hExists : OpenXOutcomeTraceExistsBelow target initial evmFuel gasBound)
    (hAll :
      OpenXAllOutcomeTracesSafelyMatchBelow target initial targetResult
        evmFuel gasBound) :
    OpenXCommittedSafeBelow target initial targetResult evmFuel gasBound := by
  intro gas hLow hGasFits
  exact
    OpenXAllOutcomeTracesSafelyMatchAt.to_committedSafeAt
      (hExists gas hLow) (hAll gas hLow) hGasFits

end OpenXAllOutcomeTracesSafelyMatchBelow

namespace OpenXAllOutcomeTracesSafelyMatchForAllGas

theorem of_below_and_above
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hBelow :
      OpenXAllOutcomeTracesSafelyMatchBelow target initial targetResult
        evmFuel gasBound)
    (hAbove :
      OpenXAllOutcomeTracesSafelyMatchAbove target initial targetResult
        evmFuel gasBound) :
    OpenXAllOutcomeTracesSafelyMatchForAllGas target initial targetResult
      evmFuel := by
  intro gas hGasFits trace outcome hOutcome
  by_cases hLow : gas < gasBound
  · exact hBelow gas hLow hGasFits trace outcome hOutcome
  · exact hAbove gas (Nat.le_of_not_gt hLow) hGasFits trace outcome hOutcome

theorem to_committedSafeForAllGas
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel : Nat}
    (hExists : OpenXOutcomeTraceExistsForAllGas target initial evmFuel)
    (hAll :
      OpenXAllOutcomeTracesSafelyMatchForAllGas target initial targetResult
        evmFuel) :
    OpenXCommittedSafeForAllGas target initial targetResult evmFuel := by
  intro gas hGasFits
  exact
    OpenXAllOutcomeTracesSafelyMatchAt.to_committedSafeAt
      (hExists gas) (hAll gas) hGasFits

end OpenXAllOutcomeTracesSafelyMatchForAllGas

namespace OpenXCommittedSafeForAllGas

theorem of_below_and_above
    {target : Assembly.TargetProgram} {initial : EVMState}
    {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hBelow :
      OpenXCommittedSafeBelow target initial targetResult evmFuel gasBound)
    (hAbove :
      OpenXCommittedSafeAbove target initial targetResult evmFuel gasBound) :
    OpenXCommittedSafeForAllGas target initial targetResult evmFuel := by
  intro gas hGasFits
  by_cases hLow : gas < gasBound
  · exact hBelow gas hLow hGasFits
  · exact hAbove gas (Nat.le_of_not_gt hLow) hGasFits

end OpenXCommittedSafeForAllGas

theorem openX_current_gasless_call_continue_exists_of_step_checks
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hRest :
      ∀ {gasPost : EVMState},
        Assembly.GasAware.GasExecRel gasPost
          (EvmYul.EVM.State.incrPC (call.resume response)) →
        ∃ result,
          OpenXTraceResult validJumps fuel gasPost tailTrace result ∧
          OpenXResultAgrees targetResult result) :
    ∃ result,
      OpenXTraceResult validJumps (fuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace) result ∧
      OpenXResultAgrees targetResult result := by
  obtain ⟨gasCall, hGasCall, hSite, hPostRel⟩ :=
    evmOpenCall?_gasChargedState_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall response
  obtain ⟨result, hRestTrace, hAgree⟩ := hRest hPostRel
  have hTrace :
      OpenExternal.OpenResultResolves
        (openX (fuel + 1) validJumps full)
        ({ site := gasCall.site, response := response } :: tailTrace)
        (.ok result) :=
    openX_current_call_continue
      (fuel := fuel) (validJumps := validJumps) (state := full)
      (op := op) (arg := arg) (kind := kind) (call := gasCall)
      (response := response) (tailTrace := tailTrace) (result := result)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hKind hGasCall hRestTrace
  exact ⟨result, by simpa [hSite] using hTrace, hAgree⟩

theorem openX_current_gasless_call_continue_exists_of_step_checks_actual_post
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hRest :
      ∀ {gasCall : OpenExternal.OpenCall EVMState},
        OpenExternal.CallKind.evmOpenCall? (gasChargedState full op) kind =
            some gasCall →
          ∃ result,
            OpenXTraceResult validJumps fuel
              (EvmYul.EVM.State.incrPC
                (finishGasAwareCall gasCall response))
              tailTrace result ∧
            OpenXResultAgrees targetResult result) :
    ∃ result,
      OpenXTraceResult validJumps (fuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace) result ∧
      OpenXResultAgrees targetResult result := by
  obtain ⟨gasCall, hGasCall, hSite, _hPostRel⟩ :=
    evmOpenCall?_gasChargedState_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall response
  obtain ⟨result, hRestTrace, hAgree⟩ := hRest hGasCall
  have hTrace :
      OpenExternal.OpenResultResolves
        (openX (fuel + 1) validJumps full)
        ({ site := gasCall.site, response := response } :: tailTrace)
        (.ok result) :=
    openX_current_call_continue
      (fuel := fuel) (validJumps := validJumps) (state := full)
      (op := op) (arg := arg) (kind := kind) (call := gasCall)
      (response := response) (tailTrace := tailTrace) (result := result)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hKind hGasCall hRestTrace
  exact ⟨result, by simpa [hSite] using hTrace, hAgree⟩

theorem openX_current_gasless_call_continue_outcome_inv_of_step_checks_actual_post
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace)
        outcome) :
    ∃ gasCall : OpenExternal.OpenCall EVMState,
      OpenExternal.CallKind.evmOpenCall? (gasChargedState full op) kind =
          some gasCall ∧
        gasCall.site = call.site ∧
          OpenXOutcomeTraceResult validJumps fuel
            (EvmYul.EVM.State.incrPC
              (finishGasAwareCall gasCall response))
            tailTrace outcome := by
  obtain ⟨gasCall, hGasCall, hSite, _hPostRel⟩ :=
    evmOpenCall?_gasChargedState_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall response
  refine ⟨gasCall, hGasCall, hSite, ?_⟩
  have hTraceGas :
      OpenXOutcomeTraceResult validJumps (fuel + 1) full
        ({ site := gasCall.site, response := response } :: tailTrace)
        outcome := by
    simpa [hSite] using hTrace
  exact
    openX_current_call_continue_outcome_inv
      (fuel := fuel) (validJumps := validJumps) (state := full)
      (op := op) (arg := arg) (kind := kind) (call := gasCall)
      (response := response) (tailTrace := tailTrace)
      (outcome := outcome)
      hDecode (xStepException?_none_of_step_checks hStepChecks)
      hKind hGasCall hTraceGas

theorem openX_current_gasless_call_any_outcome_inv_of_step_checks_actual_post
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {candidateTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) full candidateTrace
        outcome) :
    ∃ response : OpenExternal.CallResponse,
    ∃ tailTrace : OpenExternal.OpenTrace,
    ∃ gasCall : OpenExternal.OpenCall EVMState,
      candidateTrace =
          OpenExternal.OpenEvent.call call.site response :: tailTrace ∧
        OpenExternal.CallKind.evmOpenCall? (gasChargedState full op) kind =
            some gasCall ∧
          gasCall.site = call.site ∧
            OpenXOutcomeTraceResult validJumps fuel
              (EvmYul.EVM.State.incrPC
                (finishGasAwareCall gasCall response))
              tailTrace outcome := by
  obtain ⟨gasCall, hGasCall, hSite⟩ :=
    evmOpenCall?_gasChargedState_site_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall
  have hTrace' :
      OpenExternal.OpenResultResolves
        (OpenExternal.OpenResult.bind (evmGasAwareCallResult gasCall)
          (continueAfterStep (openX fuel validJumps) op))
        candidateTrace outcome := by
    unfold OpenXOutcomeTraceResult at hTrace
    rw [openX_succ] at hTrace
    simp [hDecode, xStepException?_none_of_step_checks hStepChecks] at hTrace
    rw [openStepAfterChecks_call (fuel := fuel) (arg := arg)
      (state := full) hKind hGasCall] at hTrace
    exact hTrace
  rcases OpenExternal.OpenResultResolves.bind_inv hTrace' with
    hError | hOk
  · rcases hError with ⟨err, hSource, _hOutcome⟩
    unfold evmGasAwareCallResult at hSource
    cases hSource with
    | call hTail =>
        cases hTail
  · rcases hOk with
      ⟨left, right, value, hTraceEq, hSource, hSuffix⟩
    unfold evmGasAwareCallResult at hSource
    cases hSource with
    | @call sourceCall response sourceTrace sourceResult hTail =>
        cases hTail
        simp at hTraceEq
        refine ⟨response, right, gasCall, ?_, hGasCall, hSite, ?_⟩
        · simpa [hSite] using hTraceEq
        · have hNoHalt :
              Assembly.GasAware.XStepHaltOutput? op
                (EvmYul.EVM.State.incrPC
                  (finishGasAwareCall gasCall response)) = none :=
            XStepHaltOutput?_none_of_callKind hKind
          simpa [OpenXOutcomeTraceResult, continueAfterStep, hNoHalt]
            using hSuffix

theorem openX_current_gasless_call_any_outcome_inv_of_exception_actual_post
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {candidateTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hException : xStepException? validJumps full op = none)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) full candidateTrace
        outcome) :
    ∃ response : OpenExternal.CallResponse,
    ∃ tailTrace : OpenExternal.OpenTrace,
    ∃ gasCall : OpenExternal.OpenCall EVMState,
      candidateTrace =
          OpenExternal.OpenEvent.call call.site response :: tailTrace ∧
        OpenExternal.CallKind.evmOpenCall? (gasChargedState full op) kind =
            some gasCall ∧
          gasCall.site = call.site ∧
            OpenXOutcomeTraceResult validJumps fuel
              (EvmYul.EVM.State.incrPC
                (finishGasAwareCall gasCall response))
              tailTrace outcome := by
  obtain ⟨gasCall, hGasCall, hSite⟩ :=
    evmOpenCall?_gasChargedState_site_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall
  have hTrace' :
      OpenExternal.OpenResultResolves
        (OpenExternal.OpenResult.bind (evmGasAwareCallResult gasCall)
          (continueAfterStep (openX fuel validJumps) op))
        candidateTrace outcome := by
    unfold OpenXOutcomeTraceResult at hTrace
    rw [openX_succ] at hTrace
    simp [hDecode, hException] at hTrace
    rw [openStepAfterChecks_call (fuel := fuel) (arg := arg)
      (state := full) hKind hGasCall] at hTrace
    exact hTrace
  rcases OpenExternal.OpenResultResolves.bind_inv hTrace' with
    hError | hOk
  · rcases hError with ⟨err, hSource, _hOutcome⟩
    unfold evmGasAwareCallResult at hSource
    cases hSource with
    | call hTail =>
        cases hTail
  · rcases hOk with
      ⟨left, right, value, hTraceEq, hSource, hSuffix⟩
    unfold evmGasAwareCallResult at hSource
    cases hSource with
    | @call sourceCall response sourceTrace sourceResult hTail =>
        cases hTail
        simp at hTraceEq
        refine ⟨response, right, gasCall, ?_, hGasCall, hSite, ?_⟩
        · simpa [hSite] using hTraceEq
        · have hNoHalt :
              Assembly.GasAware.XStepHaltOutput? op
                (EvmYul.EVM.State.incrPC
                  (finishGasAwareCall gasCall response)) = none :=
            XStepHaltOutput?_none_of_callKind hKind
          simpa [OpenXOutcomeTraceResult, continueAfterStep, hNoHalt]
            using hSuffix

theorem openX_current_gasless_call_continue_outcome_safelyTracks_of_step_checks_actual_post
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hTail :
      ∀ {gasCall : OpenExternal.OpenCall EVMState},
        OpenExternal.CallKind.evmOpenCall? (gasChargedState full op) kind =
            some gasCall →
          OpenXStateAllOutcomeTracesSafelyTrackResult validJumps fuel
            (EvmYul.EVM.State.incrPC
              (finishGasAwareCall gasCall response))
            reference)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace)
        outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  rcases
      openX_current_gasless_call_continue_outcome_inv_of_step_checks_actual_post
        (fuel := fuel) (validJumps := validJumps) (full := full)
        (target := target) (op := op) (arg := arg) (kind := kind)
        (call := call) (response := response) (tailTrace := tailTrace)
        (outcome := outcome)
        hRel hDecode hStepChecks hKind hCall hTrace with
    ⟨gasCall, hGasCall, _hSite, hTailTrace⟩
  exact hTail hGasCall tailTrace outcome hTailTrace

theorem openX_current_gasless_call_continue_outcome_safelyTracks_of_step_checks_actual_post_gasrel_tail
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {outcome : Except EVMException EVMResult}
    {reference : EVMResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hTail :
      OpenXGasRelStateAllOutcomeTracesSafelyTrackResult validJumps fuel
        (EvmYul.EVM.State.incrPC (call.resume response)) reference)
    (hTrace :
      OpenXOutcomeTraceResult validJumps (fuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace)
        outcome) :
    Assembly.GasAware.XRunOutcomeSafelyTracks outcome (.ok reference) := by
  rcases
      openX_current_gasless_call_continue_outcome_inv_of_step_checks_actual_post
        (fuel := fuel) (validJumps := validJumps) (full := full)
        (target := target) (op := op) (arg := arg) (kind := kind)
        (call := call) (response := response) (tailTrace := tailTrace)
        (outcome := outcome)
        hRel hDecode hStepChecks hKind hCall hTrace with
    ⟨gasCall, hGasCall, _hSite, hTailTrace⟩
  have hPostRel :
      Assembly.GasAware.GasExecRel
        (EvmYul.EVM.State.incrPC
          (finishGasAwareCall gasCall response))
        (EvmYul.EVM.State.incrPC (call.resume response)) :=
    evmOpenCall?_gasChargedState_resume_gasExecRel_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall hGasCall response
  exact hTail _ hPostRel tailTrace outcome hTailTrace

theorem openX_current_gasless_call_continue_trace_observation_or_failure_of_step_checks_actual_post
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hRest :
      ∀ {gasCall : OpenExternal.OpenCall EVMState},
        OpenExternal.CallKind.evmOpenCall?
            (gasChargedState full op) kind = some gasCall →
          (∃ result,
            OpenXTraceResult validJumps fuel
              (EvmYul.EVM.State.incrPC
                (finishGasAwareCall gasCall response))
              tailTrace result ∧
              Assembly.GasAware.XResultCommittedObservation result =
                Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
          (∃ outcome : Except EVMException EVMResult,
            OpenXOutcomeTraceResult validJumps fuel
              (EvmYul.EVM.State.incrPC
                (finishGasAwareCall gasCall response))
              tailTrace outcome ∧
              Assembly.GasAware.XRunOutcomeFails outcome)) :
    (∃ result,
      OpenXTraceResult validJumps (fuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace) result ∧
        Assembly.GasAware.XResultCommittedObservation result =
          Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
    (∃ outcome : Except EVMException EVMResult,
      OpenXOutcomeTraceResult validJumps (fuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace) outcome ∧
        Assembly.GasAware.XRunOutcomeFails outcome) := by
  obtain ⟨gasCall, hGasCall, hSite, _hPostRel⟩ :=
    evmOpenCall?_gasChargedState_of_gasExecRel
      (full := full) (target := target) (op := op)
      hRel hCall response
  rcases hRest hGasCall with
    ⟨result, hRestTrace, hObservation⟩ |
    ⟨outcome, hRestTrace, hFails⟩
  · have hTrace :
        OpenExternal.OpenResultResolves
          (openX (fuel + 1) validJumps full)
          ({ site := gasCall.site, response := response } :: tailTrace)
          (.ok result) :=
      openX_current_call_continue
        (fuel := fuel) (validJumps := validJumps) (state := full)
        (op := op) (arg := arg) (kind := kind) (call := gasCall)
        (response := response) (tailTrace := tailTrace) (result := result)
        hDecode (xStepException?_none_of_step_checks hStepChecks)
        hKind hGasCall hRestTrace
    exact
      Or.inl
        ⟨result, by simpa [hSite] using hTrace, hObservation⟩
  · have hTrace :
        OpenExternal.OpenResultResolves
          (openX (fuel + 1) validJumps full)
          ({ site := gasCall.site, response := response } :: tailTrace)
          outcome :=
      openX_current_call_continue_outcome
        (fuel := fuel) (validJumps := validJumps) (state := full)
        (op := op) (arg := arg) (kind := kind) (call := gasCall)
        (response := response) (tailTrace := tailTrace)
        (outcome := outcome)
        hDecode (xStepException?_none_of_step_checks hStepChecks)
        hKind hGasCall hRestTrace
    exact
      Or.inr
        ⟨outcome, by simpa [hSite] using hTrace, hFails⟩

theorem openX_current_gasless_call_continue_traceObservationOrFailure_of_step_checks_actual_post
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hRest :
      ∀ {gasCall : OpenExternal.OpenCall EVMState},
        OpenExternal.CallKind.evmOpenCall?
            (gasChargedState full op) kind = some gasCall →
          OpenXTraceObservationOrFailure validJumps fuel
            (EvmYul.EVM.State.incrPC
              (finishGasAwareCall gasCall response))
            tailTrace targetResult) :
    OpenXTraceObservationOrFailure validJumps (fuel + 1) full
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      targetResult :=
  openX_current_gasless_call_continue_trace_observation_or_failure_of_step_checks_actual_post
    hRel hDecode hStepChecks hKind hCall hRest

theorem openX_current_gasless_call_continue_traceObservationOrFailure_exists_of_nonGas_actual_post
    {fuel : Nat} {validJumps : Array Word}
    {full target : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    (hRel : Assembly.GasAware.GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc = some (op, arg))
    (hNonGas :
      Assembly.GasAware.XNonGasChecksPass validJumps full op)
    (hKind : OpenExternal.CallKind.ofEVMOperation? op = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? target kind = some call)
    (hRest :
      ∀ {gasCall : OpenExternal.OpenCall EVMState},
        OpenExternal.CallKind.evmOpenCall?
            (gasChargedState full op) kind = some gasCall →
          OpenXTraceObservationOrFailure validJumps fuel
            (EvmYul.EVM.State.incrPC
              (finishGasAwareCall gasCall response))
            tailTrace targetResult) :
    ∃ candidateTrace : OpenExternal.OpenTrace,
      OpenXTraceObservationOrFailure validJumps (fuel + 1) full
        candidateTrace targetResult := by
  rcases xStepException?_none_or_outOfGas_of_nonGas_checks hNonGas with
    hNoException | hOutOfGas
  · obtain ⟨gasCall, hGasCall, hSite, _hPostRel⟩ :=
      evmOpenCall?_gasChargedState_of_gasExecRel
        (full := full) (target := target) (op := op)
        hRel hCall response
    refine
      ⟨OpenExternal.OpenEvent.call call.site response :: tailTrace, ?_⟩
    rcases hRest hGasCall with
      ⟨result, hRestTrace, hObservation⟩ |
      ⟨outcome, hRestTrace, hFails⟩
    · have hTrace :
          OpenExternal.OpenResultResolves
            (openX (fuel + 1) validJumps full)
            ({ site := gasCall.site, response := response } :: tailTrace)
            (.ok result) :=
        openX_current_call_continue
          (fuel := fuel) (validJumps := validJumps) (state := full)
          (op := op) (arg := arg) (kind := kind) (call := gasCall)
          (response := response) (tailTrace := tailTrace) (result := result)
          hDecode hNoException hKind hGasCall hRestTrace
      exact
        Or.inl
          ⟨result, by simpa [hSite] using hTrace, hObservation⟩
    · have hTrace :
          OpenExternal.OpenResultResolves
            (openX (fuel + 1) validJumps full)
            ({ site := gasCall.site, response := response } :: tailTrace)
            outcome :=
        openX_current_call_continue_outcome
          (fuel := fuel) (validJumps := validJumps) (state := full)
          (op := op) (arg := arg) (kind := kind) (call := gasCall)
          (response := response) (tailTrace := tailTrace)
          (outcome := outcome)
          hDecode hNoException hKind hGasCall hRestTrace
      exact
        Or.inr
          ⟨outcome, by simpa [hSite] using hTrace, hFails⟩
  · exact
      ⟨[],
        OpenXTraceObservationOrFailure.of_current_outOfGas_exception
          (fuel := fuel) hDecode hOutOfGas⟩

def OpenXReplayAbove
    (target : Assembly.TargetProgram) (initial : EVMState)
    (trace : OpenExternal.OpenTrace) (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      gas < EvmYul.UInt256.size →
        ∃ result,
          OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
            (Assembly.GasAware.installCodeAndGas target gas initial)
            trace result ∧
          OpenXResultAgrees targetResult result

def OpenXReplayAt
    (target : Assembly.TargetProgram) (initial : EVMState)
    (trace : OpenExternal.OpenTrace) (targetResult : Assembly.StepResult)
    (evmFuel gas : Nat) : Prop :=
  gas < EvmYul.UInt256.size ∧
    ∃ result,
      OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
        (Assembly.GasAware.installCodeAndGas target gas initial)
        trace result ∧
      OpenXResultAgrees targetResult result

def OpenXReplaySomeGas
    (target : Assembly.TargetProgram) (initial : EVMState)
    (trace : OpenExternal.OpenTrace) (targetResult : Assembly.StepResult)
    (evmFuel : Nat) : Prop :=
  ∃ gas : Nat, OpenXReplayAt target initial trace targetResult evmFuel gas

namespace OpenXReplayAt

theorem to_outcomeSafelyTracksResult
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gas : Nat}
    (hReplay :
      OpenXReplayAt target initial trace targetResult evmFuel gas) :
    ∃ reference : EVMResult,
      OpenXResultAgrees targetResult reference ∧
        OpenXOutcomeSafelyTracksResult
          (Assembly.GasAware.validJumps target) evmFuel
          (Assembly.GasAware.installCodeAndGas target gas initial)
          reference := by
  rcases hReplay with ⟨_hGasFits, result, hTrace, hAgree⟩
  exact
    ⟨result, hAgree,
      OpenXOutcomeSafelyTracksResult.of_trace hTrace⟩

theorem to_committedSafeAt
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gas : Nat}
    (hReplay :
      OpenXReplayAt target initial trace targetResult evmFuel gas) :
    OpenXCommittedSafeAt target initial targetResult evmFuel gas := by
  rcases hReplay with ⟨hGasFits, result, hTrace, hAgree⟩
  exact
    ⟨hGasFits, .ok result, ⟨trace, hTrace⟩,
      hAgree.outcomeSafelyMatches⟩

end OpenXReplayAt

namespace OpenXReplayAbove

theorem to_replayAt
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound gas : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hGasAtLeast : gasBound ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    OpenXReplayAt target initial trace targetResult evmFuel gas :=
  ⟨hGasFits, hReplay gas hGasAtLeast hGasFits⟩

theorem to_outcomeSafelyTracksResult
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound gas : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hGasAtLeast : gasBound ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    ∃ reference : EVMResult,
      OpenXResultAgrees targetResult reference ∧
        OpenXOutcomeSafelyTracksResult
          (Assembly.GasAware.validJumps target) evmFuel
          (Assembly.GasAware.installCodeAndGas target gas initial)
          reference :=
  (hReplay.to_replayAt hGasAtLeast hGasFits).to_outcomeSafelyTracksResult

theorem to_replaySomeGas
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hFeasible :
      ∃ gas : Nat, gasBound ≤ gas ∧ gas < EvmYul.UInt256.size) :
    OpenXReplaySomeGas target initial trace targetResult evmFuel := by
  rcases hFeasible with ⟨gas, hGasAtLeast, hGasFits⟩
  exact ⟨gas, hReplay.to_replayAt hGasAtLeast hGasFits⟩

theorem to_replaySomeGas_of_bound_lt
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hGasBoundFits : gasBound < EvmYul.UInt256.size) :
    OpenXReplaySomeGas target initial trace targetResult evmFuel :=
  hReplay.to_replaySomeGas ⟨gasBound, Nat.le_refl gasBound, hGasBoundFits⟩

theorem to_committedSafeAbove
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound) :
    OpenXCommittedSafeAbove target initial targetResult evmFuel gasBound := by
  intro gas hGasAtLeast hGasFits
  exact
    (hReplay.to_replayAt hGasAtLeast hGasFits).to_committedSafeAt

theorem to_committedSafeForAllGas_of_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hBelow :
      OpenXCommittedSafeBelow target initial targetResult evmFuel gasBound) :
    OpenXCommittedSafeForAllGas target initial targetResult evmFuel :=
  OpenXCommittedSafeForAllGas.of_below_and_above hBelow
    hReplay.to_committedSafeAbove

theorem to_committedSafeForAllGas_of_trace_or_failure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hAt :
      ∀ gas,
        gas < gasBound →
          gas < EvmYul.UInt256.size →
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ result : EVMResult,
                OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace result ∧
                  OpenXResultAgrees targetResult result) ∨
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ outcome : Except EVMException EVMResult,
                OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
                  evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace outcome ∧
                  Assembly.GasAware.XRunOutcomeFails outcome)) :
    OpenXCommittedSafeForAllGas target initial targetResult evmFuel :=
  hReplay.to_committedSafeForAllGas_of_below
    (OpenXCommittedSafeBelow.of_trace_or_failure_below hAt)

theorem to_committedSafeForAllGas_of_trace_observation_or_failure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hAt :
      ∀ gas,
        gas < gasBound →
          gas < EvmYul.UInt256.size →
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ result : EVMResult,
                OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace result ∧
                  Assembly.GasAware.XResultCommittedObservation result =
                    Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
            (∃ candidateTrace : OpenExternal.OpenTrace,
              ∃ outcome : Except EVMException EVMResult,
                OpenXOutcomeTraceResult (Assembly.GasAware.validJumps target)
                  evmFuel
                  (Assembly.GasAware.installCodeAndGas target gas initial)
                  candidateTrace outcome ∧
                  Assembly.GasAware.XRunOutcomeFails outcome)) :
    OpenXCommittedSafeForAllGas target initial targetResult evmFuel :=
  hReplay.to_committedSafeForAllGas_of_below
    (OpenXCommittedSafeBelow.of_trace_observation_or_failure_below hAt)

theorem to_committedSafeForAllGas_of_traceObservationOrFailure_below
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hAt :
      ∀ gas,
        gas < gasBound →
          gas < EvmYul.UInt256.size →
            ∃ candidateTrace : OpenExternal.OpenTrace,
              OpenXTraceObservationOrFailure
                (Assembly.GasAware.validJumps target) evmFuel
                (Assembly.GasAware.installCodeAndGas target gas initial)
                candidateTrace targetResult) :
    OpenXCommittedSafeForAllGas target initial targetResult evmFuel :=
  hReplay.to_committedSafeForAllGas_of_below
    (OpenXCommittedSafeBelow.of_traceObservationOrFailure_below hAt)

theorem to_committedSafeForAllGas_of_traceObservationOrFailure_exists
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget target)
    (hClassified :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps target) evmFuel full
              candidateTrace targetResult) :
    OpenXCommittedSafeForAllGas target initial targetResult evmFuel :=
  hReplay.to_committedSafeForAllGas_of_below
    (OpenXCommittedSafeBelow.of_traceObservationOrFailure_exists
      hInitialCode hClassified)

theorem to_committedSafeForAllGas_of_fixedTrace_le
    {target : Assembly.TargetProgram} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound lowGasBound : Nat} {reference : EVMResult}
    (hReplay :
      OpenXReplayAbove target initial trace targetResult evmFuel gasBound)
    (hLe : gasBound ≤ lowGasBound)
    (hTrace :
      OpenXCommittedSafeBelowTracksFixedTraceResult target initial
        targetResult evmFuel lowGasBound reference) :
    OpenXCommittedSafeForAllGas target initial targetResult evmFuel :=
  hReplay.to_committedSafeForAllGas_of_below
    (OpenXCommittedSafeBelow.of_tracksResult
      (OpenXCommittedSafeBelowTracksResult.of_fixedResult
        (OpenXCommittedSafeBelowTracksFixedResult.of_traceResult
          (OpenXCommittedSafeBelowTracksFixedTraceResult.mono hLe
            hTrace))))

end OpenXReplayAbove

def OpenXTracePathDoneContinuation
    (validJumps : Array Word) (targetResult : Assembly.StepResult)
    (evmFuel : Nat) : Prop :=
  ∀ {finalState fullFinal : EVMState},
    targetResult = .running finalState →
      Assembly.GasAware.GasExecRel fullFinal finalState →
        ∃ result,
          OpenXTraceResult validJumps evmFuel fullFinal [] result ∧
          OpenXResultAgrees targetResult result

theorem OpenXTracePathDoneContinuation.halted
    {validJumps : Array Word} {halt : Assembly.Halt} :
    OpenXTracePathDoneContinuation validJumps (.halted halt) 0 := by
  intro finalState _fullFinal hResult _hRel
  cases hResult

theorem OpenXTracePathDoneContinuation.running_of_fallthrough_stop
    {validJumps : Array Word} {target : EVMState}
    (hReady :
      Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
        target) :
    OpenXTracePathDoneContinuation validJumps (.running target) 2 := by
  intro finalState fullFinal hResult hRel
  cases hResult
  obtain ⟨hDecodeNone, hStack, post, hStep, hHalt, hAgree⟩ :=
    hReady fullFinal hRel
  refine
    ⟨EvmYul.EVM.ExecutionResult.success post ByteArray.empty, ?_,
      OpenXResultAgrees.of_assembly hAgree⟩
  exact
    openX_fallthrough_stop_success_of_checks
      (fuel := 1) (validJumps := validJumps) (state := fullFinal)
      (post := post) (output := ByteArray.empty)
      hDecodeNone
      (Assembly.GasAware.XStepChecksPass_stop hStack)
      hStep hHalt

theorem OpenXTracePathDoneContinuation.running_of_clean_fallthrough_stop
    {validJumps : Array Word} {target : EVMState}
    (hReady :
      Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady target) :
    OpenXTracePathDoneContinuation validJumps (.running target) 2 :=
  OpenXTracePathDoneContinuation.running_of_fallthrough_stop
    (Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady.of_clean
      hReady)

theorem OpenXTracePathDoneContinuation.running_of_fallthrough_stop_clear_return_buffers
    {validJumps : Array Word} {target : EVMState}
    (hDecodeNone :
      ∀ full : EVMState,
        Assembly.GasAware.GasExecRel full target →
          EvmYul.EVM.decode full.executionEnv.code full.pc = none)
    (hStack : target.stack.length ≤ 1024) :
    OpenXTracePathDoneContinuation validJumps (.running target) 2 := by
  intro finalState fullFinal hResult hRel
  cases hResult
  let fullStop := Assembly.GasAware.memoryGasState fullFinal
    EvmYul.Operation.STOP
  let chargedStop : EVMState :=
    { fullStop with
      execLength := fullStop.execLength + 1,
      gasAvailable :=
        fullStop.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.C' fullStop EvmYul.Operation.STOP) }
  let post : EVMState := clearReturnBuffers chargedStop
  have hFullStack : fullFinal.stack.length ≤ 1024 := by
    rw [hRel.stack_eq]
    exact hStack
  have hChargedRel :
      Assembly.GasAware.GasExecRel chargedStop target := by
    dsimp [chargedStop, fullStop, Assembly.GasAware.memoryGasState,
      Assembly.GasAware.GasExecRel]
    rw [hRel]
  refine
    ⟨EvmYul.EVM.ExecutionResult.success post ByteArray.empty, ?_, ?_⟩
  · exact
      openX_fallthrough_stop_success_of_checks
        (fuel := 1) (validJumps := validJumps) (state := fullFinal)
        (post := post) (output := ByteArray.empty)
        (hDecodeNone fullFinal hRel)
        (Assembly.GasAware.XStepChecksPass_stop hFullStack)
        (by
          dsimp [post, clearReturnBuffers, chargedStop, fullStop]
          rfl)
        (by
          simp [Assembly.GasAware.XHaltOutput?])
  · exact
      OpenXResultAgrees.running_success_of_gasExecRel_clear_return_buffers
        hChargedRel

def OpenXTracePathDoneObservationOrFailure
    (validJumps : Array Word) (targetResult : Assembly.StepResult)
    (evmFuel : Nat) : Prop :=
  ∀ {finalState fullFinal : EVMState},
    targetResult = .running finalState →
      Assembly.GasAware.GasExecRel fullFinal finalState →
        ∃ candidateTrace : OpenExternal.OpenTrace,
          OpenXTraceObservationOrFailure validJumps evmFuel fullFinal
            candidateTrace targetResult

theorem OpenXTracePathDoneObservationOrFailure.running_of_fallthrough_stop_clear_return_buffers
    {validJumps : Array Word} {target : EVMState}
    (hDecodeNone :
      ∀ full : EVMState,
        Assembly.GasAware.GasExecRel full target →
          EvmYul.EVM.decode full.executionEnv.code full.pc = none)
    (hStack : target.stack.length ≤ 1024) :
    OpenXTracePathDoneObservationOrFailure validJumps (.running target) 2 := by
  intro finalState fullFinal hResult hRel
  cases hResult
  have hFullStack : fullFinal.stack.length ≤ 1024 := by
    rw [hRel.stack_eq]
    exact hStack
  have hNonGas :
      Assembly.GasAware.XNonGasChecksPass validJumps fullFinal
        EvmYul.Operation.STOP :=
    Assembly.GasAware.XNonGasChecksPass_stop hFullStack
  rcases
      xStepException?_none_or_outOfGas_of_nonGas_checks
        hNonGas with hException | hException
  · let fullStop := Assembly.GasAware.memoryGasState fullFinal
      EvmYul.Operation.STOP
    let chargedStop : EVMState :=
      { fullStop with
        execLength := fullStop.execLength + 1,
        gasAvailable :=
          fullStop.gasAvailable -
            EvmYul.UInt256.ofNat
              (EvmYul.EVM.C' fullStop EvmYul.Operation.STOP) }
    let post : EVMState := clearReturnBuffers chargedStop
    have hChargedRel :
        Assembly.GasAware.GasExecRel chargedStop target := by
      dsimp [chargedStop, fullStop, Assembly.GasAware.memoryGasState,
        Assembly.GasAware.GasExecRel]
      rw [hRel]
    refine ⟨[], ?_⟩
    have hTrace :
        OpenXTraceResult validJumps 2 fullFinal []
          (EvmYul.EVM.ExecutionResult.success post ByteArray.empty) := by
      have hTrace' :=
        openX_fallthrough_stop_success_of_exception_none
          (fuel := 1) (validJumps := validJumps) (state := fullFinal)
          (post := post) (output := ByteArray.empty)
          (hDecodeNone fullFinal hRel) hException
          (by
            dsimp [post, clearReturnBuffers, chargedStop, fullStop]
            rfl)
          (by
            dsimp [post, clearReturnBuffers, chargedStop, fullStop,
              Assembly.GasAware.XHaltOutput?]
            rfl)
      simpa [OpenXTraceResult] using hTrace'
    exact
      OpenXTraceObservationOrFailure.of_trace_target_observation
        hTrace
        (OpenXResultAgrees.running_success_of_gasExecRel_clear_return_buffers
          hChargedRel).committedObservation
  · refine ⟨[], ?_⟩
    exact
      OpenXTraceObservationOrFailure.of_fallthrough_stop_outOfGas_exception
        (validJumps := validJumps) (fuel := 1) (state := fullFinal)
        (targetResult := .running target)
        (hDecodeNone fullFinal hRel) hException

def OpenXTraceRelAbove
    (target : Assembly.TargetProgram) (initial : EVMState)
    (trace : OpenExternal.OpenTrace) (targetResult : Assembly.StepResult)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ {full : EVMState},
    gasBound ≤ full.gasAvailable.toNat →
      Assembly.GasAware.GasExecRel full initial →
        ∃ result,
          OpenXTraceResult (Assembly.GasAware.validJumps target) evmFuel
            full trace result ∧
          OpenXResultAgrees targetResult result

theorem openXReplayAbove_of_traceRelAbove
    {targetProgram : Assembly.TargetProgram}
    {gasBound evmFuel : Nat} {initial : EVMState}
    {trace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReplay :
      OpenXTraceRelAbove targetProgram initial trace targetResult
        evmFuel gasBound) :
    OpenXReplayAbove targetProgram initial trace targetResult
      evmFuel gasBound := by
  intro gas hGasAtLeast hGasFits
  have hGasBound :
      gasBound ≤
        (Assembly.GasAware.installCodeAndGas targetProgram gas initial).gasAvailable.toNat := by
    rw [Assembly.GasAware.installCodeAndGas_gasAvailable_toNat hGasFits]
    exact hGasAtLeast
  exact
    hReplay hGasBound
      (Assembly.GasAware.GasExecRel.installCodeAndGas_of_code_eq
        (target := targetProgram) (gas := gas) (initial := initial)
        hInitialCode)

theorem openXTraceRelAbove_done_of_path_done
    {targetProgram : Assembly.TargetProgram}
    {gasBound doneFuel : Nat} {initial : EVMState}
    (hDone :
      OpenXTracePathDoneContinuation
        (Assembly.GasAware.validJumps targetProgram)
        (.running initial) doneFuel) :
    OpenXTraceRelAbove targetProgram initial [] (.running initial)
      doneFuel gasBound := by
  intro full _hGasBound hRel
  exact hDone rfl hRel

theorem openX_runListResult_with_path_continuation_exists_agrees_of_path_ready
    {validJumps : Array Word} :
    ∀ {code : List Assembly.TargetInstr} {target full : EVMState}
      {blockResult finalResult : Assembly.StepResult},
      Assembly.GasAware.XStepTrace.XRunListPathReady validJumps code target
        full blockResult →
      (∀ halt, blockResult = .halted halt → finalResult = .halted halt) →
      (∀ targetFinal fullFinal,
        blockResult = .running targetFinal →
          Assembly.GasAware.GasExecRel fullFinal targetFinal →
            ∃ fuel : Nat, ∃ evmResult,
              OpenXTraceResult validJumps fuel.succ fullFinal []
                evmResult ∧
              OpenXResultAgrees finalResult evmResult) →
      ∃ fuel : Nat, ∃ evmResult,
        OpenXTraceResult validJumps fuel.succ full [] evmResult ∧
          OpenXResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target full blockResult finalResult hReady _hHalted hContinue
      rcases hReady with ⟨hResult, hRel⟩
      subst blockResult
      exact hContinue target full rfl hRel
  | cons instr rest ih =>
      intro target full blockResult finalResult hReady hHalted hContinue
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          Assembly.GasAware.XStepChecksPass validJumps full instr.op :=
        Assembly.GasAware.XStepChecksPass.of_nonGas_required_le
          hNonGas hGas
      cases hStepResult :
          Assembly.Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Assembly.GasAware.Target.stepInstrResult_running_stepInstr
                  hStepResult
              obtain ⟨fullPost, hStepZero, hRelPost⟩ :=
                Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨fuelRest, evmResult, hRestTrace, hAgree⟩ :=
                ih (hStepReady hStepZero) hHalted hContinue
              have hStepFuel :
                  EvmYul.EVM.step fuelRest.succ
                      (EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (Assembly.GasAware.memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := fuelRest)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStepZero
                exact hStepZero
              have hNoHalt :
                  Assembly.GasAware.XStepHaltOutput? instr.op fullPost =
                    none :=
                by
                  simpa [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                    using
                      Assembly.GasAware.XHaltOutput?_none_of_targetInstr_haltKind_none
                        hKind
              refine ⟨fuelRest.succ, evmResult, ?_, hAgree⟩
              exact
                openX_current_running_continue_of_openStepAfterChecks_done
                  (fuel := fuelRest.succ)
                  (validJumps := validJumps)
                  (state := full)
                  (post := fullPost)
                  (op := instr.op)
                  (arg := instr.arg)
                  (tailTrace := [])
                  (result := evmResult)
                  hDecode hChecks
                  (openStepAfterChecks_of_targetInstr_no_callCreate
                    (fuel := fuelRest.succ) hNoCallCreate)
                  hStepFuel hNoHalt hRestTrace
          | halted halt =>
              simp [hStepResult] at hStepReady
              have hFinal : finalResult = .halted halt :=
                hHalted halt hStepReady
              subst finalResult
              obtain ⟨hTargetStep, hKind, hOutput⟩ :=
                Assembly.GasAware.Target.stepInstrResult_halted_stepInstr
                  hStepResult
              obtain ⟨fullPost, hStepOne, hRelPost⟩ :=
                Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              have hHalt :
                  Assembly.GasAware.XStepHaltOutput? instr.op fullPost =
                    some halt.output := by
                have hHaltFull :=
                  Assembly.GasAware.XHaltOutput?_some_of_targetInstr_haltKind_some
                    (instr := instr) (state := fullPost) hKind
                rw [Assembly.GasAware.HaltKind.output_eq_of_gasExecRel
                  halt.kind hRelPost, ← hOutput] at hHaltFull
                simpa [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                  using hHaltFull
              by_cases hRevert : halt.kind = .revert
              · have hRevertOp :
                    instr.op = EvmYul.Operation.REVERT :=
                  Assembly.GasAware.targetInstr_op_eq_revert_of_haltKind_revert
                    (by simpa [hRevert] using hKind)
                refine
                  ⟨1,
                    EvmYul.EVM.ExecutionResult.revert
                      fullPost.gasAvailable halt.output,
                    ?_,
                    OpenXResultAgrees.of_assembly
                      (Assembly.GasAware.XResultAgrees_halted_revert
                        hRevert rfl)⟩
                exact
                  openX_current_revert_of_openStepAfterChecks_done
                    (fuel := 1)
                    (validJumps := validJumps)
                    (state := full)
                    (post := fullPost)
                    (op := instr.op)
                    (arg := instr.arg)
                    (output := halt.output)
                    hDecode hChecks
                    (openStepAfterChecks_of_targetInstr_no_callCreate
                      (fuel := 1) hNoCallCreate)
                    hStepOne hHalt hRevertOp
              · have hNotRevertOp :
                    instr.op ≠ EvmYul.Operation.REVERT :=
                  Assembly.GasAware.targetInstr_op_ne_revert_of_haltKind_some_ne
                    hKind hRevert
                refine
                  ⟨1,
                    EvmYul.EVM.ExecutionResult.success fullPost halt.output,
                    ?_,
                    OpenXResultAgrees.of_assembly
                      (Assembly.GasAware.XResultAgrees_halted_success_of_gasExecRel
                        hRevert hRelPost rfl)⟩
                exact
                  openX_current_success_of_openStepAfterChecks_done
                    (fuel := 1)
                    (validJumps := validJumps)
                    (state := full)
                    (post := fullPost)
                    (op := instr.op)
                    (arg := instr.arg)
                    (output := halt.output)
                    hDecode hChecks
                    (openStepAfterChecks_of_targetInstr_no_callCreate
                      (fuel := 1) hNoCallCreate)
                    hStepOne hHalt hNotRevertOp

theorem openX_runListResult_with_positive_path_continuation_agrees_of_path_ready
    {validJumps : Array Word} :
    ∀ {code : List Assembly.TargetInstr} {target full : EVMState}
      {blockResult finalResult : Assembly.StepResult} {tailFuel : Nat},
      Assembly.GasAware.XStepTrace.XRunListPathReady validJumps code target
        full blockResult →
      (∀ halt, blockResult = .halted halt → finalResult = .halted halt) →
      (∀ targetFinal fullFinal,
        blockResult = .running targetFinal →
          Assembly.GasAware.GasExecRel fullFinal targetFinal →
            ∃ evmResult,
              OpenXTraceResult validJumps tailFuel.succ fullFinal []
                evmResult ∧
              OpenXResultAgrees finalResult evmResult) →
      ∃ evmResult,
        OpenXTraceResult validJumps (tailFuel + code.length).succ full []
          evmResult ∧
          OpenXResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target full blockResult finalResult tailFuel hReady _hHalted
        hContinue
      rcases hReady with ⟨hResult, hRel⟩
      subst blockResult
      simpa using hContinue target full rfl hRel
  | cons instr rest ih =>
      intro target full blockResult finalResult tailFuel hReady hHalted
        hContinue
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          Assembly.GasAware.XStepChecksPass validJumps full instr.op :=
        Assembly.GasAware.XStepChecksPass.of_nonGas_required_le
          hNonGas hGas
      cases hStepResult :
          Assembly.Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Assembly.GasAware.Target.stepInstrResult_running_stepInstr
                  hStepResult
              obtain ⟨fullPost, hStepZero, hRelPost⟩ :=
                Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
                ih (tailFuel := tailFuel) (hStepReady hStepZero)
                  hHalted hContinue
              have hStepFuel :
                  EvmYul.EVM.step (tailFuel + rest.length).succ
                      (EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (Assembly.GasAware.memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel + rest.length)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStepZero
                exact hStepZero
              have hNoHalt :
                  Assembly.GasAware.XStepHaltOutput? instr.op fullPost =
                    none := by
                simpa [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                  using
                    Assembly.GasAware.XHaltOutput?_none_of_targetInstr_haltKind_none
                      hKind
              refine ⟨evmResult, ?_, hAgree⟩
              have hTrace :=
                openX_current_running_continue_of_openStepAfterChecks_done
                  (fuel := (tailFuel + rest.length).succ)
                  (validJumps := validJumps)
                  (state := full)
                  (post := fullPost)
                  (op := instr.op)
                  (arg := instr.arg)
                  (tailTrace := [])
                  (result := evmResult)
                  hDecode hChecks
                  (openStepAfterChecks_of_targetInstr_no_callCreate
                    (fuel := (tailFuel + rest.length).succ)
                    hNoCallCreate)
                  hStepFuel hNoHalt hRestTrace
              simpa [List.length_cons, Nat.add_assoc] using hTrace
          | halted halt =>
              simp [hStepResult] at hStepReady
              have hFinal : finalResult = .halted halt :=
                hHalted halt hStepReady
              subst finalResult
              obtain ⟨hTargetStep, hKind, hOutput⟩ :=
                Assembly.GasAware.Target.stepInstrResult_halted_stepInstr
                  hStepResult
              obtain ⟨fullPost, hStepOne, hRelPost⟩ :=
                Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              have hStepFuel :
                  EvmYul.EVM.step (tailFuel + rest.length).succ
                      (EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (Assembly.GasAware.memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel + rest.length)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStepOne
                exact hStepOne
              have hHalt :
                  Assembly.GasAware.XStepHaltOutput? instr.op fullPost =
                    some halt.output := by
                have hHaltFull :=
                  Assembly.GasAware.XHaltOutput?_some_of_targetInstr_haltKind_some
                    (instr := instr) (state := fullPost) hKind
                rw [Assembly.GasAware.HaltKind.output_eq_of_gasExecRel
                  halt.kind hRelPost, ← hOutput] at hHaltFull
                simpa [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                  using hHaltFull
              by_cases hRevert : halt.kind = .revert
              · have hRevertOp :
                    instr.op = EvmYul.Operation.REVERT :=
                  Assembly.GasAware.targetInstr_op_eq_revert_of_haltKind_revert
                    (by simpa [hRevert] using hKind)
                refine
                  ⟨EvmYul.EVM.ExecutionResult.revert
                      fullPost.gasAvailable halt.output,
                    ?_,
                    OpenXResultAgrees.of_assembly
                      (Assembly.GasAware.XResultAgrees_halted_revert
                        hRevert rfl)⟩
                have hTrace :=
                  openX_current_revert_of_openStepAfterChecks_done
                    (fuel := (tailFuel + rest.length).succ)
                    (validJumps := validJumps)
                    (state := full)
                    (post := fullPost)
                    (op := instr.op)
                    (arg := instr.arg)
                    (output := halt.output)
                    hDecode hChecks
                    (openStepAfterChecks_of_targetInstr_no_callCreate
                      (fuel := (tailFuel + rest.length).succ)
                      hNoCallCreate)
                    hStepFuel hHalt hRevertOp
                simpa [List.length_cons, Nat.add_assoc] using hTrace
              · have hNotRevertOp :
                    instr.op ≠ EvmYul.Operation.REVERT :=
                  Assembly.GasAware.targetInstr_op_ne_revert_of_haltKind_some_ne
                    hKind hRevert
                refine
                  ⟨EvmYul.EVM.ExecutionResult.success fullPost halt.output,
                    ?_,
                    OpenXResultAgrees.of_assembly
                      (Assembly.GasAware.XResultAgrees_halted_success_of_gasExecRel
                        hRevert hRelPost rfl)⟩
                have hTrace :=
                  openX_current_success_of_openStepAfterChecks_done
                    (fuel := (tailFuel + rest.length).succ)
                    (validJumps := validJumps)
                    (state := full)
                    (post := fullPost)
                    (op := instr.op)
                    (arg := instr.arg)
                    (output := halt.output)
                    hDecode hChecks
                    (openStepAfterChecks_of_targetInstr_no_callCreate
                      (fuel := (tailFuel + rest.length).succ)
                      hNoCallCreate)
                    hStepFuel hHalt hNotRevertOp
                simpa [List.length_cons, Nat.add_assoc] using hTrace

theorem openX_runListResult_running_with_positive_path_continuation_agrees_of_path_ready
    {validJumps : Array Word} :
    ∀ {code : List Assembly.TargetInstr} {target full targetFinal : EVMState}
      {finalResult : Assembly.StepResult} {tailFuel : Nat}
      {tailTrace : OpenExternal.OpenTrace},
      Assembly.GasAware.XStepTrace.XRunListPathReady validJumps code target
        full (.running targetFinal) →
      (∀ fullFinal,
        Assembly.GasAware.GasExecRel fullFinal targetFinal →
          ∃ evmResult,
            OpenXTraceResult validJumps tailFuel.succ fullFinal tailTrace
              evmResult ∧
            OpenXResultAgrees finalResult evmResult) →
      ∃ evmResult,
        OpenXTraceResult validJumps (tailFuel + code.length).succ full
          tailTrace evmResult ∧
          OpenXResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal finalResult tailFuel tailTrace hReady
        hContinue
      rcases hReady with ⟨hResult, hRel⟩
      cases hResult
      simpa using hContinue full hRel
  | cons instr rest ih =>
      intro target full targetFinal finalResult tailFuel tailTrace hReady
        hContinue
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          Assembly.GasAware.XStepChecksPass validJumps full instr.op :=
        Assembly.GasAware.XStepChecksPass.of_nonGas_required_le
          hNonGas hGas
      cases hStepResult :
          Assembly.Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Assembly.GasAware.Target.stepInstrResult_running_stepInstr
                  hStepResult
              obtain ⟨fullPost, hStepZero, _hRelPost⟩ :=
                Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
                ih (tailFuel := tailFuel) (tailTrace := tailTrace)
                  (hStepReady hStepZero) hContinue
              have hStepFuel :
                  EvmYul.EVM.step (tailFuel + rest.length).succ
                      (EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (Assembly.GasAware.memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel + rest.length)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStepZero
                exact hStepZero
              have hNoHalt :
                  Assembly.GasAware.XStepHaltOutput? instr.op fullPost =
                    none := by
                simpa [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                  using
                    Assembly.GasAware.XHaltOutput?_none_of_targetInstr_haltKind_none
                      hKind
              refine ⟨evmResult, ?_, hAgree⟩
              have hTrace :=
                openX_current_running_continue_of_openStepAfterChecks_done
                  (fuel := (tailFuel + rest.length).succ)
                  (validJumps := validJumps)
                  (state := full)
                  (post := fullPost)
                  (op := instr.op)
                  (arg := instr.arg)
                  (tailTrace := tailTrace)
                  (result := evmResult)
                  hDecode hChecks
                  (openStepAfterChecks_of_targetInstr_no_callCreate
                    (fuel := (tailFuel + rest.length).succ)
                    hNoCallCreate)
                  hStepFuel hNoHalt hRestTrace
              simpa [List.length_cons, Nat.add_assoc] using hTrace
          | halted halt =>
              simp [hStepResult] at hStepReady

theorem openX_runListResult_running_traceObservationOrFailure_exists_of_path_decode_checks
    {validJumps : Array Word} :
    ∀ {code : List Assembly.TargetInstr} {target full targetFinal : EVMState}
      {targetResult : Assembly.StepResult} {tailFuel : Nat},
      Assembly.GasAware.XStepTrace.XRunListPathDecodeReady code target full
        (.running targetFinal) →
      Assembly.GasAware.XStepTrace.XRunListPathChecksReady validJumps code
        target full (.running targetFinal) →
      (∀ fullFinal,
        Assembly.GasAware.GasExecRel fullFinal targetFinal →
          ∃ candidateTailTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure validJumps tailFuel fullFinal
              candidateTailTrace targetResult) →
      ∃ candidateTrace : OpenExternal.OpenTrace,
        OpenXTraceObservationOrFailure validJumps (tailFuel + code.length)
          full candidateTrace targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal targetResult tailFuel _hDecode hChecks
        hContinue
      rcases hChecks with ⟨hResult, hRel⟩
      cases hResult
      simpa using hContinue full hRel
  | cons instr rest ih =>
      intro target full targetFinal targetResult tailFuel hDecodePath
        hChecksPath hContinue
      rcases hDecodePath with ⟨hDecode, hDecodeReady⟩
      rcases hChecksPath with
        ⟨hRel, hNonGas, hNoCallCreate, hStepReady⟩
      cases hStepResult :
          Assembly.Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hStepReady
          | running targetPost =>
              simp [hStepResult] at hDecodeReady hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Assembly.GasAware.Target.stepInstrResult_running_stepInstr
                  hStepResult
              rcases
                  xStepException?_none_or_outOfGas_of_nonGas_checks
                    hNonGas with hException | hException
              · cases hFuelSum : tailFuel + rest.length with
                | zero =>
                    obtain ⟨fullPost, hStepOne, _hRelPost⟩ :=
                      Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                        (fuel := 0)
                        (gasCost :=
                          EvmYul.EVM.C'
                            (Assembly.GasAware.memoryGasState full instr.op)
                            instr.op)
                        hNoCallCreate
                        (hRel.memoryGasState_left (op := instr.op))
                        hTargetStep
                    have hRestChecks := hStepReady hStepOne
                    cases rest with
                    | nil =>
                        rcases hRestChecks with ⟨hRestResult, hRelFinal⟩
                        cases hRestResult
                        obtain ⟨candidateTailTrace, hTailClassified⟩ :=
                          hContinue fullPost hRelFinal
                        have hTailFuelZero : tailFuel = 0 := by
                          omega
                        have hTailZero :
                            OpenXTraceObservationOrFailure validJumps 0
                              fullPost candidateTailTrace targetResult := by
                          simpa [hTailFuelZero] using hTailClassified
                        exact False.elim
                          (OpenXTraceObservationOrFailure.zero_false
                            hTailZero)
                    | cons restHead restTail =>
                        simp at hFuelSum
                | succ stepFuel =>
                    obtain ⟨fullPost, hStep, hRelPost⟩ :=
                      Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                        (fuel := stepFuel)
                        (gasCost :=
                          EvmYul.EVM.C'
                            (Assembly.GasAware.memoryGasState full instr.op)
                            instr.op)
                        hNoCallCreate
                        (hRel.memoryGasState_left (op := instr.op))
                        hTargetStep
                    have hStepFuel :
                        EvmYul.EVM.step (tailFuel + rest.length)
                            (EvmYul.EVM.C'
                              (Assembly.GasAware.memoryGasState full instr.op)
                              instr.op)
                            (some (instr.op, instr.arg))
                            (Assembly.GasAware.memoryGasState full instr.op) =
                          .ok fullPost := by
                      simpa [hFuelSum] using hStep
                    have hNoHalt :
                        Assembly.GasAware.XStepHaltOutput? instr.op
                          fullPost = none := by
                      simpa
                        [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                        using
                          Assembly.GasAware.XHaltOutput?_none_of_targetInstr_haltKind_none
                            hKind
                    obtain ⟨candidateTrace, hRestClassified⟩ :=
                      ih
                        (target := targetPost) (full := fullPost)
                        (targetFinal := targetFinal)
                        (targetResult := targetResult)
                        (tailFuel := tailFuel)
                        (hDecodeReady hStep)
                        (hStepReady hStep)
                        hContinue
                    rcases hRestClassified with
                      ⟨result, hRestTrace, hObservation⟩ |
                      ⟨outcome, hRestTrace, hFails⟩
                    · have hTrace :
                          OpenXTraceResult validJumps
                            (tailFuel + (instr :: rest).length) full
                            candidateTrace result := by
                        have hTraceOutcome :=
                          openX_current_running_continue_outcome_of_openStepAfterChecks_done
                            (fuel := tailFuel + rest.length)
                            (validJumps := validJumps)
                            (state := full) (post := fullPost)
                            (op := instr.op) (arg := instr.arg)
                            (tailTrace := candidateTrace)
                            (outcome := (.ok result))
                            hDecode hException
                            (openStepAfterChecks_of_targetInstr_no_callCreate
                              (fuel := tailFuel + rest.length)
                              hNoCallCreate)
                            hStepFuel hNoHalt hRestTrace
                        simpa [OpenXTraceResult, List.length_cons,
                          Nat.add_assoc] using hTraceOutcome
                      exact
                        ⟨candidateTrace,
                          OpenXTraceObservationOrFailure.of_trace_target_observation
                            hTrace hObservation⟩
                    · have hTrace :
                          OpenXOutcomeTraceResult validJumps
                            (tailFuel + (instr :: rest).length) full
                            candidateTrace outcome := by
                        have hTraceOutcome :=
                          openX_current_running_continue_outcome_of_openStepAfterChecks_done
                            (fuel := tailFuel + rest.length)
                            (validJumps := validJumps)
                            (state := full) (post := fullPost)
                            (op := instr.op) (arg := instr.arg)
                            (tailTrace := candidateTrace)
                            (outcome := outcome)
                            hDecode hException
                            (openStepAfterChecks_of_targetInstr_no_callCreate
                              (fuel := tailFuel + rest.length)
                              hNoCallCreate)
                            hStepFuel hNoHalt hRestTrace
                        simpa [OpenXOutcomeTraceResult, List.length_cons,
                          Nat.add_assoc] using hTraceOutcome
                      exact
                        ⟨candidateTrace,
                          OpenXTraceObservationOrFailure.of_failure_trace
                            hTrace hFails⟩
              · refine ⟨[], ?_⟩
                have hClassified :=
                  OpenXTraceObservationOrFailure.of_current_outOfGas_exception
                    (validJumps := validJumps)
                  (fuel := tailFuel + rest.length)
                  (state := full) (op := instr.op) (arg := instr.arg)
                  (targetResult := targetResult)
                  hDecode hException
                simpa [List.length_cons, Nat.add_assoc] using hClassified

theorem openX_runListResult_running_all_outcomes_safelyTracks_of_path_decode_checks
    {validJumps : Array Word} :
    ∀ {code : List Assembly.TargetInstr} {target full targetFinal : EVMState}
      {tailFuel : Nat} {reference : EVMResult},
      Assembly.GasAware.XStepTrace.XRunListPathDecodeReady code target full
        (.running targetFinal) →
      Assembly.GasAware.XStepTrace.XRunListPathChecksReady validJumps code
        target full (.running targetFinal) →
      OpenXGasRelStateAllOutcomeTracesSafelyTrackResult validJumps tailFuel
        targetFinal reference →
      OpenXStateAllOutcomeTracesSafelyTrackResult validJumps
        (tailFuel + code.length) full reference := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal tailFuel reference _hDecode hChecks
        hContinue
      rcases hChecks with ⟨hResult, hRel⟩
      cases hResult
      simpa using hContinue full hRel
  | cons instr rest ih =>
      intro target full targetFinal tailFuel reference hDecodePath
        hChecksPath hContinue
      rcases hDecodePath with ⟨hDecode, hDecodeReady⟩
      rcases hChecksPath with
        ⟨hRel, hNonGas, hNoCallCreate, hStepReady⟩
      cases hStepResult :
          Assembly.Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hStepReady
          | running targetPost =>
              simp [hStepResult] at hDecodeReady hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Assembly.GasAware.Target.stepInstrResult_running_stepInstr
                  hStepResult
              intro candidateTrace candidateOutcome hTrace
              rcases
                  xStepException?_none_or_outOfGas_of_nonGas_checks
                    hNonGas with hException | hException
              · cases hFuelSum : tailFuel + rest.length with
                | zero =>
                    obtain ⟨fullPost, hStepOne, _hRelPost⟩ :=
                      Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                        (fuel := 0)
                        (gasCost :=
                          EvmYul.EVM.C'
                            (Assembly.GasAware.memoryGasState full instr.op)
                            instr.op)
                        hNoCallCreate
                        (hRel.memoryGasState_left (op := instr.op))
                        hTargetStep
                    have hRestChecks := hStepReady hStepOne
                    cases rest with
                    | nil =>
                        rcases hRestChecks with ⟨hRestResult, hRelFinal⟩
                        cases hRestResult
                        have hTailFuelZero : tailFuel = 0 := by
                          omega
                        have hZeroTrace :
                            OpenXOutcomeTraceResult validJumps tailFuel
                              fullPost [] (.error (.OutOfFuel : EVMException)) := by
                          subst tailFuel
                          unfold OpenXOutcomeTraceResult
                          rw [openX_zero]
                          exact OpenExternal.OpenResultResolves.done
                        have hSafe :=
                          hContinue fullPost hRelFinal [] (.error (.OutOfFuel : EVMException))
                            hZeroTrace
                        simp [Assembly.GasAware.XRunOutcomeSafelyTracks,
                          Assembly.GasAware.XRunOutcomeCommitsTo,
                          Assembly.GasAware.XRunOutcomeFails] at hSafe
                    | cons restHead restTail =>
                        simp at hFuelSum
                | succ stepFuel =>
                    obtain ⟨fullPost, hStep, hRelPost⟩ :=
                      Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                        (fuel := stepFuel)
                        (gasCost :=
                          EvmYul.EVM.C'
                            (Assembly.GasAware.memoryGasState full instr.op)
                            instr.op)
                        hNoCallCreate
                        (hRel.memoryGasState_left (op := instr.op))
                        hTargetStep
                    have hStepFuel :
                        EvmYul.EVM.step (tailFuel + rest.length)
                            (EvmYul.EVM.C'
                              (Assembly.GasAware.memoryGasState full instr.op)
                              instr.op)
                            (some (instr.op, instr.arg))
                            (Assembly.GasAware.memoryGasState full instr.op) =
                          .ok fullPost := by
                      simpa [hFuelSum] using hStep
                    have hNoHalt :
                        Assembly.GasAware.XStepHaltOutput? instr.op
                          fullPost = none := by
                      simpa
                        [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                        using
                          Assembly.GasAware.XHaltOutput?_none_of_targetInstr_haltKind_none
                            hKind
                    have hTail :
                        OpenXStateAllOutcomeTracesSafelyTrackResult validJumps
                          (tailFuel + rest.length) fullPost reference :=
                      ih
                        (target := targetPost) (full := fullPost)
                        (targetFinal := targetFinal)
                        (tailFuel := tailFuel) (reference := reference)
                        (hDecodeReady hStep)
                        (hStepReady hStep)
                        hContinue
                    have hCurrent :=
                      openX_current_running_all_outcomes_safelyTracks_of_openStepAfterChecks_done
                        (fuel := tailFuel + rest.length)
                        (validJumps := validJumps)
                        (state := full) (post := fullPost)
                        (op := instr.op) (arg := instr.arg)
                        (trace := candidateTrace)
                        (outcome := candidateOutcome)
                        (reference := reference)
                        hDecode hException
                        (by
                          rw [openStepAfterChecks_of_targetInstr_no_callCreate
                            (fuel := tailFuel + rest.length)
                            hNoCallCreate]
                          exact congrArg OpenExternal.OpenResult.done
                            hStepFuel)
                        hNoHalt hTail hTrace
                    simpa [List.length_cons, Nat.add_assoc] using hCurrent
              · have hCurrent :=
                  openX_current_outOfGas_exception_all_outcomes_safelyTracks
                    (fuel := tailFuel + rest.length)
                    (validJumps := validJumps)
                    (state := full) (op := instr.op) (arg := instr.arg)
                    (trace := candidateTrace)
                    (outcome := candidateOutcome)
                    (reference := reference)
                    hDecode hException
                simpa [List.length_cons, Nat.add_assoc] using
                  hCurrent hTrace

theorem openX_runListResult_halted_traceObservationOrFailure_exists_of_path_decode_checks
    {validJumps : Array Word} :
    ∀ {code : List Assembly.TargetInstr} {target full : EVMState}
      {halt : Assembly.Halt},
      Assembly.GasAware.XStepTrace.XRunListPathDecodeReady code target full
        (.halted halt) →
      Assembly.GasAware.XStepTrace.XRunListPathChecksReady validJumps code
        target full (.halted halt) →
      ∃ candidateTrace : OpenExternal.OpenTrace,
        OpenXTraceObservationOrFailure validJumps (code.length + 1)
          full candidateTrace (.halted halt) := by
  intro code
  induction code with
  | nil =>
      intro target full halt _hDecode hChecks
      rcases hChecks with ⟨hResult, _hRel⟩
      cases hResult
  | cons instr rest ih =>
      intro target full halt hDecodePath hChecksPath
      rcases hDecodePath with ⟨hDecode, hDecodeReady⟩
      rcases hChecksPath with
        ⟨hRel, hNonGas, hNoCallCreate, hStepReady⟩
      cases hStepResult :
          Assembly.Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hDecodeReady hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Assembly.GasAware.Target.stepInstrResult_running_stepInstr
                  hStepResult
              rcases
                  xStepException?_none_or_outOfGas_of_nonGas_checks
                    hNonGas with hException | hException
              · obtain ⟨fullPost, hStep, _hRelPost⟩ :=
                  Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                    (fuel := rest.length)
                    (gasCost :=
                      EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                    hNoCallCreate
                    (hRel.memoryGasState_left (op := instr.op))
                    hTargetStep
                have hStepFuel :
                    EvmYul.EVM.step (rest.length + 1)
                        (EvmYul.EVM.C'
                          (Assembly.GasAware.memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (Assembly.GasAware.memoryGasState full instr.op) =
                      .ok fullPost := by
                  simpa [Nat.succ_eq_add_one] using hStep
                have hNoHalt :
                    Assembly.GasAware.XStepHaltOutput? instr.op
                      fullPost = none := by
                  simpa
                    [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                    using
                      Assembly.GasAware.XHaltOutput?_none_of_targetInstr_haltKind_none
                        hKind
                obtain ⟨candidateTrace, hRestClassified⟩ :=
                  ih
                    (target := targetPost) (full := fullPost)
                    (halt := halt)
                    (hDecodeReady hStep) (hStepReady hStep)
                rcases hRestClassified with
                  ⟨result, hRestTrace, hObservation⟩ |
                  ⟨outcome, hRestTrace, hFails⟩
                · have hTrace :
                      OpenXTraceResult validJumps
                        ((instr :: rest).length + 1) full
                        candidateTrace result := by
                    have hTraceOutcome :=
                      openX_current_running_continue_outcome_of_openStepAfterChecks_done
                        (fuel := rest.length + 1)
                        (validJumps := validJumps)
                        (state := full) (post := fullPost)
                        (op := instr.op) (arg := instr.arg)
                        (tailTrace := candidateTrace)
                        (outcome := (.ok result))
                        hDecode hException
                        (openStepAfterChecks_of_targetInstr_no_callCreate
                          (fuel := rest.length + 1)
                          hNoCallCreate)
                        hStepFuel hNoHalt hRestTrace
                    simpa [OpenXTraceResult, List.length_cons,
                      Nat.succ_eq_add_one, Nat.add_assoc]
                      using hTraceOutcome
                  exact
                    ⟨candidateTrace,
                      OpenXTraceObservationOrFailure.of_trace_target_observation
                        hTrace hObservation⟩
                · have hTrace :
                      OpenXOutcomeTraceResult validJumps
                        ((instr :: rest).length + 1) full
                        candidateTrace outcome := by
                    have hTraceOutcome :=
                      openX_current_running_continue_outcome_of_openStepAfterChecks_done
                        (fuel := rest.length + 1)
                        (validJumps := validJumps)
                        (state := full) (post := fullPost)
                        (op := instr.op) (arg := instr.arg)
                        (tailTrace := candidateTrace)
                        (outcome := outcome)
                        hDecode hException
                        (openStepAfterChecks_of_targetInstr_no_callCreate
                          (fuel := rest.length + 1)
                          hNoCallCreate)
                        hStepFuel hNoHalt hRestTrace
                    simpa [OpenXOutcomeTraceResult, List.length_cons,
                      Nat.succ_eq_add_one, Nat.add_assoc]
                      using hTraceOutcome
                  exact
                    ⟨candidateTrace,
                      OpenXTraceObservationOrFailure.of_failure_trace
                        hTrace hFails⟩
              · refine ⟨[], ?_⟩
                have hClassified :=
                    OpenXTraceObservationOrFailure.of_current_outOfGas_exception
                      (validJumps := validJumps)
                    (fuel := rest.length + 1)
                    (state := full) (op := instr.op) (arg := instr.arg)
                    (targetResult := .halted halt)
                    hDecode hException
                simpa [List.length_cons, Nat.succ_eq_add_one,
                  Nat.add_assoc] using hClassified
          | halted currentHalt =>
              simp [hStepResult] at hStepReady
              cases hStepReady
              obtain ⟨hTargetStep, hKind, hOutput⟩ :=
                Assembly.GasAware.Target.stepInstrResult_halted_stepInstr
                  hStepResult
              rcases
                  xStepException?_none_or_outOfGas_of_nonGas_checks
                    hNonGas with hException | hException
              · obtain ⟨fullPost, hStep, hRelPost⟩ :=
                  Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                    (fuel := rest.length)
                    (gasCost :=
                      EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                    hNoCallCreate
                    (hRel.memoryGasState_left (op := instr.op))
                    hTargetStep
                have hStepFuel :
                    EvmYul.EVM.step (rest.length + 1)
                        (EvmYul.EVM.C'
                          (Assembly.GasAware.memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (Assembly.GasAware.memoryGasState full instr.op) =
                      .ok fullPost := by
                  simpa [Nat.succ_eq_add_one] using hStep
                have hHalt :
                    Assembly.GasAware.XStepHaltOutput? instr.op
                      fullPost = some halt.output := by
                  have hHaltFull :=
                    Assembly.GasAware.XHaltOutput?_some_of_targetInstr_haltKind_some
                      (instr := instr) (state := fullPost) hKind
                  rw [Assembly.GasAware.HaltKind.output_eq_of_gasExecRel
                    halt.kind hRelPost, ← hOutput] at hHaltFull
                  simpa
                    [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                    using hHaltFull
                by_cases hRevert : halt.kind = .revert
                · refine ⟨[], ?_⟩
                  have hRevertOp :
                      instr.op = EvmYul.Operation.REVERT :=
                    Assembly.GasAware.targetInstr_op_eq_revert_of_haltKind_revert
                      (by simpa [hRevert] using hKind)
                  have hTrace :
                      OpenXTraceResult validJumps
                        ((instr :: rest).length + 1) full []
                        (EvmYul.EVM.ExecutionResult.revert
                          fullPost.gasAvailable halt.output) := by
                    have hTrace' :=
                      openX_current_revert_of_openStepAfterChecks_done_of_exception_none
                        (fuel := rest.length + 1)
                        (validJumps := validJumps)
                        (state := full)
                        (post := fullPost)
                        (op := instr.op)
                        (arg := instr.arg)
                        (output := halt.output)
                        hDecode hException
                        (openStepAfterChecks_of_targetInstr_no_callCreate
                          (fuel := rest.length + 1)
                          hNoCallCreate)
                        hStepFuel hHalt hRevertOp
                    simpa [OpenXTraceResult, List.length_cons,
                      Nat.succ_eq_add_one, Nat.add_assoc]
                      using hTrace'
                  exact
                    OpenXTraceObservationOrFailure.of_trace_target_observation
                      hTrace
                      (OpenXResultAgrees.of_assembly
                        (Assembly.GasAware.XResultAgrees_halted_revert
                          hRevert rfl)).committedObservation
                · refine ⟨[], ?_⟩
                  have hNotRevertOp :
                      instr.op ≠ EvmYul.Operation.REVERT :=
                    Assembly.GasAware.targetInstr_op_ne_revert_of_haltKind_some_ne
                      hKind hRevert
                  have hTrace :
                      OpenXTraceResult validJumps
                        ((instr :: rest).length + 1) full []
                        (EvmYul.EVM.ExecutionResult.success
                          fullPost halt.output) := by
                    have hTrace' :=
                      openX_current_success_of_openStepAfterChecks_done_of_exception_none
                        (fuel := rest.length + 1)
                        (validJumps := validJumps)
                        (state := full)
                        (post := fullPost)
                        (op := instr.op)
                        (arg := instr.arg)
                        (output := halt.output)
                        hDecode hException
                        (openStepAfterChecks_of_targetInstr_no_callCreate
                          (fuel := rest.length + 1)
                          hNoCallCreate)
                        hStepFuel hHalt hNotRevertOp
                    simpa [OpenXTraceResult, List.length_cons,
                      Nat.succ_eq_add_one, Nat.add_assoc]
                      using hTrace'
                  exact
                    OpenXTraceObservationOrFailure.of_trace_target_observation
                      hTrace
                      (OpenXResultAgrees.of_assembly
                        (Assembly.GasAware.XResultAgrees_halted_success_of_gasExecRel
                          hRevert hRelPost rfl)).committedObservation
              · refine ⟨[], ?_⟩
                have hClassified :=
                  OpenXTraceObservationOrFailure.of_current_outOfGas_exception
                    (validJumps := validJumps)
                    (fuel := rest.length + 1)
                    (state := full) (op := instr.op) (arg := instr.arg)
                    (targetResult := .halted halt)
                    hDecode hException
                simpa [List.length_cons, Nat.succ_eq_add_one,
                  Nat.add_assoc] using hClassified

theorem openX_runListResult_halted_all_outcomes_safelyTracks_of_path_decode_checks
    {validJumps : Array Word} :
    ∀ {code : List Assembly.TargetInstr} {target full : EVMState}
      {halt : Assembly.Halt} {reference : EVMResult},
      Assembly.GasAware.XStepTrace.XRunListPathDecodeReady code target full
        (.halted halt) →
      Assembly.GasAware.XStepTrace.XRunListPathChecksReady validJumps code
        target full (.halted halt) →
      OpenXResultAgrees (.halted halt) reference →
      OpenXStateAllOutcomeTracesSafelyTrackResult validJumps
        (code.length + 1) full reference := by
  intro code
  induction code with
  | nil =>
      intro target full halt reference _hDecode hChecks _hReference
      rcases hChecks with ⟨hResult, _hRel⟩
      cases hResult
  | cons instr rest ih =>
      intro target full halt reference hDecodePath hChecksPath hReference
      rcases hDecodePath with ⟨hDecode, hDecodeReady⟩
      rcases hChecksPath with
        ⟨hRel, hNonGas, hNoCallCreate, hStepReady⟩
      cases hStepResult :
          Assembly.Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hDecodeReady hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Assembly.GasAware.Target.stepInstrResult_running_stepInstr
                  hStepResult
              intro candidateTrace candidateOutcome hTrace
              rcases
                  xStepException?_none_or_outOfGas_of_nonGas_checks
                    hNonGas with hException | hException
              · obtain ⟨fullPost, hStep, _hRelPost⟩ :=
                  Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                    (fuel := rest.length)
                    (gasCost :=
                      EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                    hNoCallCreate
                    (hRel.memoryGasState_left (op := instr.op))
                    hTargetStep
                have hStepFuel :
                    EvmYul.EVM.step (rest.length + 1)
                        (EvmYul.EVM.C'
                          (Assembly.GasAware.memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (Assembly.GasAware.memoryGasState full instr.op) =
                      .ok fullPost := by
                  simpa [Nat.succ_eq_add_one] using hStep
                have hNoHalt :
                    Assembly.GasAware.XStepHaltOutput? instr.op
                      fullPost = none := by
                  simpa
                    [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                    using
                      Assembly.GasAware.XHaltOutput?_none_of_targetInstr_haltKind_none
                        hKind
                have hTail :
                    OpenXStateAllOutcomeTracesSafelyTrackResult validJumps
                      (rest.length + 1) fullPost reference :=
                  ih
                    (target := targetPost) (full := fullPost)
                    (halt := halt) (reference := reference)
                    (hDecodeReady hStep) (hStepReady hStep)
                    hReference
                have hCurrent :=
                  openX_current_running_all_outcomes_safelyTracks_of_openStepAfterChecks_done
                    (fuel := rest.length + 1)
                    (validJumps := validJumps)
                    (state := full) (post := fullPost)
                    (op := instr.op) (arg := instr.arg)
                    (trace := candidateTrace)
                    (outcome := candidateOutcome)
                    (reference := reference)
                    hDecode hException
                    (by
                      rw [openStepAfterChecks_of_targetInstr_no_callCreate
                        (fuel := rest.length + 1)
                        hNoCallCreate]
                      exact congrArg OpenExternal.OpenResult.done
                        hStepFuel)
                    hNoHalt hTail hTrace
                simpa [List.length_cons, Nat.succ_eq_add_one,
                  Nat.add_assoc] using hCurrent
              · have hCurrent :=
                  openX_current_outOfGas_exception_all_outcomes_safelyTracks
                    (fuel := rest.length + 1)
                    (validJumps := validJumps)
                    (state := full) (op := instr.op) (arg := instr.arg)
                    (trace := candidateTrace) (outcome := candidateOutcome)
                    (reference := reference)
                    hDecode hException
                simpa [List.length_cons, Nat.succ_eq_add_one,
                  Nat.add_assoc] using hCurrent hTrace
          | halted currentHalt =>
              simp [hStepResult] at hStepReady
              cases hStepReady
              obtain ⟨hTargetStep, hKind, hOutput⟩ :=
                Assembly.GasAware.Target.stepInstrResult_halted_stepInstr
                  hStepResult
              intro candidateTrace candidateOutcome hTrace
              rcases
                  xStepException?_none_or_outOfGas_of_nonGas_checks
                    hNonGas with hException | hException
              · obtain ⟨fullPost, hStep, hRelPost⟩ :=
                  Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                    (fuel := rest.length)
                    (gasCost :=
                      EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                    hNoCallCreate
                    (hRel.memoryGasState_left (op := instr.op))
                    hTargetStep
                have hStepFuel :
                    EvmYul.EVM.step (rest.length + 1)
                        (EvmYul.EVM.C'
                          (Assembly.GasAware.memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (Assembly.GasAware.memoryGasState full instr.op) =
                      .ok fullPost := by
                  simpa [Nat.succ_eq_add_one] using hStep
                have hHalt :
                    Assembly.GasAware.XStepHaltOutput? instr.op
                      fullPost = some halt.output := by
                  have hHaltFull :=
                    Assembly.GasAware.XHaltOutput?_some_of_targetInstr_haltKind_some
                      (instr := instr) (state := fullPost) hKind
                  rw [Assembly.GasAware.HaltKind.output_eq_of_gasExecRel
                    halt.kind hRelPost, ← hOutput] at hHaltFull
                  simpa
                    [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                    using hHaltFull
                by_cases hRevert : halt.kind = .revert
                · have hRevertOp :
                      instr.op = EvmYul.Operation.REVERT :=
                    Assembly.GasAware.targetInstr_op_eq_revert_of_haltKind_revert
                      (by simpa [hRevert] using hKind)
                  exact
                    Assembly.GasAware.XRunOutcomeSafelyTracks.retarget_ok
                      (openX_current_revert_all_outcomes_safelyTracks_of_openStepAfterChecks_done
                        (fuel := rest.length + 1)
                        (validJumps := validJumps)
                        (state := full)
                        (post := fullPost)
                        (op := instr.op)
                        (arg := instr.arg)
                        (trace := candidateTrace)
                        (outcome := candidateOutcome)
                        (output := halt.output)
                        hDecode hException
                        (by
                          rw [openStepAfterChecks_of_targetInstr_no_callCreate
                            (fuel := rest.length + 1)
                            hNoCallCreate]
                          exact congrArg OpenExternal.OpenResult.done
                            hStepFuel)
                        hHalt hRevertOp hTrace)
                      ((OpenXResultAgrees.of_assembly
                        (Assembly.GasAware.XResultAgrees_halted_revert
                          hRevert rfl)).committedObservation.trans
                        hReference.committedObservation.symm)
                · have hNotRevertOp :
                      instr.op ≠ EvmYul.Operation.REVERT :=
                    Assembly.GasAware.targetInstr_op_ne_revert_of_haltKind_some_ne
                      hKind hRevert
                  exact
                    Assembly.GasAware.XRunOutcomeSafelyTracks.retarget_ok
                      (openX_current_success_all_outcomes_safelyTracks_of_openStepAfterChecks_done
                        (fuel := rest.length + 1)
                        (validJumps := validJumps)
                        (state := full)
                        (post := fullPost)
                        (op := instr.op)
                        (arg := instr.arg)
                        (trace := candidateTrace)
                        (outcome := candidateOutcome)
                        (output := halt.output)
                        hDecode hException
                        (by
                          rw [openStepAfterChecks_of_targetInstr_no_callCreate
                            (fuel := rest.length + 1)
                            hNoCallCreate]
                          exact congrArg OpenExternal.OpenResult.done
                            hStepFuel)
                        hHalt hNotRevertOp hTrace)
                      ((OpenXResultAgrees.of_assembly
                        (Assembly.GasAware.XResultAgrees_halted_success_of_gasExecRel
                          hRevert hRelPost rfl)).committedObservation.trans
                        hReference.committedObservation.symm)
              · have hCurrent :=
                  openX_current_outOfGas_exception_all_outcomes_safelyTracks
                    (fuel := rest.length + 1)
                    (validJumps := validJumps)
                    (state := full) (op := instr.op) (arg := instr.arg)
                    (trace := candidateTrace) (outcome := candidateOutcome)
                    (reference := reference)
                    hDecode hException
                simpa [List.length_cons, Nat.succ_eq_add_one,
                  Nat.add_assoc] using hCurrent hTrace

theorem openX_runListResult_running_with_positive_path_continuation_agrees_of_path_ready_and_budget
    {validJumps : Array Word} :
    ∀ {code : List Assembly.TargetInstr} {target full targetFinal : EVMState}
      {finalResult : Assembly.StepResult} {tailFuel restBudget : Nat}
      {tailTrace : OpenExternal.OpenTrace},
      Assembly.GasAware.XStepTrace.XRunListPathReady validJumps code target
        full (.running targetFinal) →
      Assembly.GasAware.XStepTrace.XRunListGasBudget code target +
          restBudget ≤ full.gasAvailable.toNat →
      (∀ fullFinal,
        Assembly.GasAware.GasExecRel fullFinal targetFinal →
          restBudget ≤ fullFinal.gasAvailable.toNat →
            ∃ evmResult,
              OpenXTraceResult validJumps tailFuel.succ fullFinal tailTrace
                evmResult ∧
              OpenXResultAgrees finalResult evmResult) →
      ∃ evmResult,
        OpenXTraceResult validJumps (tailFuel + code.length).succ full
          tailTrace evmResult ∧
          OpenXResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal finalResult tailFuel restBudget tailTrace
        hReady hBudget hContinue
      rcases hReady with ⟨hResult, hRel⟩
      cases hResult
      have hRestBudget : restBudget ≤ full.gasAvailable.toNat := by
        simpa [Assembly.GasAware.XStepTrace.XRunListGasBudget] using hBudget
      simpa using hContinue full hRel hRestBudget
  | cons instr rest ih =>
      intro target full targetFinal finalResult tailFuel restBudget tailTrace
        hReady hBudget hContinue
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          Assembly.GasAware.XStepChecksPass validJumps full instr.op :=
        Assembly.GasAware.XStepChecksPass.of_nonGas_required_le
          hNonGas hGas
      cases hStepResult :
          Assembly.Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hStepReady
          | running targetPost =>
              simp [hStepResult] at hStepReady
              have hBudgetRun :
                  Assembly.GasAware.XStepTrace.XRunListGasBudget
                      (instr :: rest) target =
                    Assembly.GasAware.XGasRequiredAt target instr.op +
                      Assembly.GasAware.XStepTrace.XRunListGasBudget rest
                        targetPost := by
                simp [Assembly.GasAware.XStepTrace.XRunListGasBudget,
                  hStepResult]
              have hBudgetStep :
                  Assembly.GasAware.XGasRequiredAt full instr.op +
                      (Assembly.GasAware.XStepTrace.XRunListGasBudget rest
                          targetPost + restBudget) ≤
                    full.gasAvailable.toNat := by
                rw [hBudgetRun] at hBudget
                rw [←
                  Assembly.GasAware.XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
                    hNoCallCreate hRel] at hBudget
                omega
              obtain ⟨hTargetStep, hKind⟩ :=
                Assembly.GasAware.Target.stepInstrResult_running_stepInstr
                  hStepResult
              obtain ⟨fullPost, hStepZero, hRelPost⟩ :=
                Assembly.GasAware.EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              have hStepBody :
                  EvmYul.step instr.op instr.arg
                      (Assembly.GasAware.xBodyState full instr.op) =
                    .ok fullPost := by
                rw [← Assembly.GasAware.EVM_step_targetInstr_eq_xBodyState
                  (fuel := 0) (state := full) (instr := instr)
                  hNoCallCreate]
                exact hStepZero
              have hRestBudgetBody :
                  Assembly.GasAware.XStepTrace.XRunListGasBudget rest
                      targetPost + restBudget ≤
                    (Assembly.GasAware.xBodyState full instr.op).gasAvailable.toNat :=
                Assembly.GasAware.xBodyState_gasAvailable_toNat_of_required
                  hBudgetStep
              have hRestBudget :
                  Assembly.GasAware.XStepTrace.XRunListGasBudget rest
                      targetPost + restBudget ≤
                    fullPost.gasAvailable.toNat := by
                rw [Assembly.GasAware.XStepTrace.TargetInstrBodyPreservesGas.of_no_call_create
                  hNoCallCreate hStepBody]
                exact hRestBudgetBody
              obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
                ih (tailFuel := tailFuel) (restBudget := restBudget)
                  (tailTrace := tailTrace) (hStepReady hStepZero)
                  hRestBudget hContinue
              have hStepFuel :
                  EvmYul.EVM.step (tailFuel + rest.length).succ
                      (EvmYul.EVM.C'
                        (Assembly.GasAware.memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (Assembly.GasAware.memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel + rest.length)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [Assembly.GasAware.EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C'
                      (Assembly.GasAware.memoryGasState full instr.op)
                      instr.op)
                  (state := Assembly.GasAware.memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStepZero
                exact hStepZero
              have hNoHalt :
                  Assembly.GasAware.XStepHaltOutput? instr.op fullPost =
                    none := by
                simpa [Assembly.GasAware.XHaltOutput?_eq_XStepHaltOutput?]
                  using
                    Assembly.GasAware.XHaltOutput?_none_of_targetInstr_haltKind_none
                      hKind
              refine ⟨evmResult, ?_, hAgree⟩
              have hTrace :=
                openX_current_running_continue_of_openStepAfterChecks_done
                  (fuel := (tailFuel + rest.length).succ)
                  (validJumps := validJumps)
                  (state := full)
                  (post := fullPost)
                  (op := instr.op)
                  (arg := instr.arg)
                  (tailTrace := tailTrace)
                  (result := evmResult)
                  hDecode hChecks
                  (openStepAfterChecks_of_targetInstr_no_callCreate
                    (fuel := (tailFuel + rest.length).succ)
                    hNoCallCreate)
                  hStepFuel hNoHalt hRestTrace
              simpa [List.length_cons, Nat.add_assoc] using hTrace

theorem openXTraceRelAbove_current_emitted_prim_call_continue_of_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {result : EVMResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hRest :
      ∀ {full gasPost : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.GasExecRel gasPost
              (EvmYul.EVM.State.incrPC (call.resume response)) →
              OpenExternal.OpenResultResolves
                (openX tailFuel
                  (Assembly.GasAware.validJumps targetProgram) gasPost)
                tailTrace (.ok result))
    (hAgree : OpenXResultAgrees targetResult result) :
    OpenXTraceRelAbove targetProgram initial
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      targetResult (tailFuel + 1) gasBound := by
  intro full hGasBound hRel
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  refine ⟨result, ?_, hAgree⟩
  exact
    openX_current_emitted_prim_call_continue_of_step_checks
      (program := program) (targetProgram := targetProgram)
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (full := full) (target := initial)
      (pc := pc) (op := op) (emitted := emitted)
      (before := before) (after := after) (kind := kind)
      (call := call) (response := response)
      (tailTrace := tailTrace) (result := result)
      hEncoding hSafety hAt hEmit hTargetBlock hRel hCode
      (hStepChecks hGasBound hRel) hKind hCall
      (fun hRelPost => hRest hGasBound hRel hRelPost)

theorem openXTraceRelAbove_current_emitted_prim_call_continue_exists_of_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hRest :
      ∀ {full gasPost : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.GasExecRel gasPost
              (EvmYul.EVM.State.incrPC (call.resume response)) →
              ∃ result,
                OpenXTraceResult (Assembly.GasAware.validJumps targetProgram)
                  tailFuel gasPost tailTrace result ∧
                OpenXResultAgrees targetResult result) :
    OpenXTraceRelAbove targetProgram initial
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      targetResult (tailFuel + 1) gasBound := by
  intro full hGasBound hRel
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hEmit' := hEmit
  simp [Assembly.emitInstr?] at hEmit'
  subst emitted
  have hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (op.toEVM, none) := by
    have hDecodeLocated :=
      Assembly.GasAware.decode_of_gasExecRel_instrAt_mem_emitted_of_safety
        (program := program) (target := targetProgram)
        (targetState := initial) (fullState := full)
        (pc := pc) (instr := Assembly.Instr.prim op)
        (located := { pc := pc, instr := Assembly.TargetInstr.prim op })
        (before := before)
        (emitted := [{ pc := pc, instr := Assembly.TargetInstr.prim op }])
        (after := after)
        hEncoding hSafety hAt hTargetBlock (by simp) (by rfl)
        hRel hCode
    simpa [Assembly.TargetInstr.op, Assembly.TargetInstr.arg] using
      hDecodeLocated
  exact
    openX_current_gasless_call_continue_exists_of_step_checks
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (full := full) (target := initial) (op := op.toEVM)
      (arg := none) (kind := kind) (call := call)
      (response := response) (tailTrace := tailTrace)
      (targetResult := targetResult)
      hRel hDecode (hStepChecks hGasBound hRel) hKind hCall
      (fun hRelPost => hRest hGasBound hRel hRelPost)

theorem openXTraceRelAbove_current_emitted_prim_call_continue_exists_of_step_checks_actual_post
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hRest :
      ∀ {full : EVMState} {gasCall : OpenExternal.OpenCall EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            OpenExternal.CallKind.evmOpenCall?
                (gasChargedState full op.toEVM) kind = some gasCall →
              ∃ result,
                OpenXTraceResult (Assembly.GasAware.validJumps targetProgram)
                  tailFuel
                  (EvmYul.EVM.State.incrPC
                    (finishGasAwareCall gasCall response))
                  tailTrace result ∧
                OpenXResultAgrees targetResult result) :
    OpenXTraceRelAbove targetProgram initial
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      targetResult (tailFuel + 1) gasBound := by
  intro full hGasBound hRel
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hEmit' := hEmit
  simp [Assembly.emitInstr?] at hEmit'
  subst emitted
  have hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (op.toEVM, none) := by
    have hDecodeLocated :=
      Assembly.GasAware.decode_of_gasExecRel_instrAt_mem_emitted_of_safety
        (program := program) (target := targetProgram)
        (targetState := initial) (fullState := full)
        (pc := pc) (instr := Assembly.Instr.prim op)
        (located := { pc := pc, instr := Assembly.TargetInstr.prim op })
        (before := before)
        (emitted := [{ pc := pc, instr := Assembly.TargetInstr.prim op }])
        (after := after)
        hEncoding hSafety hAt hTargetBlock (by simp) (by rfl)
        hRel hCode
    simpa [Assembly.TargetInstr.op, Assembly.TargetInstr.arg] using
      hDecodeLocated
  exact
    openX_current_gasless_call_continue_exists_of_step_checks_actual_post
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (full := full) (target := initial) (op := op.toEVM)
      (arg := none) (kind := kind) (call := call)
      (response := response) (tailTrace := tailTrace)
      (targetResult := targetResult)
      hRel hDecode (hStepChecks hGasBound hRel) hKind hCall
      (fun hGasCall => hRest hGasBound hRel hGasCall)

theorem openX_current_emitted_prim_call_continue_trace_observation_or_failure_of_step_checks_actual_post
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial full : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRel : Assembly.GasAware.GasExecRel full initial)
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass
        (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hRest :
      ∀ {gasCall : OpenExternal.OpenCall EVMState},
        OpenExternal.CallKind.evmOpenCall?
            (gasChargedState full op.toEVM) kind = some gasCall →
          (∃ result,
            OpenXTraceResult (Assembly.GasAware.validJumps targetProgram)
              tailFuel
              (EvmYul.EVM.State.incrPC
                (finishGasAwareCall gasCall response))
              tailTrace result ∧
              Assembly.GasAware.XResultCommittedObservation result =
                Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
          (∃ outcome : Except EVMException EVMResult,
            OpenXOutcomeTraceResult
              (Assembly.GasAware.validJumps targetProgram) tailFuel
              (EvmYul.EVM.State.incrPC
                (finishGasAwareCall gasCall response))
              tailTrace outcome ∧
              Assembly.GasAware.XRunOutcomeFails outcome)) :
    (∃ result,
      OpenXTraceResult (Assembly.GasAware.validJumps targetProgram)
        (tailFuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace) result ∧
        Assembly.GasAware.XResultCommittedObservation result =
          Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
    (∃ outcome : Except EVMException EVMResult,
      OpenXOutcomeTraceResult (Assembly.GasAware.validJumps targetProgram)
        (tailFuel + 1) full
        (OpenExternal.OpenEvent.call call.site response :: tailTrace) outcome ∧
        Assembly.GasAware.XRunOutcomeFails outcome) := by
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hEmit' := hEmit
  simp [Assembly.emitInstr?] at hEmit'
  subst emitted
  have hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (op.toEVM, none) := by
    have hDecodeLocated :=
      Assembly.GasAware.decode_of_gasExecRel_instrAt_mem_emitted_of_safety
        (program := program) (target := targetProgram)
        (targetState := initial) (fullState := full)
        (pc := pc) (instr := Assembly.Instr.prim op)
        (located := { pc := pc, instr := Assembly.TargetInstr.prim op })
        (before := before)
        (emitted := [{ pc := pc, instr := Assembly.TargetInstr.prim op }])
        (after := after)
        hEncoding hSafety hAt hTargetBlock (by simp) (by rfl)
        hRel hCode
    simpa [Assembly.TargetInstr.op, Assembly.TargetInstr.arg] using
      hDecodeLocated
  exact
    openX_current_gasless_call_continue_trace_observation_or_failure_of_step_checks_actual_post
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (full := full) (target := initial) (op := op.toEVM)
      (arg := none) (kind := kind) (call := call)
      (response := response) (tailTrace := tailTrace)
      (targetResult := targetResult)
      hRel hDecode hStepChecks hKind hCall hRest

theorem openX_current_emitted_prim_call_continue_traceObservationOrFailure_of_step_checks_actual_post
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial full : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRel : Assembly.GasAware.GasExecRel full initial)
    (hStepChecks :
      Assembly.GasAware.XStepChecksPass
        (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hRest :
      ∀ {gasCall : OpenExternal.OpenCall EVMState},
        OpenExternal.CallKind.evmOpenCall?
            (gasChargedState full op.toEVM) kind = some gasCall →
          OpenXTraceObservationOrFailure
            (Assembly.GasAware.validJumps targetProgram) tailFuel
            (EvmYul.EVM.State.incrPC
              (finishGasAwareCall gasCall response))
            tailTrace targetResult) :
    OpenXTraceObservationOrFailure
      (Assembly.GasAware.validJumps targetProgram) (tailFuel + 1) full
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      targetResult :=
  openX_current_emitted_prim_call_continue_trace_observation_or_failure_of_step_checks_actual_post
    (program := program) (targetProgram := targetProgram)
    (tailFuel := tailFuel) (initial := initial) (full := full)
    (pc := pc) (op := op) (emitted := emitted) (before := before)
    (after := after) (kind := kind) (call := call) (response := response)
    (tailTrace := tailTrace) (targetResult := targetResult)
    hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRel hStepChecks
    hKind hCall hRest

theorem openX_current_emitted_prim_call_continue_traceObservationOrFailure_exists_of_nonGas_actual_post
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial full : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRel : Assembly.GasAware.GasExecRel full initial)
    (hNonGas :
      Assembly.GasAware.XNonGasChecksPass
        (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hRest :
      ∀ {gasCall : OpenExternal.OpenCall EVMState},
        OpenExternal.CallKind.evmOpenCall?
            (gasChargedState full op.toEVM) kind = some gasCall →
          OpenXTraceObservationOrFailure
            (Assembly.GasAware.validJumps targetProgram) tailFuel
            (EvmYul.EVM.State.incrPC
              (finishGasAwareCall gasCall response))
            tailTrace targetResult) :
    ∃ candidateTrace : OpenExternal.OpenTrace,
      OpenXTraceObservationOrFailure
        (Assembly.GasAware.validJumps targetProgram) (tailFuel + 1) full
        candidateTrace targetResult := by
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hEmit' := hEmit
  simp [Assembly.emitInstr?] at hEmit'
  subst emitted
  have hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (op.toEVM, none) := by
    have hDecodeLocated :=
      Assembly.GasAware.decode_of_gasExecRel_instrAt_mem_emitted_of_safety
        (program := program) (target := targetProgram)
        (targetState := initial) (fullState := full)
        (pc := pc) (instr := Assembly.Instr.prim op)
        (located := { pc := pc, instr := Assembly.TargetInstr.prim op })
        (before := before)
        (emitted := [{ pc := pc, instr := Assembly.TargetInstr.prim op }])
        (after := after)
        hEncoding hSafety hAt hTargetBlock (by simp) (by rfl)
        hRel hCode
    simpa [Assembly.TargetInstr.op, Assembly.TargetInstr.arg] using
      hDecodeLocated
  exact
    openX_current_gasless_call_continue_traceObservationOrFailure_exists_of_nonGas_actual_post
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (full := full) (target := initial) (op := op.toEVM)
      (arg := none) (kind := kind) (call := call)
      (response := response) (tailTrace := tailTrace)
      (targetResult := targetResult)
      hRel hDecode hNonGas hKind hCall hRest

theorem openXTraceRelAbove_current_running_continue_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    (hDecode :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.GasExecRel gasPost post ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost = none)
    (hRest :
      ∀ {full gasPost : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.GasExecRel gasPost post →
              ∃ result,
                OpenXTraceResult (Assembly.GasAware.validJumps targetProgram)
                  tailFuel gasPost tailTrace result ∧
                OpenXResultAgrees targetResult result) :
    OpenXTraceRelAbove targetProgram initial tailTrace targetResult
      (tailFuel + 1) gasBound := by
  intro full hGasBound hRel
  obtain ⟨gasPost, hStepOk, hRelPost, hNoHalt⟩ :=
    hStep hGasBound hRel
  obtain ⟨result, hRestTrace, hAgree⟩ :=
    hRest hGasBound hRel hRelPost
  refine ⟨result, ?_, hAgree⟩
  exact
    openX_current_running_continue_of_openStepAfterChecks_done
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (state := full) (post := gasPost) (op := op) (arg := arg)
      (tailTrace := tailTrace) (result := result)
      (hDecode hGasBound hRel)
      (hStepChecks hGasBound hRel)
      (hOpenStep hGasBound hRel)
      hStepOk hNoHalt hRestTrace

theorem openXTraceRelAbove_current_success_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {targetResult : Assembly.StepResult}
    (hDecode :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost =
                some output ∧
              op ≠ EvmYul.Operation.REVERT ∧
              OpenXResultAgrees targetResult
                (EvmYul.EVM.ExecutionResult.success gasPost output)) :
    OpenXTraceRelAbove targetProgram initial [] targetResult
      (tailFuel + 1) gasBound := by
  intro full hGasBound hRel
  obtain ⟨gasPost, output, hStepOk, hHalt, hNotRevert, hAgree⟩ :=
    hStep hGasBound hRel
  refine
    ⟨EvmYul.EVM.ExecutionResult.success gasPost output, ?_, hAgree⟩
  exact
    openX_current_success_of_openStepAfterChecks_done
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (state := full) (post := gasPost) (op := op) (arg := arg)
      (output := output)
      (hDecode hGasBound hRel)
      (hStepChecks hGasBound hRel)
      (hOpenStep hGasBound hRel)
      hStepOk hHalt hNotRevert

theorem openXTraceRelAbove_current_revert_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {targetResult : Assembly.StepResult}
    (hDecode :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost =
                some output ∧
              op = EvmYul.Operation.REVERT ∧
              OpenXResultAgrees targetResult
                (EvmYul.EVM.ExecutionResult.revert
                  gasPost.gasAvailable output)) :
    OpenXTraceRelAbove targetProgram initial [] targetResult
      (tailFuel + 1) gasBound := by
  intro full hGasBound hRel
  obtain ⟨gasPost, output, hStepOk, hHalt, hRevert, hAgree⟩ :=
    hStep hGasBound hRel
  refine
    ⟨EvmYul.EVM.ExecutionResult.revert gasPost.gasAvailable output, ?_,
      hAgree⟩
  exact
    openX_current_revert_of_openStepAfterChecks_done
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (state := full) (post := gasPost) (op := op) (arg := arg)
      (output := output)
      (hDecode hGasBound hRel)
      (hStepChecks hGasBound hRel)
      (hOpenStep hGasBound hRel)
      hStepOk hHalt hRevert

def OpenXRunListRunningRelReady
    (targetProgram : Assembly.TargetProgram)
    (state mid : EVMState) (trace : OpenExternal.OpenTrace)
    (evmFuel tailFuel gasBound tailGasBound : Nat) : Prop :=
  ∀ {full : EVMState}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult},
    gasBound ≤ full.gasAvailable.toNat →
      Assembly.GasAware.GasExecRel full state →
        (∀ {gasPost : EVMState},
          tailGasBound ≤ gasPost.gasAvailable.toNat →
            Assembly.GasAware.GasExecRel gasPost mid →
              ∃ result,
                OpenXTraceResult (Assembly.GasAware.validJumps targetProgram)
                  tailFuel gasPost tailTrace result ∧
                OpenXResultAgrees targetResult result) →
          ∃ result,
            OpenXTraceResult (Assembly.GasAware.validJumps targetProgram)
              evmFuel full (trace ++ tailTrace) result ∧
            OpenXResultAgrees targetResult result

def OpenXRunListHaltedRelReady
    (targetProgram : Assembly.TargetProgram)
    (state : EVMState) (trace : OpenExternal.OpenTrace)
    (halt : Assembly.Halt) (evmFuel gasBound : Nat) : Prop :=
  ∀ {full : EVMState},
    gasBound ≤ full.gasAvailable.toNat →
      Assembly.GasAware.GasExecRel full state →
        ∃ result,
          OpenXTraceResult (Assembly.GasAware.validJumps targetProgram)
            evmFuel full trace result ∧
          OpenXResultAgrees (.halted halt) result

def OpenXRunListRunningTraceObservationOrFailureReady
    (targetProgram : Assembly.TargetProgram)
    (state mid : EVMState) (trace : OpenExternal.OpenTrace)
    (evmFuel tailFuel : Nat) : Prop :=
  ∀ {full : EVMState}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult},
    Assembly.GasAware.GasExecRel full state →
      (∀ {gasPost : EVMState},
        Assembly.GasAware.GasExecRel gasPost mid →
          OpenXTraceObservationOrFailure
            (Assembly.GasAware.validJumps targetProgram) tailFuel
            gasPost tailTrace targetResult) →
        OpenXTraceObservationOrFailure
          (Assembly.GasAware.validJumps targetProgram) evmFuel full
          (trace ++ tailTrace) targetResult

def OpenXRunListRunningTraceObservationOrFailureExistsReady
    (targetProgram : Assembly.TargetProgram)
    (state mid : EVMState)
    (evmFuel tailFuel : Nat) : Prop :=
  ∀ {full : EVMState} {targetResult : Assembly.StepResult},
    Assembly.GasAware.GasExecRel full state →
      (∀ {gasPost : EVMState},
        Assembly.GasAware.GasExecRel gasPost mid →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps targetProgram) tailFuel
              gasPost candidateTrace targetResult) →
        ∃ candidateTrace : OpenExternal.OpenTrace,
          OpenXTraceObservationOrFailure
            (Assembly.GasAware.validJumps targetProgram) evmFuel
            full candidateTrace targetResult

def OpenXRunListHaltedTraceObservationOrFailureExistsReady
    (targetProgram : Assembly.TargetProgram)
    (state : EVMState) (halt : Assembly.Halt)
    (evmFuel : Nat) : Prop :=
  ∀ {full : EVMState},
    Assembly.GasAware.GasExecRel full state →
      ∃ candidateTrace : OpenExternal.OpenTrace,
        OpenXTraceObservationOrFailure
          (Assembly.GasAware.validJumps targetProgram) evmFuel
          full candidateTrace (.halted halt)

theorem openXRunListRunningTraceObservationOrFailureReady_current_emitted_prim_call_actual_post
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    OpenXRunListRunningTraceObservationOrFailureReady targetProgram initial
      (EvmYul.EVM.State.incrPC (call.resume response))
      [OpenExternal.OpenEvent.call call.site response]
      (tailFuel + 1) tailFuel := by
  intro full tailTrace targetResult hRel hTail
  have hClassified :=
    openX_current_emitted_prim_call_continue_traceObservationOrFailure_of_step_checks_actual_post
      (program := program) (targetProgram := targetProgram)
      (tailFuel := tailFuel) (initial := initial) (full := full)
      (pc := pc) (op := op) (emitted := emitted) (before := before)
      (after := after) (kind := kind) (call := call) (response := response)
      (tailTrace := tailTrace) (targetResult := targetResult)
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRel
      (hStepChecks hRel) hKind hCall
      (fun hGasCall =>
        hTail
          (evmOpenCall?_gasChargedState_resume_gasExecRel_of_gasExecRel
            (op := op.toEVM) hRel hCall hGasCall response))
  simpa using hClassified

theorem openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_prim_call_actual_post
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
      initial (EvmYul.EVM.State.incrPC (call.resume response))
      (tailFuel + 1) tailFuel := by
  intro full targetResult hRel hTail
  obtain ⟨gasCall, hGasCall, _hSite, hPostRel⟩ :=
    evmOpenCall?_gasChargedState_of_gasExecRel
      (full := full) (target := initial) (op := op.toEVM)
      hRel hCall response
  obtain ⟨candidateTailTrace, hTailClassified⟩ := hTail hPostRel
  refine ⟨OpenExternal.OpenEvent.call call.site response :: candidateTailTrace, ?_⟩
  exact
    openX_current_emitted_prim_call_continue_traceObservationOrFailure_of_step_checks_actual_post
      (program := program) (targetProgram := targetProgram)
      (tailFuel := tailFuel) (initial := initial) (full := full)
      (pc := pc) (op := op) (emitted := emitted) (before := before)
      (after := after) (kind := kind) (call := call) (response := response)
      (tailTrace := candidateTailTrace) (targetResult := targetResult)
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRel
      (hStepChecks hRel) hKind hCall
      (fun {gasCall'} hGasCall' => by
        rw [hGasCall] at hGasCall'
        cases hGasCall'
        exact hTailClassified)

theorem openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_prim_call_of_nonGas_actual_post
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hNonGas :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XNonGasChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
      initial (EvmYul.EVM.State.incrPC (call.resume response))
      (tailFuel + 1) tailFuel := by
  intro full targetResult hRel hTail
  obtain ⟨gasCall, hGasCall, _hSite, hPostRel⟩ :=
    evmOpenCall?_gasChargedState_of_gasExecRel
      (full := full) (target := initial) (op := op.toEVM)
      hRel hCall response
  obtain ⟨candidateTailTrace, hTailClassified⟩ := hTail hPostRel
  exact
    openX_current_emitted_prim_call_continue_traceObservationOrFailure_exists_of_nonGas_actual_post
      (program := program) (targetProgram := targetProgram)
      (tailFuel := tailFuel) (initial := initial) (full := full)
      (pc := pc) (op := op) (emitted := emitted) (before := before)
      (after := after) (kind := kind) (call := call)
      (response := response) (tailTrace := candidateTailTrace)
      (targetResult := targetResult)
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRel
      (hNonGas hRel) hKind hCall
      (fun {gasCall'} hGasCall' => by
        rw [hGasCall] at hGasCall'
        cases hGasCall'
        exact hTailClassified)

theorem openXRunListRunningRelReady_current_emitted_prim_call
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound tailGasBound : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hPostBudget :
      ∀ {full gasPost : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.GasExecRel gasPost
              (EvmYul.EVM.State.incrPC (call.resume response)) →
              tailGasBound ≤ gasPost.gasAvailable.toNat) :
    OpenXRunListRunningRelReady targetProgram initial
      (EvmYul.EVM.State.incrPC (call.resume response))
      [OpenExternal.OpenEvent.call call.site response]
      (tailFuel + 1) tailFuel gasBound tailGasBound := by
  intro full tailTrace targetResult hGasBound hRel hTail
  exact
    openXTraceRelAbove_current_emitted_prim_call_continue_exists_of_step_checks
      (program := program) (targetProgram := targetProgram)
      (tailFuel := tailFuel) (gasBound := gasBound)
      (initial := initial) (pc := pc) (op := op)
      (emitted := emitted) (before := before) (after := after)
      (kind := kind) (call := call) (response := response)
      (tailTrace := tailTrace) (targetResult := targetResult)
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
      hStepChecks hKind hCall
      (fun hGasBound' hRel' hRelPost =>
        hTail (hPostBudget hGasBound' hRel' hRelPost) hRelPost)
      hGasBound hRel

theorem openXRunListRunningRelReady_current_emitted_prim_call_actual_post
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound tailGasBound : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hPostBudget :
      ∀ {full : EVMState} {gasCall : OpenExternal.OpenCall EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            OpenExternal.CallKind.evmOpenCall?
                (gasChargedState full op.toEVM) kind = some gasCall →
              tailGasBound ≤
                (EvmYul.EVM.State.incrPC
                  (finishGasAwareCall gasCall response)).gasAvailable.toNat) :
    OpenXRunListRunningRelReady targetProgram initial
      (EvmYul.EVM.State.incrPC (call.resume response))
      [OpenExternal.OpenEvent.call call.site response]
      (tailFuel + 1) tailFuel gasBound tailGasBound := by
  intro full tailTrace targetResult hGasBound hRel hTail
  exact
    openXTraceRelAbove_current_emitted_prim_call_continue_exists_of_step_checks_actual_post
      (program := program) (targetProgram := targetProgram)
      (tailFuel := tailFuel) (gasBound := gasBound)
      (initial := initial) (pc := pc) (op := op)
      (emitted := emitted) (before := before) (after := after)
      (kind := kind) (call := call) (response := response)
      (tailTrace := tailTrace) (targetResult := targetResult)
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
      hStepChecks hKind hCall
      (fun hGasBound' hRel' hGasCall =>
        hTail (hPostBudget hGasBound' hRel' hGasCall)
          (evmOpenCall?_gasChargedState_resume_gasExecRel_of_gasExecRel
            (op := op.toEVM) hRel' hCall hGasCall response))
      hGasBound hRel

theorem openXRunListRunningRelReady_current_running
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound tailGasBound : Nat}
    {initial post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    (hDecode :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.GasExecRel gasPost post ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost = none)
    (hPostBudget :
      ∀ {full gasPost : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.GasExecRel gasPost post →
              tailGasBound ≤ gasPost.gasAvailable.toNat) :
    OpenXRunListRunningRelReady targetProgram initial post []
      (tailFuel + 1) tailFuel gasBound tailGasBound := by
  intro full tailTrace targetResult hGasBound hRel hTail
  have hRelAbove :
      OpenXTraceRelAbove targetProgram initial tailTrace targetResult
        (tailFuel + 1) gasBound :=
    openXTraceRelAbove_current_running_continue_of_openStepAfterChecks_done
      (targetProgram := targetProgram)
      (tailFuel := tailFuel) (gasBound := gasBound)
      (initial := initial) (post := post) (op := op) (arg := arg)
      (tailTrace := tailTrace) (targetResult := targetResult)
      hDecode hStepChecks hOpenStep hStep
      (fun hGasBound' hRel' hRelPost =>
        hTail (hPostBudget hGasBound' hRel' hRelPost) hRelPost)
  simpa using hRelAbove hGasBound hRel

theorem openXRunListHaltedRelReady_current_success
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {halt : Assembly.Halt}
    (hDecode :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost =
                some output ∧
              op ≠ EvmYul.Operation.REVERT ∧
              OpenXResultAgrees (.halted halt)
                (EvmYul.EVM.ExecutionResult.success gasPost output)) :
    OpenXRunListHaltedRelReady targetProgram initial [] halt
      (tailFuel + 1) gasBound := by
  intro full hGasBound hRel
  exact
    openXTraceRelAbove_current_success_of_openStepAfterChecks_done
      (targetProgram := targetProgram)
      (tailFuel := tailFuel) (gasBound := gasBound)
      (initial := initial) (op := op) (arg := arg)
      (targetResult := .halted halt)
      hDecode hStepChecks hOpenStep hStep
      hGasBound hRel

theorem openXRunListHaltedRelReady_current_revert
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {halt : Assembly.Halt}
    (hDecode :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost =
                some output ∧
              op = EvmYul.Operation.REVERT ∧
              OpenXResultAgrees (.halted halt)
                (EvmYul.EVM.ExecutionResult.revert
                  gasPost.gasAvailable output)) :
    OpenXRunListHaltedRelReady targetProgram initial [] halt
      (tailFuel + 1) gasBound := by
  intro full hGasBound hRel
  exact
    openXTraceRelAbove_current_revert_of_openStepAfterChecks_done
      (targetProgram := targetProgram)
      (tailFuel := tailFuel) (gasBound := gasBound)
      (initial := initial) (op := op) (arg := arg)
      (targetResult := .halted halt)
      hDecode hStepChecks hOpenStep hStep
      hGasBound hRel

inductive OpenXBlockTraceRelReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Nat → EVMState → OpenExternal.OpenTrace → Assembly.StepResult →
      Nat → Nat → Prop where
  | done {state : EVMState} {evmFuel gasBound : Nat}
      (hDone :
        OpenXTracePathDoneContinuation
          (Assembly.GasAware.validJumps targetProgram)
          (.running state) evmFuel) :
      OpenXBlockTraceRelReady program targetProgram 0 state []
        (.running state) evmFuel gasBound
  | stepRunning
      {targetFuel tailFuel evmFuel gasBound tailGasBound : Nat}
      {state mid : EVMState}
      {trace tailTrace : OpenExternal.OpenTrace}
      {targetResult : Assembly.StepResult}
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
      (hRunReady :
        OpenXRunListRunningRelReady targetProgram state mid trace
          evmFuel tailFuel gasBound tailGasBound)
      (hRest :
        OpenXBlockTraceRelReady program targetProgram targetFuel mid
          tailTrace targetResult tailFuel tailGasBound) :
      OpenXBlockTraceRelReady program targetProgram (targetFuel + 1) state
        (trace ++ tailTrace) targetResult evmFuel gasBound
  | stepHalted
      {targetFuel evmFuel gasBound : Nat}
      {state : EVMState}
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
      (hRunReady :
        OpenXRunListHaltedRelReady targetProgram state trace halt
          evmFuel gasBound) :
      OpenXBlockTraceRelReady program targetProgram (targetFuel + 1) state
        trace (.halted halt) evmFuel gasBound

namespace OpenXBlockTraceRelReady

def DoneRelReady (targetProgram : Assembly.TargetProgram) : Prop :=
  ∀ {state : EVMState},
    ∃ evmFuel : Nat, ∃ _gasBound : Nat,
      OpenXTracePathDoneContinuation
        (Assembly.GasAware.validJumps targetProgram)
        (.running state) evmFuel

def DoneContinuationReady
    (targetProgram : Assembly.TargetProgram)
    (targetResult : Assembly.StepResult) : Prop :=
  ∃ evmFuel : Nat, ∃ _gasBound : Nat,
    OpenXTracePathDoneContinuation
      (Assembly.GasAware.validJumps targetProgram) targetResult evmFuel

def DoneObservationOrFailureReady
    (targetProgram : Assembly.TargetProgram)
    (targetResult : Assembly.StepResult) : Prop :=
  ∃ evmFuel : Nat,
    OpenXTracePathDoneObservationOrFailure
      (Assembly.GasAware.validJumps targetProgram) targetResult evmFuel

def DoneReplayAndObservationOrFailureReady
    (targetProgram : Assembly.TargetProgram)
    (targetResult : Assembly.StepResult) : Prop :=
  ∃ evmFuel : Nat, ∃ gasBound : Nat,
    OpenXTracePathDoneContinuation
      (Assembly.GasAware.validJumps targetProgram) targetResult evmFuel ∧
    OpenXTracePathDoneObservationOrFailure
      (Assembly.GasAware.validJumps targetProgram) targetResult evmFuel

theorem DoneContinuationReady.halted
    {targetProgram : Assembly.TargetProgram} {halt : Assembly.Halt} :
    DoneContinuationReady targetProgram (.halted halt) := by
  exact ⟨0, 0, OpenXTracePathDoneContinuation.halted⟩

theorem DoneContinuationReady.running_of_fallthrough_stop
    {targetProgram : Assembly.TargetProgram} {target : EVMState}
    (hReady :
      Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
        target) :
    DoneContinuationReady targetProgram (.running target) := by
  exact
    ⟨2, 0,
      OpenXTracePathDoneContinuation.running_of_fallthrough_stop hReady⟩

theorem DoneContinuationReady.running_of_clean_fallthrough_stop
    {targetProgram : Assembly.TargetProgram} {target : EVMState}
    (hReady :
      Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady target) :
    DoneContinuationReady targetProgram (.running target) := by
  exact
    DoneContinuationReady.running_of_fallthrough_stop
      (Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady.of_clean
        hReady)

theorem DoneContinuationReady.running_of_fallthrough_stop_clear_return_buffers
    {targetProgram : Assembly.TargetProgram} {target : EVMState}
    (hDecodeNone :
      ∀ full : EVMState,
        Assembly.GasAware.GasExecRel full target →
          EvmYul.EVM.decode full.executionEnv.code full.pc = none)
    (hStack : target.stack.length ≤ 1024) :
    DoneContinuationReady targetProgram (.running target) := by
  exact
    ⟨2, 0,
      OpenXTracePathDoneContinuation.running_of_fallthrough_stop_clear_return_buffers
        hDecodeNone hStack⟩

theorem DoneObservationOrFailureReady.running_of_fallthrough_stop_clear_return_buffers
    {targetProgram : Assembly.TargetProgram} {target : EVMState}
    (hDecodeNone :
      ∀ full : EVMState,
        Assembly.GasAware.GasExecRel full target →
          EvmYul.EVM.decode full.executionEnv.code full.pc = none)
    (hStack : target.stack.length ≤ 1024) :
    DoneObservationOrFailureReady targetProgram (.running target) := by
  exact
    ⟨2,
      OpenXTracePathDoneObservationOrFailure.running_of_fallthrough_stop_clear_return_buffers
        hDecodeNone hStack⟩

theorem DoneReplayAndObservationOrFailureReady.running_of_fallthrough_stop_clear_return_buffers
    {targetProgram : Assembly.TargetProgram} {target : EVMState}
    (hDecodeNone :
      ∀ full : EVMState,
        Assembly.GasAware.GasExecRel full target →
          EvmYul.EVM.decode full.executionEnv.code full.pc = none)
    (hStack : target.stack.length ≤ 1024) :
    DoneReplayAndObservationOrFailureReady targetProgram
      (.running target) := by
  exact
    ⟨2, 0,
      OpenXTracePathDoneContinuation.running_of_fallthrough_stop_clear_return_buffers
        hDecodeNone hStack,
      OpenXTracePathDoneObservationOrFailure.running_of_fallthrough_stop_clear_return_buffers
        hDecodeNone hStack⟩

theorem DoneReplayAndObservationOrFailureReady.running_of_clean_fallthrough_stop
    {targetProgram : Assembly.TargetProgram} {target : EVMState}
    (hReady :
      Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady target) :
    DoneReplayAndObservationOrFailureReady targetProgram
      (.running target) :=
  DoneReplayAndObservationOrFailureReady.running_of_fallthrough_stop_clear_return_buffers
    hReady.1 hReady.2.1

theorem done_all_outcomes_safelyTracks_two_of_fallthrough_stop_clear_return_buffers
    {targetProgram : Assembly.TargetProgram} {target : EVMState}
    {reference : EVMResult}
    (hDecodeNone :
      ∀ full : EVMState,
        Assembly.GasAware.GasExecRel full target →
          EvmYul.EVM.decode full.executionEnv.code full.pc = none)
    (hStack : target.stack.length ≤ 1024)
    (hReference : OpenXResultAgrees (.running target) reference) :
    ∀ {full : EVMState}
      {candidateTrace : OpenExternal.OpenTrace}
      {candidateOutcome : Except EVMException EVMResult},
      Assembly.GasAware.GasExecRel full target →
        OpenXOutcomeTraceResult
          (Assembly.GasAware.validJumps targetProgram)
          2 full candidateTrace candidateOutcome →
          Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
            (.ok reference) := by
  intro full candidateTrace candidateOutcome hRel hTrace
  have hFullStack : full.stack.length ≤ 1024 := by
    rw [hRel.stack_eq]
    exact hStack
  have hNonGas :
      Assembly.GasAware.XNonGasChecksPass
        (Assembly.GasAware.validJumps targetProgram) full
        EvmYul.Operation.STOP :=
    Assembly.GasAware.XNonGasChecksPass_stop hFullStack
  rcases
      xStepException?_none_or_outOfGas_of_nonGas_checks
        hNonGas with hException | hException
  · let fullStop := Assembly.GasAware.memoryGasState full
      EvmYul.Operation.STOP
    let chargedStop : EVMState :=
      { fullStop with
        execLength := fullStop.execLength + 1,
        gasAvailable :=
          fullStop.gasAvailable -
            EvmYul.UInt256.ofNat
              (EvmYul.EVM.C' fullStop EvmYul.Operation.STOP) }
    let post : EVMState := clearReturnBuffers chargedStop
    have hChargedRel :
        Assembly.GasAware.GasExecRel chargedStop target := by
      dsimp [chargedStop, fullStop, Assembly.GasAware.memoryGasState,
        Assembly.GasAware.GasExecRel]
      rw [hRel]
    have hStep :
        EvmYul.EVM.step 1
            (EvmYul.EVM.C'
              (Assembly.GasAware.memoryGasState full EvmYul.Operation.STOP)
              EvmYul.Operation.STOP)
            (some (EvmYul.Operation.STOP, none))
            (Assembly.GasAware.memoryGasState full EvmYul.Operation.STOP) =
          .ok post := by
      dsimp [post, clearReturnBuffers, chargedStop, fullStop]
      rfl
    have hResolved :
        OpenExternal.OpenResultResolves
          ((.done
            (.ok
              (EvmYul.EVM.ExecutionResult.success post ByteArray.empty))) :
            OpenExternal.OpenResult EVMException EVMResult)
          candidateTrace candidateOutcome := by
      unfold OpenXOutcomeTraceResult at hTrace
      rw [show (2 : Nat) = 1 + 1 by rfl] at hTrace
      rw [openX_succ] at hTrace
      simp [hDecodeNone full hRel, hException] at hTrace
      have hKind :
          OpenExternal.CallKind.ofEVMOperation? EvmYul.Operation.STOP =
            none := by
        rfl
      rw [openStepAfterChecks_of_not_callKind
        (fuel := 1) (op := EvmYul.Operation.STOP) (arg := none)
        (state := full) hKind] at hTrace
      rw [hStep] at hTrace
      simpa [continueAfterStep, Assembly.GasAware.XStepHaltOutput?] using
        hTrace
    cases hResolved
    exact
      Assembly.GasAware.XRunOutcomeSafelyTracks.retarget_ok
        (Assembly.GasAware.XRunOutcomeSafelyTracks.ok_refl
          (EvmYul.EVM.ExecutionResult.success post ByteArray.empty))
        ((OpenXResultAgrees.running_success_of_gasExecRel_clear_return_buffers
          hChargedRel).committedObservation.trans
            hReference.committedObservation.symm)
  · exact
      openX_fallthrough_stop_outOfGas_exception_all_outcomes_safelyTracks
        (fuel := 1)
        (validJumps := Assembly.GasAware.validJumps targetProgram)
        (state := full) (trace := candidateTrace)
        (outcome := candidateOutcome) (reference := reference)
        (hDecodeNone full hRel) hException hTrace

theorem done_all_outcomes_safelyTracks_of_fallthrough_stop_clear_return_buffers
    {targetProgram : Assembly.TargetProgram} {target : EVMState}
    {reference : EVMResult}
    (hDecodeNone :
      ∀ full : EVMState,
        Assembly.GasAware.GasExecRel full target →
          EvmYul.EVM.decode full.executionEnv.code full.pc = none)
    (hStack : target.stack.length ≤ 1024)
    (hReference : OpenXResultAgrees (.running target) reference) :
    ∃ evmFuel,
      ∀ {full : EVMState}
        {candidateTrace : OpenExternal.OpenTrace}
        {candidateOutcome : Except EVMException EVMResult},
        Assembly.GasAware.GasExecRel full target →
          OpenXOutcomeTraceResult
            (Assembly.GasAware.validJumps targetProgram)
            evmFuel full candidateTrace candidateOutcome →
            Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
              (.ok reference) :=
  ⟨2,
    done_all_outcomes_safelyTracks_two_of_fallthrough_stop_clear_return_buffers
      hDecodeNone hStack hReference⟩

def RunningPathRelReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {tailFuel tailGasBound : Nat},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      trace (.ok (.running mid)) →
    ∃ evmFuel gasBound,
      OpenXRunListRunningRelReady targetProgram state mid trace
        evmFuel tailFuel gasBound tailGasBound

def HaltedPathRelReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      trace (.ok (.halted halt)) →
    ∃ evmFuel gasBound,
      OpenXRunListHaltedRelReady targetProgram state trace halt
        evmFuel gasBound

def RunListRunningReadyFor
    (targetProgram : Assembly.TargetProgram)
    (state mid : EVMState) (trace : OpenExternal.OpenTrace) : Prop :=
  ∀ {tailFuel tailGasBound : Nat},
    ∃ evmFuel gasBound,
      OpenXRunListRunningRelReady targetProgram state mid trace
        evmFuel tailFuel gasBound tailGasBound

def RunListRunningTraceObservationOrFailureReadyFor
    (targetProgram : Assembly.TargetProgram)
    (state mid : EVMState) (trace : OpenExternal.OpenTrace) : Prop :=
  ∀ {tailFuel : Nat},
    ∃ evmFuel,
      OpenXRunListRunningTraceObservationOrFailureReady targetProgram state
        mid trace evmFuel tailFuel

def RunListRunningTraceObservationOrFailureExistsReadyFor
    (targetProgram : Assembly.TargetProgram)
    (state mid : EVMState) : Prop :=
  ∀ {tailFuel : Nat},
    ∃ evmFuel,
      OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
        state mid evmFuel tailFuel

def RunListHaltedReadyFor
    (targetProgram : Assembly.TargetProgram)
    (state : EVMState) (trace : OpenExternal.OpenTrace)
    (halt : Assembly.Halt) : Prop :=
  ∃ evmFuel gasBound,
    OpenXRunListHaltedRelReady targetProgram state trace halt
      evmFuel gasBound

def RunListHaltedTraceObservationOrFailureExistsReadyFor
    (targetProgram : Assembly.TargetProgram)
    (state : EVMState) (halt : Assembly.Halt) : Prop :=
  ∃ evmFuel,
    OpenXRunListHaltedTraceObservationOrFailureExistsReady targetProgram
      state halt evmFuel

def RunningPathTraceObservationOrFailureExistsReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      trace (.ok (.running mid)) →
    RunListRunningTraceObservationOrFailureExistsReadyFor targetProgram
      state mid

def HaltedPathTraceObservationOrFailureExistsReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      trace (.ok (.halted halt)) →
    RunListHaltedTraceObservationOrFailureExistsReadyFor targetProgram
      state halt

def RunningPathReplayAndTraceObservationOrFailureExistsReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {tailFuel tailGasBound : Nat},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      trace (.ok (.running mid)) →
    ∃ evmFuel gasBound,
      OpenXRunListRunningRelReady targetProgram state mid trace
        evmFuel tailFuel gasBound tailGasBound ∧
      OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
        state mid evmFuel tailFuel

def HaltedPathReplayAndTraceObservationOrFailureExistsReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      trace (.ok (.halted halt)) →
    ∃ evmFuel gasBound,
      OpenXRunListHaltedRelReady targetProgram state trace halt
        evmFuel gasBound ∧
      OpenXRunListHaltedTraceObservationOrFailureExistsReady targetProgram
        state halt evmFuel

def OpenXRunListRunningAllOutcomeTracksReady
    (targetProgram : Assembly.TargetProgram)
    (state mid : EVMState)
    (evmFuel tailFuel : Nat)
    (reference : EVMResult) : Prop :=
  ∀ {full : EVMState}
    {candidateTrace : OpenExternal.OpenTrace}
    {candidateOutcome : Except EVMException EVMResult},
    Assembly.GasAware.GasExecRel full state →
      (∀ {gasPost : EVMState},
        Assembly.GasAware.GasExecRel gasPost mid →
          OpenXStateAllOutcomeTracesSafelyTrackResult
            (Assembly.GasAware.validJumps targetProgram)
            tailFuel gasPost reference) →
        OpenXOutcomeTraceResult
          (Assembly.GasAware.validJumps targetProgram)
          evmFuel full candidateTrace candidateOutcome →
          Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
            (.ok reference)

def OpenXRunListHaltedAllOutcomeTracksReady
    (targetProgram : Assembly.TargetProgram)
    (state : EVMState)
    (evmFuel : Nat)
    (reference : EVMResult) : Prop :=
  ∀ {full : EVMState}
    {candidateTrace : OpenExternal.OpenTrace}
    {candidateOutcome : Except EVMException EVMResult},
    Assembly.GasAware.GasExecRel full state →
      OpenXOutcomeTraceResult
        (Assembly.GasAware.validJumps targetProgram)
        evmFuel full candidateTrace candidateOutcome →
        Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
          (.ok reference)

def RunListRunningAllOutcomeTracksReadyFor
    (targetProgram : Assembly.TargetProgram)
    (state mid : EVMState)
    (reference : EVMResult) : Prop :=
  ∀ {tailFuel : Nat},
    ∃ evmFuel,
      OpenXRunListRunningAllOutcomeTracksReady targetProgram state mid
        evmFuel tailFuel reference

def RunListHaltedAllOutcomeTracksReadyFor
    (targetProgram : Assembly.TargetProgram)
    (state : EVMState)
    (reference : EVMResult) : Prop :=
  ∃ evmFuel,
    OpenXRunListHaltedAllOutcomeTracksReady targetProgram state evmFuel
      reference

def RunningPathAllOutcomeTracksReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram)
    (reference : EVMResult) : Prop :=
  ∀ {state mid : EVMState}
    {referenceTrace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {tailFuel : Nat},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      referenceTrace (.ok (.running mid)) →
    ∃ evmFuel,
      OpenXRunListRunningAllOutcomeTracksReady targetProgram state mid
        evmFuel tailFuel reference

def HaltedPathAllOutcomeTracksReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram)
    (reference : EVMResult) : Prop :=
  ∀ {state : EVMState}
    {referenceTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      referenceTrace (.ok (.halted halt)) →
    ∃ evmFuel,
      OpenXRunListHaltedAllOutcomeTracksReady targetProgram state
        evmFuel reference

theorem openRunListResult_emitInstr_prim_call_running_inv
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {emitted : List Assembly.LocatedTarget} {state mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        trace (.ok (.running mid))) :
    ∃ response : OpenExternal.CallResponse,
      trace = [OpenExternal.OpenEvent.call call.site response] ∧
        mid = EvmYul.EVM.State.incrPC (call.resume response) := by
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
  rw [OpenAssembly.Target.openStepInstr_of_prim_call hKind hCall] at hRun
  unfold OpenAssembly.evmInstructionCallResult at hRun
  rw [OpenExternal.OpenResult.bind_call] at hRun
  cases hRun with
  | call hTail =>
      have hHalt : (Assembly.TargetInstr.prim op).haltKind? = none := by
        simpa [Assembly.TargetInstr.haltKind?] using
          OpenAssembly.Target.prim_haltKind?_none_of_callKind hKind
      simp [OpenAssembly.Target.stepResultAfter, hHalt,
        OpenAssembly.Target.openRunListResult_nil] at hTail
      cases hTail
      exact ⟨_, rfl, rfl⟩

theorem openRunListResult_emitInstr_no_call_inv
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {result : Assembly.StepResult}
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) state)
        trace (.ok result)) :
    trace = [] ∧
      Assembly.Target.runListResult
        (emitted.map Assembly.LocatedTarget.instr) state =
        .ok result := by
  have hCode :
      OpenAssembly.Target.codeUsesCallCreate
        (emitted.map Assembly.LocatedTarget.instr) = false :=
    OpenAssembly.Target.codeUsesCallCreate_false_of_emitInstr_no_call
      hNoInstr hEmit
  exact
    OpenAssembly.Target.openRunListResult_resolves_closed_inv_of_no_callCreate
      hCode hRun

theorem runListRunningReadyFor_no_call_of_path_ready
    {targetProgram : Assembly.TargetProgram}
    {code : List Assembly.TargetInstr}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    (hTrace : trace = [])
    (hReady :
      ∀ {tailGasBound : Nat},
        ∃ gasBound : Nat,
          (∀ {full : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.XStepTrace.XRunListPathReady
                  (Assembly.GasAware.validJumps targetProgram)
                  code initial full (.running mid)) ∧
          (∀ {full gasPost : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.GasExecRel gasPost mid →
                  tailGasBound ≤ gasPost.gasAvailable.toNat)) :
    RunListRunningReadyFor targetProgram initial mid trace := by
  subst trace
  intro tailFuel tailGasBound
  obtain ⟨gasBound, hPathReady, hPostBudget⟩ :=
    hReady (tailGasBound := tailGasBound)
  refine ⟨tailFuel + code.length, gasBound, ?_⟩
  intro full tailTrace targetResult hGasBound hRel hTail
  have hPath := hPathReady hGasBound hRel
  cases tailFuel with
  | zero =>
      obtain ⟨_prefixFuel, fullFinal, hRelFinal, _hPrefix⟩ :=
        Assembly.GasAware.XStepTrace.XRunListPathReady.running_prefix
          hPath
      obtain ⟨result, hZero, _hAgree⟩ :=
        hTail (hPostBudget hGasBound hRel hRelFinal) hRelFinal
      exact False.elim (OpenXTraceResult.zero_false hZero)
  | succ tailFuel' =>
      obtain ⟨result, hTraceRun, hAgree⟩ :=
        openX_runListResult_running_with_positive_path_continuation_agrees_of_path_ready
          (validJumps := Assembly.GasAware.validJumps targetProgram)
          (code := code) (target := initial) (full := full)
          (targetFinal := mid)
          (finalResult := targetResult)
          (tailFuel := tailFuel')
          (tailTrace := tailTrace)
          hPath
          (fun fullFinal hRelFinal => by
            obtain ⟨tailResult, hTailTrace, hTailAgree⟩ :=
              hTail (hPostBudget hGasBound hRel hRelFinal) hRelFinal
            exact ⟨tailResult, hTailTrace, hTailAgree⟩)
      refine ⟨result, ?_, hAgree⟩
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hTraceRun

theorem runListHaltedReadyFor_no_call_of_path_ready
    {targetProgram : Assembly.TargetProgram}
    {code : List Assembly.TargetInstr}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    (hTrace : trace = [])
    (hReady :
      ∃ gasBound : Nat,
        ∀ {full : EVMState},
          gasBound ≤ full.gasAvailable.toNat →
            Assembly.GasAware.GasExecRel full initial →
              Assembly.GasAware.XStepTrace.XRunListPathReady
                (Assembly.GasAware.validJumps targetProgram)
                code initial full (.halted halt)) :
    RunListHaltedReadyFor targetProgram initial trace halt := by
  subst trace
  obtain ⟨gasBound, hPathReady⟩ := hReady
  refine ⟨code.length.succ, gasBound, ?_⟩
  intro full hGasBound hRel
  have hPath := hPathReady hGasBound hRel
  obtain ⟨result, hTraceRun, hAgree⟩ :=
    openX_runListResult_with_positive_path_continuation_agrees_of_path_ready
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (code := code) (target := initial) (full := full)
      (blockResult := .halted halt)
      (finalResult := .halted halt)
      (tailFuel := 0)
      hPath
      (fun halt' hEq => by cases hEq; rfl)
      (fun targetFinal fullFinal hEq _hRelFinal => by
        cases hEq)
  exact ⟨result, by simpa using hTraceRun, hAgree⟩

theorem runListRunningReadyFor_current_emitted_no_call_of_path_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hReady :
      ∀ {tailGasBound : Nat},
        ∃ gasBound : Nat,
          (∀ {full : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.XStepTrace.XRunListPathReady
                  (Assembly.GasAware.validJumps targetProgram)
                  (emitted.map Assembly.LocatedTarget.instr)
                  initial full (.running mid)) ∧
          (∀ {full gasPost : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.GasExecRel gasPost mid →
                  tailGasBound ≤ gasPost.gasAvailable.toNat)) :
    RunListRunningReadyFor targetProgram initial mid trace := by
  obtain ⟨hTrace, _hClosedRun⟩ :=
    openRunListResult_emitInstr_no_call_inv
      hNoInstr hEmit hRun
  exact
    runListRunningReadyFor_no_call_of_path_ready
      (targetProgram := targetProgram)
      (code := emitted.map Assembly.LocatedTarget.instr)
      (initial := initial) (mid := mid) (trace := trace)
      hTrace hReady

theorem runListHaltedReadyFor_current_emitted_no_call_of_path_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hReady :
      ∃ gasBound : Nat,
        ∀ {full : EVMState},
          gasBound ≤ full.gasAvailable.toNat →
            Assembly.GasAware.GasExecRel full initial →
              Assembly.GasAware.XStepTrace.XRunListPathReady
                (Assembly.GasAware.validJumps targetProgram)
                (emitted.map Assembly.LocatedTarget.instr)
                initial full (.halted halt)) :
    RunListHaltedReadyFor targetProgram initial trace halt := by
  obtain ⟨hTrace, _hClosedRun⟩ :=
    openRunListResult_emitInstr_no_call_inv
      hNoInstr hEmit hRun
  exact
    runListHaltedReadyFor_no_call_of_path_ready
      (targetProgram := targetProgram)
      (code := emitted.map Assembly.LocatedTarget.instr)
      (initial := initial) (trace := trace) (halt := halt)
      hTrace hReady

def CurrentNoCallPathChecksReady
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state full : EVMState} {result : Assembly.StepResult}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget},
    Assembly.Program.instrAtPc program state.pc.toNat = some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    Assembly.Instr.usesCallCreate instr = false →
    Assembly.Target.runListResult
        (emitted.map Assembly.LocatedTarget.instr) state =
      .ok result →
    Assembly.GasAware.GasExecRel full state →
      Assembly.GasAware.XStepTrace.XRunListPathChecksReady
        (Assembly.GasAware.validJumps targetProgram)
        (emitted.map Assembly.LocatedTarget.instr) state full result

def CurrentNoCallInstrCoreResidualResources
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {pc : Nat} {instr : Assembly.Instr}
      {emitted before after : List Assembly.LocatedTarget}
      {blockState : EVMState} {blockResult : Assembly.StepResult},
    Assembly.Program.instrAtPc program blockState.pc.toNat =
        some (pc, instr) →
      Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
          Assembly.Instr.usesCallCreate instr = false →
            Assembly.Target.runListResult
                (emitted.map Assembly.LocatedTarget.instr) blockState =
              .ok blockResult →
            Assembly.GasAware.XStepTrace.InstrCoreResidualInputsReady
              targetProgram instr blockState

inductive CurrentNoCallInstrCoreResidualTraceReadyFor
    {program : Assembly.Program} (targetProgram : Assembly.TargetProgram) :
    {targetFuel : Nat} → {state : EVMState} →
      {trace : OpenExternal.OpenTrace} →
        {targetResult : Assembly.StepResult} →
          OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
            state trace targetResult → Prop where
  | done (state : EVMState) :
      CurrentNoCallInstrCoreResidualTraceReadyFor targetProgram
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
      (hResidual :
        Assembly.Instr.usesCallCreate instr = false →
          Assembly.GasAware.XStepTrace.InstrCoreResidualInputsReady
            targetProgram instr state)
      (hRestReady :
        CurrentNoCallInstrCoreResidualTraceReadyFor targetProgram hRest) :
      CurrentNoCallInstrCoreResidualTraceReadyFor targetProgram
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
      (hResidual :
        Assembly.Instr.usesCallCreate instr = false →
          Assembly.GasAware.XStepTrace.InstrCoreResidualInputsReady
            targetProgram instr state) :
      CurrentNoCallInstrCoreResidualTraceReadyFor targetProgram
        (OpenAssembly.OpenBlockTraceResult.stepHalted
          hAt hEmit hTargetBlock hRun)

namespace CurrentNoCallInstrCoreResidualTraceReadyFor

theorem cast_trace
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {hTrace hTrace' :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        state trace targetResult}
    (hReady :
      CurrentNoCallInstrCoreResidualTraceReadyFor targetProgram hTrace) :
    CurrentNoCallInstrCoreResidualTraceReadyFor targetProgram hTrace' := by
  have hEq : hTrace = hTrace' := proof_irrel hTrace hTrace'
  subst hTrace'
  exact hReady

theorem of_current_resources
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        state trace targetResult}
    (hResources :
      CurrentNoCallInstrCoreResidualResources program targetProgram) :
    CurrentNoCallInstrCoreResidualTraceReadyFor targetProgram hTrace := by
  induction hTrace with
  | done state =>
      exact done (targetProgram := targetProgram) state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      exact stepRunning hAt hEmit hTargetBlock hRun
        (fun hNoCall =>
          hResources hAt hEmit hTargetBlock hNoCall
            (openRunListResult_emitInstr_no_call_inv
              hNoCall hEmit hRun).2)
        ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state trace halt pc instr emitted before after
      exact stepHalted (fuel := fuel) hAt hEmit hTargetBlock hRun
        (fun hNoCall =>
          hResources hAt hEmit hTargetBlock hNoCall
            (openRunListResult_emitInstr_no_call_inv
              hNoCall hEmit hRun).2)

end CurrentNoCallInstrCoreResidualTraceReadyFor

theorem CurrentNoCallPathChecksReady.of_blockPathChecks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hChecks :
      Assembly.GasAware.XStepTrace.XBlockPathChecksReady program
        targetProgram (Assembly.GasAware.validJumps targetProgram)) :
    CurrentNoCallPathChecksReady program targetProgram := by
  intro state full result pc instr emitted before after
    hAt hEmit hTargetBlock _hNoCall hRun hRel
  exact hChecks hAt hEmit hTargetBlock hRun hRel

theorem CurrentNoCallPathChecksReady.of_core_noReturnDataCopy_current_no_call
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hCore :
      Assembly.GasAware.XStepTrace.XBlockReplayCoreNonGasReady program
        targetProgram (Assembly.GasAware.validJumps targetProgram))
    (hNoReturnDataCopy :
      Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy program
        targetProgram) :
    CurrentNoCallPathChecksReady program targetProgram := by
  intro state full result pc instr emitted before after hAt hEmit
    hTargetBlock hNoCall hRun hRel
  exact
    Assembly.GasAware.XStepTrace.XRunListPathChecksReady.of_suffix_core_noReturnDataCopy_noCallCreate
      hRun
      (hCore hAt hEmit hTargetBlock hRun)
      (fun targetInstr hMem =>
        hNoReturnDataCopy hAt hEmit hTargetBlock hRun targetInstr hMem)
      (fun targetInstr hMem => by
        rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
        subst targetInstr
        exact
          Assembly.GasAware.targetInstr_usesCallCreate_false_of_emitInstr_mem
            hNoCall hEmit hLocatedMem)
      hRel

theorem current_no_call_path_checks_of_residual_noReturnDataCopy
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {state full : EVMState} {result : Assembly.StepResult}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hAssemble : Assembly.assemble? program = some targetProgram)
    (hJumpdest : Assembly.Bytecode.JumpdestCorrect targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hNoCall : Assembly.Instr.usesCallCreate instr = false)
    (hRun :
      Assembly.Target.runListResult
          (emitted.map Assembly.LocatedTarget.instr) state =
        .ok result)
    (hRel : Assembly.GasAware.GasExecRel full state)
    (hResidual :
      Assembly.GasAware.XStepTrace.InstrCoreResidualInputsReady
        targetProgram instr state)
    (hNoReturnDataCopy :
      Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy program
        targetProgram) :
    Assembly.GasAware.XStepTrace.XRunListPathChecksReady
      (Assembly.GasAware.validJumps targetProgram)
      (emitted.map Assembly.LocatedTarget.instr) state full result := by
  have hBlockInputs :
      Assembly.GasAware.XStepTrace.InstrCoreBlockInputsReady targetProgram
        instr state :=
    Assembly.GasAware.XStepTrace.InstrCoreBlockInputsReady.of_residual_no_call_create
      hEmit hNoCall hRun hResidual
  have hBlockReady :
      Assembly.GasAware.XStepTrace.InstrCoreBlockReady targetProgram instr
        state :=
    Assembly.GasAware.XStepTrace.InstrCoreBlockReady.of_inputs_ready
      hBlockInputs
  have hCoreRun :
      Assembly.GasAware.XStepTrace.CoreRunListResult
        (Assembly.GasAware.validJumps targetProgram)
        (emitted.map Assembly.LocatedTarget.instr) state result :=
    Assembly.GasAware.XStepTrace.CoreRunListResult.of_emitInstr_coreBlockReady
      hAssemble hJumpdest
      hEmit hBlockReady hRun
  have hNoCallCode :
      ∀ targetInstr ∈ emitted.map Assembly.LocatedTarget.instr,
        Assembly.GasAware.targetInstrUsesCallCreate targetInstr = false := by
    intro targetInstr hMem
    rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
    subst targetInstr
    exact
      Assembly.GasAware.targetInstr_usesCallCreate_false_of_emitInstr_mem
        hNoCall hEmit hLocatedMem
  have hCorePath :
      Assembly.GasAware.XStepTrace.XRunListPathCoreChecksReady
        (Assembly.GasAware.validJumps targetProgram)
        (emitted.map Assembly.LocatedTarget.instr) state full result :=
    Assembly.GasAware.XStepTrace.CoreRunListResult.to_path_core_checks
      hCoreRun hNoCallCode hRel
  exact
    Assembly.GasAware.XStepTrace.XRunListPathChecksReady.of_path_core_noReturnDataCopy_noCallCreate
      hCorePath
      (fun targetInstr hMem =>
        hNoReturnDataCopy hAt hEmit hTargetBlock hRun targetInstr hMem)
      hNoCallCode

theorem CurrentNoCallPathChecksReady.of_current_residual_noReturnDataCopy_current_no_call
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hCompile : Assembly.compile? program = some targetProgram)
    (hJumpdest : Assembly.Bytecode.JumpdestCorrect targetProgram)
    (hResidual :
      CurrentNoCallInstrCoreResidualResources program targetProgram)
    (hNoReturnDataCopy :
      Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy program
        targetProgram) :
    CurrentNoCallPathChecksReady program targetProgram := by
  intro state full result pc instr emitted before after hAt hEmit
    hTargetBlock hNoCall hRun hRel
  exact
    current_no_call_path_checks_of_residual_noReturnDataCopy
      (Assembly.Preservation.compile?_some_assemble hCompile) hJumpdest
      hAt hEmit hTargetBlock hNoCall hRun hRel
      (hResidual hAt hEmit hTargetBlock hNoCall hRun)
      hNoReturnDataCopy

theorem CurrentNoCallPathChecksReady.of_residual_noReturnDataCopy_current_no_call
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hCompile : Assembly.compile? program = some targetProgram)
    (hJumpdest : Assembly.Bytecode.JumpdestCorrect targetProgram)
    (hResidual :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreResidualResources program
        targetProgram)
    (hNoReturnDataCopy :
      Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy program
        targetProgram) :
    CurrentNoCallPathChecksReady program targetProgram := by
  intro state full result pc instr emitted before after hAt hEmit
    hTargetBlock hNoCall hRun hRel
  have hBlockInputs :
      Assembly.GasAware.XStepTrace.InstrCoreBlockInputsReady targetProgram
        instr state :=
    Assembly.GasAware.XStepTrace.InstrCoreBlockInputsReady.of_residual_no_call_create
      hEmit hNoCall hRun (hResidual hAt hEmit hTargetBlock hRun)
  have hBlockReady :
      Assembly.GasAware.XStepTrace.InstrCoreBlockReady targetProgram instr
        state :=
    Assembly.GasAware.XStepTrace.InstrCoreBlockReady.of_inputs_ready
      hBlockInputs
  have hCoreRun :
      Assembly.GasAware.XStepTrace.CoreRunListResult
        (Assembly.GasAware.validJumps targetProgram)
        (emitted.map Assembly.LocatedTarget.instr) state result :=
    Assembly.GasAware.XStepTrace.CoreRunListResult.of_emitInstr_coreBlockReady
      (Assembly.Preservation.compile?_some_assemble hCompile) hJumpdest
      hEmit hBlockReady hRun
  have hNoCallCode :
      ∀ targetInstr ∈ emitted.map Assembly.LocatedTarget.instr,
        Assembly.GasAware.targetInstrUsesCallCreate targetInstr = false := by
    intro targetInstr hMem
    rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
    subst targetInstr
    exact
      Assembly.GasAware.targetInstr_usesCallCreate_false_of_emitInstr_mem
        hNoCall hEmit hLocatedMem
  have hCorePath :
      Assembly.GasAware.XStepTrace.XRunListPathCoreChecksReady
        (Assembly.GasAware.validJumps targetProgram)
        (emitted.map Assembly.LocatedTarget.instr) state full result :=
    Assembly.GasAware.XStepTrace.CoreRunListResult.to_path_core_checks
      hCoreRun hNoCallCode hRel
  exact
    Assembly.GasAware.XStepTrace.XRunListPathChecksReady.of_path_core_noReturnDataCopy_noCallCreate
      hCorePath
      (fun targetInstr hMem =>
        hNoReturnDataCopy hAt hEmit hTargetBlock hRun targetInstr hMem)
      hNoCallCode

theorem openXRunListRunningRelReady_current_emitted_no_call_of_current_path_checks_and_budget
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel tailGasBound : Nat}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.running mid)) :
    OpenXRunListRunningRelReady targetProgram initial mid trace
      (tailFuel + (emitted.map Assembly.LocatedTarget.instr).length)
      tailFuel
      (Assembly.GasAware.XStepTrace.XRunListGasBudget
        (emitted.map Assembly.LocatedTarget.instr) initial +
        tailGasBound)
      tailGasBound := by
  obtain ⟨hTrace, hClosedRun⟩ :=
    openRunListResult_emitInstr_no_call_inv
      hNoInstr hEmit hRun
  subst trace
  let code := emitted.map Assembly.LocatedTarget.instr
  let gasBound :=
    Assembly.GasAware.XStepTrace.XRunListGasBudget code initial +
      tailGasBound
  intro full tailTrace targetResult hGasBound hRel hTail
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hChecksCode :
      Assembly.GasAware.XStepTrace.XRunListPathChecksReady
        (Assembly.GasAware.validJumps targetProgram) code initial full
        (.running mid) := by
    dsimp [code]
    exact hChecks hRel
  have hNoCallCode :
      ∀ targetInstr ∈ code,
        Assembly.GasAware.targetInstrUsesCallCreate targetInstr = false := by
    intro targetInstr hMem
    dsimp [code] at hMem
    rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
    subst targetInstr
    exact Assembly.GasAware.targetInstr_usesCallCreate_false_of_emitInstr_mem
      hNoInstr hEmit hLocatedMem
  have hBudgetBlock :
      Assembly.GasAware.XStepTrace.XRunListGasBudget code initial ≤
        full.gasAvailable.toNat := by
    have hBudgetFull :
        Assembly.GasAware.XStepTrace.XRunListGasBudget code initial +
            tailGasBound ≤ full.gasAvailable.toNat := by
      simpa [code] using hGasBound
    omega
  have hPath :
      Assembly.GasAware.XStepTrace.XRunListPathReady
        (Assembly.GasAware.validJumps targetProgram) code initial full
        (.running mid) :=
    Assembly.GasAware.XStepTrace.XRunListPathReady.of_emitInstr_checks_and_budget
      (program := program) (target := targetProgram)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (blockState := initial) (fullState := full)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      (blockResult := .running mid)
      hEncoding hSafety hAt hEmit hTargetBlock
      (by simpa [code] using hClosedRun)
      hRel hCode (by simpa [code] using hChecksCode)
      (by simpa [code] using hNoCallCode) hBudgetBlock
  cases tailFuel with
  | zero =>
      obtain ⟨_prefixFuel, fullFinal, hRelFinal, _hPrefix,
          hTailBudget⟩ :=
        Assembly.GasAware.XStepTrace.XRunListPathReady.running_prefix_with_budget
          (validJumps := Assembly.GasAware.validJumps targetProgram)
          (code := code) (target := initial) (full := full)
          (targetFinal := mid) (restBudget := tailGasBound)
          hPath
          (by
            simpa [code] using hGasBound)
      obtain ⟨result, hZero, _hAgree⟩ :=
        hTail hTailBudget hRelFinal
      exact False.elim (OpenXTraceResult.zero_false hZero)
  | succ tailFuel' =>
      obtain ⟨result, hTraceRun, hAgree⟩ :=
        openX_runListResult_running_with_positive_path_continuation_agrees_of_path_ready_and_budget
          (validJumps := Assembly.GasAware.validJumps targetProgram)
          (code := code) (target := initial) (full := full)
          (targetFinal := mid)
          (finalResult := targetResult)
          (tailFuel := tailFuel')
          (restBudget := tailGasBound)
          (tailTrace := tailTrace)
          hPath
          (by
            simpa [code] using hGasBound)
          (fun fullFinal hRelFinal hTailBudget => by
            obtain ⟨tailResult, hTailTrace, hTailAgree⟩ :=
              hTail hTailBudget hRelFinal
            exact ⟨tailResult, hTailTrace, hTailAgree⟩)
      refine ⟨result, ?_, hAgree⟩
      simpa [code, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hTraceRun

theorem runListRunningReadyFor_current_emitted_no_call_of_current_path_checks_and_budget
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.running mid)) :
    RunListRunningReadyFor targetProgram initial mid trace := by
  intro tailFuel tailGasBound
  exact
    ⟨tailFuel + (emitted.map Assembly.LocatedTarget.instr).length,
      Assembly.GasAware.XStepTrace.XRunListGasBudget
        (emitted.map Assembly.LocatedTarget.instr) initial +
        tailGasBound,
      openXRunListRunningRelReady_current_emitted_no_call_of_current_path_checks_and_budget
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (tailGasBound := tailGasBound)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock
        hRun hChecks⟩

theorem openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.running mid)) :
    OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
      initial mid (tailFuel + (emitted.map Assembly.LocatedTarget.instr).length)
      tailFuel := by
  intro full targetResult hRel hTail
  obtain ⟨_hTrace, hClosedRun⟩ :=
    openRunListResult_emitInstr_no_call_inv hNoInstr hEmit hRun
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hDecodePath :
      Assembly.GasAware.XStepTrace.XRunListPathDecodeReady
        (emitted.map Assembly.LocatedTarget.instr) initial full
        (.running mid) :=
    Assembly.GasAware.XStepTrace.XRunListPathDecodeReady.of_emitInstr
      hEncoding hSafety hAt hEmit hTargetBlock hClosedRun hRel hCode
  exact
    openX_runListResult_running_traceObservationOrFailure_exists_of_path_decode_checks
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (code := emitted.map Assembly.LocatedTarget.instr)
      (target := initial) (full := full) (targetFinal := mid)
      (targetResult := targetResult) (tailFuel := tailFuel)
      hDecodePath (hChecks hRel) (fun fullFinal hRelFinal =>
        hTail hRelFinal)

theorem runListRunningReadyFor_current_emitted_no_call_of_path_checks_and_budget
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram) :
    RunListRunningReadyFor targetProgram initial mid trace :=
  runListRunningReadyFor_current_emitted_no_call_of_current_path_checks_and_budget
    hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock hRun
    (fun hRel => hChecks hAt hEmit hTargetBlock hNoInstr
      (by
        obtain ⟨_hTrace, hClosedRun⟩ :=
          openRunListResult_emitInstr_no_call_inv
            hNoInstr hEmit hRun
        exact hClosedRun)
      hRel)

theorem runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.running mid)) :
    RunListRunningTraceObservationOrFailureExistsReadyFor targetProgram
      initial mid := by
  intro tailFuel
  exact
    ⟨tailFuel + (emitted.map Assembly.LocatedTarget.instr).length,
      openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_no_call_of_current_path_checks
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (initial := initial) (mid := mid)
        (trace := trace) (pc := pc) (instr := instr)
        (emitted := emitted) (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock
        hRun hChecks⟩

theorem openXRunListRunningAllOutcomeTracksReady_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {reference : EVMResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.running mid)) :
    OpenXRunListRunningAllOutcomeTracksReady targetProgram initial mid
      (tailFuel + (emitted.map Assembly.LocatedTarget.instr).length)
      tailFuel reference := by
  intro full candidateTrace candidateOutcome hRel hTail hOutcome
  obtain ⟨_hTrace, hClosedRun⟩ :=
    openRunListResult_emitInstr_no_call_inv hNoInstr hEmit hRun
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hDecodePath :
      Assembly.GasAware.XStepTrace.XRunListPathDecodeReady
        (emitted.map Assembly.LocatedTarget.instr) initial full
        (.running mid) :=
    Assembly.GasAware.XStepTrace.XRunListPathDecodeReady.of_emitInstr
      hEncoding hSafety hAt hEmit hTargetBlock hClosedRun hRel hCode
  have hAll :=
    openX_runListResult_running_all_outcomes_safelyTracks_of_path_decode_checks
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (code := emitted.map Assembly.LocatedTarget.instr)
      (target := initial) (full := full) (targetFinal := mid)
      (tailFuel := tailFuel) (reference := reference)
      hDecodePath (hChecks hRel)
      (fun gasPost hRelPost => hTail hRelPost)
  exact hAll candidateTrace candidateOutcome hOutcome

theorem runListRunningAllOutcomeTracksReadyFor_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {reference : EVMResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.running mid)) :
    RunListRunningAllOutcomeTracksReadyFor targetProgram initial mid
      reference := by
  intro tailFuel
  exact
    ⟨tailFuel + (emitted.map Assembly.LocatedTarget.instr).length,
      openXRunListRunningAllOutcomeTracksReady_current_emitted_no_call_of_current_path_checks
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (initial := initial) (mid := mid)
        (trace := trace) (pc := pc) (instr := instr)
        (emitted := emitted) (before := before) (after := after)
        (reference := reference)
        hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock
        hRun hChecks⟩

theorem openXRunListHaltedAllOutcomeTracksReady_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {reference : EVMResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hReference : OpenXResultAgrees (.halted halt) reference)
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.halted halt)) :
    OpenXRunListHaltedAllOutcomeTracksReady targetProgram initial
      ((emitted.map Assembly.LocatedTarget.instr).length + 1)
      reference := by
  intro full candidateTrace candidateOutcome hRel hOutcome
  obtain ⟨_hTrace, hClosedRun⟩ :=
    openRunListResult_emitInstr_no_call_inv hNoInstr hEmit hRun
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hDecodePath :
      Assembly.GasAware.XStepTrace.XRunListPathDecodeReady
        (emitted.map Assembly.LocatedTarget.instr) initial full
        (.halted halt) :=
    Assembly.GasAware.XStepTrace.XRunListPathDecodeReady.of_emitInstr
      hEncoding hSafety hAt hEmit hTargetBlock hClosedRun hRel hCode
  have hAll :=
    openX_runListResult_halted_all_outcomes_safelyTracks_of_path_decode_checks
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (code := emitted.map Assembly.LocatedTarget.instr)
      (target := initial) (full := full) (halt := halt)
      (reference := reference)
      hDecodePath (hChecks hRel) hReference
  exact hAll candidateTrace candidateOutcome hOutcome

theorem runListHaltedAllOutcomeTracksReadyFor_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {reference : EVMResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hReference : OpenXResultAgrees (.halted halt) reference)
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.halted halt)) :
    RunListHaltedAllOutcomeTracksReadyFor targetProgram initial
      reference :=
  ⟨(emitted.map Assembly.LocatedTarget.instr).length + 1,
    openXRunListHaltedAllOutcomeTracksReady_current_emitted_no_call_of_current_path_checks
      (program := program) (targetProgram := targetProgram)
      (initial := initial) (trace := trace) (halt := halt)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      (reference := reference)
      hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock
      hRun hReference hChecks⟩

theorem runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram) :
    RunListRunningTraceObservationOrFailureExistsReadyFor targetProgram
      initial mid :=
  runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_current_path_checks
    hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock hRun
    (fun hRel => hChecks hAt hEmit hTargetBlock hNoInstr
      (by
        obtain ⟨_hTrace, hClosedRun⟩ :=
          openRunListResult_emitInstr_no_call_inv
            hNoInstr hEmit hRun
        exact hClosedRun)
      hRel)

theorem runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel tailGasBound : Nat}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.running mid)) :
    ∃ evmFuel gasBound,
      OpenXRunListRunningRelReady targetProgram initial mid trace
        evmFuel tailFuel gasBound tailGasBound ∧
      OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
        initial mid evmFuel tailFuel := by
  refine
    ⟨tailFuel + (emitted.map Assembly.LocatedTarget.instr).length,
      Assembly.GasAware.XStepTrace.XRunListGasBudget
        (emitted.map Assembly.LocatedTarget.instr) initial +
        tailGasBound,
      ?_, ?_⟩
  · exact
      openXRunListRunningRelReady_current_emitted_no_call_of_current_path_checks_and_budget
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (tailGasBound := tailGasBound)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock
        hRun hChecks
  · exact
      openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_no_call_of_current_path_checks
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (initial := initial) (mid := mid)
        (trace := trace) (pc := pc) (instr := instr)
        (emitted := emitted) (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock
        hRun hChecks

theorem runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel tailGasBound : Nat}
    {initial mid : EVMState} {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram) :
    ∃ evmFuel gasBound,
      OpenXRunListRunningRelReady targetProgram initial mid trace
        evmFuel tailFuel gasBound tailGasBound ∧
      OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
        initial mid evmFuel tailFuel :=
  runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_current_path_checks
    hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock hRun
    (fun hRel => hChecks hAt hEmit hTargetBlock hNoInstr
      (by
        obtain ⟨_hTrace, hClosedRun⟩ :=
          openRunListResult_emitInstr_no_call_inv
            hNoInstr hEmit hRun
        exact hClosedRun)
      hRel)

theorem openXRunListHaltedTraceObservationOrFailureExistsReady_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.halted halt)) :
    OpenXRunListHaltedTraceObservationOrFailureExistsReady targetProgram
      initial halt ((emitted.map Assembly.LocatedTarget.instr).length + 1) := by
  intro full hRel
  obtain ⟨_hTrace, hClosedRun⟩ :=
    openRunListResult_emitInstr_no_call_inv hNoInstr hEmit hRun
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hDecodePath :
      Assembly.GasAware.XStepTrace.XRunListPathDecodeReady
        (emitted.map Assembly.LocatedTarget.instr) initial full
        (.halted halt) :=
    Assembly.GasAware.XStepTrace.XRunListPathDecodeReady.of_emitInstr
      hEncoding hSafety hAt hEmit hTargetBlock hClosedRun hRel hCode
  exact
    openX_runListResult_halted_traceObservationOrFailure_exists_of_path_decode_checks
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (code := emitted.map Assembly.LocatedTarget.instr)
      (target := initial) (full := full) (halt := halt)
      hDecodePath (hChecks hRel)

theorem runListHaltedTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.halted halt)) :
    RunListHaltedTraceObservationOrFailureExistsReadyFor targetProgram
      initial halt :=
  ⟨(emitted.map Assembly.LocatedTarget.instr).length + 1,
    openXRunListHaltedTraceObservationOrFailureExistsReady_current_emitted_no_call_of_current_path_checks
      (program := program) (targetProgram := targetProgram)
      (initial := initial) (trace := trace) (halt := halt)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock hRun
      hChecks⟩

theorem runListHaltedTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram) :
    RunListHaltedTraceObservationOrFailureExistsReadyFor targetProgram
      initial halt :=
  runListHaltedTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_current_path_checks
    hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock hRun
    (fun hRel => hChecks hAt hEmit hTargetBlock hNoInstr
      (by
        obtain ⟨_hTrace, hClosedRun⟩ :=
          openRunListResult_emitInstr_no_call_inv
            hNoInstr hEmit hRun
        exact hClosedRun)
      hRel)

theorem openXRunListHaltedRelReady_current_emitted_no_call_of_current_path_checks_and_budget
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.halted halt)) :
    OpenXRunListHaltedRelReady targetProgram initial trace halt
      ((emitted.map Assembly.LocatedTarget.instr).length + 1)
      (Assembly.GasAware.XStepTrace.XRunListGasBudget
        (emitted.map Assembly.LocatedTarget.instr) initial) := by
  obtain ⟨hTrace, hClosedRun⟩ :=
    openRunListResult_emitInstr_no_call_inv
      hNoInstr hEmit hRun
  subst trace
  let code := emitted.map Assembly.LocatedTarget.instr
  intro full hGasBound hRel
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    rw [Assembly.GasAware.GasExecRel.executionEnv_eq hRel]
    exact hInitialCode
  have hChecksCode :
      Assembly.GasAware.XStepTrace.XRunListPathChecksReady
        (Assembly.GasAware.validJumps targetProgram) code initial full
        (.halted halt) := by
    dsimp [code]
    exact hChecks hRel
  have hNoCallCode :
      ∀ targetInstr ∈ code,
        Assembly.GasAware.targetInstrUsesCallCreate targetInstr = false := by
    intro targetInstr hMem
    dsimp [code] at hMem
    rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
    subst targetInstr
    exact Assembly.GasAware.targetInstr_usesCallCreate_false_of_emitInstr_mem
      hNoInstr hEmit hLocatedMem
  have hPath :
      Assembly.GasAware.XStepTrace.XRunListPathReady
        (Assembly.GasAware.validJumps targetProgram) code initial full
        (.halted halt) :=
    Assembly.GasAware.XStepTrace.XRunListPathReady.of_emitInstr_checks_and_budget
      (program := program) (target := targetProgram)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (blockState := initial) (fullState := full)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      (blockResult := .halted halt)
      hEncoding hSafety hAt hEmit hTargetBlock
      (by simpa [code] using hClosedRun)
      hRel hCode (by simpa [code] using hChecksCode)
      (by simpa [code] using hNoCallCode) hGasBound
  obtain ⟨result, hTraceRun, hAgree⟩ :=
    openX_runListResult_with_positive_path_continuation_agrees_of_path_ready
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (code := code) (target := initial) (full := full)
      (blockResult := .halted halt)
      (finalResult := .halted halt)
      (tailFuel := 0)
      hPath
      (fun halt' hEq => by cases hEq; rfl)
      (fun targetFinal fullFinal hEq _hRelFinal => by
        cases hEq)
  refine ⟨result, ?_, hAgree⟩
  simpa [code, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hTraceRun

theorem runListHaltedReadyFor_current_emitted_no_call_of_current_path_checks_and_budget
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepTrace.XRunListPathChecksReady
            (Assembly.GasAware.validJumps targetProgram)
            (emitted.map Assembly.LocatedTarget.instr) initial full
            (.halted halt)) :
    RunListHaltedReadyFor targetProgram initial trace halt :=
  ⟨(emitted.map Assembly.LocatedTarget.instr).length + 1,
    Assembly.GasAware.XStepTrace.XRunListGasBudget
      (emitted.map Assembly.LocatedTarget.instr) initial,
    openXRunListHaltedRelReady_current_emitted_no_call_of_current_path_checks_and_budget
      (program := program) (targetProgram := targetProgram)
      (initial := initial) (trace := trace) (halt := halt)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock hRun
      hChecks⟩

theorem runListHaltedReadyFor_current_emitted_no_call_of_path_checks_and_budget
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState} {trace : OpenExternal.OpenTrace}
    {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram) :
    RunListHaltedReadyFor targetProgram initial trace halt :=
  runListHaltedReadyFor_current_emitted_no_call_of_current_path_checks_and_budget
    hEncoding hSafety hInitialCode hNoInstr hAt hEmit hTargetBlock hRun
    (fun hRel => hChecks hAt hEmit hTargetBlock hNoInstr
      (by
        obtain ⟨_hTrace, hClosedRun⟩ :=
          openRunListResult_emitInstr_no_call_inv
            hNoInstr hEmit hRun
        exact hClosedRun)
      hRel)

theorem runListRunningReadyFor_current_emitted_prim_call_of_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {gasBound : Nat} {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hPostBudget :
      ∀ {tailGasBound : Nat},
        ∃ gasBound : Nat,
          ∀ {full gasPost : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.GasExecRel gasPost
                  (EvmYul.EVM.State.incrPC
                    (call.resume response)) →
                  tailGasBound ≤ gasPost.gasAvailable.toNat) :
    RunListRunningReadyFor targetProgram initial
      (EvmYul.EVM.State.incrPC (call.resume response))
      [OpenExternal.OpenEvent.call call.site response] := by
  intro tailFuel tailGasBound
  obtain ⟨gasBound, hPostBudget'⟩ :=
    hPostBudget (tailGasBound := tailGasBound)
  exact
    ⟨tailFuel + 1, gasBound,
      openXRunListRunningRelReady_current_emitted_prim_call
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (gasBound := gasBound)
        (tailGasBound := tailGasBound)
        (initial := initial) (pc := pc) (op := op)
        (emitted := emitted) (before := before) (after := after)
        (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        (fun hGasBound hRel => hStepChecks hGasBound hRel)
        hKind hCall hPostBudget'⟩

theorem runListRunningReadyFor_current_emitted_prim_call_of_run_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hStepChecks :
      ∀ {gasBound : Nat} {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hPostBudget :
      ∀ {response : OpenExternal.CallResponse} {tailGasBound : Nat},
        ∃ gasBound : Nat,
          ∀ {full gasPost : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.GasExecRel gasPost
                  (EvmYul.EVM.State.incrPC
                    (call.resume response)) →
                  tailGasBound ≤ gasPost.gasAvailable.toNat) :
    RunListRunningReadyFor targetProgram initial mid trace := by
  obtain ⟨response, hTrace, hMid⟩ :=
    openRunListResult_emitInstr_prim_call_running_inv
      hEmit hKind hCall hRun
  subst trace
  subst mid
  exact
    runListRunningReadyFor_current_emitted_prim_call_of_step_checks
      (program := program) (targetProgram := targetProgram)
      (initial := initial) (pc := pc) (op := op)
      (emitted := emitted) (before := before) (after := after)
      (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        hStepChecks hKind hCall hPostBudget

theorem runListRunningTraceObservationOrFailureReadyFor_current_emitted_prim_call_of_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    RunListRunningTraceObservationOrFailureReadyFor targetProgram initial
      (EvmYul.EVM.State.incrPC (call.resume response))
      [OpenExternal.OpenEvent.call call.site response] := by
  intro tailFuel
  exact
    ⟨tailFuel + 1,
      openXRunListRunningTraceObservationOrFailureReady_current_emitted_prim_call_actual_post
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (initial := initial) (pc := pc) (op := op)
        (emitted := emitted) (before := before) (after := after)
        (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        hStepChecks hKind hCall⟩

theorem runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    RunListRunningTraceObservationOrFailureExistsReadyFor targetProgram
      initial (EvmYul.EVM.State.incrPC (call.resume response)) := by
  intro tailFuel
  exact
    ⟨tailFuel + 1,
      openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_prim_call_actual_post
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (initial := initial) (pc := pc) (op := op)
        (emitted := emitted) (before := before) (after := after)
        (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        hStepChecks hKind hCall⟩

theorem runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_nonGas
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hNonGas :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XNonGasChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    RunListRunningTraceObservationOrFailureExistsReadyFor targetProgram
      initial (EvmYul.EVM.State.incrPC (call.resume response)) := by
  intro tailFuel
  exact
    ⟨tailFuel + 1,
      openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_prim_call_of_nonGas_actual_post
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (initial := initial) (pc := pc) (op := op)
        (emitted := emitted) (before := before) (after := after)
        (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        hNonGas hKind hCall⟩

theorem runListRunningTraceObservationOrFailureReadyFor_current_emitted_prim_call_of_run_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hStepChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    RunListRunningTraceObservationOrFailureReadyFor targetProgram initial
      mid trace := by
  obtain ⟨response, hTrace, hMid⟩ :=
    openRunListResult_emitInstr_prim_call_running_inv
      hEmit hKind hCall hRun
  subst trace
  subst mid
  exact
    runListRunningTraceObservationOrFailureReadyFor_current_emitted_prim_call_of_step_checks
      (program := program) (targetProgram := targetProgram)
      (initial := initial) (pc := pc) (op := op)
      (emitted := emitted) (before := before) (after := after)
      (kind := kind) (call := call) (response := response)
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
      hStepChecks hKind hCall

theorem runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_run_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hStepChecks :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XStepChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    RunListRunningTraceObservationOrFailureExistsReadyFor targetProgram
      initial mid := by
  obtain ⟨response, hTrace, hMid⟩ :=
    openRunListResult_emitInstr_prim_call_running_inv
      hEmit hKind hCall hRun
  subst trace
  subst mid
  exact
    runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_step_checks
      (program := program) (targetProgram := targetProgram)
      (initial := initial) (pc := pc) (op := op)
      (emitted := emitted) (before := before) (after := after)
      (kind := kind) (call := call) (response := response)
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
      hStepChecks hKind hCall

theorem runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_run_nonGas
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hNonGas :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XNonGasChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    RunListRunningTraceObservationOrFailureExistsReadyFor targetProgram
      initial mid := by
  obtain ⟨response, hTrace, hMid⟩ :=
    openRunListResult_emitInstr_prim_call_running_inv
      hEmit hKind hCall hRun
  subst trace
  subst mid
  exact
    runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_nonGas
      (program := program) (targetProgram := targetProgram)
      (initial := initial) (pc := pc) (op := op)
      (emitted := emitted) (before := before) (after := after)
      (kind := kind) (call := call) (response := response)
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
      hNonGas hKind hCall

theorem runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_run_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel tailGasBound : Nat}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hStepChecks :
      ∀ {gasBound : Nat} {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hPostBudget :
      ∀ {response : OpenExternal.CallResponse} {tailGasBound : Nat},
        ∃ gasBound : Nat,
          ∀ {full gasPost : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.GasExecRel gasPost
                  (EvmYul.EVM.State.incrPC
                    (call.resume response)) →
                  tailGasBound ≤ gasPost.gasAvailable.toNat) :
    ∃ evmFuel gasBound,
      OpenXRunListRunningRelReady targetProgram initial mid trace
        evmFuel tailFuel gasBound tailGasBound ∧
      OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
        initial mid evmFuel tailFuel := by
  obtain ⟨response, hTrace, hMid⟩ :=
    openRunListResult_emitInstr_prim_call_running_inv
      hEmit hKind hCall hRun
  subst trace
  subst mid
  obtain ⟨gasBound, hPostBudget'⟩ :=
    hPostBudget (response := response) (tailGasBound := tailGasBound)
  refine ⟨tailFuel + 1, gasBound, ?_, ?_⟩
  · exact
      openXRunListRunningRelReady_current_emitted_prim_call
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (gasBound := gasBound)
        (tailGasBound := tailGasBound)
        (initial := initial) (pc := pc) (op := op)
        (emitted := emitted) (before := before) (after := after)
        (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        (fun hGasBound hRel => hStepChecks hGasBound hRel)
        hKind hCall hPostBudget'
  · exact
      openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_prim_call_actual_post
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (initial := initial) (pc := pc) (op := op)
        (emitted := emitted) (before := before) (after := after)
        (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        (fun hRel => hStepChecks (gasBound := 0) (by exact Nat.zero_le _) hRel)
        hKind hCall

theorem runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_run_budget_and_nonGas
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel tailGasBound : Nat}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hBudget :
      ∀ {response : OpenExternal.CallResponse} {tailGasBound : Nat},
        ∃ gasBound : Nat,
          (∀ {full : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.XStepChecksPass
                  (Assembly.GasAware.validJumps targetProgram)
                  full op.toEVM) ∧
          (∀ {full gasPost : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.GasExecRel gasPost
                  (EvmYul.EVM.State.incrPC
                    (call.resume response)) →
                  tailGasBound ≤ gasPost.gasAvailable.toNat))
    (hNonGas :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XNonGasChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call) :
    ∃ evmFuel gasBound,
      OpenXRunListRunningRelReady targetProgram initial mid trace
        evmFuel tailFuel gasBound tailGasBound ∧
      OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
        initial mid evmFuel tailFuel := by
  obtain ⟨response, hTrace, hMid⟩ :=
    openRunListResult_emitInstr_prim_call_running_inv
      hEmit hKind hCall hRun
  subst trace
  subst mid
  obtain ⟨gasBound, hStepChecks, hPostBudget⟩ :=
    hBudget (response := response) (tailGasBound := tailGasBound)
  refine ⟨tailFuel + 1, gasBound, ?_, ?_⟩
  · exact
      openXRunListRunningRelReady_current_emitted_prim_call
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (gasBound := gasBound)
        (tailGasBound := tailGasBound)
        (initial := initial) (pc := pc) (op := op)
        (emitted := emitted) (before := before) (after := after)
        (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        hStepChecks hKind hCall hPostBudget
  · exact
      openXRunListRunningTraceObservationOrFailureExistsReady_current_emitted_prim_call_of_nonGas_actual_post
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (initial := initial) (pc := pc) (op := op)
        (emitted := emitted) (before := before) (after := after)
        (kind := kind) (call := call) (response := response)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock
        hNonGas hKind hCall

theorem openRunListResult_emitInstr_prim_call_running_preserves_code_of_trace_response_stable
    {program : Assembly.Program}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hStable :
      ∀ {response : OpenExternal.CallResponse},
        OpenExternal.OpenEvent.call call.site response ∈ trace →
          (call.resume response).executionEnv.code =
            initial.executionEnv.code) :
    mid.executionEnv.code = initial.executionEnv.code := by
  obtain ⟨response, hTrace, hMid⟩ :=
    openRunListResult_emitInstr_prim_call_running_inv
      hEmit hKind hCall hRun
  subst trace
  subst mid
  simpa [EvmYul.EVM.State.incrPC] using
    hStable (response := response) (by simp)

theorem runListRunningReadyFor_current_emitted_prim_call_of_run_step_checks_and_trace_response_stable
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hStepChecks :
      ∀ {gasBound : Nat} {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hPostBudget :
      ∀ {response : OpenExternal.CallResponse} {tailGasBound : Nat},
        ∃ gasBound : Nat,
          ∀ {full gasPost : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.GasExecRel gasPost
                  (EvmYul.EVM.State.incrPC
                    (call.resume response)) →
                  tailGasBound ≤ gasPost.gasAvailable.toNat)
    (hStable :
      ∀ {response : OpenExternal.CallResponse},
        OpenExternal.OpenEvent.call call.site response ∈ trace →
          (call.resume response).executionEnv.code =
            initial.executionEnv.code) :
    RunListRunningReadyFor targetProgram initial mid trace ∧
      mid.executionEnv.code = initial.executionEnv.code :=
  ⟨runListRunningReadyFor_current_emitted_prim_call_of_run_step_checks
      hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRun hStepChecks
      hKind hCall hPostBudget,
    openRunListResult_emitInstr_prim_call_running_preserves_code_of_trace_response_stable
      hEmit hRun hKind hCall hStable⟩

def CurrentRunningInstrReadyCase
    (targetProgram : Assembly.TargetProgram)
    (state : EVMState) (instr : Assembly.Instr) : Prop :=
  Assembly.Instr.usesCallCreate instr = false ∨
    ∃ op : Assembly.PrimOp,
      ∃ kind : OpenExternal.CallKind,
        ∃ call : OpenExternal.OpenCall EVMState,
          instr = .prim op ∧
            OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind ∧
              OpenExternal.CallKind.evmOpenCall? state kind = some call ∧
                (∀ {gasBound : Nat} {full : EVMState},
                  gasBound ≤ full.gasAvailable.toNat →
                    Assembly.GasAware.GasExecRel full state →
                      Assembly.GasAware.XStepChecksPass
                        (Assembly.GasAware.validJumps targetProgram)
                        full op.toEVM) ∧
                  (∀ response : OpenExternal.CallResponse,
                    (call.resume response).executionEnv.code =
                      state.executionEnv.code) ∧
                  (∀ {response : OpenExternal.CallResponse}
                      {tailGasBound : Nat},
                    ∃ gasBound : Nat,
                      ∀ {full gasPost : EVMState},
                        gasBound ≤ full.gasAvailable.toNat →
                          Assembly.GasAware.GasExecRel full state →
                            Assembly.GasAware.GasExecRel gasPost
                              (EvmYul.EVM.State.incrPC
                                (call.resume response)) →
                              tailGasBound ≤
                                gasPost.gasAvailable.toNat)

def CurrentRunningInstrTraceReadyCase
    (targetProgram : Assembly.TargetProgram)
    (state : EVMState) (instr : Assembly.Instr)
    (trace : OpenExternal.OpenTrace) : Prop :=
  Assembly.Instr.usesCallCreate instr = false ∨
    ∃ op : Assembly.PrimOp,
      ∃ kind : OpenExternal.CallKind,
        ∃ call : OpenExternal.OpenCall EVMState,
          instr = .prim op ∧
            OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind ∧
              OpenExternal.CallKind.evmOpenCall? state kind = some call ∧
                (∀ {gasBound : Nat} {full : EVMState},
                  gasBound ≤ full.gasAvailable.toNat →
                    Assembly.GasAware.GasExecRel full state →
                      Assembly.GasAware.XStepChecksPass
                        (Assembly.GasAware.validJumps targetProgram)
                        full op.toEVM) ∧
                  (∀ {response : OpenExternal.CallResponse},
                    OpenExternal.OpenEvent.call call.site response ∈ trace →
                      (call.resume response).executionEnv.code =
                        state.executionEnv.code) ∧
                  (∀ {response : OpenExternal.CallResponse}
                      {tailGasBound : Nat},
                    ∃ gasBound : Nat,
                      ∀ {full gasPost : EVMState},
                        gasBound ≤ full.gasAvailable.toNat →
                          Assembly.GasAware.GasExecRel full state →
                            Assembly.GasAware.GasExecRel gasPost
                              (EvmYul.EVM.State.incrPC
                                (call.resume response)) →
                              tailGasBound ≤
                                gasPost.gasAvailable.toNat)

namespace CurrentRunningInstrReadyCase

theorem to_trace_ready_case
    {targetProgram : Assembly.TargetProgram}
    {state : EVMState} {instr : Assembly.Instr}
    {trace : OpenExternal.OpenTrace}
    (hReady :
      CurrentRunningInstrReadyCase targetProgram state instr) :
    CurrentRunningInstrTraceReadyCase targetProgram state instr trace := by
  rcases hReady with hNoCall | hCall
  · exact Or.inl hNoCall
  · rcases hCall with
      ⟨op, kind, call, hInstr, hKind, hCall, hStepChecks,
        hCodeStable, hPostBudget⟩
    exact
      Or.inr
        ⟨op, kind, call, hInstr, hKind, hCall, hStepChecks,
          (fun {response} _hMem => hCodeStable response), hPostBudget⟩

theorem not_create_like
    {targetProgram : Assembly.TargetProgram}
    {state : EVMState} {op : Assembly.PrimOp}
    (hReady :
      CurrentRunningInstrReadyCase targetProgram state (.prim op))
    (hUses : op.isCallCreate = true)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = none) :
    False := by
  rcases hReady with hNoCall | hCall
  · simp [Assembly.Instr.usesCallCreate, hUses] at hNoCall
  · rcases hCall with
      ⟨op', kind, call, hInstr, hKindSome, _hCall, _hStepChecks,
        _hCodeStable, _hPostBudget⟩
    cases hInstr
    rw [hKind] at hKindSome
    cases hKindSome

end CurrentRunningInstrReadyCase

namespace CurrentRunningInstrTraceReadyCase

theorem not_create_like
    {targetProgram : Assembly.TargetProgram}
    {state : EVMState} {op : Assembly.PrimOp}
    {trace : OpenExternal.OpenTrace}
    (hReady :
      CurrentRunningInstrTraceReadyCase targetProgram state (.prim op) trace)
    (hUses : op.isCallCreate = true)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = none) :
    False := by
  rcases hReady with hNoCall | hCall
  · simp [Assembly.Instr.usesCallCreate, hUses] at hNoCall
  · rcases hCall with
      ⟨op', kind, call, hInstr, hKindSome, _hCall, _hStepChecks,
        _hCodeStable, _hPostBudget⟩
    cases hInstr
    rw [hKind] at hKindSome
    cases hKindSome

end CurrentRunningInstrTraceReadyCase

theorem openRunListResult_current_emitted_running_preserves_code_of_trace_ready_case
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (_hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hReady :
      CurrentRunningInstrTraceReadyCase targetProgram initial instr trace) :
    mid.executionEnv.code = initial.executionEnv.code := by
  rcases hReady with hNoCall | hCall
  · obtain ⟨_hTrace, hClosedRun⟩ :=
      openRunListResult_emitInstr_no_call_inv
        hNoCall hEmit hRun
    have hNoCallTargets :
        ∀ targetInstr ∈ emitted.map Assembly.LocatedTarget.instr,
          Assembly.GasAware.targetInstrUsesCallCreate targetInstr = false := by
      intro targetInstr hMem
      rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
      subst targetInstr
      exact
        Assembly.GasAware.targetInstr_usesCallCreate_false_of_emitInstr_mem
          hNoCall hEmit hLocatedMem
    exact
      Assembly.GasAware.XStepTrace.Target.runListResult_preserves_code_of_no_call_create
        hClosedRun hNoCallTargets
  · rcases hCall with
      ⟨op, kind, call, hInstr, hKind, hCall, _hStepChecks, hCodeStable,
        _hPostBudget⟩
    subst instr
    exact
      openRunListResult_emitInstr_prim_call_running_preserves_code_of_trace_response_stable
        hEmit hRun hKind hCall hCodeStable

theorem runListRunningReadyFor_current_emitted_of_trace_ready_case_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hNoCallChecks :
      Assembly.Instr.usesCallCreate instr = false →
        ∀ {full : EVMState},
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepTrace.XRunListPathChecksReady
              (Assembly.GasAware.validJumps targetProgram)
              (emitted.map Assembly.LocatedTarget.instr) initial full
              (.running mid))
    (hReady :
      CurrentRunningInstrTraceReadyCase targetProgram initial instr trace) :
    RunListRunningReadyFor targetProgram initial mid trace ∧
      mid.executionEnv.code = initial.executionEnv.code := by
  rcases hReady with hNoCall | hCall
  · exact
      ⟨runListRunningReadyFor_current_emitted_no_call_of_current_path_checks_and_budget
          (program := program) (targetProgram := targetProgram)
          (initial := initial) (mid := mid) (trace := trace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hEncoding hSafety hInitialCode hNoCall hAt hEmit hTargetBlock hRun
          (hNoCallChecks hNoCall),
        openRunListResult_current_emitted_running_preserves_code_of_trace_ready_case
          hEmit hTargetBlock hRun (Or.inl hNoCall)⟩
  · rcases hCall with
      ⟨op, kind, call, hInstr, hKind, hCall, hStepChecks, hCodeStable,
        hPostBudget⟩
    subst instr
    exact
      runListRunningReadyFor_current_emitted_prim_call_of_run_step_checks_and_trace_response_stable
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (op := op) (emitted := emitted)
        (before := before) (after := after)
        (kind := kind) (call := call)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRun
        hStepChecks hKind hCall hPostBudget hCodeStable

theorem openRunListResult_current_emitted_running_preserves_code_of_ready_case
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (_hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hReady :
      CurrentRunningInstrReadyCase targetProgram initial instr) :
    mid.executionEnv.code = Assembly.Bytecode.encodeTarget targetProgram := by
  rcases hReady with hNoCall | hCall
  · obtain ⟨_hTrace, hClosedRun⟩ :=
      openRunListResult_emitInstr_no_call_inv
        hNoCall hEmit hRun
    have hNoCallTargets :
        ∀ targetInstr ∈ emitted.map Assembly.LocatedTarget.instr,
          Assembly.GasAware.targetInstrUsesCallCreate targetInstr = false := by
      intro targetInstr hMem
      rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
      subst targetInstr
      exact
        Assembly.GasAware.targetInstr_usesCallCreate_false_of_emitInstr_mem
          hNoCall hEmit hLocatedMem
    have hCode :=
      Assembly.GasAware.XStepTrace.Target.runListResult_preserves_code_of_no_call_create
        hClosedRun hNoCallTargets
    simpa [hInitialCode] using hCode
  · rcases hCall with
      ⟨op, kind, call, hInstr, hKind, hCall, _hStepChecks,
        hCodeStable, _hPostBudget⟩
    subst instr
    obtain ⟨response, _hTrace, hMid⟩ :=
      openRunListResult_emitInstr_prim_call_running_inv
        hEmit hKind hCall hRun
    subst mid
    simpa [EvmYul.EVM.State.incrPC, hCodeStable response,
      hInitialCode]

theorem openBlockTrace_result_running_preserves_code_of_current_emitted_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {initial final : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        initial trace targetResult)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hResult : targetResult = .running final) :
    final.executionEnv.code =
      Assembly.Bytecode.encodeTarget targetProgram := by
  induction targetFuel generalizing initial trace targetResult final with
  | zero =>
      cases hTrace
      cases hResult
      simpa using hInitialCode
  | succ fuel ih =>
      cases hTrace with
      | stepRunning hAt hEmit hTargetBlock hRun hRest =>
          rename_i mid currentTrace tailTrace pc instr emitted before after
          have hMidCode :
              mid.executionEnv.code =
                Assembly.Bytecode.encodeTarget targetProgram :=
            openRunListResult_current_emitted_running_preserves_code_of_ready_case
              hInitialCode hEmit hTargetBlock hRun
              (hReady hAt hEmit hTargetBlock hRun)
          exact ih hRest hMidCode hResult
      | stepHalted hAt hEmit hTargetBlock hRun =>
          cases hResult

theorem openBlockTrace_running_preserves_code_of_current_emitted_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {initial final : EVMState}
    {trace : OpenExternal.OpenTrace}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        initial trace (.running final))
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr) :
    final.executionEnv.code =
      Assembly.Bytecode.encodeTarget targetProgram :=
  openBlockTrace_result_running_preserves_code_of_current_emitted_ready_cases_of_initial_code
    hTrace hInitialCode hReady rfl

theorem finalCleanReady_of_openBlockTrace_running_fallthrough
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {initial final : EVMState}
    {trace : OpenExternal.OpenTrace}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        initial trace (.running final))
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hPc :
      final.pc.toNat =
        Assembly.Bytecode.codeByteLength targetProgram.code)
    (hStack : final.stack.length ≤ 1024)
    (hClean :
      Assembly.GasAware.XStepTrace.ReturnBuffersClean final) :
    Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady final := by
  have hFinalCode :
      final.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram :=
    openBlockTrace_running_preserves_code_of_current_emitted_ready_cases_of_initial_code
      hTrace hInitialCode hReady
  exact
    Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady.of_observation_stack
      (Assembly.GasAware.XStepTrace.XFallthroughStopObservationReady.of_pc_code_cleanReturn
        hFinalCode hPc hClean)
      hStack

theorem runListRunningReadyFor_current_emitted_of_ready_case
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      CurrentRunningInstrReadyCase targetProgram initial instr) :
    RunListRunningReadyFor targetProgram initial mid trace := by
  rcases hReady with hNoCall | hCall
  · exact
      runListRunningReadyFor_current_emitted_no_call_of_path_checks_and_budget
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoCall hAt hEmit
        hTargetBlock hRun hChecks
  · rcases hCall with
      ⟨op, kind, call, hInstr, hKind, hCall, hStepChecks,
        _hCodeStable, hPostBudget⟩
    subst instr
    exact
      runListRunningReadyFor_current_emitted_prim_call_of_run_step_checks
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (op := op) (emitted := emitted)
        (before := before) (after := after)
        (kind := kind) (call := call)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRun
        hStepChecks hKind hCall hPostBudget

theorem runListRunningReadyFor_current_emitted_of_ready_case_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hNoCallChecks :
      Assembly.Instr.usesCallCreate instr = false →
        ∀ {full : EVMState},
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepTrace.XRunListPathChecksReady
              (Assembly.GasAware.validJumps targetProgram)
              (emitted.map Assembly.LocatedTarget.instr) initial full
              (.running mid))
    (hReady :
      CurrentRunningInstrReadyCase targetProgram initial instr) :
    RunListRunningReadyFor targetProgram initial mid trace := by
  rcases hReady with hNoCall | hCall
  · exact
      runListRunningReadyFor_current_emitted_no_call_of_current_path_checks_and_budget
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoCall hAt hEmit
        hTargetBlock hRun (hNoCallChecks hNoCall)
  · rcases hCall with
      ⟨op, kind, call, hInstr, hKind, hCall, hStepChecks,
        _hCodeStable, hPostBudget⟩
    subst instr
    exact
      runListRunningReadyFor_current_emitted_prim_call_of_run_step_checks
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (op := op) (emitted := emitted)
        (before := before) (after := after)
        (kind := kind) (call := call)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRun
        hStepChecks hKind hCall hPostBudget

theorem runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_of_ready_case_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hNoCallChecks :
      Assembly.Instr.usesCallCreate instr = false →
        ∀ {full : EVMState},
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepTrace.XRunListPathChecksReady
              (Assembly.GasAware.validJumps targetProgram)
              (emitted.map Assembly.LocatedTarget.instr) initial full
              (.running mid))
    (hReady :
      CurrentRunningInstrReadyCase targetProgram initial instr) :
    RunListRunningTraceObservationOrFailureExistsReadyFor targetProgram
      initial mid := by
  rcases hReady with hNoCall | hCall
  · exact
      runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_current_path_checks
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoCall hAt hEmit
        hTargetBlock hRun (hNoCallChecks hNoCall)
  · rcases hCall with
      ⟨op, kind, call, hInstr, hKind, hCall, hStepChecks,
        _hCodeStable, _hPostBudget⟩
    subst instr
    exact
      runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_run_step_checks
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (op := op) (emitted := emitted)
        (before := before) (after := after)
        (kind := kind) (call := call)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRun
        (fun hRel =>
          hStepChecks (gasBound := 0) (by exact Nat.zero_le _) hRel)
        hKind hCall

theorem runListHaltedReadyFor_current_emitted_of_no_call_case
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoCall : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram) :
    RunListHaltedReadyFor targetProgram initial trace halt :=
  runListHaltedReadyFor_current_emitted_no_call_of_path_checks_and_budget
    (program := program) (targetProgram := targetProgram)
    (initial := initial) (trace := trace) (halt := halt)
    (pc := pc) (instr := instr) (emitted := emitted)
    (before := before) (after := after)
    hEncoding hSafety hInitialCode hNoCall hAt hEmit hTargetBlock hRun
    hChecks

theorem runListHaltedTraceObservationOrFailureExistsReadyFor_current_emitted_of_no_call_case
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoCall : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram) :
    RunListHaltedTraceObservationOrFailureExistsReadyFor targetProgram
      initial halt :=
  runListHaltedTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_path_checks
    (program := program) (targetProgram := targetProgram)
    (initial := initial) (trace := trace) (halt := halt)
    (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
    hEncoding hSafety hInitialCode hNoCall hAt hEmit hTargetBlock hRun
    hChecks

theorem runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_of_ready_case_current_path_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel tailGasBound : Nat}
    {initial mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.running mid)))
    (hNoCallChecks :
      Assembly.Instr.usesCallCreate instr = false →
        ∀ {full : EVMState},
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepTrace.XRunListPathChecksReady
              (Assembly.GasAware.validJumps targetProgram)
              (emitted.map Assembly.LocatedTarget.instr) initial full
              (.running mid))
    (hReady :
      CurrentRunningInstrReadyCase targetProgram initial instr) :
    ∃ evmFuel gasBound,
      OpenXRunListRunningRelReady targetProgram initial mid trace
        evmFuel tailFuel gasBound tailGasBound ∧
      OpenXRunListRunningTraceObservationOrFailureExistsReady targetProgram
        initial mid evmFuel tailFuel := by
  rcases hReady with hNoCall | hCall
  · exact
      runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_no_call_of_current_path_checks
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (tailGasBound := tailGasBound)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoCall hAt hEmit
        hTargetBlock hRun (hNoCallChecks hNoCall)
  · rcases hCall with
      ⟨op, kind, call, hInstr, hKind, hCall, hStepChecks,
        _hCodeStable, hPostBudget⟩
    subst instr
    exact
      runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_prim_call_of_run_step_checks
        (program := program) (targetProgram := targetProgram)
        (tailFuel := tailFuel) (tailGasBound := tailGasBound)
        (initial := initial) (mid := mid) (trace := trace)
        (pc := pc) (op := op) (emitted := emitted)
        (before := before) (after := after)
        (kind := kind) (call := call)
        hEncoding hSafety hInitialCode hAt hEmit hTargetBlock hRun
        hStepChecks hKind hCall hPostBudget

theorem runListHaltedReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_of_no_call_case
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hNoCall : Assembly.Instr.usesCallCreate instr = false)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, instr))
    (hEmit :
      Assembly.emitInstr? program pc instr =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Target.openRunListResult
          (emitted.map Assembly.LocatedTarget.instr) initial)
        trace (.ok (.halted halt)))
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram) :
    ∃ evmFuel gasBound,
      OpenXRunListHaltedRelReady targetProgram initial trace halt
        evmFuel gasBound ∧
      OpenXRunListHaltedTraceObservationOrFailureExistsReady targetProgram
        initial halt evmFuel := by
  refine
    ⟨(emitted.map Assembly.LocatedTarget.instr).length + 1,
      Assembly.GasAware.XStepTrace.XRunListGasBudget
        (emitted.map Assembly.LocatedTarget.instr) initial,
      ?_, ?_⟩
  · exact
      openXRunListHaltedRelReady_current_emitted_no_call_of_current_path_checks_and_budget
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (trace := trace) (halt := halt)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoCall hAt hEmit hTargetBlock
        hRun
        (fun hRel => hChecks hAt hEmit hTargetBlock hNoCall
          (by
            obtain ⟨_hTrace, hClosedRun⟩ :=
              openRunListResult_emitInstr_no_call_inv
                hNoCall hEmit hRun
            exact hClosedRun)
          hRel)
  · exact
      openXRunListHaltedTraceObservationOrFailureExistsReady_current_emitted_no_call_of_current_path_checks
        (program := program) (targetProgram := targetProgram)
        (initial := initial) (trace := trace) (halt := halt)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety hInitialCode hNoCall hAt hEmit hTargetBlock hRun
        (fun hRel => hChecks hAt hEmit hTargetBlock hNoCall
          (by
            obtain ⟨_hTrace, hClosedRun⟩ :=
              openRunListResult_emitInstr_no_call_inv
                hNoCall hEmit hRun
            exact hClosedRun)
          hRel)

theorem runListRunningReadyFor_current_running_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {initial post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    (hDecode :
      ∀ {gasBound : Nat} {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {gasBound : Nat} {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {tailFuel gasBound : Nat} {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {tailFuel gasBound : Nat} {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.GasExecRel gasPost post ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost = none)
    (hPostBudget :
      ∀ {tailGasBound : Nat},
        ∃ gasBound : Nat,
          ∀ {full gasPost : EVMState},
            gasBound ≤ full.gasAvailable.toNat →
              Assembly.GasAware.GasExecRel full initial →
                Assembly.GasAware.GasExecRel gasPost post →
                  tailGasBound ≤ gasPost.gasAvailable.toNat) :
    RunListRunningReadyFor targetProgram initial post [] := by
  intro tailFuel tailGasBound
  obtain ⟨gasBound, hPostBudget'⟩ :=
    hPostBudget (tailGasBound := tailGasBound)
  exact
    ⟨tailFuel + 1, gasBound,
      openXRunListRunningRelReady_current_running
        (targetProgram := targetProgram)
        (tailFuel := tailFuel) (gasBound := gasBound)
        (tailGasBound := tailGasBound)
        (initial := initial) (post := post) (op := op) (arg := arg)
        (fun hGasBound hRel => hDecode hGasBound hRel)
        (fun hGasBound hRel => hStepChecks hGasBound hRel)
        (fun hGasBound hRel => hOpenStep hGasBound hRel)
        (fun hGasBound hRel => hStep hGasBound hRel)
        hPostBudget'⟩

theorem runListHaltedReadyFor_current_success_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {halt : Assembly.Halt}
    (hDecode :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost =
                some output ∧
              op ≠ EvmYul.Operation.REVERT ∧
              OpenXResultAgrees (.halted halt)
                (EvmYul.EVM.ExecutionResult.success gasPost output)) :
    RunListHaltedReadyFor targetProgram initial [] halt := by
  exact
    ⟨tailFuel + 1, gasBound,
      openXRunListHaltedRelReady_current_success
        (targetProgram := targetProgram)
        (tailFuel := tailFuel) (gasBound := gasBound)
        (initial := initial) (op := op) (arg := arg) (halt := halt)
        hDecode hStepChecks hOpenStep hStep⟩

theorem runListHaltedReadyFor_current_revert_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {halt : Assembly.Halt}
    (hDecode :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            EvmYul.EVM.decode full.executionEnv.code full.pc =
              some (op, arg))
    (hStepChecks :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram) full op)
    (hOpenStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            openStepAfterChecks tailFuel op arg full =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op)))
    (hStep :
      ∀ {full : EVMState},
        gasBound ≤ full.gasAvailable.toNat →
          Assembly.GasAware.GasExecRel full initial →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState full op) op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState full op) =
                .ok gasPost ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost =
                some output ∧
              op = EvmYul.Operation.REVERT ∧
              OpenXResultAgrees (.halted halt)
                (EvmYul.EVM.ExecutionResult.revert
                  gasPost.gasAvailable output)) :
    RunListHaltedReadyFor targetProgram initial [] halt := by
  exact
    ⟨tailFuel + 1, gasBound,
      openXRunListHaltedRelReady_current_revert
        (targetProgram := targetProgram)
        (tailFuel := tailFuel) (gasBound := gasBound)
        (initial := initial) (op := op) (arg := arg) (halt := halt)
        hDecode hStepChecks hOpenStep hStep⟩

theorem openXRunListRunningAllOutcomeTracksReady_current_running_of_nonGas_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {reference : EVMResult}
    (hDecode :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          EvmYul.EVM.decode full.executionEnv.code full.pc =
            some (op, arg))
    (hNonGas :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XNonGasChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op)
    (hStep :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          xStepException?
              (Assembly.GasAware.validJumps targetProgram) full op =
            none →
            ∃ gasPost : EVMState,
              openStepAfterChecks tailFuel op arg full =
                  .done (.ok gasPost) ∧
                Assembly.GasAware.GasExecRel gasPost post ∧
                  Assembly.GasAware.XStepHaltOutput? op gasPost = none) :
    OpenXRunListRunningAllOutcomeTracksReady targetProgram initial post
      (tailFuel + 1) tailFuel reference := by
  intro full candidateTrace candidateOutcome hRel hTail hOutcome
  exact
    openX_gasrel_current_running_all_outcomes_safelyTracks_of_nonGas_openStepAfterChecks_done
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (initial := initial) (post := post) (op := op) (arg := arg)
      (reference := reference)
      hDecode hNonGas hStep
      (fun gasPost hRelPost => hTail hRelPost)
      full hRel candidateTrace candidateOutcome hOutcome

theorem openXRunListHaltedAllOutcomeTracksReady_current_success_of_nonGas_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {halt : Assembly.Halt} {reference : EVMResult}
    (hReference : OpenXResultAgrees (.halted halt) reference)
    (hDecode :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          EvmYul.EVM.decode full.executionEnv.code full.pc =
            some (op, arg))
    (hNonGas :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XNonGasChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op)
    (hStep :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          xStepException?
              (Assembly.GasAware.validJumps targetProgram) full op =
            none →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              openStepAfterChecks tailFuel op arg full =
                  .done (.ok gasPost) ∧
                Assembly.GasAware.XStepHaltOutput? op gasPost =
                  some output ∧
                  op ≠ EvmYul.Operation.REVERT ∧
                    OpenXResultAgrees (.halted halt)
                      (EvmYul.EVM.ExecutionResult.success gasPost
                        output)) :
    OpenXRunListHaltedAllOutcomeTracksReady targetProgram initial
      (tailFuel + 1) reference := by
  intro full candidateTrace candidateOutcome hRel hOutcome
  rcases xStepException?_none_or_outOfGas_of_nonGas_checks
      (hNonGas hRel) with hException | hException
  · obtain ⟨gasPost, output, hOpenStep, hHalt, hNotRevert, hAgree⟩ :=
      hStep hRel hException
    exact
      Assembly.GasAware.XRunOutcomeSafelyTracks.retarget_ok
        (openX_current_success_all_outcomes_safelyTracks_of_openStepAfterChecks_done
          (fuel := tailFuel)
          (validJumps := Assembly.GasAware.validJumps targetProgram)
          (state := full) (post := gasPost) (op := op) (arg := arg)
          (trace := candidateTrace) (outcome := candidateOutcome)
          (output := output)
          (hDecode hRel) hException hOpenStep hHalt hNotRevert hOutcome)
        (hAgree.committedObservation.trans
          hReference.committedObservation.symm)
  · exact
      openX_current_outOfGas_exception_all_outcomes_safelyTracks
        (fuel := tailFuel)
        (validJumps := Assembly.GasAware.validJumps targetProgram)
        (state := full) (op := op) (arg := arg)
        (trace := candidateTrace) (outcome := candidateOutcome)
        (reference := reference)
        (hDecode hRel) hException hOutcome

theorem openXRunListHaltedAllOutcomeTracksReady_current_revert_of_nonGas_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {halt : Assembly.Halt} {reference : EVMResult}
    (hReference : OpenXResultAgrees (.halted halt) reference)
    (hDecode :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          EvmYul.EVM.decode full.executionEnv.code full.pc =
            some (op, arg))
    (hNonGas :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          Assembly.GasAware.XNonGasChecksPass
            (Assembly.GasAware.validJumps targetProgram) full op)
    (hStep :
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full initial →
          xStepException?
              (Assembly.GasAware.validJumps targetProgram) full op =
            none →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              openStepAfterChecks tailFuel op arg full =
                  .done (.ok gasPost) ∧
                Assembly.GasAware.XStepHaltOutput? op gasPost =
                  some output ∧
                  op = EvmYul.Operation.REVERT ∧
                    OpenXResultAgrees (.halted halt)
                      (EvmYul.EVM.ExecutionResult.revert
                        gasPost.gasAvailable output)) :
    OpenXRunListHaltedAllOutcomeTracksReady targetProgram initial
      (tailFuel + 1) reference := by
  intro full candidateTrace candidateOutcome hRel hOutcome
  rcases xStepException?_none_or_outOfGas_of_nonGas_checks
      (hNonGas hRel) with hException | hException
  · obtain ⟨gasPost, output, hOpenStep, hHalt, hRevert, hAgree⟩ :=
      hStep hRel hException
    exact
      Assembly.GasAware.XRunOutcomeSafelyTracks.retarget_ok
        (openX_current_revert_all_outcomes_safelyTracks_of_openStepAfterChecks_done
          (fuel := tailFuel)
          (validJumps := Assembly.GasAware.validJumps targetProgram)
          (state := full) (post := gasPost) (op := op) (arg := arg)
          (trace := candidateTrace) (outcome := candidateOutcome)
          (output := output)
          (hDecode hRel) hException hOpenStep hHalt hRevert hOutcome)
        (hAgree.committedObservation.trans
          hReference.committedObservation.symm)
  · exact
      openX_current_outOfGas_exception_all_outcomes_safelyTracks
        (fuel := tailFuel)
        (validJumps := Assembly.GasAware.validJumps targetProgram)
        (state := full) (op := op) (arg := arg)
        (trace := candidateTrace) (outcome := candidateOutcome)
        (reference := reference)
        (hDecode hRel) hException hOutcome

def RunningBlockReadyFor
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state mid : EVMState}
    {trace : OpenExternal.OpenTrace}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      trace (.ok (.running mid)) →
    RunListRunningReadyFor targetProgram state mid trace

def HaltedBlockReadyFor
    (program : Assembly.Program) (targetProgram : Assembly.TargetProgram) :
    Prop :=
  ∀ {state : EVMState}
    {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
    {pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget},
    Assembly.Program.instrAtPc program state.pc.toNat =
      some (pc, instr) →
    Assembly.emitInstr? program pc instr = some emitted →
    targetProgram.code = before ++ emitted ++ after →
    OpenExternal.OpenResultResolves
      (OpenAssembly.Target.openRunListResult
        (emitted.map Assembly.LocatedTarget.instr) state)
      trace (.ok (.halted halt)) →
    RunListHaltedReadyFor targetProgram state trace halt

theorem runningBlockReadyFor_of_current_emitted_ready_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr) :
    RunningBlockReadyFor program targetProgram := by
  intro state mid trace pc instr emitted before after
    hAt hEmit hTargetBlock hRun
  exact
    runListRunningReadyFor_current_emitted_of_ready_case
      (program := program) (targetProgram := targetProgram)
      (initial := state) (mid := mid) (trace := trace)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      hEncoding hSafety (hStateCode hAt) hAt hEmit hTargetBlock hRun
      hChecks (hReady hAt hEmit hTargetBlock hRun)

theorem haltedBlockReadyFor_of_current_emitted_no_call_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    HaltedBlockReadyFor program targetProgram := by
  intro state trace halt pc instr emitted before after
    hAt hEmit hTargetBlock hRun
  exact
    runListHaltedReadyFor_current_emitted_of_no_call_case
      (program := program) (targetProgram := targetProgram)
      (initial := state) (trace := trace) (halt := halt)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      hEncoding hSafety (hStateCode hAt)
      (hNoCall hAt hEmit hTargetBlock hRun)
      hAt hEmit hTargetBlock hRun hChecks

theorem runningPathTraceObservationOrFailureExistsReady_of_current_emitted_ready_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr) :
    RunningPathTraceObservationOrFailureExistsReady program
      targetProgram := by
  intro state mid trace pc instr emitted before after
    hAt hEmit hTargetBlock hRun
  exact
    runListRunningTraceObservationOrFailureExistsReadyFor_current_emitted_of_ready_case_current_path_checks
      (program := program) (targetProgram := targetProgram)
      (initial := state) (mid := mid) (trace := trace)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      hEncoding hSafety (hStateCode hAt) hAt hEmit hTargetBlock hRun
      (fun hNoInstr {full} hRel => by
        obtain ⟨_hTrace, hClosedRun⟩ :=
          openRunListResult_emitInstr_no_call_inv
            hNoInstr hEmit hRun
        exact hChecks hAt hEmit hTargetBlock hNoInstr hClosedRun hRel)
      (hReady hAt hEmit hTargetBlock hRun)

theorem haltedPathTraceObservationOrFailureExistsReady_of_current_emitted_no_call_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    HaltedPathTraceObservationOrFailureExistsReady program
      targetProgram := by
  intro state trace halt pc instr emitted before after
    hAt hEmit hTargetBlock hRun
  exact
    runListHaltedTraceObservationOrFailureExistsReadyFor_current_emitted_of_no_call_case
      (program := program) (targetProgram := targetProgram)
      (initial := state) (trace := trace) (halt := halt)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      hEncoding hSafety (hStateCode hAt)
      (hNoCall hAt hEmit hTargetBlock hRun)
      hAt hEmit hTargetBlock hRun hChecks

theorem runningPathReplayAndTraceObservationOrFailureExistsReady_of_current_emitted_ready_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr) :
    RunningPathReplayAndTraceObservationOrFailureExistsReady program
      targetProgram := by
  intro state mid trace pc instr emitted before after tailFuel tailGasBound
    hAt hEmit hTargetBlock hRun
  exact
    runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_of_ready_case_current_path_checks
      (program := program) (targetProgram := targetProgram)
      (tailFuel := tailFuel) (tailGasBound := tailGasBound)
      (initial := state) (mid := mid) (trace := trace)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      hEncoding hSafety (hStateCode hAt) hAt hEmit hTargetBlock hRun
      (fun hNoInstr {full} hRel => by
        obtain ⟨_hTrace, hClosedRun⟩ :=
          openRunListResult_emitInstr_no_call_inv
            hNoInstr hEmit hRun
        exact hChecks hAt hEmit hTargetBlock hNoInstr hClosedRun hRel)
      (hReady hAt hEmit hTargetBlock hRun)

theorem haltedPathReplayAndTraceObservationOrFailureExistsReady_of_current_emitted_no_call_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    HaltedPathReplayAndTraceObservationOrFailureExistsReady program
      targetProgram := by
  intro state trace halt pc instr emitted before after
    hAt hEmit hTargetBlock hRun
  exact
    runListHaltedReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_of_no_call_case
      (program := program) (targetProgram := targetProgram)
      (initial := state) (trace := trace) (halt := halt)
      (pc := pc) (instr := instr) (emitted := emitted)
      (before := before) (after := after)
      hEncoding hSafety (hStateCode hAt)
      (hNoCall hAt hEmit hTargetBlock hRun)
      hAt hEmit hTargetBlock hRun hChecks

theorem runningBlockReadyFor_of_runningPathRelReady
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hReady : RunningPathRelReady program targetProgram) :
    RunningBlockReadyFor program targetProgram := by
  intro state mid trace pc instr emitted before after
    hAt hEmit hTargetBlock hRun tailFuel tailGasBound
  exact hReady hAt hEmit hTargetBlock hRun

theorem haltedBlockReadyFor_of_haltedPathRelReady
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    (hReady : HaltedPathRelReady program targetProgram) :
    HaltedBlockReadyFor program targetProgram := by
  intro state trace halt pc instr emitted before after
    hAt hEmit hTargetBlock hRun
  exact hReady hAt hEmit hTargetBlock hRun

inductive TraceReadyFor
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram} :
    {targetFuel : Nat} → {state : EVMState} →
      {trace : OpenExternal.OpenTrace} →
        {targetResult : Assembly.StepResult} →
          OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
            state trace targetResult → Prop where
  | done (state : EVMState) :
      TraceReadyFor
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
      (hRunReady :
        RunListRunningReadyFor targetProgram state mid trace)
      (hRestReady : TraceReadyFor hRest) :
      TraceReadyFor
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
      (hRunReady :
        RunListHaltedReadyFor targetProgram state trace halt) :
      TraceReadyFor
        (OpenAssembly.OpenBlockTraceResult.stepHalted
          hAt hEmit hTargetBlock hRun)

inductive CurrentEmittedTraceReadyFor
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram} :
    {targetFuel : Nat} → {state : EVMState} →
      {trace : OpenExternal.OpenTrace} →
        {targetResult : Assembly.StepResult} →
          OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
            state trace targetResult → Prop where
  | done (state : EVMState) :
      CurrentEmittedTraceReadyFor
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
      (hRunReady :
        RunListRunningReadyFor targetProgram state mid trace)
      (hCodeStable :
        mid.executionEnv.code = state.executionEnv.code)
      (hRestReady : CurrentEmittedTraceReadyFor hRest) :
      CurrentEmittedTraceReadyFor
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
      (hRunReady :
        RunListHaltedReadyFor targetProgram state trace halt) :
      CurrentEmittedTraceReadyFor
        (OpenAssembly.OpenBlockTraceResult.stepHalted
          hAt hEmit hTargetBlock hRun)

theorem currentEmittedTraceReadyFor_of_openBlockTrace_running_halted_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hRunningReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        RunListRunningReadyFor targetProgram state mid trace)
    (hRunningCode :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        mid.executionEnv.code = state.executionEnv.code)
    (hHaltedReady :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        RunListHaltedReadyFor targetProgram state trace halt) :
    CurrentEmittedTraceReadyFor hTrace := by
  induction hTrace with
  | done state =>
      exact CurrentEmittedTraceReadyFor.done state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      exact
        CurrentEmittedTraceReadyFor.stepRunning
          hAt hEmit hTargetBlock hRun
          (hRunningReady hAt hEmit hTargetBlock hRun)
          (hRunningCode hAt hEmit hTargetBlock hRun)
          ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state trace halt pc instr emitted before after
      exact
        CurrentEmittedTraceReadyFor.stepHalted
          (fuel := fuel)
          hAt hEmit hTargetBlock hRun
          (hHaltedReady hAt hEmit hTargetBlock hRun)

theorem currentEmittedTraceReadyFor_of_openBlockTrace_current_emitted_ready_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    CurrentEmittedTraceReadyFor hTrace :=
  currentEmittedTraceReadyFor_of_openBlockTrace_running_halted_ready hTrace
    (fun {state mid trace pc instr emitted before after}
        hAt hEmit hTargetBlock hRun =>
      runListRunningReadyFor_current_emitted_of_ready_case
        (program := program) (targetProgram := targetProgram)
        (initial := state) (mid := mid) (trace := trace)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety (hStateCode hAt) hAt hEmit hTargetBlock hRun
        hChecks (hReady hAt hEmit hTargetBlock hRun))
    (fun {state mid trace pc instr emitted before after}
        hAt hEmit hTargetBlock hRun => by
      have hReadyCase := hReady hAt hEmit hTargetBlock hRun
      have hMidCode :
          mid.executionEnv.code =
            Assembly.Bytecode.encodeTarget targetProgram :=
        openRunListResult_current_emitted_running_preserves_code_of_ready_case
          (program := program) (targetProgram := targetProgram)
          (initial := state) (mid := mid) (trace := trace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          (hStateCode hAt) hEmit hTargetBlock hRun hReadyCase
      rw [hStateCode hAt]
      exact hMidCode)
    (fun {state trace halt pc instr emitted before after}
        hAt hEmit hTargetBlock hRun =>
      runListHaltedReadyFor_current_emitted_of_no_call_case
        (program := program) (targetProgram := targetProgram)
        (initial := state) (trace := trace) (halt := halt)
        (pc := pc) (instr := instr) (emitted := emitted)
        (before := before) (after := after)
        hEncoding hSafety (hStateCode hAt)
        (hNoCall hAt hEmit hTargetBlock hRun)
        hAt hEmit hTargetBlock hRun hChecks)

theorem currentEmittedTraceReadyFor_of_openBlockTrace_current_emitted_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    CurrentEmittedTraceReadyFor hTrace := by
  revert hInitialCode
  induction hTrace with
  | done state =>
      intro _hCode
      exact CurrentEmittedTraceReadyFor.done state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid currentTrace tailTrace result pc instr emitted
        before after
      intro hCode
      have hReadyCase := hReady hAt hEmit hTargetBlock hRun
      have hRunReady :
          RunListRunningReadyFor targetProgram state mid currentTrace :=
        runListRunningReadyFor_current_emitted_of_ready_case
          (program := program) (targetProgram := targetProgram)
          (initial := state) (mid := mid) (trace := currentTrace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hEncoding hSafety hCode hAt hEmit hTargetBlock hRun
          hChecks hReadyCase
      have hMidCode :
          mid.executionEnv.code =
            Assembly.Bytecode.encodeTarget targetProgram :=
        openRunListResult_current_emitted_running_preserves_code_of_ready_case
          (program := program) (targetProgram := targetProgram)
          (initial := state) (mid := mid) (trace := currentTrace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hCode hEmit hTargetBlock hRun hReadyCase
      have hCodeStable :
          mid.executionEnv.code = state.executionEnv.code := by
        rw [hCode]
        exact hMidCode
      exact
        CurrentEmittedTraceReadyFor.stepRunning
          hAt hEmit hTargetBlock hRun hRunReady hCodeStable (ih hMidCode)
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state currentTrace halt pc instr emitted before after
      intro hCode
      exact
        CurrentEmittedTraceReadyFor.stepHalted
          (fuel := fuel) hAt hEmit hTargetBlock hRun
          (runListHaltedReadyFor_current_emitted_of_no_call_case
            (program := program) (targetProgram := targetProgram)
            (initial := state) (trace := currentTrace) (halt := halt)
            (pc := pc) (instr := instr) (emitted := emitted)
            (before := before) (after := after)
            hEncoding hSafety hCode
            (hNoCall hAt hEmit hTargetBlock hRun)
            hAt hEmit hTargetBlock hRun hChecks)

theorem currentEmittedTraceReadyFor_of_openBlockTrace_current_emitted_trace_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrTraceReadyCase targetProgram state instr trace)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    CurrentEmittedTraceReadyFor hTrace := by
  revert hInitialCode
  induction hTrace with
  | done state =>
      intro _hCode
      exact CurrentEmittedTraceReadyFor.done state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid currentTrace tailTrace result pc instr emitted
        before after
      intro hCode
      obtain ⟨hRunReady, hCodeStable⟩ :=
        runListRunningReadyFor_current_emitted_of_trace_ready_case_current_path_checks
          (program := program) (targetProgram := targetProgram)
          (initial := state) (mid := mid) (trace := currentTrace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hEncoding hSafety hCode hAt hEmit hTargetBlock hRun
          (fun hNoInstr {full} hRel => by
            obtain ⟨_hTrace, hClosedRun⟩ :=
              openRunListResult_emitInstr_no_call_inv
                hNoInstr hEmit hRun
            exact hChecks hAt hEmit hTargetBlock hNoInstr hClosedRun hRel)
          (hReady hAt hEmit hTargetBlock hRun)
      have hMidCode :
          mid.executionEnv.code =
            Assembly.Bytecode.encodeTarget targetProgram := by
        rw [hCodeStable]
        exact hCode
      exact
        CurrentEmittedTraceReadyFor.stepRunning
          hAt hEmit hTargetBlock hRun hRunReady hCodeStable (ih hMidCode)
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state currentTrace halt pc instr emitted before after
      intro hCode
      exact
        CurrentEmittedTraceReadyFor.stepHalted
          (fuel := fuel) hAt hEmit hTargetBlock hRun
          (runListHaltedReadyFor_current_emitted_of_no_call_case
            (program := program) (targetProgram := targetProgram)
            (initial := state) (trace := currentTrace) (halt := halt)
            (pc := pc) (instr := instr) (emitted := emitted)
            (before := before) (after := after)
            hEncoding hSafety hCode
            (hNoCall hAt hEmit hTargetBlock hRun)
            hAt hEmit hTargetBlock hRun hChecks)

theorem traceReadyFor_of_current_emitted_trace_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hReady : CurrentEmittedTraceReadyFor hTrace) :
    TraceReadyFor hTrace := by
  revert hInitialCode
  induction hReady with
  | done state =>
      intro _hInitialCode
      exact TraceReadyFor.done state
  | stepRunning hAt hEmit hTargetBlock hRun hRunReady hCodeStable
      _hRestReady ih =>
      rename_i fuel state mid currentTrace tailTrace result pc instr emitted
        before after hRest
      intro hCode
      have hMidCode :
          mid.executionEnv.code =
            Assembly.Bytecode.encodeTarget targetProgram :=
        by
          rw [hCodeStable]
          exact hCode
      exact
        TraceReadyFor.stepRunning
          hAt hEmit hTargetBlock hRun hRunReady (ih hMidCode)
  | stepHalted hAt hEmit hTargetBlock hRun hRunReady =>
      rename_i fuel state currentTrace halt pc instr emitted before after
      intro _hCode
      exact
        TraceReadyFor.stepHalted
          (fuel := fuel)
          hAt hEmit hTargetBlock hRun hRunReady

theorem openBlockTrace_result_running_preserves_code_of_current_emitted_trace_ready_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        initial trace targetResult}
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady : CurrentEmittedTraceReadyFor hTrace)
    {final : EVMState}
    (hResult : targetResult = .running final) :
    final.executionEnv.code =
      Assembly.Bytecode.encodeTarget targetProgram := by
  revert final hInitialCode
  induction hReady with
  | done state =>
      intro hCode final hResult
      cases hResult
      simpa using hCode
  | stepRunning hAt hEmit hTargetBlock hRun _hRunReady hCodeStable
      _hRestReady ih =>
      rename_i fuel state mid currentTrace tailTrace result pc instr emitted
        before after hRest
      intro hCode final hResult
      have hMidCode :
          mid.executionEnv.code =
            Assembly.Bytecode.encodeTarget targetProgram :=
        by
          rw [hCodeStable]
          exact hCode
      exact ih hMidCode hResult
  | stepHalted hAt hEmit hTargetBlock hRun hRunReady =>
      intro _hCode final hResult
      cases hResult

theorem openBlockTrace_running_preserves_code_of_current_emitted_trace_ready_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {initial final : EVMState}
    {trace : OpenExternal.OpenTrace}
    {hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        initial trace (.running final)}
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady : CurrentEmittedTraceReadyFor hTrace) :
    final.executionEnv.code =
      Assembly.Bytecode.encodeTarget targetProgram :=
  openBlockTrace_result_running_preserves_code_of_current_emitted_trace_ready_of_initial_code
    hInitialCode hReady rfl

theorem finalCleanReady_of_openBlockTrace_running_fallthrough_current_emitted_trace_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {initial final : EVMState}
    {trace : OpenExternal.OpenTrace}
    {hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel
        initial trace (.running final)}
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady : CurrentEmittedTraceReadyFor hTrace)
    (hPc :
      final.pc.toNat =
        Assembly.Bytecode.codeByteLength targetProgram.code)
    (hStack : final.stack.length ≤ 1024)
    (hClean :
      Assembly.GasAware.XStepTrace.ReturnBuffersClean final) :
    Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady final := by
  have hFinalCode :
      final.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram :=
    openBlockTrace_running_preserves_code_of_current_emitted_trace_ready_of_initial_code
      hInitialCode hReady
  exact
    Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady.of_observation_stack
      (Assembly.GasAware.XStepTrace.XFallthroughStopObservationReady.of_pc_code_cleanReturn
        hFinalCode hPc hClean)
      hStack

theorem traceReadyFor_of_openBlockTrace
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hRunningReady : RunningBlockReadyFor program targetProgram)
    (hHaltedReady : HaltedBlockReadyFor program targetProgram) :
    TraceReadyFor hTrace := by
  induction hTrace with
  | done state =>
      exact TraceReadyFor.done state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      exact
        TraceReadyFor.stepRunning
          hAt hEmit hTargetBlock hRun
          (hRunningReady hAt hEmit hTargetBlock hRun) ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state trace halt pc instr emitted before after
      refine
        TraceReadyFor.stepHalted
          (fuel := fuel) hAt hEmit hTargetBlock hRun ?_
      exact hHaltedReady hAt hEmit hTargetBlock hRun

theorem traceReadyFor_of_openBlockTrace_pathRelReady
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hRunningReady : RunningPathRelReady program targetProgram)
    (hHaltedReady : HaltedPathRelReady program targetProgram) :
    TraceReadyFor hTrace :=
  traceReadyFor_of_openBlockTrace hTrace
    (runningBlockReadyFor_of_runningPathRelReady hRunningReady)
    (haltedBlockReadyFor_of_haltedPathRelReady hHaltedReady)

theorem traceReadyFor_of_openBlockTrace_current_emitted_ready_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    TraceReadyFor hTrace :=
  traceReadyFor_of_openBlockTrace hTrace
    (runningBlockReadyFor_of_current_emitted_ready_cases
      hEncoding hSafety hStateCode hChecks hReady)
    (haltedBlockReadyFor_of_current_emitted_no_call_cases
      hEncoding hSafety hStateCode hChecks hNoCall)

theorem traceReadyFor_of_openBlockTrace_current_emitted_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    TraceReadyFor hTrace := by
  revert hInitialCode
  induction hTrace with
  | done state =>
      intro _hInitialCode
      exact TraceReadyFor.done state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid trace tailTrace result pc instr emitted before after
      intro hCode
      have hReadyCase := hReady hAt hEmit hTargetBlock hRun
      have hRunReady :
          RunListRunningReadyFor targetProgram state mid trace :=
        runListRunningReadyFor_current_emitted_of_ready_case
          (program := program) (targetProgram := targetProgram)
          (initial := state) (mid := mid) (trace := trace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hEncoding hSafety hCode hAt hEmit hTargetBlock hRun
          hChecks hReadyCase
      have hMidCode :
          mid.executionEnv.code =
            Assembly.Bytecode.encodeTarget targetProgram :=
        openRunListResult_current_emitted_running_preserves_code_of_ready_case
          (program := program) (targetProgram := targetProgram)
          (initial := state) (mid := mid) (trace := trace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hCode hEmit hTargetBlock hRun hReadyCase
      exact
        TraceReadyFor.stepRunning
          hAt hEmit hTargetBlock hRun hRunReady (ih hMidCode)
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state trace halt pc instr emitted before after
      intro hCode
      exact
        TraceReadyFor.stepHalted
          (fuel := fuel)
          hAt hEmit hTargetBlock hRun
          (runListHaltedReadyFor_current_emitted_of_no_call_case
            (program := program) (targetProgram := targetProgram)
            (initial := state) (trace := trace) (halt := halt)
            (pc := pc) (instr := instr) (emitted := emitted)
            (before := before) (after := after)
            hEncoding hSafety hCode
            (hNoCall hAt hEmit hTargetBlock hRun)
            hAt hEmit hTargetBlock hRun hChecks)

theorem of_openBlockTrace
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady : DoneRelReady targetProgram)
    (hRunningReady : RunningPathRelReady program targetProgram)
    (hHaltedReady : HaltedPathRelReady program targetProgram) :
    ∃ evmFuel gasBound,
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound := by
  induction hTrace with
  | done state =>
      obtain ⟨evmFuel, gasBound, hDone⟩ := hDoneReady
      exact ⟨evmFuel, gasBound, OpenXBlockTraceRelReady.done hDone⟩
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      obtain ⟨tailFuel, tailGasBound, hRestReady⟩ := ih
      obtain ⟨evmFuel, gasBound, hRunReady⟩ :=
        hRunningReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, gasBound,
          OpenXBlockTraceRelReady.stepRunning
            hAt hEmit hTargetBlock hRun hRunReady hRestReady⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      obtain ⟨evmFuel, gasBound, hRunReady⟩ :=
        hHaltedReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, gasBound,
          OpenXBlockTraceRelReady.stepHalted
            hAt hEmit hTargetBlock hRun hRunReady⟩

theorem of_openBlockTrace_with_done_continuation
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady : DoneContinuationReady targetProgram targetResult)
    (hRunningReady : RunningPathRelReady program targetProgram)
    (hHaltedReady : HaltedPathRelReady program targetProgram) :
    ∃ evmFuel gasBound,
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound := by
  induction hTrace with
  | done state =>
      obtain ⟨evmFuel, gasBound, hDone⟩ := hDoneReady
      exact ⟨evmFuel, gasBound, OpenXBlockTraceRelReady.done hDone⟩
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      obtain ⟨tailFuel, tailGasBound, hRestReady⟩ := ih hDoneReady
      obtain ⟨evmFuel, gasBound, hRunReady⟩ :=
        hRunningReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, gasBound,
          OpenXBlockTraceRelReady.stepRunning
            hAt hEmit hTargetBlock hRun hRunReady hRestReady⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      obtain ⟨evmFuel, gasBound, hRunReady⟩ :=
        hHaltedReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, gasBound,
          OpenXBlockTraceRelReady.stepHalted
            hAt hEmit hTargetBlock hRun hRunReady⟩

theorem openBlockTraceResult_traceObservationOrFailure_exists_of_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady : DoneObservationOrFailureReady targetProgram targetResult)
    (hRunningReady :
      RunningPathTraceObservationOrFailureExistsReady program targetProgram)
    (hHaltedReady :
      HaltedPathTraceObservationOrFailureExistsReady program targetProgram) :
    ∃ evmFuel : Nat,
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full state →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps targetProgram) evmFuel full
              candidateTrace targetResult := by
  induction hTrace with
  | done state =>
      obtain ⟨evmFuel, hDone⟩ := hDoneReady
      exact
        ⟨evmFuel, by
          intro full hRel
          exact hDone rfl hRel⟩
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      obtain ⟨tailFuel, hTail⟩ := ih hDoneReady
      obtain ⟨evmFuel, hRunReady⟩ :=
        hRunningReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, by
          intro full hRel
          exact hRunReady hRel (fun hRelPost => hTail hRelPost)⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      obtain ⟨evmFuel, hRunReady⟩ :=
        hHaltedReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, by
          intro full hRel
          exact hRunReady hRel⟩

theorem openBlockTraceResult_all_outcomes_safelyTracks_of_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {referenceTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    {reference : EVMResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        referenceTrace targetResult)
    (hDoneReady :
      ∀ {state : EVMState},
        ∃ evmFuel,
          ∀ {full : EVMState}
            {candidateTrace : OpenExternal.OpenTrace}
            {candidateOutcome : Except EVMException EVMResult},
            Assembly.GasAware.GasExecRel full state →
              OpenXOutcomeTraceResult
                (Assembly.GasAware.validJumps targetProgram)
                evmFuel full candidateTrace candidateOutcome →
                Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
                  (.ok reference))
    (hRunningReady :
      RunningPathAllOutcomeTracksReady program targetProgram reference)
    (hHaltedReady :
      HaltedPathAllOutcomeTracksReady program targetProgram reference) :
    ∃ evmFuel,
      ∀ {full : EVMState}
        {candidateTrace : OpenExternal.OpenTrace}
        {candidateOutcome : Except EVMException EVMResult},
        Assembly.GasAware.GasExecRel full state →
          OpenXOutcomeTraceResult
            (Assembly.GasAware.validJumps targetProgram)
            evmFuel full candidateTrace candidateOutcome →
            Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
              (.ok reference) := by
  induction hTrace with
  | done state =>
      exact hDoneReady
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      obtain ⟨tailFuel, hTail⟩ := ih
      obtain ⟨evmFuel, hRunReady⟩ :=
        hRunningReady (tailFuel := tailFuel) hAt hEmit hTargetBlock hRun
      refine ⟨evmFuel, ?_⟩
      intro full candidateTrace candidateOutcome hRel hOutcome
      exact
        hRunReady hRel
          (fun {gasPost} hRelPost =>
            by
              intro candidateTailTrace candidateTailOutcome hTailOutcome
              exact hTail hRelPost hTailOutcome)
          hOutcome
  | stepHalted hAt hEmit hTargetBlock hRun =>
      obtain ⟨evmFuel, hRunReady⟩ :=
        hHaltedReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, by
          intro full candidateTrace candidateOutcome hRel hOutcome
          exact hRunReady hRel hOutcome⟩

theorem openBlockTraceResult_all_outcomes_safelyTracks_of_target_done_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {referenceTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    {reference : EVMResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        referenceTrace targetResult)
    (hDoneReady :
      ∀ {doneState : EVMState},
        targetResult = .running doneState →
          ∃ evmFuel,
            ∀ {full : EVMState}
              {candidateTrace : OpenExternal.OpenTrace}
              {candidateOutcome : Except EVMException EVMResult},
              Assembly.GasAware.GasExecRel full doneState →
                OpenXOutcomeTraceResult
                  (Assembly.GasAware.validJumps targetProgram)
                  evmFuel full candidateTrace candidateOutcome →
                  Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
                    (.ok reference))
    (hRunningReady :
      RunningPathAllOutcomeTracksReady program targetProgram reference)
    (hHaltedReady :
      HaltedPathAllOutcomeTracksReady program targetProgram reference) :
    ∃ evmFuel,
      ∀ {full : EVMState}
        {candidateTrace : OpenExternal.OpenTrace}
        {candidateOutcome : Except EVMException EVMResult},
        Assembly.GasAware.GasExecRel full state →
          OpenXOutcomeTraceResult
            (Assembly.GasAware.validJumps targetProgram)
            evmFuel full candidateTrace candidateOutcome →
            Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
              (.ok reference) := by
  induction hTrace with
  | done state =>
      exact hDoneReady rfl
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      obtain ⟨tailFuel, hTail⟩ := ih hDoneReady
      obtain ⟨evmFuel, hRunReady⟩ :=
        hRunningReady (tailFuel := tailFuel) hAt hEmit hTargetBlock hRun
      refine ⟨evmFuel, ?_⟩
      intro full candidateTrace candidateOutcome hRel hOutcome
      exact
        hRunReady hRel
          (fun {gasPost} hRelPost =>
            by
              intro candidateTailTrace candidateTailOutcome hTailOutcome
              exact hTail hRelPost hTailOutcome)
          hOutcome
  | stepHalted hAt hEmit hTargetBlock hRun =>
      obtain ⟨evmFuel, hRunReady⟩ :=
        hHaltedReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, by
          intro full candidateTrace candidateOutcome hRel hOutcome
          exact hRunReady hRel hOutcome⟩

theorem openBlockTraceResult_all_outcomes_safelyTracks_of_target_terminal_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {referenceTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult}
    {reference : EVMResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        referenceTrace targetResult)
    (hDoneReady :
      ∀ {doneState : EVMState},
        targetResult = .running doneState →
          ∃ evmFuel,
            ∀ {full : EVMState}
              {candidateTrace : OpenExternal.OpenTrace}
              {candidateOutcome : Except EVMException EVMResult},
              Assembly.GasAware.GasExecRel full doneState →
                OpenXOutcomeTraceResult
                  (Assembly.GasAware.validJumps targetProgram)
                  evmFuel full candidateTrace candidateOutcome →
                  Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
                    (.ok reference))
    (hRunningReady :
      RunningPathAllOutcomeTracksReady program targetProgram reference)
    (hHaltedReady :
      ∀ {haltState : EVMState}
        {currentTrace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program haltState.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) haltState)
          currentTrace (.ok (.halted halt)) →
        targetResult = .halted halt →
          ∃ evmFuel,
            OpenXRunListHaltedAllOutcomeTracksReady targetProgram haltState
              evmFuel reference) :
    ∃ evmFuel,
      ∀ {full : EVMState}
        {candidateTrace : OpenExternal.OpenTrace}
        {candidateOutcome : Except EVMException EVMResult},
        Assembly.GasAware.GasExecRel full state →
          OpenXOutcomeTraceResult
            (Assembly.GasAware.validJumps targetProgram)
            evmFuel full candidateTrace candidateOutcome →
            Assembly.GasAware.XRunOutcomeSafelyTracks candidateOutcome
              (.ok reference) := by
  induction hTrace with
  | done state =>
      exact hDoneReady rfl
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      obtain ⟨tailFuel, hTail⟩ := ih hDoneReady hHaltedReady
      obtain ⟨evmFuel, hRunReady⟩ :=
        hRunningReady (tailFuel := tailFuel) hAt hEmit hTargetBlock hRun
      refine ⟨evmFuel, ?_⟩
      intro full candidateTrace candidateOutcome hRel hOutcome
      exact
        hRunReady hRel
          (fun {gasPost} hRelPost =>
            by
              intro candidateTailTrace candidateTailOutcome hTailOutcome
              exact hTail hRelPost hTailOutcome)
          hOutcome
  | stepHalted hAt hEmit hTargetBlock hRun =>
      obtain ⟨evmFuel, hRunReady⟩ :=
        hHaltedReady hAt hEmit hTargetBlock hRun rfl
      exact
        ⟨evmFuel, by
          intro full candidateTrace candidateOutcome hRel hOutcome
          exact hRunReady hRel hOutcome⟩

theorem openBlockTraceResult_traceObservationOrFailure_exists_of_current_emitted_ready_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady : DoneObservationOrFailureReady targetProgram targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    ∃ evmFuel : Nat,
      ∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full state →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps targetProgram) evmFuel full
              candidateTrace targetResult :=
  openBlockTraceResult_traceObservationOrFailure_exists_of_ready
    hTrace hDoneReady
    (runningPathTraceObservationOrFailureExistsReady_of_current_emitted_ready_cases
      hEncoding hSafety hStateCode hChecks hReady)
    (haltedPathTraceObservationOrFailureExistsReady_of_current_emitted_no_call_cases
      hEncoding hSafety hStateCode hChecks hNoCall)

theorem openBlockTraceResult_traceRelAbove_and_traceObservationOrFailure_exists_of_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady :
      DoneReplayAndObservationOrFailureReady targetProgram targetResult)
    (hRunningReady :
      RunningPathReplayAndTraceObservationOrFailureExistsReady program
        targetProgram)
    (hHaltedReady :
      HaltedPathReplayAndTraceObservationOrFailureExistsReady program
        targetProgram) :
    ∃ evmFuel gasBound,
      OpenXTraceRelAbove targetProgram state trace targetResult evmFuel
        gasBound ∧
      (∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full state →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps targetProgram) evmFuel full
              candidateTrace targetResult) := by
  induction hTrace with
  | done state =>
      obtain ⟨evmFuel, gasBound, hDoneTrace, hDoneClass⟩ := hDoneReady
      exact
        ⟨evmFuel, gasBound,
          openXTraceRelAbove_done_of_path_done hDoneTrace,
          by
            intro full hRel
            exact hDoneClass rfl hRel⟩
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      obtain ⟨tailFuel, tailGasBound, hTailRel, hTailClass⟩ :=
        ih hDoneReady
      obtain ⟨evmFuel, gasBound, hRunRel, hRunClass⟩ :=
        hRunningReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, gasBound,
          by
            intro full hGasBound hRel
            exact hRunRel hGasBound hRel
              (fun hTailGas hTailRel' =>
                hTailRel hTailGas hTailRel'),
          by
            intro full hRel
            exact hRunClass hRel (fun hRelPost => hTailClass hRelPost)⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      obtain ⟨evmFuel, gasBound, hRunRel, hRunClass⟩ :=
        hHaltedReady hAt hEmit hTargetBlock hRun
      exact
        ⟨evmFuel, gasBound,
          by
            intro full hGasBound hRel
            exact hRunRel hGasBound hRel,
          by
            intro full hRel
            exact hRunClass hRel⟩

theorem openBlockTraceResult_replayAbove_and_traceObservationOrFailure_exists_of_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady :
      DoneReplayAndObservationOrFailureReady targetProgram targetResult)
    (hRunningReady :
      RunningPathReplayAndTraceObservationOrFailureExistsReady program
        targetProgram)
    (hHaltedReady :
      HaltedPathReplayAndTraceObservationOrFailureExistsReady program
        targetProgram) :
    ∃ evmFuel gasBound,
      OpenXReplayAbove targetProgram state trace targetResult evmFuel
        gasBound ∧
      (∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full state →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps targetProgram) evmFuel full
              candidateTrace targetResult) := by
  obtain ⟨evmFuel, gasBound, hTraceRel, hClassified⟩ :=
    openBlockTraceResult_traceRelAbove_and_traceObservationOrFailure_exists_of_ready
      hTrace hDoneReady hRunningReady hHaltedReady
  exact
    ⟨evmFuel, gasBound,
      openXReplayAbove_of_traceRelAbove hInitialCode hTraceRel,
      hClassified⟩

theorem openBlockTraceResult_committedSafeForAllGas_of_ready
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady :
      DoneReplayAndObservationOrFailureReady targetProgram targetResult)
    (hRunningReady :
      RunningPathReplayAndTraceObservationOrFailureExistsReady program
        targetProgram)
    (hHaltedReady :
      HaltedPathReplayAndTraceObservationOrFailureExistsReady program
        targetProgram) :
    ∃ evmFuel,
      OpenXCommittedSafeForAllGas targetProgram state targetResult
        evmFuel := by
  obtain ⟨evmFuel, gasBound, hReplay, hClassified⟩ :=
    openBlockTraceResult_replayAbove_and_traceObservationOrFailure_exists_of_ready
      hInitialCode hTrace hDoneReady hRunningReady hHaltedReady
  exact
    ⟨evmFuel,
      hReplay.to_committedSafeForAllGas_of_traceObservationOrFailure_exists
        hInitialCode hClassified⟩

theorem openBlockTraceResult_committedSafeForAllGas_of_current_emitted_ready_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady :
      DoneReplayAndObservationOrFailureReady targetProgram targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    ∃ evmFuel,
      OpenXCommittedSafeForAllGas targetProgram state targetResult
        evmFuel :=
  openBlockTraceResult_committedSafeForAllGas_of_ready
    hInitialCode hTrace hDoneReady
    (runningPathReplayAndTraceObservationOrFailureExistsReady_of_current_emitted_ready_cases
      hEncoding hSafety hStateCode hChecks hReady)
    (haltedPathReplayAndTraceObservationOrFailureExistsReady_of_current_emitted_no_call_cases
      hEncoding hSafety hStateCode hChecks hNoCall)

theorem openBlockTraceResult_traceRelAbove_and_traceObservationOrFailure_exists_of_current_emitted_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady :
      DoneReplayAndObservationOrFailureReady targetProgram targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    ∃ evmFuel gasBound,
      OpenXTraceRelAbove targetProgram state trace targetResult evmFuel
        gasBound ∧
      (∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full state →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps targetProgram) evmFuel full
              candidateTrace targetResult) := by
  revert hInitialCode
  induction hTrace with
  | done state =>
      intro _hCode
      obtain ⟨evmFuel, gasBound, hDoneTrace, hDoneClass⟩ := hDoneReady
      exact
        ⟨evmFuel, gasBound,
          openXTraceRelAbove_done_of_path_done hDoneTrace,
          by
            intro full hRel
            exact hDoneClass rfl hRel⟩
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid currentTrace tailTrace result pc instr emitted
        before after
      intro hCode
      have hReadyCase := hReady hAt hEmit hTargetBlock hRun
      have hMidCode :
          mid.executionEnv.code =
            Assembly.Bytecode.encodeTarget targetProgram :=
        openRunListResult_current_emitted_running_preserves_code_of_ready_case
          (program := program) (targetProgram := targetProgram)
          (initial := state) (mid := mid) (trace := currentTrace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hCode hEmit hTargetBlock hRun hReadyCase
      obtain ⟨tailFuel, tailGasBound, hTailRel, hTailClass⟩ :=
        ih hDoneReady hMidCode
      obtain ⟨evmFuel, gasBound, hRunRel, hRunClass⟩ :=
        runListRunningReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_of_ready_case_current_path_checks
          (program := program) (targetProgram := targetProgram)
          (tailFuel := tailFuel) (tailGasBound := tailGasBound)
          (initial := state) (mid := mid) (trace := currentTrace)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hEncoding hSafety hCode hAt hEmit hTargetBlock hRun
          (fun hNoInstr {full} hRel => by
            obtain ⟨_hTrace, hClosedRun⟩ :=
              openRunListResult_emitInstr_no_call_inv
                hNoInstr hEmit hRun
            exact hChecks hAt hEmit hTargetBlock hNoInstr hClosedRun hRel)
          hReadyCase
      exact
        ⟨evmFuel, gasBound,
          by
            intro full hGasBound hRel
            exact hRunRel hGasBound hRel
              (fun hTailGas hTailRel' =>
                hTailRel hTailGas hTailRel'),
          by
            intro full hRel
            exact hRunClass hRel (fun hRelPost => hTailClass hRelPost)⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state currentTrace halt pc instr emitted before after
      intro hCode
      obtain ⟨evmFuel, gasBound, hRunRel, hRunClass⟩ :=
        runListHaltedReplayAndTraceObservationOrFailureExistsReadyFor_current_emitted_of_no_call_case
          (program := program) (targetProgram := targetProgram)
          (initial := state) (trace := currentTrace) (halt := halt)
          (pc := pc) (instr := instr) (emitted := emitted)
          (before := before) (after := after)
          hEncoding hSafety hCode
          (hNoCall hAt hEmit hTargetBlock hRun)
          hAt hEmit hTargetBlock hRun hChecks
      exact
        ⟨evmFuel, gasBound,
          by
            intro full hGasBound hRel
            exact hRunRel hGasBound hRel,
          by
            intro full hRel
            exact hRunClass hRel⟩

theorem openBlockTraceResult_replayAbove_and_traceObservationOrFailure_exists_of_current_emitted_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady :
      DoneReplayAndObservationOrFailureReady targetProgram targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    ∃ evmFuel gasBound,
      OpenXReplayAbove targetProgram state trace targetResult evmFuel
        gasBound ∧
      (∀ {full : EVMState},
        Assembly.GasAware.GasExecRel full state →
          ∃ candidateTrace : OpenExternal.OpenTrace,
            OpenXTraceObservationOrFailure
              (Assembly.GasAware.validJumps targetProgram) evmFuel full
              candidateTrace targetResult) := by
  obtain ⟨evmFuel, gasBound, hTraceRel, hClassified⟩ :=
    openBlockTraceResult_traceRelAbove_and_traceObservationOrFailure_exists_of_current_emitted_ready_cases_of_initial_code
      hInitialCode hTrace hDoneReady hEncoding hSafety hChecks hReady
      hNoCall
  exact
    ⟨evmFuel, gasBound,
      openXReplayAbove_of_traceRelAbove hInitialCode hTraceRel,
      hClassified⟩

theorem openBlockTraceResult_committedSafeForAllGas_of_current_emitted_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady :
      DoneReplayAndObservationOrFailureReady targetProgram targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    ∃ evmFuel,
      OpenXCommittedSafeForAllGas targetProgram state targetResult
        evmFuel := by
  obtain ⟨evmFuel, gasBound, hReplay, hClassified⟩ :=
    openBlockTraceResult_replayAbove_and_traceObservationOrFailure_exists_of_current_emitted_ready_cases_of_initial_code
      hInitialCode hTrace hDoneReady hEncoding hSafety hChecks hReady
      hNoCall
  exact
    ⟨evmFuel,
      hReplay.to_committedSafeForAllGas_of_traceObservationOrFailure_exists
        hInitialCode hClassified⟩

theorem of_traceReadyFor_with_done_continuation
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult}
    (hReadyFor : TraceReadyFor hTrace)
    (hDoneReady : DoneContinuationReady targetProgram targetResult) :
    ∃ evmFuel gasBound,
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound := by
  induction hReadyFor with
  | done state =>
      obtain ⟨evmFuel, gasBound, hDone⟩ := hDoneReady
      exact ⟨evmFuel, gasBound, OpenXBlockTraceRelReady.done hDone⟩
  | stepRunning hAt hEmit hTargetBlock hRun hRunReady hRestReady ih =>
      obtain ⟨tailFuel, tailGasBound, hRestReady'⟩ := ih hDoneReady
      obtain ⟨evmFuel, gasBound, hRunReady'⟩ :=
        hRunReady (tailFuel := tailFuel) (tailGasBound := tailGasBound)
      exact
        ⟨evmFuel, gasBound,
          OpenXBlockTraceRelReady.stepRunning
            hAt hEmit hTargetBlock hRun hRunReady' hRestReady'⟩
  | stepHalted hAt hEmit hTargetBlock hRun hRunReady =>
      obtain ⟨evmFuel, gasBound, hRunReady'⟩ := hRunReady
      exact
        ⟨evmFuel, gasBound,
          OpenXBlockTraceRelReady.stepHalted
            hAt hEmit hTargetBlock hRun hRunReady'⟩

theorem to_openBlockTrace
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReady :
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound) :
    OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
      trace targetResult := by
  induction hReady with
  | done =>
      exact OpenAssembly.OpenBlockTraceResult.done _
  | stepRunning hAt hEmit hTargetBlock hRun _hRunReady _hRest ih =>
      exact
        OpenAssembly.OpenBlockTraceResult.stepRunning
          hAt hEmit hTargetBlock hRun ih
  | stepHalted hAt hEmit hTargetBlock hRun _hRunReady =>
      exact
        OpenAssembly.OpenBlockTraceResult.stepHalted
          hAt hEmit hTargetBlock hRun

theorem to_traceRelAbove
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hReady :
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound) :
    OpenXTraceRelAbove targetProgram state trace targetResult evmFuel
      gasBound := by
  induction hReady with
  | done hDone =>
      exact openXTraceRelAbove_done_of_path_done hDone
  | stepRunning hAt hEmit hTargetBlock hRun hRunReady hRest ih =>
      intro full hGasBound hRel
      exact hRunReady hGasBound hRel (fun hTailGas hTailRel =>
        ih hTailGas hTailRel)
  | stepHalted hAt hEmit hTargetBlock hRun hRunReady =>
      intro full hGasBound hRel
      exact hRunReady hGasBound hRel

theorem to_replayAbove
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady :
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound) :
    OpenXReplayAbove targetProgram state trace targetResult evmFuel
      gasBound :=
  openXReplayAbove_of_traceRelAbove hInitialCode
    (to_traceRelAbove hReady)

theorem to_replayAt
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound gas : Nat}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady :
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound)
    (hGasAtLeast : gasBound ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    OpenXReplayAt targetProgram state trace targetResult evmFuel gas :=
  (to_replayAbove hInitialCode hReady).to_replayAt hGasAtLeast hGasFits

theorem to_replaySomeGas
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady :
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound)
    (hFeasible :
      ∃ gas : Nat, gasBound ≤ gas ∧ gas < EvmYul.UInt256.size) :
    OpenXReplaySomeGas targetProgram state trace targetResult evmFuel :=
  (to_replayAbove hInitialCode hReady).to_replaySomeGas hFeasible

theorem to_replaySomeGas_of_bound_lt
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {evmFuel gasBound : Nat}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReady :
      OpenXBlockTraceRelReady program targetProgram targetFuel state trace
        targetResult evmFuel gasBound)
    (hGasBoundFits : gasBound < EvmYul.UInt256.size) :
    OpenXReplaySomeGas targetProgram state trace targetResult evmFuel :=
  (to_replayAbove hInitialCode hReady).to_replaySomeGas_of_bound_lt
    hGasBoundFits

theorem openBlockTrace_replayAbove
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady : DoneRelReady targetProgram)
    (hRunningReady : RunningPathRelReady program targetProgram)
    (hHaltedReady : HaltedPathRelReady program targetProgram) :
    ∃ evmFuel gasBound,
      OpenXReplayAbove targetProgram state trace targetResult evmFuel
        gasBound := by
  obtain ⟨evmFuel, gasBound, hReady⟩ :=
    of_openBlockTrace hTrace hDoneReady hRunningReady hHaltedReady
  exact ⟨evmFuel, gasBound, to_replayAbove hInitialCode hReady⟩

theorem openBlockTrace_replayAbove_with_done_continuation
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady : DoneContinuationReady targetProgram targetResult)
    (hRunningReady : RunningPathRelReady program targetProgram)
    (hHaltedReady : HaltedPathRelReady program targetProgram) :
    ∃ evmFuel gasBound,
      OpenXReplayAbove targetProgram state trace targetResult evmFuel
        gasBound := by
  obtain ⟨evmFuel, gasBound, hReady⟩ :=
    of_openBlockTrace_with_done_continuation
      hTrace hDoneReady hRunningReady hHaltedReady
  exact ⟨evmFuel, gasBound, to_replayAbove hInitialCode hReady⟩

theorem traceReadyFor_replayAbove_with_done_continuation
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hReadyFor : TraceReadyFor hTrace)
    (hDoneReady : DoneContinuationReady targetProgram targetResult) :
    ∃ evmFuel gasBound,
      OpenXReplayAbove targetProgram state trace targetResult evmFuel
        gasBound := by
  obtain ⟨evmFuel, gasBound, hReady⟩ :=
    of_traceReadyFor_with_done_continuation hReadyFor hDoneReady
  exact ⟨evmFuel, gasBound, to_replayAbove hInitialCode hReady⟩

theorem openBlockTrace_replayAbove_with_done_continuation_of_current_emitted_ready_cases
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady : DoneContinuationReady targetProgram targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hStateCode :
      ∀ {state : EVMState} {pc : Nat} {instr : Assembly.Instr},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        state.executionEnv.code =
          Assembly.Bytecode.encodeTarget targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    ∃ evmFuel gasBound,
      OpenXReplayAbove targetProgram state trace targetResult evmFuel
        gasBound := by
  exact
    traceReadyFor_replayAbove_with_done_continuation
      hInitialCode
      (traceReadyFor_of_openBlockTrace_current_emitted_ready_cases
        hTrace hEncoding hSafety hStateCode hChecks hReady hNoCall)
      hDoneReady

theorem openBlockTrace_replayAbove_with_done_continuation_of_current_emitted_ready_cases_of_initial_code
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {trace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    (hInitialCode :
      state.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hTrace :
      OpenAssembly.OpenBlockTraceResult program targetProgram targetFuel state
        trace targetResult)
    (hDoneReady : DoneContinuationReady targetProgram targetResult)
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hChecks :
      CurrentNoCallPathChecksReady program targetProgram)
    (hReady :
      ∀ {state mid : EVMState}
        {trace : OpenExternal.OpenTrace}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.running mid)) →
        CurrentRunningInstrReadyCase targetProgram state instr)
    (hNoCall :
      ∀ {state : EVMState}
        {trace : OpenExternal.OpenTrace} {halt : Assembly.Halt}
        {pc : Nat} {instr : Assembly.Instr}
        {emitted before after : List Assembly.LocatedTarget},
        Assembly.Program.instrAtPc program state.pc.toNat =
          some (pc, instr) →
        Assembly.emitInstr? program pc instr = some emitted →
        targetProgram.code = before ++ emitted ++ after →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Target.openRunListResult
            (emitted.map Assembly.LocatedTarget.instr) state)
          trace (.ok (.halted halt)) →
        Assembly.Instr.usesCallCreate instr = false) :
    ∃ evmFuel gasBound,
      OpenXReplayAbove targetProgram state trace targetResult evmFuel
        gasBound := by
  exact
    traceReadyFor_replayAbove_with_done_continuation
      hInitialCode
      (traceReadyFor_of_openBlockTrace_current_emitted_ready_cases_of_initial_code
        hTrace hInitialCode hEncoding hSafety hChecks hReady hNoCall)
      hDoneReady

end OpenXBlockTraceRelReady

theorem openXReplayAbove_done_of_path_done
    {targetProgram : Assembly.TargetProgram}
    {gasBound doneFuel : Nat} {initial : EVMState}
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hDone :
      OpenXTracePathDoneContinuation
        (Assembly.GasAware.validJumps targetProgram)
        (.running initial) doneFuel) :
    OpenXReplayAbove targetProgram initial [] (.running initial)
      doneFuel gasBound := by
  intro gas _hGasAtLeast _hGasFits
  exact
    hDone rfl
      (Assembly.GasAware.GasExecRel.installCodeAndGas_of_code_eq
        (target := targetProgram) (gas := gas) (initial := initial)
        hInitialCode)

theorem openXReplayAbove_current_emitted_prim_call_continue_of_step_checks
    {program : Assembly.Program} {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {pc : Nat} {op : Assembly.PrimOp}
    {emitted before after : List Assembly.LocatedTarget}
    {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EVMState}
    {response : OpenExternal.CallResponse}
    {tailTrace : OpenExternal.OpenTrace} {targetResult : Assembly.StepResult}
    {result : EVMResult}
    (hEncoding :
      Assembly.Bytecode.EncodingCorrect targetProgram
        (Assembly.Bytecode.encodeTarget targetProgram))
    (hSafety : Assembly.Bytecode.DecodeSafety targetProgram)
    (hInitialCode :
      initial.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram)
    (hAt :
      Assembly.Program.instrAtPc program initial.pc.toNat =
        some (pc, Assembly.Instr.prim op))
    (hEmit :
      Assembly.emitInstr? program pc (Assembly.Instr.prim op) =
        some emitted)
    (hTargetBlock : targetProgram.code = before ++ emitted ++ after)
    (hStepChecks :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram)
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
              op.toEVM)
    (hKind :
      OpenExternal.CallKind.ofEVMOperation? op.toEVM = some kind)
    (hCall :
      OpenExternal.CallKind.evmOpenCall? initial kind = some call)
    (hRest :
      ∀ {gas : Nat} {gasPost : EVMState},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            Assembly.GasAware.GasExecRel gasPost
              (EvmYul.EVM.State.incrPC (call.resume response)) →
              OpenExternal.OpenResultResolves
                (openX tailFuel
                  (Assembly.GasAware.validJumps targetProgram) gasPost)
                tailTrace (.ok result))
    (hAgree : OpenXResultAgrees targetResult result) :
    OpenXReplayAbove targetProgram initial
      (OpenExternal.OpenEvent.call call.site response :: tailTrace)
      targetResult (tailFuel + 1) gasBound := by
  intro gas hGasAtLeast hGasFits
  let full :=
    Assembly.GasAware.installCodeAndGas targetProgram gas initial
  have hRel :
      Assembly.GasAware.GasExecRel full initial :=
    Assembly.GasAware.GasExecRel.installCodeAndGas_of_code_eq
      (target := targetProgram) (gas := gas) (initial := initial)
      hInitialCode
  have hCode :
      full.executionEnv.code =
        Assembly.Bytecode.encodeTarget targetProgram := by
    simp [full, Assembly.GasAware.installCodeAndGas]
  refine ⟨result, ?_, hAgree⟩
  exact
    openX_current_emitted_prim_call_continue_of_step_checks
      (program := program) (targetProgram := targetProgram)
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (full := full) (target := initial)
      (pc := pc) (op := op) (emitted := emitted)
      (before := before) (after := after) (kind := kind)
      (call := call) (response := response)
      (tailTrace := tailTrace) (result := result)
      hEncoding hSafety hAt hEmit hTargetBlock hRel hCode
      (hStepChecks hGasAtLeast hGasFits) hKind hCall
      (fun hRelPost => hRest hGasAtLeast hGasFits hRelPost)

theorem openXReplayAbove_current_running_continue_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial post : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {tailTrace : OpenExternal.OpenTrace}
    {targetResult : Assembly.StepResult} {result : EVMResult}
    (hDecode :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.decode
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial).executionEnv.code
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial).pc =
              some (op, arg))
    (hStepChecks :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram)
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
              op)
    (hOpenStep :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            openStepAfterChecks tailFuel op arg
                (Assembly.GasAware.installCodeAndGas targetProgram gas initial) =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState
                      (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                      op)
                    op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState
                    (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                    op)))
    (hStep :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            ∃ gasPost : EVMState,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState
                      (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                      op)
                    op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState
                    (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                    op) =
                .ok gasPost ∧
              Assembly.GasAware.GasExecRel gasPost post ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost = none)
    (hRest :
      ∀ {gas : Nat} {gasPost : EVMState},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            Assembly.GasAware.GasExecRel gasPost post →
              OpenExternal.OpenResultResolves
                (openX tailFuel
                  (Assembly.GasAware.validJumps targetProgram) gasPost)
                tailTrace (.ok result))
    (hAgree : OpenXResultAgrees targetResult result) :
    OpenXReplayAbove targetProgram initial tailTrace targetResult
      (tailFuel + 1) gasBound := by
  intro gas hGasAtLeast hGasFits
  obtain ⟨gasPost, hStepOk, hRelPost, hNoHalt⟩ :=
    hStep hGasAtLeast hGasFits
  refine ⟨result, ?_, hAgree⟩
  exact
    openX_current_running_continue_of_openStepAfterChecks_done
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (state :=
        Assembly.GasAware.installCodeAndGas targetProgram gas initial)
      (post := gasPost) (op := op) (arg := arg)
      (tailTrace := tailTrace) (result := result)
      (hDecode hGasAtLeast hGasFits)
      (hStepChecks hGasAtLeast hGasFits)
      (hOpenStep hGasAtLeast hGasFits)
      hStepOk hNoHalt
      (hRest hGasAtLeast hGasFits hRelPost)

theorem openXReplayAbove_current_success_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {targetResult : Assembly.StepResult}
    (hDecode :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.decode
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial).executionEnv.code
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial).pc =
              some (op, arg))
    (hStepChecks :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram)
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
              op)
    (hOpenStep :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            openStepAfterChecks tailFuel op arg
                (Assembly.GasAware.installCodeAndGas targetProgram gas initial) =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState
                      (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                      op)
                    op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState
                    (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                    op)))
    (hStep :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState
                      (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                      op)
                    op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState
                    (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                    op) =
                .ok gasPost ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost =
                some output ∧
              op ≠ EvmYul.Operation.REVERT ∧
              OpenXResultAgrees targetResult
                (EvmYul.EVM.ExecutionResult.success gasPost output)) :
    OpenXReplayAbove targetProgram initial [] targetResult
      (tailFuel + 1) gasBound := by
  intro gas hGasAtLeast hGasFits
  obtain
    ⟨gasPost, output, hStepOk, hHalt, hNotRevert, hAgree⟩ :=
    hStep hGasAtLeast hGasFits
  refine
    ⟨EvmYul.EVM.ExecutionResult.success gasPost output, ?_, hAgree⟩
  exact
    openX_current_success_of_openStepAfterChecks_done
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (state :=
        Assembly.GasAware.installCodeAndGas targetProgram gas initial)
      (post := gasPost) (op := op) (arg := arg) (output := output)
      (hDecode hGasAtLeast hGasFits)
      (hStepChecks hGasAtLeast hGasFits)
      (hOpenStep hGasAtLeast hGasFits)
      hStepOk hHalt hNotRevert

theorem openXReplayAbove_current_revert_of_openStepAfterChecks_done
    {targetProgram : Assembly.TargetProgram}
    {tailFuel gasBound : Nat}
    {initial : EVMState}
    {op : EVMOp} {arg : Option (Word × Nat)}
    {targetResult : Assembly.StepResult}
    (hDecode :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.decode
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial).executionEnv.code
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial).pc =
              some (op, arg))
    (hStepChecks :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            Assembly.GasAware.XStepChecksPass
              (Assembly.GasAware.validJumps targetProgram)
              (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
              op)
    (hOpenStep :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            openStepAfterChecks tailFuel op arg
                (Assembly.GasAware.installCodeAndGas targetProgram gas initial) =
              .done
                (EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState
                      (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                      op)
                    op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState
                    (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                    op)))
    (hStep :
      ∀ {gas : Nat},
        gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            ∃ gasPost : EVMState, ∃ output : ByteArray,
              EvmYul.EVM.step tailFuel
                  (EvmYul.EVM.C'
                    (Assembly.GasAware.memoryGasState
                      (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                      op)
                    op)
                  (some (op, arg))
                  (Assembly.GasAware.memoryGasState
                    (Assembly.GasAware.installCodeAndGas targetProgram gas initial)
                    op) =
                .ok gasPost ∧
              Assembly.GasAware.XStepHaltOutput? op gasPost =
                some output ∧
              op = EvmYul.Operation.REVERT ∧
              OpenXResultAgrees targetResult
                (EvmYul.EVM.ExecutionResult.revert gasPost.gasAvailable
                  output)) :
    OpenXReplayAbove targetProgram initial [] targetResult
      (tailFuel + 1) gasBound := by
  intro gas hGasAtLeast hGasFits
  obtain ⟨gasPost, output, hStepOk, hHalt, hRevert, hAgree⟩ :=
    hStep hGasAtLeast hGasFits
  refine
    ⟨EvmYul.EVM.ExecutionResult.revert gasPost.gasAvailable output,
      ?_, hAgree⟩
  exact
    openX_current_revert_of_openStepAfterChecks_done
      (fuel := tailFuel)
      (validJumps := Assembly.GasAware.validJumps targetProgram)
      (state :=
        Assembly.GasAware.installCodeAndGas targetProgram gas initial)
      (post := gasPost) (op := op) (arg := arg) (output := output)
      (hDecode hGasAtLeast hGasFits)
      (hStepChecks hGasAtLeast hGasFits)
      (hOpenStep hGasAtLeast hGasFits)
      hStepOk hHalt hRevert

end OpenGasAware
end Yul
end EvmCompiler
