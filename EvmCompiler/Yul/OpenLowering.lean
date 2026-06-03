import EvmCompiler.Yul.CompilerOpen
import EvmCompiler.Yul.OpenAssembly
import EvmCompiler.Functions.Preservation

/-!
Open external-call lowering boundary above assembly.

`OpenAssembly` now proves that selected source-open assembly traces replay
through compiled emitted blocks.  The remaining adjacent compiler theorem is
one layer higher: selected compiler-open function-block executions must lower to
selected source-open assembly executions on the same external trace.
-/

namespace EvmCompiler
namespace Yul
namespace OpenLowering

def CompilerPrimitiveEVMInstructionResultRel
    (baseStack : OpenExternal.Stack)
    (compilerResult : Objects.Source.State × List Word) :
    Assembly.StepResult → Prop
  | .running evmResult =>
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack compilerResult evmResult
  | .halted _ => False

namespace CompilerPrimitiveEVMInstructionResultRel

theorem running_incrPC
    {baseStack : OpenExternal.Stack}
    {compilerResult : Objects.Source.State × List Word}
    {evmResult : EvmYul.EVM.State}
    (hRel :
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack compilerResult evmResult) :
    CompilerPrimitiveEVMInstructionResultRel baseStack compilerResult
      (.running (EvmYul.EVM.State.incrPC evmResult)) := by
  rcases hRel with ⟨hShared, hStack⟩
  exact ⟨by simpa [EvmYul.EVM.State.incrPC] using hShared,
    by simpa [EvmYul.EVM.State.incrPC] using hStack⟩

end CompilerPrimitiveEVMInstructionResultRel

theorem callKind_ofEVMOperation_toBasicOp_toPrimOp
    (kind : OpenExternal.CallKind) :
    OpenExternal.CallKind.ofEVMOperation?
      kind.toBasicOp.toPrimOp.toEVM = some kind := by
  cases kind <;> rfl

theorem basicOp_eq_toBasicOp_of_callKind
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind) :
    op = kind.toBasicOp := by
  cases op <;> cases kind <;>
    simp [OpenExternal.CallKind.ofBasicOp?,
      OpenExternal.CallKind.toBasicOp] at hKind ⊢

theorem basicOp_toPrimOp_haltKind?_none (op : Structured.BasicOp) :
    (Assembly.Instr.prim op.toPrimOp).haltKind? = none := by
  cases op <;> rfl

theorem primStep_run_pc
    {step : Assembly.PrimStep} {state mid : EvmYul.EVM.State}
    (hRun : step.run state = .ok mid) :
    mid.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases step <;>
    simp [Assembly.PrimStep.run, EvmYul.EVM.execBinOp,
      EvmYul.EVM.execUnOp, EvmYul.EVM.execTriOp,
      EvmYul.EVM.executionEnvOp, EvmYul.EVM.unaryExecutionEnvOp,
      EvmYul.EVM.machineStateOp, EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.dup, EvmYul.swap] at hRun
  all_goals repeat (first | split at hRun | split)
  all_goals
    simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hRun
  all_goals
    first
    | exact False.elim (Except.noConfusion hRun)
    | cases hRun
      rfl

theorem basicOp_no_callCreate_step_pc
    {op : Structured.BasicOp} {state mid : EvmYul.EVM.State}
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (hStep : Structured.BasicOp.step op state = .ok mid) :
    mid.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  have hContinuing :
      ∃ step : Assembly.PrimStep,
        op.toPrimOp.continuingStep? = some step := by
    cases op <;>
      simp [Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.continuingStep?,
        Assembly.PrimOp.isCallCreate] at hNoCallCreate ⊢
  rcases hContinuing with ⟨step, hStepSome⟩
  have hRun : step.run state = .ok mid := by
    have hEq :=
      Assembly.PrimOp.step_eq_continuingStep_run hStepSome state
    simpa [Structured.BasicOp.step, Assembly.Target.stepInstr, hEq] using
      hStep
  exact primStep_run_pc hRun

theorem structuredCode_frameSafe_append
    {left right : Structured.Code}
    (hLeft : Structured.Code.FrameSafe left)
    (hRight : Structured.Code.FrameSafe right) :
    Structured.Code.FrameSafe (left ++ right) := by
  intro state final hidden hRun
  rw [Locals.SourceLowering.Assignment.structuredCode_run_append] at hRun ⊢
  cases hLeftRun : Structured.Code.run left state with
  | error err =>
      simp [hLeftRun] at hRun
  | ok mid =>
      simp [hLeftRun] at hRun
      have hLeftHidden := hLeft state mid hidden hLeftRun
      rw [hLeftHidden]
      exact hRight mid final hidden hRun

theorem structuredCode_frameSafe_push (value : Word) :
    Structured.Code.FrameSafe [Structured.BasicInstr.push value] := by
  intro state final hidden hRun
  unfold Structured.Code.run at hRun ⊢
  simp [Structured.BasicInstr.step, Assembly.Target.stepInstr] at hRun ⊢
  cases hRun
  simp [Structured.Code.run, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, EvmYul.Stack.push]

theorem structuredCode_frameSafe_nil :
    Structured.Code.FrameSafe [] := by
  intro state final hidden hRun
  simp [Structured.Code.run] at hRun ⊢
  cases hRun
  simp

theorem evmYul_dup_append_hidden
    {n : Nat} {state final : EvmYul.EVM.State}
    {hidden : EvmYul.Stack Word}
    (hRun : EvmYul.dup n state = .ok final) :
    EvmYul.dup n { state with stack := state.stack ++ hidden } =
      .ok { final with stack := final.stack ++ hidden } := by
  unfold EvmYul.dup at hRun ⊢
  by_cases hLe : n ≤ state.stack.length
  · have hLen : (state.stack.take n).length = n := by
      simp [List.length_take, Nat.min_eq_left hLe]
    have hTakeAppend :
        (state.stack ++ hidden).take n = state.stack.take n :=
      List.take_append_of_le_length hLe
    have hLenAppend :
        ((state.stack ++ hidden).take n).length = n := by
      simp [hTakeAppend, hLen]
    simp [hLen, hTakeAppend] at hRun ⊢
    cases hRun
    simp [
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · have hLen : ¬ (state.stack.take n).length = n := by
      have hLt : state.stack.length < n := Nat.lt_of_not_ge hLe
      simp [List.length_take, Nat.min_eq_right (Nat.le_of_lt hLt)]
      omega
    simp [hLe] at hRun

theorem evmYul_swap_append_hidden
    {n : Nat} {state final : EvmYul.EVM.State}
    {hidden : EvmYul.Stack Word}
    (hRun : EvmYul.swap n state = .ok final) :
    EvmYul.swap n { state with stack := state.stack ++ hidden } =
      .ok { final with stack := final.stack ++ hidden } := by
  unfold EvmYul.swap at hRun ⊢
  by_cases hLe : n + 1 ≤ state.stack.length
  · have hLen : (state.stack.take (n + 1)).length = n + 1 := by
      simp [List.length_take, Nat.min_eq_left hLe]
    have hTakeAppend :
        (state.stack ++ hidden).take (n + 1) =
          state.stack.take (n + 1) :=
      List.take_append_of_le_length hLe
    have hDropAppend :
        (state.stack ++ hidden).drop (n + 1) =
          state.stack.drop (n + 1) ++ hidden :=
      List.drop_append_of_le_length hLe
    have hLenAppend :
        ((state.stack ++ hidden).take (n + 1)).length = n + 1 := by
      simp [hTakeAppend, hLen]
    simp [hLen, hTakeAppend, hDropAppend] at hRun ⊢
    cases hRun
    simp [
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, List.append_assoc]
  · have hLen : ¬ (state.stack.take (n + 1)).length = n + 1 := by
      have hLt : state.stack.length < n + 1 := Nat.lt_of_not_ge hLe
      simp [List.length_take, Nat.min_eq_right (Nat.le_of_lt hLt)]
      omega
    simp [hLe] at hRun

theorem structuredCode_frameSafe_basicOp_dup
    {op : Structured.BasicOp} {n : Nat}
    (hStep : op.toPrimOp.continuingStep? = some (.dup n)) :
    Structured.Code.FrameSafe [Structured.BasicInstr.op op] := by
  intro state final hidden hRun
  have hRunBind :
      (do
        let state' ← EvmYul.dup n state
        Except.ok state') = .ok final := by
    simpa [Structured.Code.run, Structured.BasicInstr.step,
      Structured.BasicOp.step, Assembly.Target.stepInstr,
      Assembly.PrimOp.step_eq_continuingStep_run hStep,
      Assembly.PrimStep.run] using hRun
  have hRunDup : EvmYul.dup n state = .ok final := by
    cases hDup : EvmYul.dup n state with
    | error err =>
        simp [hDup] at hRunBind
    | ok mid =>
        simp [hDup] at hRunBind
        cases hRunBind
        rfl
  have hHidden := evmYul_dup_append_hidden (hidden := hidden) hRunDup
  have hHiddenBind :
      (do
        let state' ← EvmYul.dup n { state with stack := state.stack ++ hidden }
        Except.ok state') =
        .ok { final with stack := final.stack ++ hidden } := by
    simp [hHidden]
  simpa [Structured.Code.run, Structured.BasicInstr.step,
    Structured.BasicOp.step, Assembly.Target.stepInstr,
    Assembly.PrimOp.step_eq_continuingStep_run hStep,
    Assembly.PrimStep.run] using hHiddenBind

theorem structuredCode_frameSafe_basicOp_swap
    {op : Structured.BasicOp} {n : Nat}
    (hStep : op.toPrimOp.continuingStep? = some (.swap n)) :
    Structured.Code.FrameSafe [Structured.BasicInstr.op op] := by
  intro state final hidden hRun
  have hRunBind :
      (do
        let state' ← EvmYul.swap n state
        Except.ok state') = .ok final := by
    simpa [Structured.Code.run, Structured.BasicInstr.step,
      Structured.BasicOp.step, Assembly.Target.stepInstr,
      Assembly.PrimOp.step_eq_continuingStep_run hStep,
      Assembly.PrimStep.run] using hRun
  have hRunSwap : EvmYul.swap n state = .ok final := by
    cases hSwap : EvmYul.swap n state with
    | error err =>
        simp [hSwap] at hRunBind
    | ok mid =>
        simp [hSwap] at hRunBind
        cases hRunBind
        rfl
  have hHidden := evmYul_swap_append_hidden (hidden := hidden) hRunSwap
  have hHiddenBind :
      (do
        let state' ← EvmYul.swap n { state with stack := state.stack ++ hidden }
        Except.ok state') =
        .ok { final with stack := final.stack ++ hidden } := by
    simp [hHidden]
  simpa [Structured.Code.run, Structured.BasicInstr.step,
    Structured.BasicOp.step, Assembly.Target.stepInstr,
    Assembly.PrimOp.step_eq_continuingStep_run hStep,
    Assembly.PrimStep.run] using hHiddenBind

theorem structuredCode_frameSafe_stackOp_dup?
    {n : Nat} {op : Structured.BasicOp}
    (hDup : Locals.StackOp.dup? n = some op) :
    Structured.Code.FrameSafe [Structured.BasicInstr.op op] := by
  match n with
  | 0 =>
      simp [Locals.StackOp.dup?] at hDup
  | 1 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 2 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 3 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 4 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 5 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 6 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 7 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 8 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 9 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 10 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 11 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 12 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 13 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 14 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 15 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | 16 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact structuredCode_frameSafe_basicOp_dup (by rfl)
  | k + 17 =>
      simp [Locals.StackOp.dup?] at hDup

theorem structuredCode_frameSafe_stackOp_swap?
    {n : Nat} {op : Structured.BasicOp}
    (hSwap : Locals.StackOp.swap? n = some op) :
    Structured.Code.FrameSafe [Structured.BasicInstr.op op] := by
  match n with
  | 0 =>
      simp [Locals.StackOp.swap?] at hSwap
  | 1 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 2 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 3 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 4 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 5 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 6 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 7 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 8 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 9 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 10 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 11 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 12 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 13 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 14 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 15 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | 16 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact structuredCode_frameSafe_basicOp_swap (by rfl)
  | k + 17 =>
      simp [Locals.StackOp.swap?] at hSwap

theorem structuredCode_frameSafe_swapRestoreUpTo?
    {n : Nat} {code : Structured.Code}
    (hCode : Locals.Ctx.swapRestoreUpTo? n = some code) :
    Structured.Code.FrameSafe code := by
  induction n generalizing code with
  | zero =>
      simp [Locals.Ctx.swapRestoreUpTo?] at hCode
      cases hCode
      exact structuredCode_frameSafe_nil
  | succ n ih =>
      simp [Locals.Ctx.swapRestoreUpTo?] at hCode
      cases hRest : Locals.Ctx.swapRestoreUpTo? n with
      | none =>
          simp [hRest] at hCode
      | some rest =>
          cases hSwap : Locals.StackOp.swap? (n + 1) with
          | none =>
              simp [hRest, hSwap] at hCode
          | some op =>
              simp [hRest, hSwap] at hCode
              cases hCode
              exact
                structuredCode_frameSafe_append
                  (ih hRest)
                  (structuredCode_frameSafe_stackOp_swap? hSwap)

theorem structuredCode_frameSafe_cleanupOnePreserving?
    {temps : Nat} {code : Structured.Code}
    (hCode : Locals.Ctx.cleanupOnePreserving? temps = some code) :
    Structured.Code.FrameSafe code := by
  cases temps with
  | zero =>
      simp [Locals.Ctx.cleanupOnePreserving?] at hCode
      cases hCode
      exact Structured.Preservation.Code.pop_frameSafe
  | succ temps =>
      simp [Locals.Ctx.cleanupOnePreserving?] at hCode
      cases hSwap : Locals.StackOp.swap? (temps + 1) with
      | none =>
          simp [hSwap] at hCode
      | some op =>
          cases hRestore : Locals.Ctx.swapRestoreUpTo? temps with
          | none =>
              simp [hSwap, hRestore] at hCode
          | some restore =>
              simp [hSwap, hRestore] at hCode
              cases hCode
              exact
                structuredCode_frameSafe_append
                  (structuredCode_frameSafe_append
                    (structuredCode_frameSafe_stackOp_swap? hSwap)
                    Structured.Preservation.Code.pop_frameSafe)
                  (structuredCode_frameSafe_swapRestoreUpTo? hRestore)

theorem structuredCode_frameSafe_cleanupManyPreserving?
    {count temps : Nat} {code : Structured.Code}
    (hCode : Locals.Ctx.cleanupManyPreserving? count temps = some code) :
    Structured.Code.FrameSafe code := by
  induction count generalizing code with
  | zero =>
      simp [Locals.Ctx.cleanupManyPreserving?] at hCode
      cases hCode
      exact structuredCode_frameSafe_nil
  | succ count ih =>
      simp [Locals.Ctx.cleanupManyPreserving?] at hCode
      cases hHead : Locals.Ctx.cleanupOnePreserving? temps with
      | none =>
          simp [hHead] at hCode
      | some head =>
          cases hTail : Locals.Ctx.cleanupManyPreserving? count temps with
          | none =>
              simp [hHead, hTail] at hCode
          | some tail =>
              simp [hHead, hTail] at hCode
              cases hCode
              exact
                structuredCode_frameSafe_append
                  (structuredCode_frameSafe_cleanupOnePreserving? hHead)
                  (ih hTail)

theorem structuredCode_frameSafe_cleanupToPreserving?
    {ctx : Locals.Ctx} {preserve targetDepth : Nat}
    {code : Structured.Code}
    (hCode : ctx.cleanupToPreserving? preserve targetDepth = some code) :
    Structured.Code.FrameSafe code := by
  unfold Locals.Ctx.cleanupToPreserving? at hCode
  by_cases hLe : targetDepth ≤ ctx.layout.length
  · simp [hLe] at hCode
    exact structuredCode_frameSafe_cleanupManyPreserving? hCode
  · simp [hLe] at hCode

theorem structuredBasicInstr_controlSafe_basicOp_dup
    {op : Structured.BasicOp} {n : Nat}
    (hStep : op.toPrimOp.continuingStep? = some (.dup n)) :
    Structured.Preservation.BasicInstr.ControlSafe (.op op) := by
  intro source target source' hEq hInstrStep
  have hRunDup : EvmYul.dup n source = .ok source' := by
    simpa [Structured.BasicInstr.step, Structured.BasicOp.step,
      Assembly.Target.stepInstr,
      Assembly.PrimOp.step_eq_continuingStep_run hStep,
      Assembly.PrimStep.run] using hInstrStep
  have hStack := Structured.Preservation.stack_eq_of_eraseControl_eq hEq
  unfold EvmYul.dup at hRunDup
  by_cases hLe : n ≤ source.stack.length
  · simp [hLe] at hRunDup
    cases hRunDup
    have hTake : target.stack.take n = source.stack.take n := by
      rw [hStack]
    let target' : EvmYul.EVM.State :=
      target.replaceStackAndIncrPC
        ((source.stack.take n).getLast?.getD default :: target.stack)
    refine ⟨target', ?_, ?_⟩
    · have hTargetDup : EvmYul.dup n target = .ok target' := by
        unfold target'
        unfold EvmYul.dup
        simp [hTake, hLe]
      simpa [Structured.BasicInstr.step, Structured.BasicOp.step,
        Assembly.Target.stepInstr,
        Assembly.PrimOp.step_eq_continuingStep_run hStep,
        Assembly.PrimStep.run] using hTargetDup
    · exact
        Structured.Preservation.eraseControl_replaceStackAndIncrPC_of_eq
          hEq (by rw [hStack])
  · simp [hLe] at hRunDup

theorem structuredBasicInstr_stepPC_basicOp_dup
    {op : Structured.BasicOp} {n : Nat}
    (hStep : op.toPrimOp.continuingStep? = some (.dup n)) :
    Structured.Preservation.BasicInstr.StepPC (.op op) := by
  intro state final hInstrStep
  have hRunDup : EvmYul.dup n state = .ok final := by
    simpa [Structured.BasicInstr.step, Structured.BasicOp.step,
      Assembly.Target.stepInstr,
      Assembly.PrimOp.step_eq_continuingStep_run hStep,
      Assembly.PrimStep.run] using hInstrStep
  have hRunPrim : (Assembly.PrimStep.dup n).run state = .ok final := by
    simpa [Assembly.PrimStep.run] using hRunDup
  have hPc := primStep_run_pc hRunPrim
  simpa [Structured.BasicInstr.toAssembly, Assembly.Instr.byteSize] using hPc

theorem structuredBasicInstr_runnerSafe_basicOp_dup
    {op : Structured.BasicOp} {n : Nat}
    (hStep : op.toPrimOp.continuingStep? = some (.dup n)) :
    Structured.Preservation.BasicInstr.RunnerSafe (.op op) := by
  exact
    ⟨structuredBasicInstr_controlSafe_basicOp_dup hStep,
      structuredBasicInstr_stepPC_basicOp_dup hStep⟩

theorem structuredBasicInstr_controlSafe_basicOp_swap
    {op : Structured.BasicOp} {n : Nat}
    (hStep : op.toPrimOp.continuingStep? = some (.swap n)) :
    Structured.Preservation.BasicInstr.ControlSafe (.op op) := by
  intro source target source' hEq hInstrStep
  have hRunSwap : EvmYul.swap n source = .ok source' := by
    simpa [Structured.BasicInstr.step, Structured.BasicOp.step,
      Assembly.Target.stepInstr,
      Assembly.PrimOp.step_eq_continuingStep_run hStep,
      Assembly.PrimStep.run] using hInstrStep
  have hStack := Structured.Preservation.stack_eq_of_eraseControl_eq hEq
  unfold EvmYul.swap at hRunSwap
  by_cases hLe : n + 1 ≤ source.stack.length
  · simp [hLe] at hRunSwap
    cases hRunSwap
    have hTake : target.stack.take (n + 1) =
        source.stack.take (n + 1) := by
      rw [hStack]
    have hDrop : target.stack.drop (n + 1) =
        source.stack.drop (n + 1) := by
      rw [hStack]
    let target' : EvmYul.EVM.State :=
      target.replaceStackAndIncrPC
        ((source.stack.take (n + 1)).getLast?.getD default ::
          ((source.stack.take (n + 1)).tail!.dropLast ++
            (source.stack.take (n + 1)).head! ::
            target.stack.drop (n + 1)))
    refine ⟨target', ?_, ?_⟩
    · have hTargetSwap : EvmYul.swap n target = .ok target' := by
        unfold target'
        unfold EvmYul.swap
        simp [hTake, hDrop, hLe, List.append_assoc]
      simpa [Structured.BasicInstr.step, Structured.BasicOp.step,
        Assembly.Target.stepInstr,
        Assembly.PrimOp.step_eq_continuingStep_run hStep,
        Assembly.PrimStep.run] using hTargetSwap
    · exact
        Structured.Preservation.eraseControl_replaceStackAndIncrPC_of_eq
          hEq (by rw [hStack])
  · simp [hLe] at hRunSwap

theorem structuredBasicInstr_stepPC_basicOp_swap
    {op : Structured.BasicOp} {n : Nat}
    (hStep : op.toPrimOp.continuingStep? = some (.swap n)) :
    Structured.Preservation.BasicInstr.StepPC (.op op) := by
  intro state final hInstrStep
  have hRunSwap : EvmYul.swap n state = .ok final := by
    simpa [Structured.BasicInstr.step, Structured.BasicOp.step,
      Assembly.Target.stepInstr,
      Assembly.PrimOp.step_eq_continuingStep_run hStep,
      Assembly.PrimStep.run] using hInstrStep
  have hRunPrim : (Assembly.PrimStep.swap n).run state = .ok final := by
    simpa [Assembly.PrimStep.run] using hRunSwap
  have hPc := primStep_run_pc hRunPrim
  simpa [Structured.BasicInstr.toAssembly, Assembly.Instr.byteSize] using hPc

theorem structuredBasicInstr_runnerSafe_basicOp_swap
    {op : Structured.BasicOp} {n : Nat}
    (hStep : op.toPrimOp.continuingStep? = some (.swap n)) :
    Structured.Preservation.BasicInstr.RunnerSafe (.op op) := by
  exact
    ⟨structuredBasicInstr_controlSafe_basicOp_swap hStep,
      structuredBasicInstr_stepPC_basicOp_swap hStep⟩

theorem structuredCode_runnerSafe_append
    {left right : Structured.Code}
    (hLeft : Structured.Preservation.Code.RunnerSafe left)
    (hRight : Structured.Preservation.Code.RunnerSafe right) :
    Structured.Preservation.Code.RunnerSafe (left ++ right) := by
  induction hLeft with
  | nil =>
      simpa using hRight
  | cons hInstr _hRest ih =>
      simpa using
        Structured.Preservation.Code.RunnerSafe.cons hInstr ih

theorem structuredCode_runnerSafe_push (value : Word) :
    Structured.Preservation.Code.RunnerSafe
      [Structured.BasicInstr.push value] := by
  exact
    Structured.Preservation.Code.RunnerSafe.cons
      (Structured.Preservation.BasicInstr.push_runnerSafe value)
      Structured.Preservation.Code.RunnerSafe.nil

theorem structuredCode_runnerSafe_nil :
    Structured.Preservation.Code.RunnerSafe [] := by
  exact Structured.Preservation.Code.RunnerSafe.nil

theorem structuredCode_runnerSafe_stackOp_dup?
    {n : Nat} {op : Structured.BasicOp}
    (hDup : Locals.StackOp.dup? n = some op) :
    Structured.Preservation.Code.RunnerSafe [Structured.BasicInstr.op op] := by
  match n with
  | 0 =>
      simp [Locals.StackOp.dup?] at hDup
  | 1 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 2 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 3 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 4 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 5 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 6 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 7 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 8 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 9 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 10 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 11 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 12 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 13 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 14 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 15 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 16 =>
      simp [Locals.StackOp.dup?] at hDup
      cases hDup
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_dup (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | k + 17 =>
      simp [Locals.StackOp.dup?] at hDup

theorem structuredCode_runnerSafe_stackOp_swap?
    {n : Nat} {op : Structured.BasicOp}
    (hSwap : Locals.StackOp.swap? n = some op) :
    Structured.Preservation.Code.RunnerSafe [Structured.BasicInstr.op op] := by
  match n with
  | 0 =>
      simp [Locals.StackOp.swap?] at hSwap
  | 1 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 2 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 3 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 4 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 5 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 6 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 7 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 8 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 9 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 10 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 11 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 12 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 13 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 14 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 15 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | 16 =>
      simp [Locals.StackOp.swap?] at hSwap
      cases hSwap
      exact Structured.Preservation.Code.RunnerSafe.cons
        (structuredBasicInstr_runnerSafe_basicOp_swap (by rfl))
        Structured.Preservation.Code.RunnerSafe.nil
  | k + 17 =>
      simp [Locals.StackOp.swap?] at hSwap

theorem structuredCode_runnerSafe_swapRestoreUpTo?
    {n : Nat} {code : Structured.Code}
    (hCode : Locals.Ctx.swapRestoreUpTo? n = some code) :
    Structured.Preservation.Code.RunnerSafe code := by
  induction n generalizing code with
  | zero =>
      simp [Locals.Ctx.swapRestoreUpTo?] at hCode
      cases hCode
      exact structuredCode_runnerSafe_nil
  | succ n ih =>
      simp [Locals.Ctx.swapRestoreUpTo?] at hCode
      cases hRest : Locals.Ctx.swapRestoreUpTo? n with
      | none =>
          simp [hRest] at hCode
      | some rest =>
          cases hSwap : Locals.StackOp.swap? (n + 1) with
          | none =>
              simp [hRest, hSwap] at hCode
          | some op =>
              simp [hRest, hSwap] at hCode
              cases hCode
              exact
                structuredCode_runnerSafe_append
                  (ih hRest)
                  (structuredCode_runnerSafe_stackOp_swap? hSwap)

theorem structuredCode_runnerSafe_cleanupOnePreserving?
    {temps : Nat} {code : Structured.Code}
    (hCode : Locals.Ctx.cleanupOnePreserving? temps = some code) :
    Structured.Preservation.Code.RunnerSafe code := by
  cases temps with
  | zero =>
      simp [Locals.Ctx.cleanupOnePreserving?] at hCode
      cases hCode
      exact Structured.Preservation.Code.pop_runnerSafe
  | succ temps =>
      simp [Locals.Ctx.cleanupOnePreserving?] at hCode
      cases hSwap : Locals.StackOp.swap? (temps + 1) with
      | none =>
          simp [hSwap] at hCode
      | some op =>
          cases hRestore : Locals.Ctx.swapRestoreUpTo? temps with
          | none =>
              simp [hSwap, hRestore] at hCode
          | some restore =>
              simp [hSwap, hRestore] at hCode
              cases hCode
              exact
                structuredCode_runnerSafe_append
                  (structuredCode_runnerSafe_append
                    (structuredCode_runnerSafe_stackOp_swap? hSwap)
                    Structured.Preservation.Code.pop_runnerSafe)
                  (structuredCode_runnerSafe_swapRestoreUpTo? hRestore)

theorem structuredCode_runnerSafe_cleanupManyPreserving?
    {count temps : Nat} {code : Structured.Code}
    (hCode : Locals.Ctx.cleanupManyPreserving? count temps = some code) :
    Structured.Preservation.Code.RunnerSafe code := by
  induction count generalizing code with
  | zero =>
      simp [Locals.Ctx.cleanupManyPreserving?] at hCode
      cases hCode
      exact structuredCode_runnerSafe_nil
  | succ count ih =>
      simp [Locals.Ctx.cleanupManyPreserving?] at hCode
      cases hHead : Locals.Ctx.cleanupOnePreserving? temps with
      | none =>
          simp [hHead] at hCode
      | some head =>
          cases hTail : Locals.Ctx.cleanupManyPreserving? count temps with
          | none =>
              simp [hHead, hTail] at hCode
          | some tail =>
              simp [hHead, hTail] at hCode
              cases hCode
              exact
                structuredCode_runnerSafe_append
                  (structuredCode_runnerSafe_cleanupOnePreserving? hHead)
                  (ih hTail)

theorem structuredCode_runnerSafe_cleanupToPreserving?
    {ctx : Locals.Ctx} {preserve targetDepth : Nat}
    {code : Structured.Code}
    (hCode : ctx.cleanupToPreserving? preserve targetDepth = some code) :
    Structured.Preservation.Code.RunnerSafe code := by
  unfold Locals.Ctx.cleanupToPreserving? at hCode
  by_cases hLe : targetDepth ≤ ctx.layout.length
  · simp [hLe] at hCode
    exact structuredCode_runnerSafe_cleanupManyPreserving? hCode
  · simp [hLe] at hCode

theorem localsExprSeq_compileCode_mpr {ctx : Locals.Ctx} {offset : Nat}
    {n m : Nat} (h : m = n) (exprs : Locals.ExprSeq n) :
    Locals.ExprSeq.compileCode ctx offset
        (Eq.mpr (congrArg Locals.ExprSeq h) exprs) =
      Locals.ExprSeq.compileCode ctx offset exprs := by
  cases h
  rfl

theorem structuredCode_frameSafe_returnExprs_compileCode
    {ctx : Locals.Ctx} {offset : Nat} :
    ∀ {returns : List Name} {code : Structured.Code},
      Locals.ExprSeq.compileCode ctx offset
        (Functions.Lower.returnExprs returns) = some code →
      Structured.Code.FrameSafe code := by
  intro returns
  induction returns generalizing offset with
  | nil =>
      intro code hCompile
      simp [Functions.Lower.returnExprs, Locals.ExprSeq.compileCode]
        at hCompile
      cases hCompile
      exact structuredCode_frameSafe_nil
  | cons name rest ih =>
      intro code hCompile
      unfold Functions.Lower.returnExprs at hCompile
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons (.var name) (Functions.Lower.returnExprs rest)
      have hLen : rest.length + 1 = 1 + rest.length := by omega
      change
        Locals.ExprSeq.compileCode ctx offset
            (Eq.mpr (congrArg Locals.ExprSeq hLen) exprs) =
          some code at hCompile
      rw [localsExprSeq_compileCode_mpr hLen exprs] at hCompile
      simp [exprs, Locals.ExprSeq.compileCode, Locals.Expr.compileCode]
        at hCompile
      cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
      | none =>
          simp [hDepth] at hCompile
      | some depth =>
          cases hDup : Locals.StackOp.dup? (offset + depth) with
          | none =>
              simp [hDepth, hDup] at hCompile
          | some op =>
              cases hTail :
                  Locals.ExprSeq.compileCode ctx (offset + 1)
                    (Functions.Lower.returnExprs rest) with
              | none =>
                  simp [hDepth, hDup, hTail] at hCompile
              | some tailCode =>
                  simp [hDepth, hDup, hTail] at hCompile
                  cases hCompile
                  exact
                    structuredCode_frameSafe_append
                      (structuredCode_frameSafe_stackOp_dup? hDup)
                      (ih hTail)

theorem structuredCode_runnerSafe_returnExprs_compileCode
    {ctx : Locals.Ctx} {offset : Nat} :
    ∀ {returns : List Name} {code : Structured.Code},
      Locals.ExprSeq.compileCode ctx offset
        (Functions.Lower.returnExprs returns) = some code →
      Structured.Preservation.Code.RunnerSafe code := by
  intro returns
  induction returns generalizing offset with
  | nil =>
      intro code hCompile
      simp [Functions.Lower.returnExprs, Locals.ExprSeq.compileCode]
        at hCompile
      cases hCompile
      exact structuredCode_runnerSafe_nil
  | cons name rest ih =>
      intro code hCompile
      unfold Functions.Lower.returnExprs at hCompile
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons (.var name) (Functions.Lower.returnExprs rest)
      have hLen : rest.length + 1 = 1 + rest.length := by omega
      change
        Locals.ExprSeq.compileCode ctx offset
            (Eq.mpr (congrArg Locals.ExprSeq hLen) exprs) =
          some code at hCompile
      rw [localsExprSeq_compileCode_mpr hLen exprs] at hCompile
      simp [exprs, Locals.ExprSeq.compileCode, Locals.Expr.compileCode]
        at hCompile
      cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
      | none =>
          simp [hDepth] at hCompile
      | some depth =>
          cases hDup : Locals.StackOp.dup? (offset + depth) with
          | none =>
              simp [hDepth, hDup] at hCompile
          | some op =>
              cases hTail :
                  Locals.ExprSeq.compileCode ctx (offset + 1)
                    (Functions.Lower.returnExprs rest) with
              | none =>
                  simp [hDepth, hDup, hTail] at hCompile
              | some tailCode =>
                  simp [hDepth, hDup, hTail] at hCompile
                  cases hCompile
                  exact
                    structuredCode_runnerSafe_append
                      (structuredCode_runnerSafe_stackOp_dup? hDup)
                      (ih hTail)

theorem structuredCode_noCall_returnExprs_compileCode
    {ctx : Locals.Ctx} {offset : Nat} {returns : List Name}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset
        (Functions.Lower.returnExprs returns) = some code) :
    Structured.Code.usesCallCreate code = false :=
  Locals.CompilerFacts.ExprSeq.compileCode_noCallCreate ctx offset
    (Functions.Lower.returnExprs returns)
    (Functions.CompilerFacts.Lower.returnExprs_noCallCreate returns)
    hCompile

theorem evmOpenCall?_resume_pc
    {state : EvmYul.EVM.State} {kind : OpenExternal.CallKind}
    {call : OpenExternal.OpenCall EvmYul.EVM.State}
    (hCall :
      OpenExternal.CallKind.evmOpenCall? state kind = some call)
    (response : OpenExternal.CallResponse) :
    (call.resume response).pc = state.pc := by
  unfold OpenExternal.CallKind.evmOpenCall? at hCall
  cases hSite : kind.evmCallSite? state with
  | none =>
      simp [hSite] at hCall
  | some pair =>
      rcases pair with ⟨rest, site⟩
      simp [hSite] at hCall
      cases hCall
      rfl

def BasicOpOpenSupported (op : Structured.BasicOp) : Prop :=
  op.toPrimOp.isCallCreate = false ∨
    ∃ kind : OpenExternal.CallKind,
      OpenExternal.CallKind.ofBasicOp? op = some kind

mutual
  def LocalsExprOpenSupported {results : Nat} :
      Locals.Expr results → Prop
    | .lit _value => True
    | .var _name => True
    | .code _code => False
    | .prim op args =>
        LocalsExprSeqOpenSupported args ∧ BasicOpOpenSupported op

  def LocalsExprSeqOpenSupported {results : Nat} :
      Locals.ExprSeq results → Prop
    | .nil => True
    | .cons head tail =>
        LocalsExprOpenSupported head ∧
          LocalsExprSeqOpenSupported tail
end

theorem localsExprSeqOpenSupported_mpr {n m : Nat} (h : m = n)
    (exprs : Locals.ExprSeq n) :
    LocalsExprSeqOpenSupported
        (Eq.mpr (congrArg Locals.ExprSeq h) exprs) ↔
      LocalsExprSeqOpenSupported exprs := by
  cases h
  rfl

def FunctionsArgListOpenSupported :
    List (Functions.Expr 1) → Prop
  | [] => True
  | arg :: rest =>
      LocalsExprOpenSupported arg ∧
        FunctionsArgListOpenSupported rest

theorem functions_argExprs_openSupported :
    ∀ {args : List (Functions.Expr 1)},
      FunctionsArgListOpenSupported args →
        LocalsExprSeqOpenSupported (Functions.Lower.argExprs args)
  | [], _hSupported => by
      simp [Functions.Lower.argExprs, LocalsExprSeqOpenSupported]
  | arg :: rest, hSupported => by
      rcases hSupported with ⟨hArg, hRest⟩
      have hTail :
          LocalsExprSeqOpenSupported
            (Functions.Lower.argExprs rest) :=
        functions_argExprs_openSupported (args := rest) hRest
      rw [Functions.Lower.argExprs]
      rw [localsExprSeqOpenSupported_mpr (by simp [Nat.add_comm])
        (Locals.ExprSeq.cons arg (Functions.Lower.argExprs rest))]
      simp [LocalsExprSeqOpenSupported, hArg, hTail]

theorem basicOpOpenSupported_of_no_callCreate
    {op : Structured.BasicOp}
    (hNoCallCreate : op.toPrimOp.isCallCreate = false) :
    BasicOpOpenSupported op :=
  Or.inl hNoCallCreate

mutual
  theorem localsExprOpenSupported_of_sourceOwned_no_callCreate :
      ∀ {results : Nat} {expr : Locals.Expr results},
        Locals.Source.Expr.SourceOwned expr →
        expr.usesCallCreate = false →
          LocalsExprOpenSupported expr := by
    intro results expr hOwned hNoCallCreate
    cases expr with
    | lit value =>
        simp [LocalsExprOpenSupported]
    | var name =>
        simp [LocalsExprOpenSupported]
    | code code =>
        simp [Locals.Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        simp [Locals.Source.Expr.SourceOwned] at hOwned
        have hParts :
            args.usesCallCreate = false ∧
              op.toPrimOp.isCallCreate = false := by
          simpa [Locals.Expr.usesCallCreate] using hNoCallCreate
        exact
          ⟨localsExprSeqOpenSupported_of_sourceOwned_no_callCreate
              hOwned hParts.1,
            basicOpOpenSupported_of_no_callCreate hParts.2⟩

  theorem localsExprSeqOpenSupported_of_sourceOwned_no_callCreate :
      ∀ {results : Nat} {exprs : Locals.ExprSeq results},
        Locals.Source.ExprSeq.SourceOwned exprs →
        exprs.usesCallCreate = false →
          LocalsExprSeqOpenSupported exprs := by
    intro results exprs hOwned hNoCallCreate
    cases exprs with
    | nil =>
        simp [LocalsExprSeqOpenSupported]
    | @cons left right head tail =>
        simp [Locals.Source.ExprSeq.SourceOwned] at hOwned
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        have hParts :
            head.usesCallCreate = false ∧
              tail.usesCallCreate = false := by
          simpa [Locals.ExprSeq.usesCallCreate] using hNoCallCreate
        exact
          ⟨localsExprOpenSupported_of_sourceOwned_no_callCreate
              hHeadOwned hParts.1,
            localsExprSeqOpenSupported_of_sourceOwned_no_callCreate
              hTailOwned hParts.2⟩
end

theorem codeSegment_instrAtPc_start_cons
    {asm : Assembly.Program} {instr : Assembly.Instr}
    {suffix : Assembly.Program}
    (segment :
      Structured.Preservation.CodeSegment asm (instr :: suffix)) :
    Assembly.Program.instrAtPc asm
      (Structured.Preservation.CodeSegment.startPc segment).toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc segment).toNat,
            instr) := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  subst asm
  have hFitsStart :
      (Assembly.Program.pcAfter pre).toNat =
        Assembly.Program.byteLength pre :=
    Structured.Preservation.AssemblyProgram.PCFitsFrom.start hFits
  unfold Structured.Preservation.CodeSegment.startPc
  unfold Assembly.Program.instrAtPc
  rw [hFitsStart]
  simpa [List.append_assoc] using
    Assembly.Program.instrAtPcFrom_append_boundary_cons
      pre (suffix ++ post) instr 0

theorem codeSegment_right_startPc_eq_left_fallthroughPc
    {asm first second : Assembly.Program}
    (segment :
      Structured.Preservation.CodeSegment asm (first ++ second)) :
    Structured.Preservation.CodeSegment.startPc
        (Structured.Preservation.CodeSegment.right segment) =
      Structured.Preservation.CodeSegment.fallthroughPc
        (Structured.Preservation.CodeSegment.left segment) := by
  rfl

theorem structuredBlock_compileFromCtx_append_code_eq
    (ctx : Structured.CompileContext) (supply : Structured.LabelSupply)
    (left right : List Structured.Stmt) :
    (Structured.Block.compileFromCtx
        { stmts := left ++ right } ctx supply).code =
      (Structured.Block.compileFromCtx { stmts := left } ctx supply).code ++
        (Structured.Block.compileFromCtx { stmts := right } ctx
          (Structured.Block.compileFromCtx
            { stmts := left } ctx supply).next).code := by
  induction left generalizing supply with
  | nil =>
      simp [Structured.Block.compileFromCtx]
  | cons stmt rest ih =>
      simp [Structured.Block.compileFromCtx, Structured.CompileResult.append,
        ih, List.append_assoc]

theorem codeSegment_structuredBlock_append_split
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {left right : List Structured.Stmt}
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := left ++ right } ctx supply).code) :
    ∃ leftSegment :
        Structured.Preservation.CodeSegment asm
          (Structured.Block.compileFromCtx
            { stmts := left } ctx supply).code,
      ∃ rightSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx
              { stmts := right } ctx
              (Structured.Block.compileFromCtx
                { stmts := left } ctx supply).next).code,
        Structured.Preservation.CodeSegment.startPc leftSegment =
          Structured.Preservation.CodeSegment.startPc segment ∧
        Structured.Preservation.CodeSegment.startPc rightSegment =
          Structured.Preservation.CodeSegment.fallthroughPc leftSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc rightSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts := left ++ right } ctx supply).code =
        (Structured.Block.compileFromCtx
          { stmts := left } ctx supply).code ++
          (Structured.Block.compileFromCtx { stmts := right } ctx
            (Structured.Block.compileFromCtx
              { stmts := left } ctx supply).next).code :=
    structuredBlock_compileFromCtx_append_code_eq ctx supply left right
  let appendSegment :
      Structured.Preservation.CodeSegment asm
        ((Structured.Block.compileFromCtx
            { stmts := left } ctx supply).code ++
          (Structured.Block.compileFromCtx { stmts := right } ctx
            (Structured.Block.compileFromCtx
              { stmts := left } ctx supply).next).code) :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  let leftSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx { stmts := left } ctx supply).code :=
    Structured.Preservation.CodeSegment.left appendSegment
  let rightSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx { stmts := right } ctx
          (Structured.Block.compileFromCtx
            { stmts := left } ctx supply).next).code :=
    Structured.Preservation.CodeSegment.right appendSegment
  refine ⟨leftSegment, rightSegment, ?_, ?_, ?_⟩
  · simp [leftSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  · simpa [leftSegment, rightSegment] using
      codeSegment_right_startPc_eq_left_fallthroughPc appendSegment
  · simp [rightSegment, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq,
      List.append_assoc]

theorem structuredBlock_compileFromCtx_cons_code_eq
    (ctx : Structured.CompileContext) (supply : Structured.LabelSupply)
    (stmt : Structured.Stmt) (rest : List Structured.Stmt) :
    (Structured.Block.compileFromCtx
        { stmts := stmt :: rest } ctx supply).code =
      (Structured.Stmt.compileFromCtxCore stmt ctx supply).code ++
        (Structured.Block.compileFromCtx { stmts := rest } ctx
          (Structured.Stmt.compileFromCtxCore stmt ctx supply).next).code := by
  simp [Structured.Block.compileFromCtx,
    Structured.CompileResult.append]

theorem codeSegment_structuredBlock_cons_split
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {stmt : Structured.Stmt}
    {rest : List Structured.Stmt}
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := stmt :: rest } ctx supply).code) :
    ∃ headSegment :
        Structured.Preservation.CodeSegment asm
          (Structured.Stmt.compileFromCtxCore stmt ctx supply).code,
      ∃ tailSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx { stmts := rest } ctx
              (Structured.Stmt.compileFromCtxCore stmt ctx supply).next).code,
        Structured.Preservation.CodeSegment.startPc headSegment =
          Structured.Preservation.CodeSegment.startPc segment ∧
        Structured.Preservation.CodeSegment.startPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts := stmt :: rest } ctx supply).code =
        (Structured.Stmt.compileFromCtxCore stmt ctx supply).code ++
          (Structured.Block.compileFromCtx { stmts := rest } ctx
            (Structured.Stmt.compileFromCtxCore stmt ctx supply).next).code :=
    structuredBlock_compileFromCtx_cons_code_eq ctx supply stmt rest
  let appendSegment :
      Structured.Preservation.CodeSegment asm
        ((Structured.Stmt.compileFromCtxCore stmt ctx supply).code ++
          (Structured.Block.compileFromCtx { stmts := rest } ctx
            (Structured.Stmt.compileFromCtxCore stmt ctx supply).next).code) :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  let headSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Stmt.compileFromCtxCore stmt ctx supply).code :=
    Structured.Preservation.CodeSegment.left appendSegment
  let tailSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx { stmts := rest } ctx
          (Structured.Stmt.compileFromCtxCore stmt ctx supply).next).code :=
    Structured.Preservation.CodeSegment.right appendSegment
  refine ⟨headSegment, tailSegment, ?_, ?_, ?_⟩
  · simp [headSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  · simpa [headSegment, tailSegment] using
      codeSegment_right_startPc_eq_left_fallthroughPc appendSegment
  · simp [tailSegment, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq,
      List.append_assoc]

theorem codeSegment_fallthroughPc_empty
    {asm : Assembly.Program}
    (segment : Structured.Preservation.CodeSegment asm []) :
    Structured.Preservation.CodeSegment.fallthroughPc segment =
      Structured.Preservation.CodeSegment.startPc segment := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  simp [Structured.Preservation.CodeSegment.fallthroughPc,
    Structured.Preservation.CodeSegment.startPc]

theorem structuredBlock_compileFromCtx_code_cons_code_eq
    (ctx : Structured.CompileContext) (supply : Structured.LabelSupply)
    (code : Structured.Code) (rest : List Structured.Stmt) :
    (Structured.Block.compileFromCtx
        { stmts := Structured.Stmt.code code :: rest } ctx supply).code =
      code.toAssembly ++
        (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code := by
  simp [Structured.Block.compileFromCtx,
    Structured.Stmt.compileFromCtxCore,
    Structured.CompileResult.append]

theorem codeSegment_structuredBlock_code_cons_split
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {code : Structured.Code}
    {rest : List Structured.Stmt}
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Structured.Stmt.code code :: rest } ctx supply).code) :
    ∃ headSegment :
        Structured.Preservation.CodeSegment asm code.toAssembly,
      ∃ tailSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code,
        Structured.Preservation.CodeSegment.startPc headSegment =
          Structured.Preservation.CodeSegment.startPc segment ∧
        Structured.Preservation.CodeSegment.startPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts := Structured.Stmt.code code :: rest } ctx supply).code =
        code.toAssembly ++
          (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code :=
    structuredBlock_compileFromCtx_code_cons_code_eq ctx supply code rest
  let appendSegment :
      Structured.Preservation.CodeSegment asm
        (code.toAssembly ++
          (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code) :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  let headSegment :
      Structured.Preservation.CodeSegment asm code.toAssembly :=
    Structured.Preservation.CodeSegment.left appendSegment
  let tailSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx { stmts := rest } ctx supply).code :=
    Structured.Preservation.CodeSegment.right appendSegment
  refine ⟨headSegment, tailSegment, ?_, ?_, ?_⟩
  · simp [headSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  · simpa [headSegment, tailSegment] using
      codeSegment_right_startPc_eq_left_fallthroughPc appendSegment
  · simp [tailSegment, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq]

theorem expressionsStmtList_toStructured_codeStmt_append
    (code : Structured.Code) (rest : List Expressions.Stmt) :
    Expressions.StmtList.toStructured (Locals.codeStmt code ++ rest) =
      Structured.Stmt.code code :: Expressions.StmtList.toStructured rest := by
  simp [Locals.codeStmt, Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured]

theorem expressionsStmtList_toStructured_append
    (left right : List Expressions.Stmt) :
    Expressions.StmtList.toStructured (left ++ right) =
      Expressions.StmtList.toStructured left ++
        Expressions.StmtList.toStructured right := by
  induction left with
  | nil =>
      simp [Expressions.StmtList.toStructured]
  | cons stmt rest ih =>
      simp [Expressions.StmtList.toStructured, ih]

theorem codeSegment_expressionsStmtList_append_split
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {left right : List Expressions.Stmt}
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured (left ++ right) }
          ctx supply).code) :
    ∃ leftSegment :
        Structured.Preservation.CodeSegment asm
          (Structured.Block.compileFromCtx
            { stmts := Expressions.StmtList.toStructured left }
            ctx supply).code,
      ∃ rightSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured right } ctx
              (Structured.Block.compileFromCtx
                { stmts := Expressions.StmtList.toStructured left }
                ctx supply).next).code,
        Structured.Preservation.CodeSegment.startPc leftSegment =
          Structured.Preservation.CodeSegment.startPc segment ∧
        Structured.Preservation.CodeSegment.startPc rightSegment =
          Structured.Preservation.CodeSegment.fallthroughPc leftSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc rightSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured (left ++ right) }
          ctx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured left ++
                Expressions.StmtList.toStructured right } ctx supply).code := by
    simp [expressionsStmtList_toStructured_append]
  let segment' :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured left ++
                Expressions.StmtList.toStructured right } ctx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  have hSegmentFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment' =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    cases segment with
    | mk pre post hAsm hFits =>
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq]
  rcases codeSegment_structuredBlock_append_split segment' with
    ⟨leftSegment, rightSegment, hLeftStart, hRightStart, hRightFall⟩
  refine ⟨leftSegment, rightSegment, ?_, hRightStart, ?_⟩
  · simpa [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hLeftStart
  · exact hRightFall.trans hSegmentFall

theorem expressionsStmtList_toStructured_call_cons
    (name : Name) (rest : List Expressions.Stmt) :
    Expressions.StmtList.toStructured
        (Expressions.Stmt.call name :: rest) =
      Structured.Stmt.call name :: Expressions.StmtList.toStructured rest := by
  simp [Expressions.StmtList.toStructured, Expressions.Stmt.toStructured]

theorem codeSegment_expressions_call_cons_split
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {name : Name}
    {rest : List Expressions.Stmt}
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Expressions.Stmt.call name :: rest) } ctx supply).code) :
    ∃ callSegment :
        Structured.Preservation.CodeSegment asm
          (Structured.Stmt.compileFromCtxCore (.call name) ctx supply).code,
      ∃ tailSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured rest } ctx
              (Structured.Stmt.compileFromCtxCore
                (.call name) ctx supply).next).code,
        Structured.Preservation.CodeSegment.startPc callSegment =
          Structured.Preservation.CodeSegment.startPc segment ∧
        Structured.Preservation.CodeSegment.startPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc callSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Expressions.Stmt.call name :: rest) } ctx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Structured.Stmt.call name ::
                Expressions.StmtList.toStructured rest } ctx supply).code := by
    simp [expressionsStmtList_toStructured_call_cons]
  let segment' :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Structured.Stmt.call name ::
                Expressions.StmtList.toStructured rest } ctx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  rcases codeSegment_structuredBlock_cons_split segment' with
    ⟨callSegment, tailSegment, hCallStart, hTailStart, hTailFall⟩
  refine ⟨callSegment, tailSegment, ?_, hTailStart, ?_⟩
  · simpa [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hCallStart
  · simpa [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc] using hTailFall

theorem codeSegment_expressions_codeStmt_cons_split
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {code : Structured.Code}
    {rest : List Expressions.Stmt}
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ rest) } ctx supply).code) :
    ∃ headSegment :
        Structured.Preservation.CodeSegment asm code.toAssembly,
      ∃ tailSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured rest }
              ctx supply).code,
        Structured.Preservation.CodeSegment.startPc headSegment =
          Structured.Preservation.CodeSegment.startPc segment ∧
        Structured.Preservation.CodeSegment.startPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ rest) } ctx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Structured.Stmt.code code ::
                Expressions.StmtList.toStructured rest } ctx supply).code := by
    simp [expressionsStmtList_toStructured_codeStmt_append]
  let segment' :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Structured.Stmt.code code ::
                Expressions.StmtList.toStructured rest } ctx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  rcases codeSegment_structuredBlock_code_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, hTailFall⟩
  refine ⟨headSegment, tailSegment, ?_, hTailStart, ?_⟩
  · simpa [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hHeadStart
  · simpa [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc] using hTailFall

theorem codeSegment_fallthroughPc_singleton
    {asm : Assembly.Program} {instr : Assembly.Instr}
    (segment :
      Structured.Preservation.CodeSegment asm [instr]) :
    Structured.Preservation.CodeSegment.fallthroughPc segment =
      Structured.Preservation.CodeSegment.startPc segment +
        EvmYul.UInt256.ofNat instr.byteSize := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  simp [Structured.Preservation.CodeSegment.fallthroughPc,
    Structured.Preservation.CodeSegment.startPc,
    Assembly.Program.pcAfter_snoc]

theorem localsExpr_compileCode_lit_eq
    {ctx : Locals.Ctx} {offset : Nat} {value : Word}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.lit value) = some code) :
    code = [Structured.BasicInstr.push value] := by
  simpa [Locals.Expr.compileCode] using hCompile.symm

theorem localsExpr_compileCode_var_inv
    {ctx : Locals.Ctx} {offset : Nat} {name : Name}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.var name) = some code) :
    ∃ depth op,
      Locals.Layout.lookupDepth? name ctx.layout = some depth ∧
      Locals.StackOp.dup? (offset + depth) = some op ∧
      code = [Structured.BasicInstr.op op] := by
  unfold Locals.Expr.compileCode at hCompile
  cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
  | none =>
      simp [hDepth] at hCompile
  | some depth =>
      cases hDup : Locals.StackOp.dup? (offset + depth) with
      | none =>
          simp [hDepth, hDup] at hCompile
      | some op =>
          simp [hDepth, hDup] at hCompile
          exact ⟨depth, op, rfl, hDup, hCompile.symm⟩

theorem localsExpr_compileCode_prim_inv
    {ctx : Locals.Ctx} {offset : Nat}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.prim op args) = some code) :
    ∃ argsCode,
      Locals.ExprSeq.compileCode ctx offset args = some argsCode ∧
      code = argsCode ++ [Structured.BasicInstr.op op] := by
  unfold Locals.Expr.compileCode at hCompile
  cases hArgs : Locals.ExprSeq.compileCode ctx offset args with
  | none =>
      simp [hArgs] at hCompile
  | some argsCode =>
      simp [hArgs] at hCompile
      exact ⟨argsCode, rfl, hCompile.symm⟩

theorem localsExprSeq_compileCode_nil_eq
    {ctx : Locals.Ctx} {offset : Nat} {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset Locals.ExprSeq.nil = some code) :
    code = [] := by
  simpa [Locals.ExprSeq.compileCode] using hCompile.symm

theorem localsExprSeq_compileCode_cons_inv
    {ctx : Locals.Ctx} {offset left right : Nat}
    {head : Locals.Expr left} {tail : Locals.ExprSeq right}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset
        (Locals.ExprSeq.cons head tail) = some code) :
    ∃ headCode tailCode,
      Locals.Expr.compileCode ctx offset head = some headCode ∧
      Locals.ExprSeq.compileCode ctx (offset + left) tail = some tailCode ∧
      code = headCode ++ tailCode := by
  unfold Locals.ExprSeq.compileCode at hCompile
  cases hHead : Locals.Expr.compileCode ctx offset head with
  | none =>
      simp [hHead] at hCompile
  | some headCode =>
      cases hTail : Locals.ExprSeq.compileCode ctx (offset + left) tail with
      | none =>
          simp [hHead, hTail] at hCompile
      | some tailCode =>
          simp [hHead, hTail] at hCompile
          exact ⟨headCode, tailCode, rfl, rfl, hCompile.symm⟩

theorem localsBlock_compileOpen_expr_cons_inv
    {ctx finalCtx : Locals.Ctx} {expr : Locals.Expr 0}
    {rest : List Locals.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Locals.Stmt.expr expr :: rest } =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.Expr.compileCode ctx 0 expr = some code ∧
        Locals.Block.compileOpen ctx { stmts := rest } =
          some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  unfold Locals.Block.compileOpen at hCompile
  cases hCode : Locals.Expr.compileCode ctx 0 expr with
  | none =>
      simp [Locals.Stmt.compile, hCode] at hCompile
  | some code =>
      cases hRest :
          Locals.Block.compileOpen ctx { stmts := rest } with
      | none =>
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
      | some restResult =>
          rcases restResult with ⟨restStmts, restCtx⟩
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
          rcases hCompile with ⟨hStmts, hFinalCtx⟩
          exact
            ⟨code, restStmts, rfl,
              by simp [hFinalCtx], hStmts.symm⟩

theorem localsBlock_compileOpen_exprs_cons_inv
    {ctx finalCtx : Locals.Ctx} {results : Nat}
    {exprs : Locals.ExprSeq results}
    {rest : List Locals.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Locals.Stmt.exprs exprs :: rest } =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.ExprSeq.compileCode ctx 0 exprs = some code ∧
        Locals.Block.compileOpen ctx { stmts := rest } =
          some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  unfold Locals.Block.compileOpen at hCompile
  cases hCode : Locals.ExprSeq.compileCode ctx 0 exprs with
  | none =>
      simp [Locals.Stmt.compile, hCode] at hCompile
  | some code =>
      cases hRest :
          Locals.Block.compileOpen ctx { stmts := rest } with
      | none =>
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
      | some restResult =>
          rcases restResult with ⟨restStmts, restCtx⟩
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
          rcases hCompile with ⟨hStmts, hFinalCtx⟩
          exact
            ⟨code, restStmts, rfl,
              by simp [hFinalCtx], hStmts.symm⟩

theorem localsBlock_compileOpen_let_cons_inv
    {ctx finalCtx : Locals.Ctx} {name : Name}
    {value : Locals.Expr 1}
    {rest : List Locals.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Locals.Stmt.let_ name value :: rest } =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.Expr.compileCode ctx 0 value = some code ∧
        Locals.Block.compileOpen (ctx.withLayout (name :: ctx.layout))
          { stmts := rest } = some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  unfold Locals.Block.compileOpen at hCompile
  cases hCode : Locals.Expr.compileCode ctx 0 value with
  | none =>
      simp [Locals.Stmt.compile, hCode] at hCompile
  | some code =>
      cases hRest :
          Locals.Block.compileOpen
            (ctx.withLayout (name :: ctx.layout)) { stmts := rest } with
      | none =>
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
      | some restResult =>
          rcases restResult with ⟨restStmts, restCtx⟩
          simp [Locals.Stmt.compile, hCode, hRest] at hCompile
          rcases hCompile with ⟨hStmts, hFinalCtx⟩
          exact
            ⟨code, restStmts, rfl,
              by simp [hFinalCtx], hStmts.symm⟩

theorem localsBlock_compileOpen_assign_cons_inv
    {ctx finalCtx : Locals.Ctx} {name : Name}
    {value : Locals.Expr 1}
    {rest : List Locals.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Locals.Stmt.assign name value :: rest } =
        some (stmts, finalCtx)) :
    ∃ depth valueCode swapOp restStmts,
      Locals.Layout.lookupDepth? name ctx.layout = some depth ∧
        Locals.Expr.compileCode ctx 0 value = some valueCode ∧
        Locals.StackOp.swap? depth = some swapOp ∧
        Locals.Block.compileOpen ctx { stmts := rest } =
          some (restStmts, finalCtx) ∧
        stmts =
          Locals.codeStmt
            (valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]) ++
            restStmts := by
  unfold Locals.Block.compileOpen at hCompile
  cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
  | none =>
      simp [Locals.Stmt.compile, hDepth] at hCompile
  | some depth =>
      cases hValue :
          Locals.Expr.compileCode ctx 0 value with
      | none =>
          simp [Locals.Stmt.compile, hDepth, hValue] at hCompile
      | some valueCode =>
          cases hSwap : Locals.StackOp.swap? depth with
          | none =>
              simp [Locals.Stmt.compile, hDepth, hValue, hSwap] at hCompile
          | some swapOp =>
              cases hRest :
                  Locals.Block.compileOpen ctx { stmts := rest } with
              | none =>
                  simp [Locals.Stmt.compile, hDepth, hValue, hSwap, hRest]
                    at hCompile
              | some restResult =>
                  rcases restResult with ⟨restStmts, restCtx⟩
                  simp [Locals.Stmt.compile, hDepth, hValue, hSwap, hRest]
                    at hCompile
                  rcases hCompile with ⟨hStmts, hFinalCtx⟩
                  exact
                    ⟨depth, valueCode, swapOp, restStmts, rfl, rfl,
                      hSwap, by simp [hFinalCtx],
                      hStmts.symm⟩

theorem functionsBlock_toLocals_compileOpen_expr_cons_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.expr expr :: rest }) =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.Expr.compileCode ctx 0 expr = some code ∧
        Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  have hCompile' :
      Locals.Block.compileOpen ctx
          { stmts :=
              Locals.Stmt.expr expr ::
                Functions.StmtList.toLocals returns rest } =
        some (stmts, finalCtx) := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Functions.Stmt.toLocals] using hCompile
  rcases localsBlock_compileOpen_expr_cons_inv hCompile' with
    ⟨code, restStmts, hCode, hRest, hStmts⟩
  refine ⟨code, restStmts, hCode, ?_, hStmts⟩
  simpa [Functions.Block.toLocals] using hRest

theorem functionsBlock_toLocals_compileOpen_let_cons_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {name : Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.let_ name value :: rest }) =
        some (stmts, finalCtx)) :
    ∃ code restStmts,
      Locals.Expr.compileCode ctx 0 value = some code ∧
        Locals.Block.compileOpen (ctx.withLayout (name :: ctx.layout))
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (restStmts, finalCtx) ∧
        stmts = Locals.codeStmt code ++ restStmts := by
  have hCompile' :
      Locals.Block.compileOpen ctx
          { stmts :=
              Locals.Stmt.let_ name value ::
                Functions.StmtList.toLocals returns rest } =
        some (stmts, finalCtx) := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Functions.Stmt.toLocals] using hCompile
  rcases localsBlock_compileOpen_let_cons_inv hCompile' with
    ⟨code, restStmts, hCode, hRest, hStmts⟩
  refine ⟨code, restStmts, hCode, ?_, hStmts⟩
  simpa [Functions.Block.toLocals] using hRest

theorem functionsBlock_toLocals_compileOpen_assign_cons_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {name : Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.assign name value :: rest }) =
        some (stmts, finalCtx)) :
    ∃ depth valueCode swapOp restStmts,
      Locals.Layout.lookupDepth? name ctx.layout = some depth ∧
        Locals.Expr.compileCode ctx 0 value = some valueCode ∧
        Locals.StackOp.swap? depth = some swapOp ∧
        Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (restStmts, finalCtx) ∧
        stmts =
          Locals.codeStmt
            (valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]) ++
            restStmts := by
  have hCompile' :
      Locals.Block.compileOpen ctx
          { stmts :=
              Locals.Stmt.assign name value ::
                Functions.StmtList.toLocals returns rest } =
        some (stmts, finalCtx) := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Functions.Stmt.toLocals] using hCompile
  rcases localsBlock_compileOpen_assign_cons_inv hCompile' with
    ⟨depth, valueCode, swapOp, restStmts, hDepth, hValue, hSwap,
      hRest, hStmts⟩
  refine ⟨depth, valueCode, swapOp, restStmts, hDepth, hValue, hSwap,
    ?_, hStmts⟩
  simpa [Functions.Block.toLocals] using hRest

theorem localsBlock_compileOpen_append_inv
    {ctx finalCtx : Locals.Ctx}
    {pre rest : List Locals.Stmt}
    {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx { stmts := pre ++ rest } =
        some (stmts, finalCtx)) :
    ∃ prefixStmts midCtx restStmts,
      Locals.Block.compileOpen ctx { stmts := pre } =
        some (prefixStmts, midCtx) ∧
        Locals.Block.compileOpen midCtx { stmts := rest } =
          some (restStmts, finalCtx) ∧
        stmts = prefixStmts ++ restStmts := by
  induction pre generalizing ctx finalCtx stmts with
  | nil =>
      refine ⟨[], ctx, stmts, ?_, ?_, ?_⟩
      · simp [Locals.Block.compileOpen]
      · simpa using hCompile
      · rfl
  | cons stmt pre ih =>
      unfold Locals.Block.compileOpen at hCompile
      cases hStmt : Locals.Stmt.compile ctx stmt with
      | none =>
          simp [hStmt] at hCompile
      | some stmtResult =>
          rcases stmtResult with ⟨stmtStmts, ctxAfterStmt⟩
          cases hTail :
              Locals.Block.compileOpen ctxAfterStmt
                { stmts := pre ++ rest } with
          | none =>
              simp [hStmt, hTail] at hCompile
          | some tailResult =>
              rcases tailResult with ⟨tailStmts, tailCtx⟩
              simp [hStmt, hTail] at hCompile
              rcases hCompile with ⟨hStmts, hTailCtx⟩
              subst tailCtx
              rcases ih hTail with
                ⟨prefixStmts, midCtx, restStmts, hPrefix, hRest,
                  hTailStmts⟩
              refine
                ⟨stmtStmts ++ prefixStmts, midCtx, restStmts, ?_, hRest,
                  ?_⟩
              · unfold Locals.Block.compileOpen
                simp [hStmt, hPrefix]
              · calc
                  stmts = stmtStmts ++ tailStmts := hStmts.symm
                  _ = stmtStmts ++ (prefixStmts ++ restStmts) := by
                    rw [hTailStmts]
                  _ = (stmtStmts ++ prefixStmts) ++ restStmts := by
                    simp [List.append_assoc]

theorem functionsBlock_toLocals_compileOpen_call_cons_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.call targets functionName args :: rest }) =
        some (stmts, finalCtx)) :
    ∃ callStmts callCtx restStmts,
      Locals.Block.compileOpen ctx
          { stmts :=
              Functions.Lower.evalArgs args ++
                [Locals.Stmt.call functionName] ++
                Functions.Lower.assignReturnedTops targets } =
        some (callStmts, callCtx) ∧
        Locals.Block.compileOpen callCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (restStmts, finalCtx) ∧
        stmts = callStmts ++ restStmts := by
  have hCompile' :
      Locals.Block.compileOpen ctx
          { stmts :=
              (Functions.Lower.evalArgs args ++
                  [Locals.Stmt.call functionName] ++
                  Functions.Lower.assignReturnedTops targets) ++
                Functions.StmtList.toLocals returns rest } =
        some (stmts, finalCtx) := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Functions.Stmt.toLocals] using hCompile
  rcases localsBlock_compileOpen_append_inv hCompile' with
    ⟨callStmts, callCtx, restStmts, hCall, hRest, hStmts⟩
  refine ⟨callStmts, callCtx, restStmts, hCall, ?_, hStmts⟩
  simpa [Functions.Block.toLocals] using hRest

theorem functionsBlock_toLocals_compileOpen_call_cons_parts_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt} {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.call targets functionName args :: rest }) =
        some (stmts, finalCtx)) :
    ∃ argStmts argCtx assignStmts afterAssignCtx restStmts,
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.evalArgs args } =
        some (argStmts, argCtx) ∧
        Locals.Block.compileOpen argCtx
          { stmts := Functions.Lower.assignReturnedTops targets } =
          some (assignStmts, afterAssignCtx) ∧
        Locals.Block.compileOpen afterAssignCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (restStmts, finalCtx) ∧
        stmts =
          argStmts ++ [Expressions.Stmt.call functionName] ++
            assignStmts ++ restStmts := by
  rcases functionsBlock_toLocals_compileOpen_call_cons_inv hCompile with
    ⟨callPrefixStmts, afterCallPrefixCtx, restStmts, hCallPrefix,
      hRest, hStmts⟩
  have hCallPrefix' :
      Locals.Block.compileOpen ctx
          { stmts :=
              Functions.Lower.evalArgs args ++
                ([Locals.Stmt.call functionName] ++
                  Functions.Lower.assignReturnedTops targets) } =
        some (callPrefixStmts, afterCallPrefixCtx) := by
    simpa [List.append_assoc] using hCallPrefix
  rcases
      localsBlock_compileOpen_append_inv
        (pre := Functions.Lower.evalArgs args) hCallPrefix' with
    ⟨argStmts, argCtx, callAssignStmts, hArgs, hCallAssign,
      hCallPrefixStmts⟩
  rcases
      localsBlock_compileOpen_append_inv
        (pre := [Locals.Stmt.call functionName]) hCallAssign with
    ⟨callStmts, afterCallCtx, assignStmts, hCall, hAssign,
      hCallAssignStmts⟩
  have hCallExact :
      [Expressions.Stmt.call functionName] = callStmts ∧
        argCtx = afterCallCtx := by
    simpa [Locals.Block.compileOpen, Locals.Stmt.compile] using hCall
  rcases hCallExact with ⟨hCallStmts, hAfterCallCtx⟩
  subst callStmts
  subst afterCallCtx
  exact
    ⟨argStmts, argCtx, assignStmts, afterCallPrefixCtx, restStmts,
      hArgs, hAssign, hRest, by
        calc
          stmts = callPrefixStmts ++ restStmts := hStmts
          _ = (argStmts ++ callAssignStmts) ++ restStmts := by
            rw [hCallPrefixStmts]
          _ =
              (argStmts ++
                ([Expressions.Stmt.call functionName] ++ assignStmts)) ++
                restStmts := by
            rw [hCallAssignStmts]
          _ =
              argStmts ++ [Expressions.Stmt.call functionName] ++
                assignStmts ++ restStmts := by
            simp [List.append_assoc]⟩

theorem functionsProgram_toExpressions?_structured_proc_lookup
    {programSource : Functions.Program} {lower : Expressions.Program}
    {name : Name} {fn : Functions.FunDef}
    (hLower : Functions.Program.toExpressions? programSource = some lower)
    (hFind :
      Functions.FunList.find? name programSource.functions = some fn) :
    ∃ exprProc,
      Expressions.ProcList.lookup? name lower.procs = some exprProc ∧
        (Functions.FunDef.toLocalsProc fn).toExpressions? = some exprProc ∧
        Structured.ProcList.lookup? name lower.toStructured.procs =
          some exprProc.toStructured := by
  have hLowerLocals :
      (Functions.Program.toLocals programSource).toExpressions? =
        some lower := by
    simpa [Functions.Program.toExpressions?] using hLower
  have hLowerProcs :
      Locals.ProcList.toExpressions?
          (Functions.Program.toLocals programSource).procs =
        some lower.procs :=
    Locals.Program.procs_toExpressions_of_toExpressions? hLowerLocals
  have hLocalLookup :
      Locals.Direct.ProcList.lookup? name
          (Functions.Program.toLocals programSource).procs =
        some (Functions.FunDef.toLocalsProc fn) := by
    simpa [Functions.Program.toLocals] using
      Functions.FunList.lookup_toLocals
        (name := name) (functions := programSource.functions) hFind
  rcases
      Locals.Direct.ProcList.lookup?_toExpressions?
        hLowerProcs hLocalLookup with
    ⟨exprProc, hExprLookup, hProcLower⟩
  have hStructuredLookup :
      Structured.ProcList.lookup? name lower.toStructured.procs =
        some exprProc.toStructured := by
    have hLookupMap :=
      Expressions.ProcList.lookup?_toStructured name lower.procs
    simpa [Expressions.Program.toStructured, hExprLookup] using hLookupMap
  exact ⟨exprProc, hExprLookup, hProcLower, hStructuredLookup⟩

theorem functionsProgram_toExpressions?_structured_proc_lookup_parts
    {programSource : Functions.Program} {lower : Expressions.Program}
    {name : Name} {fn : Functions.FunDef}
    (hLower : Functions.Program.toExpressions? programSource = some lower)
    (hFind :
      Functions.FunList.find? name programSource.functions = some fn) :
    ∃ proc,
      Structured.ProcList.lookup? name lower.toStructured.procs =
        some proc ∧
        proc.name = fn.name ∧
        proc.argc = fn.params.length ∧
        proc.retc = fn.returns.length := by
  rcases
      functionsProgram_toExpressions?_structured_proc_lookup
        hLower hFind with
    ⟨exprProc, _hExprLookup, hProcLower, hStructuredLookup⟩
  have hExprFields :
      exprProc.name = fn.name ∧
        exprProc.argc = fn.params.length ∧
        exprProc.retc = fn.returns.length := by
    unfold Locals.Proc.toExpressions? at hProcLower
    cases hBody :
        Locals.Block.compileToPreserving
          (Locals.Ctx.procEntryWithLayoutAndRetc
            (Functions.FunDef.toLocalsProc fn).entryLayout
            (Functions.FunDef.toLocalsProc fn).retc)
          (Functions.FunDef.toLocalsProc fn).retc 0
          (Functions.FunDef.toLocalsProc fn).body with
    | none =>
        simp [hBody] at hProcLower
    | some body =>
        have hSome :
            some exprProc =
              some
                ({ name := (Functions.FunDef.toLocalsProc fn).name
                   argc := (Functions.FunDef.toLocalsProc fn).argc
                   retc := (Functions.FunDef.toLocalsProc fn).retc
                   body := body } : Expressions.Proc) := by
          simpa [hBody] using hProcLower.symm
        cases hSome
        simp [Functions.FunDef.toLocalsProc]
  rcases hExprFields with ⟨hExprName, hExprArgc, hExprRetc⟩
  exact
    ⟨exprProc.toStructured, hStructuredLookup,
      by simpa [Expressions.Proc.toStructured] using hExprName,
      by simpa [Expressions.Proc.toStructured] using hExprArgc,
      by simpa [Expressions.Proc.toStructured] using hExprRetc⟩

theorem localsBlock_compileToPreserving_parts
    {ctx : Locals.Ctx} {preserve targetDepth : Nat}
    {block : Locals.Block} {lower : Expressions.Block}
    (hCompile :
      Locals.Block.compileToPreserving ctx preserve targetDepth block =
        some lower) :
    ∃ bodyStmts finalCtx cleanup,
      Locals.Block.compileOpen ctx block = some (bodyStmts, finalCtx) ∧
        finalCtx.cleanupToPreserving? preserve targetDepth = some cleanup ∧
        lower.stmts = bodyStmts ++ Locals.codeStmt cleanup := by
  unfold Locals.Block.compileToPreserving at hCompile
  cases hOpen : Locals.Block.compileOpen ctx block with
  | none =>
      simp [hOpen] at hCompile
  | some pair =>
      rcases pair with ⟨bodyStmts, actualFinalCtx⟩
      simp [hOpen] at hCompile
      cases hCleanup :
          actualFinalCtx.cleanupToPreserving? preserve targetDepth with
      | none =>
          simp [Locals.finishToPreserving, hCleanup] at hCompile
      | some cleanup =>
          simp [Locals.finishToPreserving, hCleanup] at hCompile
          cases hCompile
          exact ⟨bodyStmts, actualFinalCtx, cleanup, rfl, hCleanup, rfl⟩

theorem codeSegment_localsBlock_compileToPreserving_split
    {ctx : Locals.Ctx} {preserve targetDepth : Nat}
    {block : Locals.Block} {lower : Expressions.Block}
    {asm : Assembly.Program} {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCompile :
      Locals.Block.compileToPreserving ctx preserve targetDepth block =
        some lower)
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured lower.stmts }
          structuredCtx supply).code) :
    ∃ bodyStmts finalCtx cleanup,
      Locals.Block.compileOpen ctx block = some (bodyStmts, finalCtx) ∧
        finalCtx.cleanupToPreserving? preserve targetDepth = some cleanup ∧
        ∃ bodySegment :
            Structured.Preservation.CodeSegment asm
              (Structured.Block.compileFromCtx
                { stmts := Expressions.StmtList.toStructured bodyStmts }
                structuredCtx supply).code,
          ∃ cleanupSegment :
              Structured.Preservation.CodeSegment asm
                (Structured.Block.compileFromCtx
                  { stmts :=
                      Expressions.StmtList.toStructured
                        (Locals.codeStmt cleanup) } structuredCtx
                  (Structured.Block.compileFromCtx
                    { stmts := Expressions.StmtList.toStructured bodyStmts }
                    structuredCtx supply).next).code,
            Structured.Preservation.CodeSegment.startPc bodySegment =
              Structured.Preservation.CodeSegment.startPc segment ∧
            Structured.Preservation.CodeSegment.startPc cleanupSegment =
              Structured.Preservation.CodeSegment.fallthroughPc
                bodySegment ∧
            Structured.Preservation.CodeSegment.fallthroughPc cleanupSegment =
              Structured.Preservation.CodeSegment.fallthroughPc segment := by
  rcases
      localsBlock_compileToPreserving_parts hCompile with
    ⟨bodyStmts, finalCtx, cleanup, hOpen, hCleanup, hStmts⟩
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured lower.stmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (bodyStmts ++ Locals.codeStmt cleanup) }
          structuredCtx supply).code := by
    simp [hStmts]
  let segment' :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (bodyStmts ++ Locals.codeStmt cleanup) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hSegmentFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment' =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    cases segment with
    | mk pre post hAsm hFits =>
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq]
  rcases codeSegment_expressionsStmtList_append_split segment' with
    ⟨bodySegment, cleanupSegment, hBodyStart, hCleanupStart,
      hCleanupFall⟩
  refine
    ⟨bodyStmts, finalCtx, cleanup, hOpen, hCleanup, bodySegment, cleanupSegment,
      ?_, hCleanupStart, ?_⟩
  · exact hBodyStart.trans hSegmentStart
  · exact hCleanupFall.trans hSegmentFall

theorem locals_runCleanupToPreserving_runState_of_cleanupToPreserving
    {ctx : Locals.Ctx} {preserve targetDepth : Nat}
    {cleanup : Structured.Code} {state final : Locals.RunState}
    (hCleanup :
      ctx.cleanupToPreserving? preserve targetDepth = some cleanup)
    (hRun :
      Locals.Direct.Ctx.runCleanupToPreserving ctx preserve targetDepth
        state = .ok final) :
    Structured.Code.runState cleanup state = .ok final := by
  unfold Locals.Direct.Ctx.runCleanupToPreserving at hRun
  rw [hCleanup] at hRun
  exact hRun

theorem structuredCode_run_of_runState
    {code : Structured.Code} {state final : Locals.RunState}
    (hRunState : Structured.Code.runState code state = .ok final) :
    Structured.Code.run code state.evm = .ok final.evm := by
  unfold Structured.Code.runState at hRunState
  cases hRun : Structured.Code.run code state.evm with
  | error err =>
      rw [hRun] at hRunState
      cases hRunState
  | ok evmFinal =>
      rw [hRun] at hRunState
      cases hRunState
      simp [Structured.RunState.withEVM]

theorem functionsDirect_pushReturns_runState_of_returnExprs_compileCode
    {ctx : Locals.Ctx} {name : Name} {rest : List Name}
    {code : Structured.Code} {state final : Locals.RunState}
    (hCompile :
      Locals.ExprSeq.compileCode ctx 0
        (Functions.Lower.returnExprs (name :: rest)) = some code)
    (hRun :
      Functions.Direct.pushReturns ctx (name :: rest) state = .ok final) :
    Structured.Code.runState code state = .ok final := by
  simp [Functions.Direct.pushReturns] at hRun
  rw [Locals.Direct.Expr.ExprSeq.runCode_eq_compileCode_zero
    ctx (Functions.Lower.returnExprs (name :: rest)) code state.evm
    hCompile] at hRun
  unfold Structured.Code.runState
  cases hCodeRun : Structured.Code.run code state.evm with
  | error err =>
      simp [hCodeRun] at hRun
  | ok evmAfter =>
      simp [hCodeRun] at hRun
      cases hRun
      simp [Structured.RunState.withEVM]

theorem functionsLower_pushReturns_compileOpen_parts
    {ctx finalCtx : Locals.Ctx} {returns : List Name}
    {stmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
        { stmts := Functions.Lower.pushReturns returns } =
        some (stmts, finalCtx)) :
    (returns = [] ∧ stmts = [] ∧ finalCtx = ctx) ∨
      ∃ name rest code,
        returns = name :: rest ∧
          Locals.ExprSeq.compileCode ctx 0
            (Functions.Lower.returnExprs (name :: rest)) = some code ∧
          stmts = Locals.codeStmt code ∧ finalCtx = ctx := by
  cases returns with
  | nil =>
      simp [Functions.Lower.pushReturns, Locals.Block.compileOpen]
        at hCompile
      rcases hCompile with ⟨hStmts, hCtx⟩
      exact Or.inl ⟨rfl, hStmts, hCtx.symm⟩
  | cons name rest =>
      simp [Functions.Lower.pushReturns, Locals.Block.compileOpen]
        at hCompile
      cases hCode :
          Locals.ExprSeq.compileCode ctx 0
            (Functions.Lower.returnExprs (name :: rest)) with
      | none =>
          simp [Locals.Stmt.compile, hCode] at hCompile
      | some code =>
          simp [Locals.Stmt.compile, hCode] at hCompile
          rcases hCompile with ⟨hStmts, hCtx⟩
          exact
            Or.inr
              ⟨name, rest, code, rfl, hCode, hStmts.symm, hCtx.symm⟩

theorem compilerOpenFunctionsArgList_compileOpen_structured_next
    {args : List (Functions.Expr 1)}
    {localsCtx finalLocalsCtx : Locals.Ctx}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          { stmts := Functions.Lower.evalArgs args } =
        some (compiledStmts, finalLocalsCtx)) :
    (Structured.Block.compileFromCtx
      { stmts := Expressions.StmtList.toStructured compiledStmts }
      structuredCtx supply).next = supply := by
  cases args with
  | nil =>
      have hCompileNil :
          compiledStmts = [] ∧ localsCtx = finalLocalsCtx := by
        simpa [Functions.Lower.evalArgs, Locals.Block.compileOpen] using
          hCompileBlock
      rcases hCompileNil with ⟨hCompiledStmts, _hFinalCtx⟩
      subst compiledStmts
      simp [Expressions.StmtList.toStructured,
        Structured.Block.compileFromCtx]
  | cons arg rest =>
      let args' : List (Functions.Expr 1) := arg :: rest
      have hCompileCons :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  [Locals.Stmt.exprs
                    (Functions.Lower.argExprs args')] } =
            some (compiledStmts, finalLocalsCtx) := by
        simpa [Functions.Lower.evalArgs, args'] using hCompileBlock
      rcases
          localsBlock_compileOpen_exprs_cons_inv hCompileCons with
        ⟨code, restStmts, _hCode, hRestCompile, hCompiledStmts⟩
      have hRest :
          restStmts = [] ∧ localsCtx = finalLocalsCtx := by
        simpa [Locals.Block.compileOpen] using hRestCompile
      rcases hRest with ⟨hRestStmts, _hFinalCtx⟩
      subst restStmts
      subst compiledStmts
      simp [Locals.codeStmt, Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured, Structured.Block.compileFromCtx,
        Structured.Stmt.compileFromCtxCore,
        Structured.CompileResult.append]

theorem codeSegment_functions_call_after_args_call_split_of_compileOpen
    {args : List (Functions.Expr 1)}
    {localsCtx argCtx : Locals.Ctx}
    {argStmts compiledStmts afterCallStmts : List Expressions.Stmt}
    {asm : Assembly.Program} {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {functionName : Name}
    (hCompileArgs :
      Locals.Block.compileOpen localsCtx
          { stmts := Functions.Lower.evalArgs args } =
        some (argStmts, argCtx))
    (hCompiledStmts :
      compiledStmts =
        argStmts ++ (Expressions.Stmt.call functionName :: afterCallStmts))
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code) :
    ∃ argSegment :
        Structured.Preservation.CodeSegment asm
          (Structured.Block.compileFromCtx
            { stmts := Expressions.StmtList.toStructured argStmts }
            structuredCtx supply).code,
      ∃ callSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Stmt.compileFromCtxCore
              (.call functionName) structuredCtx supply).code,
        ∃ afterCallSegment :
            Structured.Preservation.CodeSegment asm
              (Structured.Block.compileFromCtx
                { stmts := Expressions.StmtList.toStructured afterCallStmts }
                structuredCtx
                (Structured.Stmt.compileFromCtxCore
                  (.call functionName) structuredCtx supply).next).code,
          Structured.Preservation.CodeSegment.startPc argSegment =
            Structured.Preservation.CodeSegment.startPc segment ∧
          Structured.Preservation.CodeSegment.startPc callSegment =
            Structured.Preservation.CodeSegment.fallthroughPc argSegment ∧
          Structured.Preservation.CodeSegment.startPc afterCallSegment =
            Structured.Preservation.CodeSegment.fallthroughPc callSegment ∧
          Structured.Preservation.CodeSegment.fallthroughPc afterCallSegment =
            Structured.Preservation.CodeSegment.fallthroughPc segment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (argStmts ++
                  (Expressions.Stmt.call functionName :: afterCallStmts)) }
          structuredCtx supply).code := by
    rw [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (argStmts ++
                  (Expressions.Stmt.call functionName :: afterCallStmts)) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq segment
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hSegmentFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment' =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    cases segment with
    | mk pre post hAsm hFits =>
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq]
  rcases codeSegment_expressionsStmtList_append_split segment' with
    ⟨argSegment, callTailSegment, hArgStart, hCallTailStart,
      hCallTailFall⟩
  have hArgNext :
      (Structured.Block.compileFromCtx
        { stmts := Expressions.StmtList.toStructured argStmts }
        structuredCtx supply).next = supply :=
    compilerOpenFunctionsArgList_compileOpen_structured_next
      (structuredCtx := structuredCtx) (supply := supply) hCompileArgs
  have hCallTailCodeEq :
      (Structured.Block.compileFromCtx
        { stmts :=
            Expressions.StmtList.toStructured
              (Expressions.Stmt.call functionName :: afterCallStmts) }
        structuredCtx
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured argStmts }
          structuredCtx supply).next).code =
      (Structured.Block.compileFromCtx
        { stmts :=
            Expressions.StmtList.toStructured
              (Expressions.Stmt.call functionName :: afterCallStmts) }
        structuredCtx supply).code := by
    rw [hArgNext]
  let callTailSegment' :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Expressions.Stmt.call functionName :: afterCallStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hCallTailCodeEq
      callTailSegment
  have hCallTailStart' :
      Structured.Preservation.CodeSegment.startPc callTailSegment' =
        Structured.Preservation.CodeSegment.startPc callTailSegment := by
    simp [callTailSegment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hCallTailFall' :
      Structured.Preservation.CodeSegment.fallthroughPc callTailSegment' =
        Structured.Preservation.CodeSegment.fallthroughPc callTailSegment := by
    cases callTailSegment with
    | mk pre post hAsm hFits =>
        simp [callTailSegment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc,
          hCallTailCodeEq]
  rcases codeSegment_expressions_call_cons_split callTailSegment' with
    ⟨callSegment, afterCallSegment, hCallStart, hAfterStart,
      hAfterFall⟩
  refine ⟨argSegment, callSegment, afterCallSegment, ?_, ?_, hAfterStart, ?_⟩
  · exact hArgStart.trans hSegmentStart
  · calc
      Structured.Preservation.CodeSegment.startPc callSegment =
          Structured.Preservation.CodeSegment.startPc callTailSegment' :=
        hCallStart
      _ = Structured.Preservation.CodeSegment.startPc callTailSegment :=
        hCallTailStart'
      _ = Structured.Preservation.CodeSegment.fallthroughPc argSegment :=
        hCallTailStart
  · calc
      Structured.Preservation.CodeSegment.fallthroughPc afterCallSegment =
          Structured.Preservation.CodeSegment.fallthroughPc callTailSegment' :=
        hAfterFall
      _ = Structured.Preservation.CodeSegment.fallthroughPc callTailSegment :=
        hCallTailFall'
      _ = Structured.Preservation.CodeSegment.fallthroughPc segment' :=
        hCallTailFall
      _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
        hSegmentFall

theorem compilerOpenFunctionsAssignReturnedTopsRev_compileOpen_structured_next
    {names : List Name}
    {localsCtx finalLocalsCtx : Locals.Ctx}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          { stmts := Functions.Lower.assignReturnedTopsRev names } =
        some (compiledStmts, finalLocalsCtx)) :
    (Structured.Block.compileFromCtx
      { stmts := Expressions.StmtList.toStructured compiledStmts }
      structuredCtx supply).next = supply := by
  induction names generalizing localsCtx finalLocalsCtx compiledStmts supply with
  | nil =>
      have hCompileNil :
          compiledStmts = [] ∧ localsCtx = finalLocalsCtx := by
        simpa [Functions.Lower.assignReturnedTopsRev,
          Locals.Block.compileOpen] using hCompileBlock
      rcases hCompileNil with ⟨hCompiledStmts, _hFinalCtx⟩
      subst compiledStmts
      simp [Expressions.StmtList.toStructured,
        Structured.Block.compileFromCtx]
  | cons name rest ih =>
      unfold Functions.Lower.assignReturnedTopsRev at hCompileBlock
      unfold Locals.Block.compileOpen at hCompileBlock
      cases hDepth :
          Locals.Layout.lookupDepth? name localsCtx.layout with
      | none =>
          simp [Locals.Stmt.compile, hDepth] at hCompileBlock
      | some depth =>
          cases hSwap : Locals.StackOp.swap? (rest.length + depth) with
          | none =>
              simp [Locals.Stmt.compile, hDepth, hSwap] at hCompileBlock
          | some swapOp =>
              cases hRest :
                  Locals.Block.compileOpen localsCtx
                    { stmts := Functions.Lower.assignReturnedTopsRev rest } with
              | none =>
                  simp [Locals.Stmt.compile, hDepth, hSwap, hRest]
                    at hCompileBlock
              | some restResult =>
                  rcases restResult with ⟨restStmts, restCtx⟩
                  simp [Locals.Stmt.compile, hDepth, hSwap, hRest]
                    at hCompileBlock
                  rcases hCompileBlock with ⟨hCompiledStmts, _hFinalCtx⟩
                  have hRestNext :
                      (Structured.Block.compileFromCtx
                        { stmts :=
                            Expressions.StmtList.toStructured restStmts }
                        structuredCtx supply).next = supply :=
                    ih (localsCtx := localsCtx) (finalLocalsCtx := restCtx)
                      (compiledStmts := restStmts)
                      (supply := supply) hRest
                  rw [← hCompiledStmts]
                  simp [Locals.codeStmt,
                    Expressions.StmtList.toStructured,
                    Expressions.Stmt.toStructured,
                    Structured.Block.compileFromCtx,
                    Structured.Stmt.compileFromCtxCore,
                    Structured.CompileResult.append, hRestNext]

theorem compilerOpenFunctionsAssignReturnedTops_compileOpen_structured_next
    {targets : List Name}
    {localsCtx finalLocalsCtx : Locals.Ctx}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (compiledStmts, finalLocalsCtx)) :
    (Structured.Block.compileFromCtx
      { stmts := Expressions.StmtList.toStructured compiledStmts }
      structuredCtx supply).next = supply := by
  simpa [Functions.Lower.assignReturnedTops] using
    compilerOpenFunctionsAssignReturnedTopsRev_compileOpen_structured_next
      (structuredCtx := structuredCtx) (supply := supply) hCompileBlock

theorem codeSegment_functions_call_after_assign_tail_split_of_compileOpen
    {targets : List Name}
    {localsCtx afterAssignCtx : Locals.Ctx}
    {assignStmts afterCallStmts restStmts : List Expressions.Stmt}
    {asm : Assembly.Program} {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCompileAssign :
      Locals.Block.compileOpen localsCtx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (assignStmts, afterAssignCtx))
    (hAfterCallStmts :
      afterCallStmts = assignStmts ++ restStmts)
    (afterCallSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured afterCallStmts }
          structuredCtx supply).code) :
    ∃ assignSegment :
        Structured.Preservation.CodeSegment asm
          (Structured.Block.compileFromCtx
            { stmts := Expressions.StmtList.toStructured assignStmts }
            structuredCtx supply).code,
      ∃ restSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured restStmts }
              structuredCtx supply).code,
        Structured.Preservation.CodeSegment.startPc assignSegment =
          Structured.Preservation.CodeSegment.startPc afterCallSegment ∧
        Structured.Preservation.CodeSegment.startPc restSegment =
          Structured.Preservation.CodeSegment.fallthroughPc assignSegment ∧
        Structured.Preservation.CodeSegment.fallthroughPc restSegment =
          Structured.Preservation.CodeSegment.fallthroughPc afterCallSegment := by
  have hCodeEq :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured afterCallStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (assignStmts ++ restStmts) }
          structuredCtx supply).code := by
    rw [hAfterCallStmts]
  let afterCallSegment' :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (assignStmts ++ restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq afterCallSegment
  have hAfterCallStart :
      Structured.Preservation.CodeSegment.startPc afterCallSegment' =
        Structured.Preservation.CodeSegment.startPc afterCallSegment := by
    simp [afterCallSegment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hAfterCallFall :
      Structured.Preservation.CodeSegment.fallthroughPc afterCallSegment' =
        Structured.Preservation.CodeSegment.fallthroughPc afterCallSegment := by
    cases afterCallSegment with
    | mk pre post hAsm hFits =>
        simp [afterCallSegment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq]
  rcases codeSegment_expressionsStmtList_append_split afterCallSegment' with
    ⟨assignSegment, restSegmentRaw, hAssignStart, hRestStart,
      hRestRawFall⟩
  have hAssignNext :
      (Structured.Block.compileFromCtx
        { stmts := Expressions.StmtList.toStructured assignStmts }
        structuredCtx supply).next = supply :=
    compilerOpenFunctionsAssignReturnedTops_compileOpen_structured_next
      (structuredCtx := structuredCtx) (supply := supply) hCompileAssign
  have hRestCodeEq :
      (Structured.Block.compileFromCtx
        { stmts := Expressions.StmtList.toStructured restStmts }
        structuredCtx
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured assignStmts }
          structuredCtx supply).next).code =
      (Structured.Block.compileFromCtx
        { stmts := Expressions.StmtList.toStructured restStmts }
        structuredCtx supply).code := by
    rw [hAssignNext]
  let restSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured restStmts }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hRestCodeEq restSegmentRaw
  have hRestStart' :
      Structured.Preservation.CodeSegment.startPc restSegment =
        Structured.Preservation.CodeSegment.startPc restSegmentRaw := by
    simp [restSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hRestFall' :
      Structured.Preservation.CodeSegment.fallthroughPc restSegment =
        Structured.Preservation.CodeSegment.fallthroughPc restSegmentRaw := by
    cases restSegmentRaw with
    | mk pre post hAsm hFits =>
        simp [restSegment, Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hRestCodeEq]
  refine ⟨assignSegment, restSegment, ?_, ?_, ?_⟩
  · exact hAssignStart.trans hAfterCallStart
  · calc
      Structured.Preservation.CodeSegment.startPc restSegment =
          Structured.Preservation.CodeSegment.startPc restSegmentRaw :=
        hRestStart'
      _ = Structured.Preservation.CodeSegment.fallthroughPc assignSegment :=
        hRestStart
  · calc
      Structured.Preservation.CodeSegment.fallthroughPc restSegment =
          Structured.Preservation.CodeSegment.fallthroughPc restSegmentRaw :=
        hRestFall'
      _ = Structured.Preservation.CodeSegment.fallthroughPc afterCallSegment' :=
        hRestRawFall
      _ = Structured.Preservation.CodeSegment.fallthroughPc afterCallSegment :=
        hAfterCallFall

theorem codeSegment_functions_call_cons_parts_split_of_compileOpen
    {returns : List Name} {localsCtx finalLocalsCtx : Locals.Ctx}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {asm : Assembly.Program} {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCompile :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.call targets functionName args :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code) :
    ∃ argStmts argCtx assignStmts afterAssignCtx restStmts,
      ∃ argSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured argStmts }
              structuredCtx supply).code,
        ∃ callSegment :
            Structured.Preservation.CodeSegment asm
              (Structured.Stmt.compileFromCtxCore
                (.call functionName) structuredCtx supply).code,
          ∃ assignSegment :
              Structured.Preservation.CodeSegment asm
                (Structured.Block.compileFromCtx
                  { stmts := Expressions.StmtList.toStructured assignStmts }
                  structuredCtx
                  (Structured.Stmt.compileFromCtxCore
                    (.call functionName) structuredCtx supply).next).code,
            ∃ tailSegment :
                Structured.Preservation.CodeSegment asm
                  (Structured.Block.compileFromCtx
                    { stmts := Expressions.StmtList.toStructured restStmts }
                    structuredCtx
                    (Structured.Stmt.compileFromCtxCore
                      (.call functionName) structuredCtx supply).next).code,
              Locals.Block.compileOpen localsCtx
                  { stmts := Functions.Lower.evalArgs args } =
                some (argStmts, argCtx) ∧
              Locals.Block.compileOpen argCtx
                  { stmts := Functions.Lower.assignReturnedTops targets } =
                some (assignStmts, afterAssignCtx) ∧
              Locals.Block.compileOpen afterAssignCtx
                  (Functions.Block.toLocals returns { stmts := rest }) =
                some (restStmts, finalLocalsCtx) ∧
              Structured.Preservation.CodeSegment.startPc argSegment =
                Structured.Preservation.CodeSegment.startPc segment ∧
              Structured.Preservation.CodeSegment.startPc callSegment =
                Structured.Preservation.CodeSegment.fallthroughPc argSegment ∧
              Structured.Preservation.CodeSegment.startPc assignSegment =
                Structured.Preservation.CodeSegment.fallthroughPc callSegment ∧
              Structured.Preservation.CodeSegment.startPc tailSegment =
                Structured.Preservation.CodeSegment.fallthroughPc assignSegment ∧
              Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
                Structured.Preservation.CodeSegment.fallthroughPc segment := by
  rcases functionsBlock_toLocals_compileOpen_call_cons_parts_inv hCompile with
    ⟨argStmts, argCtx, assignStmts, afterAssignCtx, restStmts,
      hArgsCompile, hAssignCompile, hRestCompile, hCompiledStmts⟩
  have hCallAfterStmts :
      compiledStmts =
        argStmts ++
          (Expressions.Stmt.call functionName ::
            (assignStmts ++ restStmts)) := by
    rw [hCompiledStmts]
    simp [List.append_assoc]
  rcases
      codeSegment_functions_call_after_args_call_split_of_compileOpen
        (structuredCtx := structuredCtx) (supply := supply)
        hArgsCompile hCallAfterStmts segment with
    ⟨argSegment, callSegment, afterCallSegment,
      hArgStart, hCallStart, hAfterCallStart, hAfterCallFall⟩
  rcases
      codeSegment_functions_call_after_assign_tail_split_of_compileOpen
        (targets := targets) (structuredCtx := structuredCtx)
        (supply :=
          (Structured.Stmt.compileFromCtxCore
            (.call functionName) structuredCtx supply).next)
        hAssignCompile (by rfl) afterCallSegment with
    ⟨assignSegment, tailSegment, hAssignStart, hTailStart,
      hTailFallAfterCall⟩
  exact
    ⟨argStmts, argCtx, assignStmts, afterAssignCtx, restStmts,
      argSegment, callSegment, assignSegment, tailSegment,
      hArgsCompile, hAssignCompile, hRestCompile,
      hArgStart, hCallStart, hAssignStart.trans hAfterCallStart, hTailStart,
      hTailFallAfterCall.trans hAfterCallFall⟩

theorem structured_callJumpCode_usesCallCreate_false
    (proc : Structured.Proc) (args : EvmYul.Stack Word)
    (token : Word) :
    Assembly.Program.usesCallCreate
      (Structured.Preservation.ProcedurePreservation.callJumpCode
        proc args token) =
        false := by
  have hSink :
      Assembly.Program.usesCallCreate
        (Structured.StackShuffle.sinkTopUnder args.length) = false :=
    Structured.CompilerFacts.GeneratedNoCallCreate.sinkTopUnder args.length
  have hPushSink :
      Assembly.Program.usesCallCreate
        ([Assembly.Instr.push token] ++
          Structured.StackShuffle.sinkTopUnder args.length) = false :=
    Assembly.Program.usesCallCreate_append_eq_false
      (by simp [Assembly.Program.usesCallCreate,
        Assembly.Instr.usesCallCreate])
      hSink
  have hJump :
      Assembly.Program.usesCallCreate
        [Assembly.Instr.jump (Structured.ProcLabel.entry proc.name)] =
          false := by
    simp [Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate]
  simpa [Structured.Preservation.ProcedurePreservation.callJumpCode] using
    Assembly.Program.usesCallCreate_append_eq_false hPushSink hJump

theorem structured_callSiteCode_usesCallCreate_false
    (proc : Structured.Proc) (args : EvmYul.Stack Word)
    (token : Word) (returnLabel : Assembly.Label) :
    Assembly.Program.usesCallCreate
      (Structured.Preservation.ProcedurePreservation.callSiteCode
        proc args token returnLabel) =
        false := by
  have hCall :=
    structured_callJumpCode_usesCallCreate_false proc args token
  have hLabel :
      Assembly.Program.usesCallCreate [Assembly.Instr.label returnLabel] =
        false := by
    simp [Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate]
  simpa [Structured.Preservation.ProcedurePreservation.callSiteCode] using
    Assembly.Program.usesCallCreate_append_eq_false hCall hLabel

theorem structured_compile_call_code_usesCallCreate_false
    {ctx : Structured.CompileContext} {supply : Structured.LabelSupply}
    {name : Name} :
    Assembly.Program.usesCallCreate
      (Structured.Stmt.compileFromCtxCore (.call name) ctx supply).code =
        false := by
  cases hLookup : Structured.ProcList.lookup? name ctx.procs with
  | none =>
      simp [Structured.Stmt.compileFromCtxCore, hLookup,
        Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate,
        Assembly.PrimOp.isCallCreate]
  | some proc =>
      have hSink :
          Assembly.Program.usesCallCreate
            (Structured.StackShuffle.sinkTopUnder proc.argc) = false :=
        Structured.CompilerFacts.GeneratedNoCallCreate.sinkTopUnder proc.argc
      have hPushSink :
          Assembly.Program.usesCallCreate
            ([Assembly.Instr.push (Structured.Stmt.callToken supply)] ++
              Structured.StackShuffle.sinkTopUnder proc.argc) = false :=
        Assembly.Program.usesCallCreate_append_eq_false
          (by simp [Assembly.Program.usesCallCreate,
            Assembly.Instr.usesCallCreate])
          hSink
      have hJumpLabel :
          Assembly.Program.usesCallCreate
            [ Assembly.Instr.jump (Structured.ProcLabel.entry name)
            , Assembly.Instr.label (Structured.LabelSupply.label supply 0) ] =
              false := by
        simp [Assembly.Program.usesCallCreate, Assembly.Instr.usesCallCreate]
      simpa [Structured.Stmt.compileFromCtxCore, hLookup,
        List.append_assoc] using
        Assembly.Program.usesCallCreate_append_eq_false hPushSink hJumpLabel

theorem codeSegment_structured_call_compile_callSiteCode_of_lookup
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {supply : Structured.LabelSupply} {name : Name}
    {proc : Structured.Proc} {args : EvmYul.Stack Word}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hArgsLen : args.length = proc.argc)
    (callSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Stmt.compileFromCtxCore (.call name) ctx supply).code) :
    ∃ callSiteSegment :
        Structured.Preservation.CodeSegment asm
          (Structured.Preservation.ProcedurePreservation.callSiteCode
            proc args (Structured.Stmt.callToken supply)
            (Structured.LabelSupply.label supply 0)),
      Structured.Preservation.CodeSegment.startPc callSiteSegment =
        Structured.Preservation.CodeSegment.startPc callSegment ∧
      Structured.Preservation.CodeSegment.fallthroughPc callSiteSegment =
        Structured.Preservation.CodeSegment.fallthroughPc callSegment := by
  have hCodeEq :
      (Structured.Stmt.compileFromCtxCore (.call name) ctx supply).code =
        Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args (Structured.Stmt.callToken supply)
          (Structured.LabelSupply.label supply 0) :=
    Structured.Preservation.ProcedurePreservation.compile_call_code_eq_callSiteCode
      (ctx := ctx) (supply := supply) (name := name) (proc := proc)
      (args := args) hLookup hArgsLen
  let callSiteSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args (Structured.Stmt.callToken supply)
          (Structured.LabelSupply.label supply 0)) :=
    Structured.Preservation.CodeSegment.cast_code hCodeEq callSegment
  refine ⟨callSiteSegment, ?_, ?_⟩
  · simp [callSiteSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  · cases callSegment with
    | mk pre post hAsm hFits =>
        simp [callSiteSegment,
          Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hCodeEq]

theorem codeSegment_functions_call_cons_callSite_parts_split_of_compileOpen
    {returns : List Name} {localsCtx finalLocalsCtx : Locals.Ctx}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {asm : Assembly.Program} {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {proc : Structured.Proc} {callArgs : EvmYul.Stack Word}
    (hCompile :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.call targets functionName args :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hLookup :
      Structured.ProcList.lookup? functionName structuredCtx.procs =
        some proc)
    (hArgsLen : callArgs.length = proc.argc)
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code) :
    ∃ argStmts argCtx assignStmts afterAssignCtx restStmts,
      ∃ argSegment :
          Structured.Preservation.CodeSegment asm
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured argStmts }
              structuredCtx supply).code,
        ∃ callSiteSegment :
            Structured.Preservation.CodeSegment asm
              (Structured.Preservation.ProcedurePreservation.callSiteCode
                proc callArgs (Structured.Stmt.callToken supply)
                (Structured.LabelSupply.label supply 0)),
          ∃ assignSegment :
              Structured.Preservation.CodeSegment asm
                (Structured.Block.compileFromCtx
                  { stmts := Expressions.StmtList.toStructured assignStmts }
                  structuredCtx
                  (Structured.Stmt.compileFromCtxCore
                    (.call functionName) structuredCtx supply).next).code,
            ∃ tailSegment :
                Structured.Preservation.CodeSegment asm
                  (Structured.Block.compileFromCtx
                    { stmts := Expressions.StmtList.toStructured restStmts }
                    structuredCtx
                    (Structured.Stmt.compileFromCtxCore
                      (.call functionName) structuredCtx supply).next).code,
              Locals.Block.compileOpen localsCtx
                  { stmts := Functions.Lower.evalArgs args } =
                some (argStmts, argCtx) ∧
              Locals.Block.compileOpen argCtx
                  { stmts := Functions.Lower.assignReturnedTops targets } =
                some (assignStmts, afterAssignCtx) ∧
              Locals.Block.compileOpen afterAssignCtx
                  (Functions.Block.toLocals returns { stmts := rest }) =
                some (restStmts, finalLocalsCtx) ∧
              Structured.Preservation.CodeSegment.startPc argSegment =
                Structured.Preservation.CodeSegment.startPc segment ∧
              Structured.Preservation.CodeSegment.startPc callSiteSegment =
                Structured.Preservation.CodeSegment.fallthroughPc argSegment ∧
              Structured.Preservation.CodeSegment.startPc assignSegment =
                Structured.Preservation.CodeSegment.fallthroughPc
                  callSiteSegment ∧
              Structured.Preservation.CodeSegment.startPc tailSegment =
                Structured.Preservation.CodeSegment.fallthroughPc
                  assignSegment ∧
              Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
                Structured.Preservation.CodeSegment.fallthroughPc segment := by
  rcases
      codeSegment_functions_call_cons_parts_split_of_compileOpen
        hCompile segment with
    ⟨argStmts, argCtx, assignStmts, afterAssignCtx, restStmts,
      argSegment, callSegment, assignSegment, tailSegment,
      hArgsCompile, hAssignCompile, hRestCompile,
      hArgStart, hCallStart, hAssignStart, hTailStart, hTailFall⟩
  rcases
      codeSegment_structured_call_compile_callSiteCode_of_lookup
        (args := callArgs) hLookup hArgsLen callSegment with
    ⟨callSiteSegment, hCallSiteStart, hCallSiteFall⟩
  refine
    ⟨argStmts, argCtx, assignStmts, afterAssignCtx, restStmts,
      argSegment, callSiteSegment, assignSegment, tailSegment,
      hArgsCompile, hAssignCompile, hRestCompile, hArgStart, ?_, ?_,
      hTailStart, hTailFall⟩
  · calc
      Structured.Preservation.CodeSegment.startPc callSiteSegment =
          Structured.Preservation.CodeSegment.startPc callSegment :=
        hCallSiteStart
      _ = Structured.Preservation.CodeSegment.fallthroughPc argSegment :=
        hCallStart
  · calc
      Structured.Preservation.CodeSegment.startPc assignSegment =
          Structured.Preservation.CodeSegment.fallthroughPc callSegment :=
        hAssignStart
      _ = Structured.Preservation.CodeSegment.fallthroughPc
            callSiteSegment :=
        hCallSiteFall.symm

theorem codeSegment_functions_call_cons_callSite_parts_split_of_source_lookup
    {programSource : Functions.Program} {lower : Expressions.Program}
    {returns : List Name} {localsCtx finalLocalsCtx : Locals.Ctx}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {asm : Assembly.Program} {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {fn : Functions.FunDef} {callArgs : EvmYul.Stack Word}
    (hLower : Functions.Program.toExpressions? programSource = some lower)
    (hCtxProcs : structuredCtx.procs = lower.toStructured.procs)
    (hFind :
      Functions.FunList.find? functionName programSource.functions =
        some fn)
    (hArgsLen : callArgs.length = fn.params.length)
    (hCompile :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := Functions.Stmt.call targets functionName args :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (segment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code) :
    ∃ proc,
      proc.name = fn.name ∧
        proc.argc = fn.params.length ∧
        proc.retc = fn.returns.length ∧
        ∃ argStmts argCtx assignStmts afterAssignCtx restStmts,
          ∃ argSegment :
              Structured.Preservation.CodeSegment asm
                (Structured.Block.compileFromCtx
                  { stmts := Expressions.StmtList.toStructured argStmts }
                  structuredCtx supply).code,
            ∃ callSiteSegment :
                Structured.Preservation.CodeSegment asm
                  (Structured.Preservation.ProcedurePreservation.callSiteCode
                    proc callArgs (Structured.Stmt.callToken supply)
                    (Structured.LabelSupply.label supply 0)),
              ∃ assignSegment :
                  Structured.Preservation.CodeSegment asm
                    (Structured.Block.compileFromCtx
                      { stmts := Expressions.StmtList.toStructured assignStmts }
                      structuredCtx
                      (Structured.Stmt.compileFromCtxCore
                        (.call functionName) structuredCtx supply).next).code,
                ∃ tailSegment :
                    Structured.Preservation.CodeSegment asm
                      (Structured.Block.compileFromCtx
                        { stmts := Expressions.StmtList.toStructured restStmts }
                        structuredCtx
                        (Structured.Stmt.compileFromCtxCore
                          (.call functionName) structuredCtx supply).next).code,
                  Locals.Block.compileOpen localsCtx
                      { stmts := Functions.Lower.evalArgs args } =
                    some (argStmts, argCtx) ∧
                  Locals.Block.compileOpen argCtx
                      { stmts := Functions.Lower.assignReturnedTops targets } =
                    some (assignStmts, afterAssignCtx) ∧
                  Locals.Block.compileOpen afterAssignCtx
                      (Functions.Block.toLocals returns { stmts := rest }) =
                    some (restStmts, finalLocalsCtx) ∧
                  Structured.Preservation.CodeSegment.startPc argSegment =
                    Structured.Preservation.CodeSegment.startPc segment ∧
                  Structured.Preservation.CodeSegment.startPc
                      callSiteSegment =
                    Structured.Preservation.CodeSegment.fallthroughPc
                      argSegment ∧
                  Structured.Preservation.CodeSegment.startPc assignSegment =
                    Structured.Preservation.CodeSegment.fallthroughPc
                      callSiteSegment ∧
                  Structured.Preservation.CodeSegment.startPc tailSegment =
                    Structured.Preservation.CodeSegment.fallthroughPc
                      assignSegment ∧
                  Structured.Preservation.CodeSegment.fallthroughPc
                      tailSegment =
                    Structured.Preservation.CodeSegment.fallthroughPc
                      segment := by
  rcases
      functionsProgram_toExpressions?_structured_proc_lookup_parts
        hLower hFind with
    ⟨proc, hLookupLower, hProcName, hProcArgc, hProcRetc⟩
  have hLookupCtx :
      Structured.ProcList.lookup? functionName structuredCtx.procs =
        some proc := by
    simpa [hCtxProcs] using hLookupLower
  have hArgsLenProc : callArgs.length = proc.argc :=
    hArgsLen.trans hProcArgc.symm
  rcases
      codeSegment_functions_call_cons_callSite_parts_split_of_compileOpen
        hCompile hLookupCtx hArgsLenProc segment with
    ⟨argStmts, argCtx, assignStmts, afterAssignCtx, restStmts,
      argSegment, callSiteSegment, assignSegment, tailSegment,
      hArgsCompile, hAssignCompile, hRestCompile, hArgStart, hCallStart,
      hAssignStart, hTailStart, hTailFall⟩
  exact
    ⟨proc, hProcName, hProcArgc, hProcRetc, argStmts, argCtx, assignStmts,
      afterAssignCtx, restStmts, argSegment, callSiteSegment, assignSegment,
      tailSegment, hArgsCompile, hAssignCompile, hRestCompile, hArgStart,
      hCallStart, hAssignStart, hTailStart, hTailFall⟩

theorem openRunNResult_source_local_instr_no_call_running_continue
    {pre post : Assembly.Program} {instr : Assembly.Instr}
    {state mid : EvmYul.EVM.State}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hLocal :
      Structured.Preservation.StackShuffle.SourceLocalInstr instr)
    (hNoInstr : Assembly.Instr.usesCallCreate instr = false)
    (hNoHalt : instr.haltKind? = none)
    (hFit : Structured.Preservation.PCFits pre)
    (hPc : state.pc = Assembly.Program.pcAfter pre)
    (hStep :
      Assembly.Target.stepInstr
        (Structured.Preservation.StackShuffle.targetInstr instr) state =
        .ok mid)
    (hRest :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (pre ++ [instr] ++ post) fuel mid)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ [instr] ++ post) (fuel + 1) state)
      tailTrace result := by
  have hAt :
      Assembly.Program.instrAtPc
          (pre ++ [instr] ++ post) state.pc.toNat =
        some (Assembly.Program.byteLength pre, instr) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  have hClosed :
      Assembly.Source.stepResult (pre ++ [instr] ++ post) state =
        .ok (.running mid) :=
    Structured.Preservation.StackShuffle.source_stepResult_local
      hLocal hNoHalt hFit hPc hStep
  exact
    OpenAssembly.Source.openRunNResult_current_no_call_running_continue_of_current_instr
      hAt hNoInstr hClosed hRest

theorem openRunNResult_source_jump_no_call_running_continue
    {pre post : Assembly.Program} {label : Assembly.Label}
    {state : EvmYul.EVM.State} {dest : Nat}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFit : Structured.Preservation.PCFits pre)
    (hPc : state.pc = Assembly.Program.pcAfter pre)
    (hLabel :
      Assembly.Program.labelPc
        (pre ++ [Assembly.Instr.jump label] ++ post) label = some dest)
    (hRest :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (pre ++ [Assembly.Instr.jump label] ++ post) fuel
          (Assembly.Source.jumpPc dest state))
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ [Assembly.Instr.jump label] ++ post) (fuel + 1) state)
      tailTrace result := by
  have hAt :
      Assembly.Program.instrAtPc
          (pre ++ [Assembly.Instr.jump label] ++ post)
          state.pc.toNat =
        some (Assembly.Program.byteLength pre,
          Assembly.Instr.jump label) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post (Assembly.Instr.jump label) 0
  have hClosed :
      Assembly.Source.stepResult
          (pre ++ [Assembly.Instr.jump label] ++ post) state =
        .ok (.running (Assembly.Source.jumpPc dest state)) := by
    unfold Assembly.Source.stepResult
    rw [hAt]
    unfold Assembly.Source.stepAtResult Assembly.Source.stepAt
    have hLabel' :
        Assembly.Program.labelPc
            (pre ++ Assembly.Instr.jump label :: post) label =
          some dest := by
      simpa using hLabel
    simp [hLabel', Assembly.Source.invalid, Bind.bind, Except.bind,
      Assembly.Instr.haltKind?]
    rfl
  have hNoInstr :
      Assembly.Instr.usesCallCreate (Assembly.Instr.jump label) = false := by
    simp [Assembly.Instr.usesCallCreate]
  exact
    OpenAssembly.Source.openRunNResult_current_no_call_running_continue_of_current_instr
      hAt hNoInstr hClosed hRest

theorem openRunNResult_source_code_no_call_running_continue
    {pre post : Assembly.Program} {code : Structured.Code}
    {state final : EvmYul.EVM.State}
    {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hNoCall : Structured.Code.usesCallCreate code = false)
    (hFits : Structured.Preservation.Code.PCFitsFrom pre code)
    (hPc : state.pc = Assembly.Program.pcAfter pre)
    (hRun : Structured.Code.run code state = .ok final)
    (hRest :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (pre ++ code.toAssembly ++ post) tailFuel final)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ code.toAssembly ++ post) (code.length + tailFuel) state)
      tailTrace result := by
  induction code generalizing pre state with
  | nil =>
      simp [Structured.Code.run] at hRun
      cases hRun
      simpa [Structured.Code.toAssembly] using hRest
  | cons instr rest ih =>
      unfold Structured.Code.run at hRun
      cases hStep : instr.step state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok mid =>
          rw [hStep] at hRun
          have hNoParts :
              instr.usesCallCreate = false ∧
                Structured.Code.usesCallCreate rest = false := by
            simpa [Structured.Code.usesCallCreate] using hNoCall
          rcases hFits with ⟨hFitHere, hFitsRest⟩
          have hStepPc :
              mid.pc =
                state.pc + EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
            cases instr with
            | push value =>
                exact Structured.Preservation.BasicInstr.push_stepPC value hStep
            | op op =>
                simpa [Structured.BasicInstr.toAssembly,
                  Assembly.Instr.byteSize] using
                  basicOp_no_callCreate_step_pc
                    (op := op) hNoParts.1 hStep
          have hMidPc :
              mid.pc =
                Assembly.Program.pcAfter (pre ++ [instr.toAssembly]) := by
            calc
              mid.pc =
                  state.pc +
                    EvmYul.UInt256.ofNat instr.toAssembly.byteSize :=
                hStepPc
              _ =
                  Assembly.Program.pcAfter pre +
                    EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
                rw [hPc]
              _ = Assembly.Program.pcAfter (pre ++ [instr.toAssembly]) := by
                simp [Assembly.Program.pcAfter,
                  Assembly.Program.byteLength_append,
                  Assembly.Program.byteLength, Assembly.UInt256_ofNat_add]
          have hRestOpen :
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult
                  ((pre ++ [instr.toAssembly]) ++
                    Structured.Code.toAssembly rest ++ post)
                  (rest.length + tailFuel) mid)
                tailTrace result := by
            exact
              ih (pre := pre ++ [instr.toAssembly]) (state := mid)
                hNoParts.2 hFitsRest hMidPc hRun
                (by simpa [Structured.Code.toAssembly, List.append_assoc]
                  using hRest)
          have hLocal :
              Structured.Preservation.StackShuffle.SourceLocalInstr
                instr.toAssembly := by
            cases instr <;> simp [Structured.BasicInstr.toAssembly,
              Structured.Preservation.StackShuffle.SourceLocalInstr]
          have hNoInstr :
              Assembly.Instr.usesCallCreate instr.toAssembly = false := by
            simpa [Structured.BasicInstr.toAssembly_usesCallCreate]
              using hNoParts.1
          have hStepTarget :
              Assembly.Target.stepInstr
                  (Structured.Preservation.StackShuffle.targetInstr
                    instr.toAssembly) state =
                .ok mid := by
            cases instr <;> simpa [Structured.BasicInstr.toAssembly,
              Structured.Preservation.StackShuffle.targetInstr] using hStep
          have hCurrent :
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult
                  (pre ++ [instr.toAssembly] ++
                    (Structured.Code.toAssembly rest ++ post))
                  ((rest.length + tailFuel) + 1) state)
                tailTrace result :=
            openRunNResult_source_local_instr_no_call_running_continue
              (pre := pre) (post := Structured.Code.toAssembly rest ++ post)
              (instr := instr.toAssembly) (state := state) (mid := mid)
              (fuel := rest.length + tailFuel)
              hLocal hNoInstr
              (Structured.Preservation.BasicInstr.toAssembly_haltKind?_none
                instr)
              hFitHere hPc hStepTarget
              (by simpa [List.append_assoc] using hRestOpen)
          simpa [Structured.Code.toAssembly, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCurrent

theorem openRunNResult_source_code_no_call_relAt_running_continue
    {pre post : Assembly.Program} {code : Structured.Code}
    {source target source' : EvmYul.EVM.State}
    {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hSafe : Structured.Preservation.Code.RunnerSafe code)
    (hNoCall : Structured.Code.usesCallCreate code = false)
    (hFits : Structured.Preservation.Code.PCFitsFrom pre code)
    (hRel :
      Structured.Preservation.RelAt
        (Assembly.Program.pcAfter pre) target source)
    (hRun : Structured.Code.run code source = .ok source')
    (hRest :
      ∀ targetFinal,
        Structured.Preservation.RelAt
          (Assembly.Program.pcAfter (pre ++ code.toAssembly))
          targetFinal source' →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ code.toAssembly ++ post) tailFuel targetFinal)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ code.toAssembly ++ post) (code.length + tailFuel) target)
      tailTrace result := by
  induction code generalizing pre source target with
  | nil =>
      simp [Structured.Code.run] at hRun
      cases hRun
      simpa [Structured.Code.toAssembly] using
        hRest target (by simpa [Structured.Code.toAssembly] using hRel)
  | cons instr rest ih =>
      cases hSafe with
      | cons hInstr hRestSafe =>
          unfold Structured.Code.run at hRun
          cases hStep : instr.step source with
          | error err =>
              rw [hStep] at hRun
              cases hRun
          | ok sourceMid =>
              rw [hStep] at hRun
              have hNoParts :
                  instr.usesCallCreate = false ∧
                    Structured.Code.usesCallCreate rest = false := by
                simpa [Structured.Code.usesCallCreate] using hNoCall
              rcases hFits with ⟨hFitHere, hFitsRest⟩
              obtain ⟨targetMid, hAssemblyStep, hRelMid⟩ :=
                Structured.Preservation.BasicInstr.source_stepResult_ctx_relAt_of_relAt
                  (instr := instr) (pre := pre)
                  (post := Structured.Code.toAssembly rest ++ post)
                  hInstr hFitHere hRel hStep
              have hRestOpen :
                  OpenExternal.OpenResultResolves
                    (OpenAssembly.Source.openRunNResult
                      ((pre ++ [instr.toAssembly]) ++
                        Structured.Code.toAssembly rest ++ post)
                      (rest.length + tailFuel) targetMid)
                    tailTrace result := by
                exact
                  ih (pre := pre ++ [instr.toAssembly])
                    (source := sourceMid) (target := targetMid)
                    hRestSafe hNoParts.2 hFitsRest hRelMid hRun
                    (by
                      intro targetFinal hRelFinal
                      simpa [Structured.Code.toAssembly, List.append_assoc]
                        using
                          hRest targetFinal
                            (by simpa [Structured.Code.toAssembly,
                              List.append_assoc] using hRelFinal))
              have hAt :
                  Assembly.Program.instrAtPc
                    (pre ++ [instr.toAssembly] ++
                      (Structured.Code.toAssembly rest ++ post))
                    target.pc.toNat =
                    some (Assembly.Program.byteLength pre,
                      instr.toAssembly) := by
                unfold Assembly.Program.instrAtPc
                rw [hRel.pc_eq, hFitHere]
                simpa using
                  Assembly.Program.instrAtPcFrom_append_boundary_cons
                    pre (Structured.Code.toAssembly rest ++ post)
                    instr.toAssembly 0
              have hNoInstr :
                  Assembly.Instr.usesCallCreate instr.toAssembly = false := by
                simpa [Structured.BasicInstr.toAssembly_usesCallCreate]
                  using hNoParts.1
              have hStepResult :
                  Assembly.Source.stepResult
                    (pre ++ [instr.toAssembly] ++
                      (Structured.Code.toAssembly rest ++ post)) target =
                    .ok (.running targetMid) := by
                simpa [List.append_assoc] using hAssemblyStep
              have hCurrent :
                  OpenExternal.OpenResultResolves
                    (OpenAssembly.Source.openRunNResult
                      (pre ++ [instr.toAssembly] ++
                        (Structured.Code.toAssembly rest ++ post))
                      ((rest.length + tailFuel) + 1) target)
                    tailTrace result :=
                OpenAssembly.Source.openRunNResult_current_no_call_running_continue_of_current_instr
                  hAt hNoInstr hStepResult
                  (by simpa [List.append_assoc] using hRestOpen)
              simpa [Structured.Code.toAssembly, List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCurrent

theorem openRunNResult_source_code_no_call_frameStateRel_running_continue
    {pre post : Assembly.Program} {code : Structured.Code}
    {source final : Structured.RunState}
    {target : EvmYul.EVM.State} {tokens : List Word}
    {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hSafe : Structured.Preservation.Code.RunnerSafe code)
    (hFrame : Structured.Code.FrameSafe code)
    (hNoCall : Structured.Code.usesCallCreate code = false)
    (hFits : Structured.Preservation.Code.PCFitsFrom pre code)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Structured.Preservation.Frame.StateRel source target tokens)
    (hRun : Structured.Code.runState code source = .ok final)
    (hRest :
      ∀ targetFinal,
        Structured.Preservation.Frame.StateRel final targetFinal tokens →
        targetFinal.pc =
          Assembly.Program.pcAfter (pre ++ code.toAssembly) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ code.toAssembly ++ post) tailFuel targetFinal)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ code.toAssembly ++ post) (code.length + tailFuel) target)
      tailTrace result := by
  rcases hRel.runState_frameSafe_hidden_exists hFrame hRun with
    ⟨hiddenFinal, hHiddenRun, hHiddenRel⟩
  have hRelAt :
      Structured.Preservation.RelAt (Assembly.Program.pcAfter pre) target
        { source.evm with stack := target.stack } := by
    exact ⟨hPc, hRel.dataRel⟩
  exact
    openRunNResult_source_code_no_call_relAt_running_continue
      (pre := pre) (post := post) (code := code)
      hSafe hNoCall hFits hRelAt hHiddenRun
      (by
        intro targetFinal hRelFinal
        have hStack : targetFinal.stack = hiddenFinal.stack :=
          Structured.Preservation.stack_eq_of_eraseControl_eq
            hRelFinal.sameData
        have hFrameRel :
            Structured.Preservation.Frame.StateRel final targetFinal
              tokens := by
          refine ⟨?_, ?_⟩
          · rw [hStack]
            exact hHiddenRel.stackRel
          · calc
              Structured.Preservation.eraseControl targetFinal
                  = Structured.Preservation.eraseControl hiddenFinal :=
                    hRelFinal.sameData
              _ =
                  Structured.Preservation.eraseControl
                    { final.evm with stack := hiddenFinal.stack } :=
                    hHiddenRel.dataRel
              _ =
                  Structured.Preservation.eraseControl
                    { final.evm with stack := targetFinal.stack } := by
                    rw [hStack]
        exact hRest targetFinal hFrameRel hRelFinal.pc_eq)

theorem structuredCode_run_no_call_fallthrough_pc
    {pre : Assembly.Program} {code : Structured.Code}
    {state final : EvmYul.EVM.State}
    (hNoCall : Structured.Code.usesCallCreate code = false)
    (hFits : Structured.Preservation.Code.PCFitsFrom pre code)
    (hPc : state.pc = Assembly.Program.pcAfter pre)
    (hRun : Structured.Code.run code state = .ok final) :
    final.pc = Assembly.Program.pcAfter (pre ++ code.toAssembly) := by
  induction code generalizing pre state with
  | nil =>
      simp [Structured.Code.run] at hRun
      cases hRun
      simpa [Structured.Code.toAssembly] using hPc
  | cons instr rest ih =>
      unfold Structured.Code.run at hRun
      cases hStep : instr.step state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok mid =>
          rw [hStep] at hRun
          have hNoParts :
              instr.usesCallCreate = false ∧
                Structured.Code.usesCallCreate rest = false := by
            simpa [Structured.Code.usesCallCreate] using hNoCall
          rcases hFits with ⟨hFitHere, hFitsRest⟩
          have hStepPc :
              mid.pc =
                state.pc + EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
            cases instr with
            | push value =>
                exact Structured.Preservation.BasicInstr.push_stepPC value hStep
            | op op =>
                simpa [Structured.BasicInstr.toAssembly,
                  Assembly.Instr.byteSize] using
                  basicOp_no_callCreate_step_pc
                    (op := op) hNoParts.1 hStep
          have hMidPc :
              mid.pc =
                Assembly.Program.pcAfter (pre ++ [instr.toAssembly]) := by
            calc
              mid.pc =
                  state.pc +
                    EvmYul.UInt256.ofNat instr.toAssembly.byteSize :=
                hStepPc
              _ =
                  Assembly.Program.pcAfter pre +
                    EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
                rw [hPc]
              _ = Assembly.Program.pcAfter (pre ++ [instr.toAssembly]) := by
                simp [Assembly.Program.pcAfter,
                  Assembly.Program.byteLength_append,
                  Assembly.Program.byteLength, Assembly.UInt256_ofNat_add]
          have hFinalPc :=
            ih hNoParts.2 hFitsRest hMidPc hRun
          simpa [Structured.Code.toAssembly, List.append_assoc] using hFinalPc

theorem structuredCode_run_codeSegment_no_call_fallthroughPc
    {program : Assembly.Program} {code : Structured.Code}
    {state final : EvmYul.EVM.State}
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hNoCall : Structured.Code.usesCallCreate code = false)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hRun : Structured.Code.run code state = .ok final) :
    final.pc = Structured.Preservation.CodeSegment.fallthroughPc segment := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  subst program
  have hCodeFits :
      Structured.Preservation.Code.PCFitsFrom pre code :=
    Structured.Preservation.Code.PCFitsFrom.of_assembly hFits
  exact structuredCode_run_no_call_fallthrough_pc hNoCall hCodeFits hPc hRun

theorem openRunNResult_codeSegment_no_call_running_continue
    {program : Assembly.Program} {code : Structured.Code}
    {state final : EvmYul.EVM.State}
    {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hNoCall : Structured.Code.usesCallCreate code = false)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hRun : Structured.Code.run code state = .ok final)
    (hRest :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program tailFuel final)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult program
        (code.length + tailFuel) state)
      tailTrace result := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  subst program
  have hCodeFits :
      Structured.Preservation.Code.PCFitsFrom pre code :=
    Structured.Preservation.Code.PCFitsFrom.of_assembly hFits
  exact
    openRunNResult_source_code_no_call_running_continue
      (pre := pre) (post := post) (code := code)
      hNoCall hCodeFits hPc hRun hRest

theorem openRunNResult_cleanupToPreserving_runState_continue
    {program : Assembly.Program} {ctx : Locals.Ctx}
    {preserve targetDepth : Nat} {cleanup : Structured.Code}
    {state final : Locals.RunState}
    {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hCleanup :
      ctx.cleanupToPreserving? preserve targetDepth = some cleanup)
    (segment :
      Structured.Preservation.CodeSegment program cleanup.toAssembly)
    (hPc :
      state.evm.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hRun :
      Locals.Direct.Ctx.runCleanupToPreserving ctx preserve targetDepth
        state = .ok final)
    (hRest :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program tailFuel final.evm)
        tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult program
        (cleanup.length + tailFuel) state.evm)
      tailTrace result := by
  have hRunState :
      Structured.Code.runState cleanup state = .ok final :=
    locals_runCleanupToPreserving_runState_of_cleanupToPreserving
      hCleanup hRun
  have hRunCode :
      Structured.Code.run cleanup state.evm = .ok final.evm :=
    structuredCode_run_of_runState hRunState
  have hNoCall :
      Structured.Code.usesCallCreate cleanup = false :=
    Locals.CompilerFacts.Ctx.cleanupToPreserving?_noCallCreate hCleanup
  exact
    openRunNResult_codeSegment_no_call_running_continue
      segment hNoCall hPc hRunCode hRest

theorem openRunNResult_cleanupToPreserving_frameStateRel_continue
    {program : Assembly.Program} {ctx : Locals.Ctx}
    {preserve targetDepth : Nat} {cleanup : Structured.Code}
    {state final : Locals.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word}
    {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hCleanup :
      ctx.cleanupToPreserving? preserve targetDepth = some cleanup)
    (segment :
      Structured.Preservation.CodeSegment program cleanup.toAssembly)
    (hPc :
      target.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hRel :
      Structured.Preservation.Frame.StateRel state target tokens)
    (hRun :
      Locals.Direct.Ctx.runCleanupToPreserving ctx preserve targetDepth
        state = .ok final)
    (hRest :
      ∀ targetFinal,
        Structured.Preservation.Frame.StateRel final targetFinal tokens →
        targetFinal.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel targetFinal)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult program
        (cleanup.length + tailFuel) target)
      tailTrace result := by
  rcases segment with ⟨pre, post, hAsm, hFits⟩
  subst program
  have hCodeFits :
      Structured.Preservation.Code.PCFitsFrom pre cleanup :=
    Structured.Preservation.Code.PCFitsFrom.of_assembly hFits
  have hRunState :
      Structured.Code.runState cleanup state = .ok final :=
    locals_runCleanupToPreserving_runState_of_cleanupToPreserving
      hCleanup hRun
  have hNoCall :
      Structured.Code.usesCallCreate cleanup = false :=
    Locals.CompilerFacts.Ctx.cleanupToPreserving?_noCallCreate hCleanup
  have hSafe :
      Structured.Preservation.Code.RunnerSafe cleanup :=
    structuredCode_runnerSafe_cleanupToPreserving? hCleanup
  have hFrame :
      Structured.Code.FrameSafe cleanup :=
    structuredCode_frameSafe_cleanupToPreserving? hCleanup
  exact
    openRunNResult_source_code_no_call_frameStateRel_running_continue
      (pre := pre) (post := post) (code := cleanup)
      hSafe hFrame hNoCall hCodeFits hPc hRel hRunState
      (by
        intro targetFinal hRelFinal hPcFinal
        exact hRest targetFinal hRelFinal hPcFinal)

theorem openRunNResult_source_jumpi_no_call_running_continue
    {pre post : Assembly.Program} {label : Assembly.Label}
    {state afterPop : EvmYul.EVM.State} {condTrue : Bool}
    {dest : Nat}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFit : Structured.Preservation.PCFits pre)
    (hPc : state.pc = Assembly.Program.pcAfter pre)
    (hLabel :
      Assembly.Program.labelPc
        (pre ++ [Assembly.Instr.jumpi label] ++ post) label = some dest)
    (hPop : Structured.Code.popCondition state = .ok (afterPop, condTrue))
    (hRest :
      ∀ afterJump : EvmYul.EVM.State,
        Structured.Preservation.RelAt
          (if condTrue then
            EvmYul.UInt256.ofNat dest
          else
            Assembly.Program.pcAfter (pre ++ [Assembly.Instr.jumpi label]))
          afterJump afterPop →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ [Assembly.Instr.jumpi label] ++ post) fuel afterJump)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ [Assembly.Instr.jumpi label] ++ post) (fuel + 1) state)
      tailTrace result := by
  have hAt :
      Assembly.Program.instrAtPc
          (pre ++ [Assembly.Instr.jumpi label] ++ post) state.pc.toNat =
        some (Assembly.Program.byteLength pre, Assembly.Instr.jumpi label) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post (Assembly.Instr.jumpi label) 0
  have hRelAt :
      Structured.Preservation.RelAt (Assembly.Program.pcAfter pre)
        state state := by
    exact ⟨hPc, rfl⟩
  rcases
      Structured.Preservation.AssemblyControl.jumpi_stepResult_ctx_relAt_of_popCondition
        (label := label) (dest := dest) (pre := pre) (post := post)
        (source := state) (target := state) (source' := afterPop)
        (condTrue := condTrue) hFit hRelAt hLabel hPop with
    ⟨afterJump, hStep, hRelAfter⟩
  have hNoInstr :
      Assembly.Instr.usesCallCreate (Assembly.Instr.jumpi label) = false := by
    simp [Assembly.Instr.usesCallCreate]
  exact
    OpenAssembly.Source.openRunNResult_current_no_call_running_continue_of_current_instr
      hAt hNoInstr hStep (hRest afterJump hRelAfter)

theorem openRunNResult_dispatchCondition_source_running_continue
    {state : EvmYul.EVM.State}
    {returnValues suffix : List Word} {token probe : Word}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        ])
    (hPc :
      ({ state with stack := returnValues ++ token :: suffix }).pc =
        Assembly.Program.pcAfter pre)
    (hBound : returnValues.length < 16)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        final.stack =
          EvmYul.UInt256.eq probe token ::
            returnValues ++ token :: suffix →
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { state with stack :=
                EvmYul.UInt256.eq probe token ::
                  returnValues ++ token :: suffix } →
        final.pc =
          Assembly.Program.pcAfter
            (pre ++
              [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
              , Assembly.Instr.push probe
              , Assembly.Instr.prim .eq
              ]) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
              , Assembly.Instr.push probe
              , Assembly.Instr.prim .eq
              ] ++ post) fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++
          [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          ] ++ post) (3 + fuel)
        { state with stack := returnValues ++ token :: suffix })
      tailTrace result := by
  let dupInstr := Structured.StackShuffle.dupInstr (returnValues.length + 1)
  let fullProgram : Assembly.Program :=
    pre ++ [dupInstr, Assembly.Instr.push probe, Assembly.Instr.prim .eq] ++
      post
  let start : EvmYul.EVM.State :=
    { state with stack := returnValues ++ token :: suffix }
  let afterDup : EvmYul.EVM.State :=
    EvmYul.EVM.State.replaceStackAndIncrPC start
      (token :: returnValues ++ token :: suffix)
  let afterPush : EvmYul.EVM.State :=
    afterDup.replaceStackAndIncrPC
      (probe :: token :: returnValues ++ token :: suffix) (pcΔ := 33)
  let finalState : EvmYul.EVM.State :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.eq probe token ::
        returnValues ++ token :: suffix)
  have hDupStep :
      Assembly.Target.stepInstr
          (Structured.Preservation.StackShuffle.targetInstr dupInstr)
          start =
        .ok afterDup := by
    rw [show dupInstr =
      Structured.StackShuffle.dupInstr (returnValues.length + 1) from rfl]
    rw [Structured.Preservation.StackShuffle.dupInstr_step_eq_dup
      (by omega) (by omega)]
    simpa [afterDup, start, List.append_assoc] using
      (Structured.Preservation.StackShuffle.dup_append_token
        (state := state) (front := returnValues)
        (suffix := suffix) (token := token))
  have hPushStep :
      Assembly.Target.stepInstr
          (Structured.Preservation.StackShuffle.targetInstr
            (Assembly.Instr.push probe)) afterDup =
        .ok afterPush := by
    simp [Structured.Preservation.StackShuffle.targetInstr, afterPush,
      afterDup, Assembly.Target.stepInstr, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  have hEqStep :
      Assembly.Target.stepInstr
          (Structured.Preservation.StackShuffle.targetInstr
            (Assembly.Instr.prim .eq)) afterPush =
        .ok finalState := by
    simp [Structured.Preservation.StackShuffle.targetInstr, finalState,
      afterPush, afterDup, Assembly.Target.stepInstr,
      Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, EvmYul.EVM.execBinOp, EvmYul.Stack.push,
      EvmYul.Stack.pop2, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hDupByte : dupInstr.byteSize = 1 := by
    exact
      Structured.Preservation.StackShuffle.dupInstr_byteSize
        (n := returnValues.length + 1) (by omega) (by omega)
  have hAfterDupPc :
      afterDup.pc = Assembly.Program.pcAfter (pre ++ [dupInstr]) := by
    have hPcState : state.pc = Assembly.Program.pcAfter pre := by
      simpa [start] using hPc
    calc
      afterDup.pc
          = state.pc + EvmYul.UInt256.ofNat 1 := by
              simp [afterDup, start, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
      _ = Assembly.Program.pcAfter pre + EvmYul.UInt256.ofNat 1 := by
              rw [hPcState]
      _ = EvmYul.UInt256.ofNat (Assembly.Program.byteLength pre + 1) := by
              rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ = Assembly.Program.pcAfter (pre ++ [dupInstr]) := by
              simp [Assembly.Program.pcAfter,
                Assembly.Program.byteLength_append,
                Assembly.Program.byteLength, hDupByte]
  have hAfterPushPc :
      afterPush.pc =
        Assembly.Program.pcAfter
          (pre ++ [dupInstr, Assembly.Instr.push probe]) := by
    calc
      afterPush.pc
          = afterDup.pc + EvmYul.UInt256.ofNat 33 := by
              simp [afterPush, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
      _ =
        Assembly.Program.pcAfter (pre ++ [dupInstr]) +
          EvmYul.UInt256.ofNat 33 := by
              rw [hAfterDupPc]
      _ =
        EvmYul.UInt256.ofNat
          (Assembly.Program.byteLength (pre ++ [dupInstr]) + 33) := by
              rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ =
        Assembly.Program.pcAfter
          (pre ++ [dupInstr, Assembly.Instr.push probe]) := by
              simp [Assembly.Program.pcAfter,
                Assembly.Program.byteLength_append,
                Assembly.Program.byteLength, Assembly.Instr.byteSize,
                Assembly.Instr.push32Size, Nat.add_assoc]
  have hEqFit :
      Structured.Preservation.PCFits
        (pre ++ [dupInstr, Assembly.Instr.push probe]) := by
    simpa [dupInstr] using hFits.2.2.1
  have hFinalStack :
      finalState.stack =
        EvmYul.UInt256.eq probe token ::
          returnValues ++ token :: suffix := by
    simp [finalState, afterPush, afterDup,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  have hFinalErase :
      Structured.Preservation.eraseControl finalState =
        Structured.Preservation.eraseControl
          { state with stack :=
              EvmYul.UInt256.eq probe token ::
                returnValues ++ token :: suffix } := by
    simp [finalState, afterPush, afterDup, start,
      Structured.Preservation.eraseControl, Assembly.eraseGas,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  have hFinalPc :
      finalState.pc =
        Assembly.Program.pcAfter
          (pre ++ [dupInstr, Assembly.Instr.push probe,
            Assembly.Instr.prim .eq]) := by
    calc
      finalState.pc
          = afterPush.pc + EvmYul.UInt256.ofNat 1 := by
              simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
      _ =
        Assembly.Program.pcAfter
            (pre ++ [dupInstr, Assembly.Instr.push probe]) +
          EvmYul.UInt256.ofNat 1 := by
              rw [hAfterPushPc]
      _ =
        EvmYul.UInt256.ofNat
          (Assembly.Program.byteLength
            (pre ++ [dupInstr, Assembly.Instr.push probe]) + 1) := by
              rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ =
        Assembly.Program.pcAfter
          (pre ++ [dupInstr, Assembly.Instr.push probe,
            Assembly.Instr.prim .eq]) := by
              simp [Assembly.Program.pcAfter,
                Assembly.Program.byteLength_append, Assembly.Program.byteLength,
                Assembly.Instr.byteSize, Nat.add_assoc]
  have hRestFinal :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult fullProgram fuel finalState)
        tailTrace result := by
    simpa [fullProgram, dupInstr] using
      hRest finalState hFinalStack hFinalErase hFinalPc
  have hEqRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult fullProgram (fuel + 1)
          afterPush)
        tailTrace result := by
    have hRun :=
      openRunNResult_source_local_instr_no_call_running_continue
        (instr := Assembly.Instr.prim .eq)
        (pre := pre ++ [dupInstr, Assembly.Instr.push probe])
        (post := post) (state := afterPush) (mid := finalState)
        (fuel := fuel) (tailTrace := tailTrace) (result := result)
        (by simp [Structured.Preservation.StackShuffle.SourceLocalInstr])
        (by simp [Assembly.Instr.usesCallCreate, Assembly.PrimOp.isCallCreate])
        rfl hEqFit hAfterPushPc hEqStep
        (by simpa [fullProgram, List.append_assoc] using hRestFinal)
    simpa [fullProgram, List.append_assoc] using hRun
  have hPushRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult fullProgram ((fuel + 1) + 1)
          afterDup)
        tailTrace result := by
    have hRun :=
      openRunNResult_source_local_instr_no_call_running_continue
        (instr := Assembly.Instr.push probe)
        (pre := pre ++ [dupInstr])
        (post := [Assembly.Instr.prim .eq] ++ post)
        (state := afterDup) (mid := afterPush)
        (fuel := fuel + 1) (tailTrace := tailTrace) (result := result)
        (by simp [Structured.Preservation.StackShuffle.SourceLocalInstr])
        (by simp [Assembly.Instr.usesCallCreate])
        rfl hFits.2.1 hAfterDupPc hPushStep
        (by simpa [fullProgram, List.append_assoc] using hEqRun)
    simpa [fullProgram, List.append_assoc] using hRun
  have hDupRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult fullProgram
          (((fuel + 1) + 1) + 1) start)
        tailTrace result := by
    have hRun :=
      openRunNResult_source_local_instr_no_call_running_continue
        (instr := dupInstr) (pre := pre)
        (post := [Assembly.Instr.push probe, Assembly.Instr.prim .eq] ++ post)
        (state := start) (mid := afterDup)
        (fuel := (fuel + 1) + 1) (tailTrace := tailTrace)
        (result := result)
        (Structured.Preservation.StackShuffle.dupInstr_sourceLocal
          (n := returnValues.length + 1) (by omega) (by omega))
        (by
          simpa [dupInstr] using
            Structured.CompilerFacts.GeneratedNoCallCreate.dupInstr
              (returnValues.length + 1))
        (Structured.Preservation.StackShuffle.dupInstr_haltKind?_none
          (n := returnValues.length + 1) (by omega) (by omega))
        hFits.1 (by simpa [start] using hPc) hDupStep
        (by simpa [fullProgram, List.append_assoc] using hPushRun)
    simpa [fullProgram, List.append_assoc] using hRun
  have hFuel : ((fuel + 1) + 1) + 1 = 3 + fuel := by
    omega
  simpa [fullProgram, dupInstr, start, hFuel] using hDupRun

theorem openRunNResult_dispatchCondition_jumpi_source_running_continue
    {state : EvmYul.EVM.State}
    {returnValues suffix : List Word} {token probe : Word}
    {label : Assembly.Label} {dest : Nat}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        , Assembly.Instr.jumpi label
        ])
    (hPc :
      ({ state with stack := returnValues ++ token :: suffix }).pc =
        Assembly.Program.pcAfter pre)
    (hBound : returnValues.length < 16)
    (hLabel :
      Assembly.Program.labelPc
        (pre ++
          [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi label
          ] ++ post)
        label = some dest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        final.stack = returnValues ++ token :: suffix →
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { state with stack := returnValues ++ token :: suffix } →
        (final.pc =
          (if probe = token then
              EvmYul.UInt256.ofNat dest
            else
              Assembly.Program.pcAfter
                (pre ++
                  [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
                  , Assembly.Instr.push probe
                  , Assembly.Instr.prim .eq
                  , Assembly.Instr.jumpi label
                  ]))) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
              , Assembly.Instr.push probe
              , Assembly.Instr.prim .eq
              , Assembly.Instr.jumpi label
              ] ++ post) fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++
          [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi label
          ] ++ post) (4 + fuel)
        { state with stack := returnValues ++ token :: suffix })
      tailTrace result := by
  let conditionCode : Assembly.Program :=
    [ Structured.StackShuffle.dupInstr (returnValues.length + 1)
    , Assembly.Instr.push probe
    , Assembly.Instr.prim .eq
    ]
  have hFitsCond :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        conditionCode := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.left
        (pre := pre) (first := conditionCode)
        (second := [Assembly.Instr.jumpi label])
        (by simpa [conditionCode] using hFits)
  have hFitsJump :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (pre ++ conditionCode) [Assembly.Instr.jumpi label] := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (pre := pre) (first := conditionCode)
        (second := [Assembly.Instr.jumpi label])
        (by simpa [conditionCode] using hFits)
  have hLabelJump :
      Assembly.Program.labelPc
        ((pre ++ conditionCode) ++ [Assembly.Instr.jumpi label] ++ post)
        label = some dest := by
    simpa [conditionCode, List.append_assoc] using hLabel
  have hConditionRun :=
    openRunNResult_dispatchCondition_source_running_continue
      (state := state) (returnValues := returnValues) (suffix := suffix)
      (token := token) (probe := probe) (pre := pre)
      (post := [Assembly.Instr.jumpi label] ++ post)
      (fuel := fuel + 1) (tailTrace := tailTrace) (result := result)
      (by simpa [conditionCode] using hFitsCond) hPc hBound
      (by
        intro mid hMidStack hMidErase hMidPc
        let afterPop : EvmYul.EVM.State :=
          { mid with stack := returnValues ++ token :: suffix }
        have hPop :
            Structured.Code.popCondition mid = .ok (afterPop, probe = token) := by
          unfold Structured.Code.popCondition
          rw [hMidStack]
          simp [EvmYul.Stack.pop, afterPop,
            Structured.Preservation.uint256_eq_ne_zero]
        have hJumpRun :=
          openRunNResult_source_jumpi_no_call_running_continue
            (label := label) (dest := dest)
            (pre := pre ++ conditionCode) (post := post)
            (state := mid) (afterPop := afterPop)
            (condTrue := probe = token)
            (fuel := fuel) (tailTrace := tailTrace) (result := result)
            (Structured.Preservation.AssemblyProgram.PCFitsFrom.start
              hFitsJump)
            (by simpa [conditionCode] using hMidPc)
            hLabelJump hPop
            (by
              intro afterJump hRelAfter
              have hStack :
                  afterJump.stack = returnValues ++ token :: suffix := by
                have hStackEq :=
                  Structured.Preservation.stack_eq_of_eraseControl_eq
                    hRelAfter.sameData
                simpa [afterPop] using hStackEq
              have hErase :
                  Structured.Preservation.eraseControl afterJump =
                    Structured.Preservation.eraseControl
                      { state with stack := returnValues ++ token :: suffix } := by
                calc
                  Structured.Preservation.eraseControl afterJump =
                      Structured.Preservation.eraseControl afterPop :=
                    hRelAfter.sameData
                  _ =
                      Structured.Preservation.eraseControl
                        { mid with stack := returnValues ++ token :: suffix } := by
                    rfl
                  _ =
                      Structured.Preservation.eraseControl
                        { { state with
                            stack :=
                              EvmYul.UInt256.eq probe token ::
                                returnValues ++ token :: suffix } with
                          stack := returnValues ++ token :: suffix } := by
                    exact
                      Structured.Preservation.eraseControl_with_stack_congr
                        (left := mid)
                        (right :=
                          { state with
                            stack :=
                              EvmYul.UInt256.eq probe token ::
                                returnValues ++ token :: suffix })
                        (stack := returnValues ++ token :: suffix)
                        hMidErase
                  _ =
                      Structured.Preservation.eraseControl
                        { state with stack := returnValues ++ token :: suffix } := by
                    simp [Structured.Preservation.eraseControl,
                      Assembly.eraseGas]
              have hPcFinal :
                  afterJump.pc =
                    (if probe = token then
                        EvmYul.UInt256.ofNat dest
                      else
                        Assembly.Program.pcAfter
                          (pre ++
                            [ Structured.StackShuffle.dupInstr
                                (returnValues.length + 1)
                            , Assembly.Instr.push probe
                            , Assembly.Instr.prim .eq
                            , Assembly.Instr.jumpi label
                            ])) := by
                simpa [conditionCode, List.append_assoc] using
                  hRelAfter.pc_eq
              simpa [conditionCode, List.append_assoc] using
                hRest afterJump hStack hErase hPcFinal)
        simpa [conditionCode, List.append_assoc] using hJumpRun)
  have hFuel : 3 + (fuel + 1) = 4 + fuel := by
    omega
  simpa [conditionCode, hFuel, List.append_assoc] using hConditionRun

theorem stackShuffle_swapInstr_usesCallCreate_false {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    Assembly.Instr.usesCallCreate (Structured.StackShuffle.swapInstr n) =
      false := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> rfl

theorem openRunNResult_sinkTopUnder_source_running_continue
    {state : EvmYul.EVM.State}
    {args suffix : List Word} {token : Word}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (Structured.StackShuffle.sinkTopUnder args.length))
    (hPc :
      ({ state with stack := token :: args ++ suffix } :
          EvmYul.EVM.State).pc =
        Assembly.Program.pcAfter pre)
    (hBound : args.length ≤ 16)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        final.stack = args ++ token :: suffix →
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { state with stack := args ++ token :: suffix } →
        final.pc =
          Assembly.Program.pcAfter
            (pre ++ Structured.StackShuffle.sinkTopUnder args.length) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ Structured.StackShuffle.sinkTopUnder args.length ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ Structured.StackShuffle.sinkTopUnder args.length ++ post)
        ((Structured.StackShuffle.sinkTopUnder args.length).length + fuel)
        { state with stack := token :: args ++ suffix })
      tailTrace result := by
  induction args using List.reverseRecOn generalizing state suffix token pre with
  | nil =>
      have hRestStart :=
        hRest { state with stack := token :: suffix }
          (by simp)
          (by rfl)
          (by simpa [Structured.StackShuffle.sinkTopUnder] using hPc)
      simpa [Structured.StackShuffle.sinkTopUnder] using hRestStart
  | append_singleton front last ih =>
      have hSwapBound : front.length + 1 ≤ 16 := by
        simpa [List.length_append] using hBound
      have hFrontBound : front.length ≤ 16 := by omega
      let swap := Structured.StackShuffle.swapInstr (front.length + 1)
      let start : EvmYul.EVM.State :=
        { state with stack := token :: front ++ [last] ++ suffix }
      let mid : EvmYul.EVM.State :=
        start.replaceStackAndIncrPC (last :: front ++ [token] ++ suffix)
      have hStep :
          Assembly.Target.stepInstr
              (Structured.Preservation.StackShuffle.targetInstr swap)
              start =
            .ok mid := by
        rw [show swap =
            Structured.StackShuffle.swapInstr (front.length + 1) from rfl]
        rw [Structured.Preservation.StackShuffle.swapInstr_step_eq_swap
          (by omega) hSwapBound]
        exact
          Structured.Preservation.StackShuffle.swap_snoc
            (state := state) (front := front) (suffix := suffix)
            (top := token) (last := last)
      have hSwapLocal :
          Structured.Preservation.StackShuffle.SourceLocalInstr swap := by
        exact
          Structured.Preservation.StackShuffle.swapInstr_sourceLocal
            (n := front.length + 1) (by omega) hSwapBound
      have hSwapNoHalt : swap.haltKind? = none := by
        exact
          Structured.Preservation.StackShuffle.swapInstr_haltKind?_none
            (n := front.length + 1) (by omega) hSwapBound
      have hSwapByte : swap.byteSize = 1 := by
        exact
          Structured.Preservation.StackShuffle.swapInstr_byteSize
            (n := front.length + 1) (by omega) hSwapBound
      have hSwapNoInstr :
          Assembly.Instr.usesCallCreate swap = false := by
        exact
          stackShuffle_swapInstr_usesCallCreate_false
            (n := front.length + 1) (by omega) hSwapBound
      have hFitsCons :
          Structured.Preservation.PCFits pre ∧
            Structured.Preservation.AssemblyProgram.PCFitsFrom
              (pre ++ [swap])
              (Structured.StackShuffle.sinkTopUnder front.length) := by
        simpa [Structured.StackShuffle.sinkTopUnder, List.length_append,
          swap, List.append_assoc] using hFits
      have hPcState : state.pc = Assembly.Program.pcAfter pre := by
        simpa [start, List.append_assoc] using hPc
      have hAfterSwapPc :
          mid.pc = Assembly.Program.pcAfter (pre ++ [swap]) := by
        calc
          mid.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
              simp [mid, start, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
          _ = Assembly.Program.pcAfter pre + EvmYul.UInt256.ofNat 1 := by
              rw [hPcState]
          _ = EvmYul.UInt256.ofNat
                (Assembly.Program.byteLength pre + 1) := by
              rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
          _ = Assembly.Program.pcAfter (pre ++ [swap]) := by
              simp [Assembly.Program.pcAfter,
                Assembly.Program.byteLength_append,
                Assembly.Program.byteLength, hSwapByte]
      have hMidStack :
          mid.stack = last :: front ++ token :: suffix := by
        simp [mid, start, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, List.append_assoc]
      have hMidRecord :
          { mid with stack := last :: front ++ token :: suffix } = mid := by
        rw [← hMidStack]
      have hMidRecord' :
          { mid with stack := last :: (front ++ token :: suffix) } = mid := by
        simpa [List.append_assoc] using hMidRecord
      have hRestForIH :
          ∀ final : EvmYul.EVM.State,
            final.stack = front ++ last :: token :: suffix →
            Structured.Preservation.eraseControl final =
              Structured.Preservation.eraseControl
                { mid with stack := front ++ last :: token :: suffix } →
            final.pc =
              Assembly.Program.pcAfter
                ((pre ++ [swap]) ++
                  Structured.StackShuffle.sinkTopUnder front.length) →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult
                ((pre ++ [swap]) ++
                  Structured.StackShuffle.sinkTopUnder front.length ++ post)
                fuel final)
              tailTrace result := by
        intro final hFinalStack hFinalErase hFinalPc
        have hFinalStackFull :
            final.stack = (front ++ [last]) ++ token :: suffix := by
          simpa [List.append_assoc] using hFinalStack
        have hFinalEraseFull :
            Structured.Preservation.eraseControl final =
              Structured.Preservation.eraseControl
                { state with stack := (front ++ [last]) ++ token :: suffix } := by
          calc
            Structured.Preservation.eraseControl final =
                Structured.Preservation.eraseControl
                  { mid with stack := front ++ last :: token :: suffix } :=
              hFinalErase
            _ =
                Structured.Preservation.eraseControl
                  { state with stack := front ++ [last] ++ token :: suffix } := by
              simp [mid, start, Structured.Preservation.eraseControl,
                Assembly.eraseGas, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC, List.append_assoc]
            _ =
                Structured.Preservation.eraseControl
                  { state with stack := (front ++ [last]) ++ token :: suffix } := by
              simp [List.append_assoc]
        have hFinalPcFull :
            final.pc =
              Assembly.Program.pcAfter
                (pre ++
                  Structured.StackShuffle.sinkTopUnder
                    (front ++ [last]).length) := by
          simpa [Structured.StackShuffle.sinkTopUnder, List.length_append,
            swap, List.append_assoc] using hFinalPc
        simpa [Structured.StackShuffle.sinkTopUnder, List.length_append,
          swap, List.append_assoc] using
          hRest final hFinalStackFull hFinalEraseFull hFinalPcFull
      have hRestMid :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult
              ((pre ++ [swap]) ++
                Structured.StackShuffle.sinkTopUnder front.length ++ post)
              ((Structured.StackShuffle.sinkTopUnder front.length).length +
                fuel)
              mid)
            tailTrace result := by
        have hPcIH :
            ({ mid with stack := last :: front ++ token :: suffix } :
                EvmYul.EVM.State).pc =
              Assembly.Program.pcAfter (pre ++ [swap]) := by
          simpa [hMidRecord] using hAfterSwapPc
        have hIH :=
          ih (state := mid) (suffix := token :: suffix) (token := last)
            (pre := pre ++ [swap]) hFitsCons.2 hPcIH hFrontBound
            hRestForIH
        simpa [hMidRecord', List.append_assoc] using hIH
      have hFirst :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult
              (pre ++ [swap] ++
                (Structured.StackShuffle.sinkTopUnder front.length ++ post))
              (((Structured.StackShuffle.sinkTopUnder front.length).length +
                fuel) + 1)
              start)
            tailTrace result := by
        exact
          openRunNResult_source_local_instr_no_call_running_continue
            hSwapLocal hSwapNoInstr hSwapNoHalt hFitsCons.1
            (by simpa [start, List.append_assoc] using hPc)
            hStep (by simpa [List.append_assoc] using hRestMid)
      have hFuel :
          ((Structured.StackShuffle.sinkTopUnder front.length).length +
              fuel) + 1 =
            (Structured.StackShuffle.sinkTopUnder
              (front ++ [last]).length).length + fuel := by
        simp [Structured.StackShuffle.sinkTopUnder, List.length_append]
        omega
      simpa [Structured.StackShuffle.sinkTopUnder, List.length_append, swap,
        start, hFuel, List.append_assoc] using hFirst

theorem openRunNResult_liftBuriedToTop_source_running_continue
    {state : EvmYul.EVM.State}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (Structured.StackShuffle.liftBuriedToTop front.length))
    (hPc :
      ({ state with stack := front ++ token :: suffix } :
          EvmYul.EVM.State).pc =
        Assembly.Program.pcAfter pre)
    (hBound : front.length ≤ 16)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        final.stack = token :: front ++ suffix →
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { state with stack := token :: front ++ suffix } →
        final.pc =
          Assembly.Program.pcAfter
            (pre ++ Structured.StackShuffle.liftBuriedToTop front.length) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ Structured.StackShuffle.liftBuriedToTop front.length ++
              post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ Structured.StackShuffle.liftBuriedToTop front.length ++ post)
        ((Structured.StackShuffle.liftBuriedToTop front.length).length + fuel)
        { state with stack := front ++ token :: suffix })
      tailTrace result := by
  induction front using List.reverseRecOn generalizing state suffix token pre post fuel with
  | nil =>
      have hRestStart :=
        hRest { state with stack := token :: suffix }
          (by simp)
          (by rfl)
          (by simpa [Structured.StackShuffle.liftBuriedToTop] using hPc)
      simpa [Structured.StackShuffle.liftBuriedToTop] using hRestStart
  | append_singleton front last ih =>
      have hSwapBound : front.length + 1 ≤ 16 := by
        simpa [List.length_append] using hBound
      have hFrontBound : front.length ≤ 16 := by omega
      let swap := Structured.StackShuffle.swapInstr (front.length + 1)
      have hCodeEq :
          Structured.StackShuffle.liftBuriedToTop (front ++ [last]).length =
            Structured.StackShuffle.liftBuriedToTop front.length ++
              [swap] := by
        simp [Structured.StackShuffle.liftBuriedToTop, List.length_append,
          swap]
      have hCodeLenEq :
          Structured.StackShuffle.liftBuriedToTop (front.length + 1) =
            Structured.StackShuffle.liftBuriedToTop front.length ++
              [swap] := by
        simpa [List.length_append] using hCodeEq
      have hFitsAppend :
          Structured.Preservation.AssemblyProgram.PCFitsFrom pre
            (Structured.StackShuffle.liftBuriedToTop front.length ++
              [swap]) := by
        simpa [hCodeEq] using hFits
      have hLiftFits :
          Structured.Preservation.AssemblyProgram.PCFitsFrom pre
            (Structured.StackShuffle.liftBuriedToTop front.length) :=
        Structured.Preservation.AssemblyProgram.PCFitsFrom.left hFitsAppend
      have hSwapFits :
          Structured.Preservation.AssemblyProgram.PCFitsFrom
            (pre ++ Structured.StackShuffle.liftBuriedToTop front.length)
            [swap] :=
        Structured.Preservation.AssemblyProgram.PCFitsFrom.right hFitsAppend
      have hSwapLocal :
          Structured.Preservation.StackShuffle.SourceLocalInstr swap := by
        exact
          Structured.Preservation.StackShuffle.swapInstr_sourceLocal
            (n := front.length + 1) (by omega) hSwapBound
      have hSwapNoHalt : swap.haltKind? = none := by
        exact
          Structured.Preservation.StackShuffle.swapInstr_haltKind?_none
            (n := front.length + 1) (by omega) hSwapBound
      have hSwapByte : swap.byteSize = 1 := by
        exact
          Structured.Preservation.StackShuffle.swapInstr_byteSize
            (n := front.length + 1) (by omega) hSwapBound
      have hSwapNoInstr :
          Assembly.Instr.usesCallCreate swap = false := by
        exact
          stackShuffle_swapInstr_usesCallCreate_false
            (n := front.length + 1) (by omega) hSwapBound
      have hRestForIH :
          ∀ mid : EvmYul.EVM.State,
            mid.stack = last :: front ++ token :: suffix →
            Structured.Preservation.eraseControl mid =
              Structured.Preservation.eraseControl
                { state with stack := last :: front ++ token :: suffix } →
            mid.pc =
              Assembly.Program.pcAfter
                (pre ++
                  Structured.StackShuffle.liftBuriedToTop front.length) →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult
                (pre ++ Structured.StackShuffle.liftBuriedToTop front.length ++
                  ([swap] ++ post))
                (fuel + 1) mid)
              tailTrace result := by
        intro mid hMidStack hMidErase hMidPc
        have hMidRecord :
            { mid with stack := last :: front ++ [token] ++ suffix } = mid := by
          rw [show last :: front ++ [token] ++ suffix =
              last :: front ++ token :: suffix by simp [List.append_assoc]]
          rw [← hMidStack]
        let finalState : EvmYul.EVM.State :=
          mid.replaceStackAndIncrPC (token :: front ++ [last] ++ suffix)
        have hStep :
            Assembly.Target.stepInstr
                (Structured.Preservation.StackShuffle.targetInstr swap)
                mid =
              .ok finalState := by
          rw [← hMidRecord]
          rw [show swap =
              Structured.StackShuffle.swapInstr (front.length + 1) from rfl]
          rw [Structured.Preservation.StackShuffle.swapInstr_step_eq_swap
            (by omega) hSwapBound]
          exact
            Structured.Preservation.StackShuffle.swap_snoc
              (state := mid) (front := front) (suffix := suffix)
              (top := last) (last := token)
        have hFinalStack :
            finalState.stack = token :: front ++ [last] ++ suffix := by
          simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, List.append_assoc]
        have hFinalErase :
            Structured.Preservation.eraseControl finalState =
              Structured.Preservation.eraseControl
                { state with stack := token :: front ++ [last] ++ suffix } := by
          calc
            Structured.Preservation.eraseControl finalState =
                Structured.Preservation.eraseControl
                  { mid with stack := token :: front ++ [last] ++ suffix } := by
              simp [finalState, Structured.Preservation.eraseControl,
                Assembly.eraseGas, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
            _ =
                Structured.Preservation.eraseControl
                  { state with stack := token :: front ++ [last] ++ suffix } := by
              simpa [Structured.Preservation.eraseControl, Assembly.eraseGas,
                List.append_assoc] using
                Structured.Preservation.eraseControl_with_stack_congr
                  (left := mid)
                  (right :=
                    { state with stack := last :: front ++ token :: suffix })
                  (stack := token :: front ++ [last] ++ suffix)
                  hMidErase
        have hFinalPc :
            finalState.pc =
              Assembly.Program.pcAfter
                (pre ++
                  Structured.StackShuffle.liftBuriedToTop front.length ++
                  [swap]) := by
          calc
            finalState.pc
                = mid.pc + EvmYul.UInt256.ofNat 1 := by
                    simp [finalState,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC]
            _ =
                Assembly.Program.pcAfter
                    (pre ++
                      Structured.StackShuffle.liftBuriedToTop front.length) +
                  EvmYul.UInt256.ofNat 1 := by
                    rw [hMidPc]
            _ =
                EvmYul.UInt256.ofNat
                  (Assembly.Program.byteLength
                    (pre ++
                      Structured.StackShuffle.liftBuriedToTop front.length) +
                    1) := by
                    rw [Assembly.Program.pcAfter,
                      Assembly.UInt256_ofNat_add]
            _ =
                Assembly.Program.pcAfter
                  (pre ++
                    Structured.StackShuffle.liftBuriedToTop front.length ++
                    [swap]) := by
                    simp [Assembly.Program.pcAfter,
                      Assembly.Program.byteLength_append,
                      Assembly.Program.byteLength, hSwapByte, Nat.add_assoc]
        have hRestFinal :
            OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult
              (pre ++
                Structured.StackShuffle.liftBuriedToTop (front ++ [last]).length ++
                post)
                fuel finalState)
              tailTrace result := by
          have hFinalPcFull :
              finalState.pc =
                Assembly.Program.pcAfter
                  (pre ++
                    Structured.StackShuffle.liftBuriedToTop
                      (front ++ [last]).length) := by
            simpa [hCodeEq, List.append_assoc] using hFinalPc
          have hFinalStackFull :
              finalState.stack = token :: (front ++ [last]) ++ suffix := by
            simpa [List.append_assoc] using hFinalStack
          have hFinalEraseFull :
              Structured.Preservation.eraseControl finalState =
                Structured.Preservation.eraseControl
                  { state with stack := token :: (front ++ [last]) ++ suffix } := by
            simpa [List.append_assoc] using hFinalErase
          exact
            hRest finalState hFinalStackFull hFinalEraseFull hFinalPcFull
        have hSwapRun :=
          openRunNResult_source_local_instr_no_call_running_continue
            hSwapLocal hSwapNoInstr hSwapNoHalt
            (Structured.Preservation.AssemblyProgram.PCFitsFrom.start
              hSwapFits)
            hMidPc hStep
            (by
              simpa [hCodeEq, hCodeLenEq, List.append_assoc] using hRestFinal)
        simpa [List.append_assoc] using hSwapRun
      have hPcIH :
          ({ state with stack := front ++ last :: token :: suffix } :
              EvmYul.EVM.State).pc =
            Assembly.Program.pcAfter pre := by
        simpa [List.append_assoc] using hPc
      have hLiftRun :=
        ih (state := state) (suffix := token :: suffix) (token := last)
          (pre := pre) (post := [swap] ++ post) (fuel := fuel + 1)
          hLiftFits hPcIH hFrontBound hRestForIH
      have hFuel :
          (Structured.StackShuffle.liftBuriedToTop front.length).length +
              (fuel + 1) =
            (Structured.StackShuffle.liftBuriedToTop
              (front ++ [last]).length).length + fuel := by
        simp [hCodeLenEq]
        omega
      simpa [hCodeEq, hCodeLenEq, hFuel, List.append_assoc] using hLiftRun

theorem openRunNResult_removeBuriedUnder_source_running_continue
    {state : EvmYul.EVM.State}
    {returnValues suffix : List Word} {token : Word}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (Structured.StackShuffle.removeBuriedUnder returnValues.length))
    (hPc :
      ({ state with stack := returnValues ++ token :: suffix } :
          EvmYul.EVM.State).pc =
        Assembly.Program.pcAfter pre)
    (hBound : returnValues.length ≤ 16)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        final.stack = returnValues ++ suffix →
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { state with stack := returnValues ++ suffix } →
        final.pc =
          Assembly.Program.pcAfter
            (pre ++ Structured.StackShuffle.removeBuriedUnder
              returnValues.length) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ Structured.StackShuffle.removeBuriedUnder
              returnValues.length ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ Structured.StackShuffle.removeBuriedUnder returnValues.length ++
          post)
        ((Structured.StackShuffle.removeBuriedUnder returnValues.length).length +
          fuel)
        { state with stack := returnValues ++ token :: suffix })
      tailTrace result := by
  have hFitsLift :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (Structured.StackShuffle.liftBuriedToTop returnValues.length) := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.left
        (by simpa [Structured.StackShuffle.removeBuriedUnder,
          List.append_assoc] using hFits)
  have hFitsPop :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (pre ++ Structured.StackShuffle.liftBuriedToTop returnValues.length)
        [Assembly.Instr.prim .pop] := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (by simpa [Structured.StackShuffle.removeBuriedUnder,
          List.append_assoc] using hFits)
  have hLiftRun :=
    openRunNResult_liftBuriedToTop_source_running_continue
      (state := state) (front := returnValues) (suffix := suffix)
      (token := token) (pre := pre)
      (post := [Assembly.Instr.prim .pop] ++ post)
      (fuel := fuel + 1) (tailTrace := tailTrace) (result := result)
      hFitsLift hPc hBound
      (by
        intro mid hMidStack hMidErase hMidPc
        have hMidRecord :
            { mid with stack := token :: returnValues ++ suffix } = mid := by
          rw [← hMidStack]
        let finalState : EvmYul.EVM.State :=
          mid.replaceStackAndIncrPC (returnValues ++ suffix)
        have hPopStep :
            Assembly.Target.stepInstr
                (Structured.Preservation.StackShuffle.targetInstr
                  (Assembly.Instr.prim .pop)) mid =
              .ok finalState := by
          rw [← hMidRecord]
          exact
            Structured.Preservation.StackShuffle.pop_cons_step
              (state := mid) (top := token)
              (suffix := returnValues ++ suffix)
        have hFinalStack :
            finalState.stack = returnValues ++ suffix := by
          simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        have hFinalErase :
            Structured.Preservation.eraseControl finalState =
              Structured.Preservation.eraseControl
                { state with stack := returnValues ++ suffix } := by
          calc
            Structured.Preservation.eraseControl finalState =
                Structured.Preservation.eraseControl
                  { mid with stack := returnValues ++ suffix } := by
              simp [finalState, Structured.Preservation.eraseControl,
                Assembly.eraseGas, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
            _ =
                Structured.Preservation.eraseControl
                  { state with stack := returnValues ++ suffix } := by
              exact
                Structured.Preservation.eraseControl_with_stack_congr
                  (left := mid)
                  (right :=
                    { state with stack := token :: returnValues ++ suffix })
                  (stack := returnValues ++ suffix)
                  hMidErase
        have hFinalPc :
            finalState.pc =
              Assembly.Program.pcAfter
                (pre ++ Structured.StackShuffle.removeBuriedUnder
                  returnValues.length) := by
          calc
            finalState.pc
                = mid.pc + EvmYul.UInt256.ofNat 1 := by
                    simp [finalState,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC]
            _ =
                Assembly.Program.pcAfter
                    (pre ++
                      Structured.StackShuffle.liftBuriedToTop
                        returnValues.length) +
                  EvmYul.UInt256.ofNat 1 := by
                    rw [hMidPc]
            _ =
                EvmYul.UInt256.ofNat
                  (Assembly.Program.byteLength
                    (pre ++
                      Structured.StackShuffle.liftBuriedToTop
                        returnValues.length) +
                    1) := by
                    rw [Assembly.Program.pcAfter,
                      Assembly.UInt256_ofNat_add]
            _ =
                Assembly.Program.pcAfter
                  (pre ++
                    Structured.StackShuffle.removeBuriedUnder
                      returnValues.length) := by
                    simp [Structured.StackShuffle.removeBuriedUnder,
                      Assembly.Program.pcAfter,
                      Assembly.Program.byteLength_append,
                      Assembly.Program.byteLength, Assembly.Instr.byteSize,
                      Nat.add_assoc]
        have hRestFinal :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult
                (pre ++ Structured.StackShuffle.removeBuriedUnder
                  returnValues.length ++ post)
                fuel finalState)
              tailTrace result :=
          hRest finalState hFinalStack hFinalErase hFinalPc
        have hPopRun :=
          openRunNResult_source_local_instr_no_call_running_continue
            (instr := Assembly.Instr.prim .pop)
            (pre := pre ++
              Structured.StackShuffle.liftBuriedToTop returnValues.length)
            (post := post) (state := mid) (mid := finalState)
            (fuel := fuel) (tailTrace := tailTrace) (result := result)
            (by simp [Structured.Preservation.StackShuffle.SourceLocalInstr])
            (by simp [Assembly.Instr.usesCallCreate,
              Assembly.PrimOp.isCallCreate])
            rfl
            (Structured.Preservation.AssemblyProgram.PCFitsFrom.start
              hFitsPop)
            hMidPc hPopStep
            (by
              simpa [Structured.StackShuffle.removeBuriedUnder,
                List.append_assoc] using hRestFinal)
        simpa [Structured.StackShuffle.removeBuriedUnder, List.append_assoc]
          using hPopRun)
  have hFuel :
      (Structured.StackShuffle.liftBuriedToTop returnValues.length).length +
          (fuel + 1) =
        (Structured.StackShuffle.removeBuriedUnder returnValues.length).length +
          fuel := by
    simp [Structured.StackShuffle.removeBuriedUnder]
    omega
  simpa [Structured.StackShuffle.removeBuriedUnder, hFuel, List.append_assoc]
    using hLiftRun

theorem openRunNResult_source_returnAttach_after_remove_continue
    {callee : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word} {token : Word}
    {frame : Structured.ReturnDest} {returns : List Structured.ReturnDest}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (Structured.StackShuffle.removeBuriedUnder callee.evm.stack.length))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Structured.Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : callee.evm.stack.length ≤ 16)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          { callee with
            evm :=
              { callee.evm with
                stack := callee.evm.stack ++ frame.callerStack }
            returns := returns }
          final tokens →
        final.pc =
          Assembly.Program.pcAfter
            (pre ++
              Structured.StackShuffle.removeBuriedUnder
                callee.evm.stack.length) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              Structured.StackShuffle.removeBuriedUnder
                callee.evm.stack.length ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++
          Structured.StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          post)
        ((Structured.StackShuffle.removeBuriedUnder callee.evm.stack.length).length +
          fuel)
        target)
      tailTrace result := by
  rcases
      Structured.Preservation.Frame.StateRel.caller_materialization_of_top_return
        hRel hReturns with
    ⟨callerTarget, hCaller, hTargetStack⟩
  have hTargetRecord :
      { target with stack := callee.evm.stack ++ token :: callerTarget } =
        target := by
    rw [← hTargetStack]
  have hRun :=
    openRunNResult_removeBuriedUnder_source_running_continue
      (state := target) (returnValues := callee.evm.stack)
      (suffix := callerTarget) (token := token) (pre := pre)
      (post := post) (fuel := fuel) (tailTrace := tailTrace)
      (result := result) hFits
      (by simpa [hTargetRecord] using hPc) hBound
      (by
        intro final hFinalStack hFinalErase hFinalPc
        have hRelFinal :
            Structured.Preservation.Frame.StateRel
              { callee with
                evm :=
                  { callee.evm with
                    stack := callee.evm.stack ++ frame.callerStack }
                returns := returns }
              final tokens := by
          refine ⟨?_, ?_⟩
          · rw [hFinalStack]
            exact
              Structured.Preservation.Frame.materializeStack_returnAttach
                hCaller
          · have hEraseTarget :
                Structured.Preservation.eraseControl final =
                  Structured.Preservation.eraseControl
                    { target with stack := callee.evm.stack ++ callerTarget } :=
              hFinalErase
            have hEraseSource :
                Structured.Preservation.eraseControl
                    { target with stack := callee.evm.stack ++ callerTarget } =
                  Structured.Preservation.eraseControl
                    { callee.evm with
                      stack := callee.evm.stack ++ callerTarget } :=
              hRel.dataRel_replace_stack
                (callee.evm.stack ++ callerTarget)
            have hEraseFinalSource :
                Structured.Preservation.eraseControl
                    { callee.evm with
                      stack := callee.evm.stack ++ callerTarget } =
                  Structured.Preservation.eraseControl
                    { { callee with
                        evm :=
                          { callee.evm with
                            stack := callee.evm.stack ++ frame.callerStack }
                        returns := returns }.evm with
                      stack := final.stack } := by
              simp [hFinalStack]
            exact hEraseTarget.trans
              (hEraseSource.trans hEraseFinalSource)
        exact hRest final hRelFinal hFinalPc)
  simpa [hTargetRecord] using hRun

theorem openRunNResult_dispatch_case_source_running_continue
    {caseLabel returnLabel : Assembly.Label}
    {dest : Nat} {pre post : Assembly.Program}
    {callee : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word} {token : Word}
    {frame : Structured.ReturnDest} {returns : List Structured.ReturnDest}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        ([Assembly.Instr.label caseLabel] ++
          Structured.StackShuffle.removeBuriedUnder
            callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel]))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Structured.Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : callee.evm.stack.length ≤ 16)
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++ [Assembly.Instr.label caseLabel] ++
          Structured.StackShuffle.removeBuriedUnder
            callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post)
        returnLabel = some dest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          { callee with
            evm :=
              { callee.evm with
                stack := callee.evm.stack ++ frame.callerStack }
            returns := returns }
          final tokens →
        final.pc = EvmYul.UInt256.ofNat dest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ [Assembly.Instr.label caseLabel] ++
              Structured.StackShuffle.removeBuriedUnder
                callee.evm.stack.length ++
              [Assembly.Instr.jump returnLabel] ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ [Assembly.Instr.label caseLabel] ++
          Structured.StackShuffle.removeBuriedUnder callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post)
        (((Structured.StackShuffle.removeBuriedUnder
              callee.evm.stack.length).length + (fuel + 1)) + 1)
        target)
      tailTrace result := by
  let removeCode :=
    Structured.StackShuffle.removeBuriedUnder callee.evm.stack.length
  have hFitsAfterLabel :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label caseLabel])
        (removeCode ++ [Assembly.Instr.jump returnLabel]) := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (pre := pre) (first := [Assembly.Instr.label caseLabel])
        (second := removeCode ++ [Assembly.Instr.jump returnLabel])
        (by simpa [removeCode, List.append_assoc] using hFits)
  have hFitsRemove :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label caseLabel]) removeCode := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.left
        (pre := pre ++ [Assembly.Instr.label caseLabel])
        (first := removeCode) (second := [Assembly.Instr.jump returnLabel])
        hFitsAfterLabel
  have hFitsAfterRemove :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.label caseLabel] ++ removeCode)
        [Assembly.Instr.jump returnLabel] := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (pre := pre ++ [Assembly.Instr.label caseLabel])
        (first := removeCode) (second := [Assembly.Instr.jump returnLabel])
        hFitsAfterLabel
  rcases
      Structured.Preservation.Frame.StateRel.label_stepResult_at
        (label := caseLabel) (pre := pre)
        (post := removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
        (source := callee) (target := target)
        (tokens := token :: tokens)
        (Structured.Preservation.AssemblyProgram.PCFitsFrom.start hFits)
        hPc hRel with
    ⟨afterLabel, hLabelStep, hRelAfter, hPcAfter⟩
  have hLabelAt :
      Assembly.Program.instrAtPc
          (pre ++ [Assembly.Instr.label caseLabel] ++
            removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
          target.pc.toNat =
        some (Assembly.Program.byteLength pre,
          Assembly.Instr.label caseLabel) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, Structured.Preservation.AssemblyProgram.PCFitsFrom.start hFits]
    simpa [removeCode, List.append_assoc] using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre (removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
        (Assembly.Instr.label caseLabel) 0
  have hAfterLabelRest :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (pre ++ [Assembly.Instr.label caseLabel] ++
            removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
          (removeCode.length + (fuel + 1)) afterLabel)
        tailTrace result := by
    have hRemoveRun :=
      openRunNResult_source_returnAttach_after_remove_continue
        (callee := callee) (target := afterLabel)
        (tokens := tokens) (token := token) (frame := frame)
        (returns := returns)
        (pre := pre ++ [Assembly.Instr.label caseLabel])
        (post := [Assembly.Instr.jump returnLabel] ++ post)
        (fuel := fuel + 1) (tailTrace := tailTrace)
        (result := result)
        (by simpa [removeCode] using hFitsRemove)
        hPcAfter hRelAfter hReturns hBound
        (by
          intro afterRemove hRelReturned hPcAfterRemove
          have hLabelJump :
              Assembly.Program.labelPc
                ((pre ++ [Assembly.Instr.label caseLabel] ++
                    removeCode) ++ [Assembly.Instr.jump returnLabel] ++
                  post)
                returnLabel = some dest := by
            simpa [removeCode, List.append_assoc] using hReturnLabel
          have hAfterJumpRel :
              Structured.Preservation.Frame.StateRel
                { callee with
                  evm :=
                    { callee.evm with
                      stack := callee.evm.stack ++ frame.callerStack }
                  returns := returns }
                (Assembly.Source.jumpPc dest afterRemove)
                tokens := by
            refine ⟨?_, ?_⟩
            · simpa [Assembly.Source.jumpPc] using
                hRelReturned.stackRel
            · simpa [Assembly.Source.jumpPc,
                Structured.Preservation.eraseControl_with_pc] using
                hRelReturned.dataRel
          have hAfterJumpPc :
              (Assembly.Source.jumpPc dest afterRemove).pc =
                EvmYul.UInt256.ofNat dest := by
            rfl
          have hJumpRun :=
            openRunNResult_source_jump_no_call_running_continue
              (pre := pre ++ [Assembly.Instr.label caseLabel] ++
                removeCode)
              (post := post) (label := returnLabel)
              (state := afterRemove) (dest := dest) (fuel := fuel)
              (tailTrace := tailTrace) (result := result)
              (Structured.Preservation.AssemblyProgram.PCFitsFrom.start
                hFitsAfterRemove)
              hPcAfterRemove hLabelJump
              (by
                simpa [removeCode, List.append_assoc] using
                  hRest (Assembly.Source.jumpPc dest afterRemove)
                    hAfterJumpRel hAfterJumpPc)
          simpa [removeCode, List.append_assoc] using hJumpRun)
    simpa [removeCode, List.append_assoc] using hRemoveRun
  have hLabelRun :=
    OpenAssembly.Source.openRunNResult_current_no_call_running_continue_of_current_instr
      hLabelAt (by simp [Assembly.Instr.usesCallCreate])
      (by simpa [List.append_assoc] using hLabelStep)
      hAfterLabelRest
  simpa [removeCode, List.append_assoc] using hLabelRun

theorem openRunNResult_dispatch_mismatched_test_source_running_continue
    {caseLabel : Assembly.Label} {caseDest : Nat}
    {pre post : Assembly.Program}
    {callee : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word} {token probe : Word}
    {frame : Structured.ReturnDest} {returns : List Structured.ReturnDest}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hNe : probe ≠ token)
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        [ Structured.StackShuffle.dupInstr (callee.evm.stack.length + 1)
        , Assembly.Instr.push probe
        , Assembly.Instr.prim .eq
        , Assembly.Instr.jumpi caseLabel
        ])
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Structured.Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : callee.evm.stack.length < 16)
    (hCaseLabel :
      Assembly.Program.labelPc
        (pre ++
          [ Structured.StackShuffle.dupInstr
              (callee.evm.stack.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ post)
        caseLabel = some caseDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel callee final (token :: tokens) →
        final.pc =
          Assembly.Program.pcAfter
            (pre ++
              [ Structured.StackShuffle.dupInstr
                  (callee.evm.stack.length + 1)
              , Assembly.Instr.push probe
              , Assembly.Instr.prim .eq
              , Assembly.Instr.jumpi caseLabel
              ]) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              [ Structured.StackShuffle.dupInstr
                  (callee.evm.stack.length + 1)
              , Assembly.Instr.push probe
              , Assembly.Instr.prim .eq
              , Assembly.Instr.jumpi caseLabel
              ] ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++
          [ Structured.StackShuffle.dupInstr
              (callee.evm.stack.length + 1)
          , Assembly.Instr.push probe
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ post)
        (4 + fuel) target)
      tailTrace result := by
  rcases
      Structured.Preservation.Frame.StateRel.caller_materialization_of_top_return
        hRel hReturns with
    ⟨callerTarget, hCaller, hTargetStack⟩
  have hTargetRecord :
      { target with stack := callee.evm.stack ++ token :: callerTarget } =
        target := by
    rw [← hTargetStack]
  have hRun :=
    openRunNResult_dispatchCondition_jumpi_source_running_continue
      (state := target) (returnValues := callee.evm.stack)
      (suffix := callerTarget) (token := token) (probe := probe)
      (label := caseLabel) (dest := caseDest) (pre := pre) (post := post)
      (fuel := fuel) (tailTrace := tailTrace) (result := result)
      hFits (by simpa [hTargetRecord] using hPc) hBound hCaseLabel
      (by
        intro afterTest hAfterStack hAfterErase hAfterPc
        have hRelAfterTest :
            Structured.Preservation.Frame.StateRel callee afterTest
              (token :: tokens) := by
          refine ⟨?_, ?_⟩
          · rw [hReturns]
            simp [Structured.Preservation.Frame.materializeStack,
              hCaller, hAfterStack]
          · calc
              Structured.Preservation.eraseControl afterTest =
                  Structured.Preservation.eraseControl
                    { target with
                      stack := callee.evm.stack ++ token :: callerTarget } :=
                hAfterErase
              _ =
                  Structured.Preservation.eraseControl
                    { callee.evm with
                      stack := callee.evm.stack ++ token :: callerTarget } :=
                hRel.dataRel_replace_stack
                  (callee.evm.stack ++ token :: callerTarget)
              _ =
                  Structured.Preservation.eraseControl
                    { callee.evm with stack := afterTest.stack } := by
                rw [hAfterStack]
        have hPcAfter :
            afterTest.pc =
              Assembly.Program.pcAfter
                (pre ++
                  [ Structured.StackShuffle.dupInstr
                      (callee.evm.stack.length + 1)
                  , Assembly.Instr.push probe
                  , Assembly.Instr.prim .eq
                  , Assembly.Instr.jumpi caseLabel
                  ]) := by
          simpa [hNe] using hAfterPc
        exact hRest afterTest hRelAfterTest hPcAfter)
  simpa [hTargetRecord] using hRun

theorem openRunNResult_dispatch_selected_site_source_running_continue
    {caseLabel returnLabel : Assembly.Label} {returnDest : Nat}
    {pre between post : Assembly.Program}
    {callee : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word} {token : Word}
    {frame : Structured.ReturnDest} {returns : List Structured.ReturnDest}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        ([ Structured.StackShuffle.dupInstr (callee.evm.stack.length + 1)
         , Assembly.Instr.push token
         , Assembly.Instr.prim .eq
         , Assembly.Instr.jumpi caseLabel
         ] ++ between ++
          [Assembly.Instr.label caseLabel] ++
          Structured.StackShuffle.removeBuriedUnder
            callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel]))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Structured.Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : callee.evm.stack.length < 16)
    (hExact :
      Structured.Preservation.ExactLabels
        (pre ++
          [ Structured.StackShuffle.dupInstr
              (callee.evm.stack.length + 1)
          , Assembly.Instr.push token
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ between ++
          [Assembly.Instr.label caseLabel] ++
          Structured.StackShuffle.removeBuriedUnder
            callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++
          [ Structured.StackShuffle.dupInstr
              (callee.evm.stack.length + 1)
          , Assembly.Instr.push token
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ between ++
          [Assembly.Instr.label caseLabel] ++
          Structured.StackShuffle.removeBuriedUnder
            callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post)
        returnLabel = some returnDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          { callee with
            evm :=
              { callee.evm with
                stack := callee.evm.stack ++ frame.callerStack }
            returns := returns }
          final tokens →
        final.pc = EvmYul.UInt256.ofNat returnDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              [ Structured.StackShuffle.dupInstr
                  (callee.evm.stack.length + 1)
              , Assembly.Instr.push token
              , Assembly.Instr.prim .eq
              , Assembly.Instr.jumpi caseLabel
              ] ++ between ++
              [Assembly.Instr.label caseLabel] ++
              Structured.StackShuffle.removeBuriedUnder
                callee.evm.stack.length ++
              [Assembly.Instr.jump returnLabel] ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++
          [ Structured.StackShuffle.dupInstr
              (callee.evm.stack.length + 1)
          , Assembly.Instr.push token
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi caseLabel
          ] ++ between ++
          [Assembly.Instr.label caseLabel] ++
          Structured.StackShuffle.removeBuriedUnder
            callee.evm.stack.length ++
          [Assembly.Instr.jump returnLabel] ++ post)
        (4 +
          (((Structured.StackShuffle.removeBuriedUnder
                callee.evm.stack.length).length + (fuel + 1)) + 1))
        target)
      tailTrace result := by
  let testCode : Assembly.Program :=
    [ Structured.StackShuffle.dupInstr (callee.evm.stack.length + 1)
    , Assembly.Instr.push token
    , Assembly.Instr.prim .eq
    , Assembly.Instr.jumpi caseLabel
    ]
  let removeCode :=
    Structured.StackShuffle.removeBuriedUnder callee.evm.stack.length
  let casePre := pre ++ testCode ++ between
  let fullProgram :=
    pre ++ testCode ++ between ++ [Assembly.Instr.label caseLabel] ++
      removeCode ++ [Assembly.Instr.jump returnLabel] ++ post
  rcases
      Structured.Preservation.Frame.StateRel.caller_materialization_of_top_return
        hRel hReturns with
    ⟨callerTarget, hCaller, hTargetStack⟩
  have hTargetRecord :
      { target with stack := callee.evm.stack ++ token :: callerTarget } =
        target := by
    rw [← hTargetStack]
  have hExactFull :
      Structured.Preservation.ExactLabels fullProgram := by
    simpa [fullProgram, testCode, removeCode, List.append_assoc] using hExact
  have hFitsTest :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre testCode := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.left
        (pre := pre) (first := testCode)
        (second := between ++ [Assembly.Instr.label caseLabel] ++
          removeCode ++ [Assembly.Instr.jump returnLabel])
        (by simpa [testCode, removeCode, List.append_assoc] using hFits)
  have hFitsCase :
      Structured.Preservation.AssemblyProgram.PCFitsFrom casePre
        ([Assembly.Instr.label caseLabel] ++ removeCode ++
          [Assembly.Instr.jump returnLabel]) := by
    simpa [casePre, List.append_assoc] using
      (Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (pre := pre) (first := testCode ++ between)
        (second :=
          [Assembly.Instr.label caseLabel] ++ removeCode ++
            [Assembly.Instr.jump returnLabel])
        (by simpa [testCode, removeCode, List.append_assoc] using hFits))
  have hCaseLabel :
      Assembly.Program.labelPc fullProgram caseLabel =
        some (Assembly.Program.byteLength casePre) := by
    have hHere :=
      hExactFull.labelPc_at casePre caseLabel
        (removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
        (by simp [fullProgram, casePre, testCode, removeCode,
          List.append_assoc])
    simpa [fullProgram] using hHere
  have hTestRun :=
    openRunNResult_dispatchCondition_jumpi_source_running_continue
      (state := target) (returnValues := callee.evm.stack)
      (suffix := callerTarget) (token := token) (probe := token)
      (label := caseLabel) (dest := Assembly.Program.byteLength casePre)
      (pre := pre)
      (post := between ++ [Assembly.Instr.label caseLabel] ++
        removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
      (fuel :=
        ((Structured.StackShuffle.removeBuriedUnder
            callee.evm.stack.length).length + (fuel + 1)) + 1)
      (tailTrace := tailTrace) (result := result)
      (by simpa [testCode] using hFitsTest)
      (by simpa [hTargetRecord] using hPc)
      hBound
      (by simpa [fullProgram, testCode, removeCode, List.append_assoc] using
        hCaseLabel)
      (by
        intro afterTest hAfterStack hAfterErase hAfterPc
        have hRelAfterTest :
            Structured.Preservation.Frame.StateRel callee afterTest
              (token :: tokens) := by
          refine ⟨?_, ?_⟩
          · simpa [hTargetStack, hAfterStack] using hRel.stackRel
          · calc
              Structured.Preservation.eraseControl afterTest =
                  Structured.Preservation.eraseControl
                    { target with
                      stack := callee.evm.stack ++ token :: callerTarget } :=
                hAfterErase
              _ =
                  Structured.Preservation.eraseControl
                    { callee.evm with
                      stack := callee.evm.stack ++ token :: callerTarget } :=
                hRel.dataRel_replace_stack
                  (callee.evm.stack ++ token :: callerTarget)
              _ =
                  Structured.Preservation.eraseControl
                    { callee.evm with stack := afterTest.stack } := by
                rw [hAfterStack]
        have hPcCase :
            afterTest.pc = Assembly.Program.pcAfter casePre := by
          have hPcNat :
              afterTest.pc =
                EvmYul.UInt256.ofNat
                  (Assembly.Program.byteLength casePre) := by
            simpa [casePre, testCode] using hAfterPc
          simpa [Assembly.Program.pcAfter] using hPcNat
        have hReturnLabelCase :
            Assembly.Program.labelPc
              (casePre ++ [Assembly.Instr.label caseLabel] ++
                removeCode ++ [Assembly.Instr.jump returnLabel] ++ post)
              returnLabel = some returnDest := by
          simpa [fullProgram, casePre, testCode, removeCode,
            List.append_assoc] using hReturnLabel
        have hCaseRun :=
          openRunNResult_dispatch_case_source_running_continue
            (caseLabel := caseLabel) (returnLabel := returnLabel)
            (dest := returnDest) (pre := casePre) (post := post)
            (callee := callee) (target := afterTest)
            (tokens := tokens) (token := token) (frame := frame)
            (returns := returns) (fuel := fuel)
            (tailTrace := tailTrace) (result := result)
            (by simpa [removeCode] using hFitsCase)
            hPcCase hRelAfterTest hReturns (by omega)
            hReturnLabelCase
            (by
              intro final hRelFinal hPcFinal
              simpa [fullProgram, casePre, testCode, removeCode,
                List.append_assoc] using hRest final hRelFinal hPcFinal)
        simpa [fullProgram, casePre, testCode, removeCode, List.append_assoc]
          using hCaseRun)
  simpa [testCode, removeCode, fullProgram, hTargetRecord, List.append_assoc]
    using hTestRun

def returnDispatchSelectedTableFuel (retc : Nat)
    (sites : List Structured.CallSite) (site : Structured.CallSite)
    (tailFuel : Nat) : Nat :=
  match sites with
  | [] => tailFuel
  | head :: rest =>
      if head.token = site.token then
        4 + (((Structured.StackShuffle.removeBuriedUnder retc).length +
          (tailFuel + 1)) + 1)
      else
        4 + returnDispatchSelectedTableFuel retc rest site tailFuel

set_option maxHeartbeats 1000000 in
theorem openRunNResult_selected_table_source_running_continue
    {base : Structured.LabelSupply} {retc idx : Nat}
    {casePrefix post pre : Assembly.Program}
    {sites : List Structured.CallSite} {site : Structured.CallSite}
    {returnDest : Nat}
    {callee : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word} {token : Word}
    {frame : Structured.ReturnDest} {returns : List Structured.ReturnDest}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hMem : site ∈ sites)
    (hNoDup : (sites.map Structured.CallSite.token).Nodup)
    (hToken : site.token = token)
    (hRetc : callee.evm.stack.length = retc)
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (Structured.Preservation.DispatchPreservation.tableCode
          base retc idx casePrefix sites))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Structured.Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : retc < 16)
    (hExact :
      Structured.Preservation.ExactLabels
        (pre ++
          Structured.Preservation.DispatchPreservation.tableCode
            base retc idx casePrefix sites ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++
          Structured.Preservation.DispatchPreservation.tableCode
            base retc idx casePrefix sites ++ post)
        site.returnLabel = some returnDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          { callee with
            evm :=
              { callee.evm with
                stack := callee.evm.stack ++ frame.callerStack }
            returns := returns }
          final tokens →
        final.pc = EvmYul.UInt256.ofNat returnDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              Structured.Preservation.DispatchPreservation.tableCode
                base retc idx casePrefix sites ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++
          Structured.Preservation.DispatchPreservation.tableCode
            base retc idx casePrefix sites ++ post)
        (returnDispatchSelectedTableFuel retc sites site fuel) target)
      tailTrace result := by
  induction sites generalizing pre idx casePrefix target with
  | nil =>
      cases hMem
  | cons head rest ih =>
      have hHeadNotIn : head.token ∉ rest.map Structured.CallSite.token := by
        exact (List.nodup_cons.mp (by simpa using hNoDup)).1
      have hNoDupRest :
          (rest.map Structured.CallSite.token).Nodup := by
        exact (List.nodup_cons.mp (by simpa using hNoDup)).2
      let headTest :=
        Structured.Preservation.DispatchPreservation.testCode base retc idx head
      let headCase :=
        Structured.Preservation.DispatchPreservation.caseCode base retc idx head
      let testsRest :=
        Structured.Dispatch.testsForRetc base retc (idx + 1) rest
      let casesRest :=
        Structured.Dispatch.casesForRetc base retc (idx + 1) rest
      have hMemCons : site = head ∨ site ∈ rest := by
        simpa using hMem
      rcases hMemCons with hEq | hMemRest
      · subst head
        have hFitsSelected :
            Structured.Preservation.AssemblyProgram.PCFitsFrom pre
              ([ Structured.StackShuffle.dupInstr
                    (callee.evm.stack.length + 1)
               , Assembly.Instr.push token
               , Assembly.Instr.prim .eq
               , Assembly.Instr.jumpi
                  (Structured.LabelSupply.label base idx)
               ] ++
                (testsRest ++ [Assembly.Instr.prim .invalid] ++
                  casePrefix) ++
                [Assembly.Instr.label
                  (Structured.LabelSupply.label base idx)] ++
                Structured.StackShuffle.removeBuriedUnder
                  callee.evm.stack.length ++
                [Assembly.Instr.jump site.returnLabel]) := by
          exact
            Structured.Preservation.AssemblyProgram.PCFitsFrom.left
              (pre := pre)
              (first :=
                [ Structured.StackShuffle.dupInstr
                    (callee.evm.stack.length + 1)
                , Assembly.Instr.push token
                , Assembly.Instr.prim .eq
                , Assembly.Instr.jumpi
                    (Structured.LabelSupply.label base idx)
                ] ++
                (testsRest ++ [Assembly.Instr.prim .invalid] ++
                  casePrefix) ++
                [Assembly.Instr.label
                  (Structured.LabelSupply.label base idx)] ++
                Structured.StackShuffle.removeBuriedUnder
                  callee.evm.stack.length ++
                [Assembly.Instr.jump site.returnLabel])
              (second := casesRest)
              (by
                simpa [
                  Structured.Preservation.DispatchPreservation.tableCode,
                  headTest, headCase, testsRest, casesRest,
                  Structured.Preservation.DispatchPreservation.testCode,
                  Structured.Preservation.DispatchPreservation.caseCode,
                  hRetc, hToken, List.append_assoc] using hFits)
        have hExactSelected :
            Structured.Preservation.ExactLabels
              (pre ++
                [ Structured.StackShuffle.dupInstr
                    (callee.evm.stack.length + 1)
                , Assembly.Instr.push token
                , Assembly.Instr.prim .eq
                , Assembly.Instr.jumpi
                    (Structured.LabelSupply.label base idx)
                ] ++
                (testsRest ++ [Assembly.Instr.prim .invalid] ++
                  casePrefix) ++
                [Assembly.Instr.label
                  (Structured.LabelSupply.label base idx)] ++
                Structured.StackShuffle.removeBuriedUnder
                  callee.evm.stack.length ++
                [Assembly.Instr.jump site.returnLabel] ++
                casesRest ++ post) := by
          simpa [
            Structured.Preservation.DispatchPreservation.tableCode,
            headTest, headCase, testsRest, casesRest,
            Structured.Preservation.DispatchPreservation.testCode,
            Structured.Preservation.DispatchPreservation.caseCode,
            hRetc, hToken, List.append_assoc] using hExact
        have hReturnSelected :
            Assembly.Program.labelPc
              (pre ++
                [ Structured.StackShuffle.dupInstr
                    (callee.evm.stack.length + 1)
                , Assembly.Instr.push token
                , Assembly.Instr.prim .eq
                , Assembly.Instr.jumpi
                    (Structured.LabelSupply.label base idx)
                ] ++
                (testsRest ++ [Assembly.Instr.prim .invalid] ++
                  casePrefix) ++
                [Assembly.Instr.label
                  (Structured.LabelSupply.label base idx)] ++
                Structured.StackShuffle.removeBuriedUnder
                  callee.evm.stack.length ++
                [Assembly.Instr.jump site.returnLabel] ++
                casesRest ++ post)
              site.returnLabel = some returnDest := by
          simpa [
            Structured.Preservation.DispatchPreservation.tableCode,
            headTest, headCase, testsRest, casesRest,
            Structured.Preservation.DispatchPreservation.testCode,
            Structured.Preservation.DispatchPreservation.caseCode,
            hRetc, hToken, List.append_assoc] using hReturnLabel
        have hRun :=
          openRunNResult_dispatch_selected_site_source_running_continue
            (caseLabel := Structured.LabelSupply.label base idx)
            (returnLabel := site.returnLabel) (returnDest := returnDest)
            (pre := pre)
            (between :=
              testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix)
            (post := casesRest ++ post)
            (callee := callee) (target := target) (tokens := tokens)
            (token := token) (frame := frame) (returns := returns)
            (fuel := fuel) (tailTrace := tailTrace) (result := result)
            hFitsSelected hPc hRel hReturns (by omega)
            (by simpa [List.append_assoc] using hExactSelected)
            (by simpa [List.append_assoc] using hReturnSelected)
            (by
              intro final hRelFinal hPcFinal
              simpa [
                Structured.Preservation.DispatchPreservation.tableCode,
                headTest, headCase, testsRest, casesRest,
                Structured.Preservation.DispatchPreservation.testCode,
                Structured.Preservation.DispatchPreservation.caseCode,
                hRetc, hToken, List.append_assoc] using
                hRest final hRelFinal hPcFinal)
        simpa [
          returnDispatchSelectedTableFuel,
          Structured.Preservation.DispatchPreservation.tableCode,
          headTest, headCase, testsRest, casesRest,
          Structured.Preservation.DispatchPreservation.testCode,
          Structured.Preservation.DispatchPreservation.caseCode,
          hRetc, hToken, List.append_assoc] using hRun
      ·
        have hNe : head.token ≠ token := by
          intro hEq
          have hSiteTokenMem : site.token ∈ rest.map Structured.CallSite.token :=
            List.mem_map_of_mem (f := Structured.CallSite.token) hMemRest
          apply hHeadNotIn
          simpa [hEq, hToken] using hSiteTokenMem
        have hHeadTokenNeSite : head.token ≠ site.token := by
          intro hEq
          exact hNe (by simpa [hToken] using hEq)
        let headCasePre :=
          pre ++ headTest ++ testsRest ++ [Assembly.Instr.prim .invalid] ++
            casePrefix
        have hHeadCaseLabel :
            Assembly.Program.labelPc
              (pre ++
                Structured.Preservation.DispatchPreservation.tableCode
                  base retc idx casePrefix (head :: rest) ++ post)
              (Structured.LabelSupply.label base idx) =
                some (Assembly.Program.byteLength headCasePre) := by
          have hHere :=
            hExact.labelPc_at headCasePre
              (Structured.LabelSupply.label base idx)
              (Structured.StackShuffle.removeBuriedUnder retc ++
                [Assembly.Instr.jump head.returnLabel] ++ casesRest ++ post)
              (by
                simp [
                  Structured.Preservation.DispatchPreservation.tableCode,
                  headCasePre, headTest, testsRest, casesRest,
                  Structured.Preservation.DispatchPreservation.testCode,
                  Structured.Preservation.DispatchPreservation.caseCode,
                  List.append_assoc])
          simpa [headCasePre] using hHere
        have hFitsHead :
            Structured.Preservation.AssemblyProgram.PCFitsFrom pre
              [ Structured.StackShuffle.dupInstr
                  (callee.evm.stack.length + 1)
              , Assembly.Instr.push head.token
              , Assembly.Instr.prim .eq
              , Assembly.Instr.jumpi
                  (Structured.LabelSupply.label base idx)
              ] := by
          have hHead :
              Structured.Preservation.AssemblyProgram.PCFitsFrom pre
                headTest :=
            Structured.Preservation.AssemblyProgram.PCFitsFrom.left
              (pre := pre) (first := headTest)
              (second :=
                testsRest ++ [Assembly.Instr.prim .invalid] ++
                  casePrefix ++ headCase ++ casesRest)
              (by
                simpa [
                  Structured.Preservation.DispatchPreservation.tableCode,
                  headTest, headCase, testsRest, casesRest,
                  Structured.Preservation.DispatchPreservation.testCode,
                  Structured.Preservation.DispatchPreservation.caseCode,
                  List.append_assoc] using hFits)
          simpa [
            headTest, Structured.Preservation.DispatchPreservation.testCode,
            hRetc] using hHead
        have hRunHead :=
          openRunNResult_dispatch_mismatched_test_source_running_continue
            (caseLabel := Structured.LabelSupply.label base idx)
            (caseDest := Assembly.Program.byteLength headCasePre)
            (pre := pre)
            (post :=
              testsRest ++ [Assembly.Instr.prim .invalid] ++ casePrefix ++
                headCase ++ casesRest ++ post)
            (callee := callee) (target := target) (tokens := tokens)
            (token := token) (probe := head.token)
            (frame := frame) (returns := returns)
            (fuel := returnDispatchSelectedTableFuel retc rest site fuel)
            (tailTrace := tailTrace) (result := result)
            hNe hFitsHead hPc hRel hReturns (by omega)
            (by
              simpa [
                Structured.Preservation.DispatchPreservation.tableCode,
                headTest, headCase, testsRest, casesRest,
                Structured.Preservation.DispatchPreservation.testCode,
                Structured.Preservation.DispatchPreservation.caseCode,
                hRetc, headCasePre, List.append_assoc]
                using hHeadCaseLabel)
            (by
              intro afterHead hRelAfterHead hPcAfterHead
              have hFitsRest :
                  Structured.Preservation.AssemblyProgram.PCFitsFrom
                    (pre ++ headTest)
                    (Structured.Preservation.DispatchPreservation.tableCode
                      base retc (idx + 1) (casePrefix ++ headCase) rest) := by
                simpa [
                  Structured.Preservation.DispatchPreservation.tableCode,
                  headTest, headCase, testsRest, casesRest,
                  Structured.Preservation.DispatchPreservation.testCode,
                  Structured.Preservation.DispatchPreservation.caseCode,
                  List.append_assoc] using
                  (Structured.Preservation.AssemblyProgram.PCFitsFrom.right
                    (pre := pre) (first := headTest)
                    (second :=
                      testsRest ++ [Assembly.Instr.prim .invalid] ++
                        casePrefix ++ headCase ++ casesRest)
                    (by
                      simpa [
                        Structured.Preservation.DispatchPreservation.tableCode,
                        headTest, headCase, testsRest, casesRest,
                        Structured.Preservation.DispatchPreservation.testCode,
                        Structured.Preservation.DispatchPreservation.caseCode,
                        List.append_assoc] using hFits))
              have hExactRest :
                  Structured.Preservation.ExactLabels
                    ((pre ++ headTest) ++
                      Structured.Preservation.DispatchPreservation.tableCode
                        base retc (idx + 1) (casePrefix ++ headCase) rest ++
                      post) := by
                simpa [
                  Structured.Preservation.DispatchPreservation.tableCode,
                  headTest, headCase, testsRest, casesRest,
                  Structured.Preservation.DispatchPreservation.testCode,
                  Structured.Preservation.DispatchPreservation.caseCode,
                  List.append_assoc] using hExact
              have hReturnRest :
                  Assembly.Program.labelPc
                    ((pre ++ headTest) ++
                      Structured.Preservation.DispatchPreservation.tableCode
                        base retc (idx + 1) (casePrefix ++ headCase) rest ++
                      post)
                    site.returnLabel = some returnDest := by
                simpa [
                  Structured.Preservation.DispatchPreservation.tableCode,
                  headTest, headCase, testsRest, casesRest,
                  Structured.Preservation.DispatchPreservation.testCode,
                  Structured.Preservation.DispatchPreservation.caseCode,
                  List.append_assoc] using hReturnLabel
              simpa [
                Structured.Preservation.DispatchPreservation.tableCode,
                headTest, headCase, testsRest, casesRest,
                Structured.Preservation.DispatchPreservation.testCode,
                Structured.Preservation.DispatchPreservation.caseCode,
                hRetc, List.append_assoc] using
                (ih (pre := pre ++ headTest) (idx := idx + 1)
                  (casePrefix := casePrefix ++ headCase)
                  (target := afterHead)
                  hMemRest hNoDupRest hFitsRest
                  (by
                    simpa [headTest,
                      Structured.Preservation.DispatchPreservation.testCode,
                      hRetc] using hPcAfterHead)
                  hRelAfterHead hExactRest hReturnRest
                  (by
                    intro final hRelFinal hPcFinal
                    simpa [
                      Structured.Preservation.DispatchPreservation.tableCode,
                      headTest, headCase, testsRest, casesRest,
                      Structured.Preservation.DispatchPreservation.testCode,
                      Structured.Preservation.DispatchPreservation.caseCode,
                      hRetc, List.append_assoc] using
                      hRest final hRelFinal hPcFinal)))
        simpa [
          returnDispatchSelectedTableFuel, hHeadTokenNeSite,
          Structured.Preservation.DispatchPreservation.tableCode,
          headTest, headCase, testsRest, casesRest,
          Structured.Preservation.DispatchPreservation.testCode,
          Structured.Preservation.DispatchPreservation.caseCode,
          hRetc, List.append_assoc] using hRunHead

theorem openRunNResult_forProc_selected_source_running_continue
    {proc : Structured.Proc} {sites : List Structured.CallSite}
    {supply : Structured.LabelSupply}
    {site : Structured.CallSite} {returnDest : Nat}
    {pre post : Assembly.Program}
    {callee : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word} {token : Word}
    {frame : Structured.ReturnDest} {returns : List Structured.ReturnDest}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hMem :
      site ∈ (sites.filter (Structured.CallSite.forProc proc.name)))
    (hNoDup :
      (((sites.filter (Structured.CallSite.forProc proc.name)).map
        Structured.CallSite.token)).Nodup)
    (hToken : site.token = token)
    (hRetc : callee.evm.stack.length = proc.retc)
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (Structured.Dispatch.forProc proc sites supply).code)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Structured.Preservation.Frame.StateRel callee target (token :: tokens))
    (hReturns : callee.returns = frame :: returns)
    (hBound : proc.retc < 16)
    (hExact :
      Structured.Preservation.ExactLabels
        (pre ++ (Structured.Dispatch.forProc proc sites supply).code ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (pre ++ (Structured.Dispatch.forProc proc sites supply).code ++ post)
        site.returnLabel = some returnDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          { callee with
            evm :=
              { callee.evm with
                stack := callee.evm.stack ++ frame.callerStack }
            returns := returns }
          final tokens →
        final.pc = EvmYul.UInt256.ofNat returnDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              (Structured.Dispatch.forProc proc sites supply).code ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ (Structured.Dispatch.forProc proc sites supply).code ++ post)
        (returnDispatchSelectedTableFuel proc.retc
          (sites.filter (Structured.CallSite.forProc proc.name)) site fuel)
        target)
      tailTrace result := by
  let procSites := sites.filter (Structured.CallSite.forProc proc.name)
  have hFitsTable :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (Structured.Preservation.DispatchPreservation.tableCode
          supply proc.retc 0 [] procSites) := by
    simpa [Structured.Dispatch.forProc,
      Structured.Preservation.DispatchPreservation.tableCode, procSites,
      List.append_assoc] using hFits
  have hExactTable :
      Structured.Preservation.ExactLabels
        (pre ++
          Structured.Preservation.DispatchPreservation.tableCode
            supply proc.retc 0 [] procSites ++ post) := by
    simpa [Structured.Dispatch.forProc,
      Structured.Preservation.DispatchPreservation.tableCode, procSites,
      List.append_assoc] using hExact
  have hReturnTable :
      Assembly.Program.labelPc
        (pre ++
          Structured.Preservation.DispatchPreservation.tableCode
            supply proc.retc 0 [] procSites ++ post)
        site.returnLabel = some returnDest := by
    simpa [Structured.Dispatch.forProc,
      Structured.Preservation.DispatchPreservation.tableCode, procSites,
      List.append_assoc] using hReturnLabel
  have hRun :=
    openRunNResult_selected_table_source_running_continue
      (base := supply) (retc := proc.retc) (idx := 0)
      (casePrefix := []) (post := post) (pre := pre)
      (sites := procSites) (site := site) (returnDest := returnDest)
      (callee := callee) (target := target) (tokens := tokens)
      (token := token) (frame := frame) (returns := returns)
      (fuel := fuel) (tailTrace := tailTrace) (result := result)
      (by simpa [procSites] using hMem)
      (by simpa [procSites] using hNoDup)
      hToken hRetc hFitsTable hPc hRel hReturns hBound hExactTable
      hReturnTable
      (by
        intro final hRelFinal hPcFinal
        simpa [Structured.Dispatch.forProc,
          Structured.Preservation.DispatchPreservation.tableCode, procSites,
          List.append_assoc] using hRest final hRelFinal hPcFinal)
  simpa [Structured.Dispatch.forProc,
    Structured.Preservation.DispatchPreservation.tableCode, procSites,
    List.append_assoc] using hRun

theorem openRunNResult_callPrologue_source_running_continue
    {state : EvmYul.EVM.State}
    {args suffix : List Word} {token : Word}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        ([Assembly.Instr.push token] ++
          Structured.StackShuffle.sinkTopUnder args.length))
    (hPc :
      ({ state with stack := args ++ suffix } : EvmYul.EVM.State).pc =
        Assembly.Program.pcAfter pre)
    (hBound : args.length ≤ 16)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        final.stack = args ++ token :: suffix →
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { state with stack := args ++ token :: suffix } →
        final.pc =
          Assembly.Program.pcAfter
            (pre ++
              ([Assembly.Instr.push token] ++
                Structured.StackShuffle.sinkTopUnder args.length)) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              ([Assembly.Instr.push token] ++
                Structured.StackShuffle.sinkTopUnder args.length) ++
              post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++
          ([Assembly.Instr.push token] ++
            Structured.StackShuffle.sinkTopUnder args.length) ++
          post)
        (([Assembly.Instr.push token] ++
          Structured.StackShuffle.sinkTopUnder args.length).length + fuel)
        { state with stack := args ++ suffix })
      tailTrace result := by
  let start : EvmYul.EVM.State := { state with stack := args ++ suffix }
  let afterPush : EvmYul.EVM.State :=
    start.replaceStackAndIncrPC (token :: args ++ suffix) (pcΔ := 33)
  have hPushStep :
      Assembly.Target.stepInstr
          (Structured.Preservation.StackShuffle.targetInstr
            (Assembly.Instr.push token))
          start =
        .ok afterPush := by
    simp [Structured.Preservation.StackShuffle.targetInstr, start,
      afterPush, Assembly.Target.stepInstr, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hAfterPushPc :
      afterPush.pc =
        Assembly.Program.pcAfter (pre ++ [Assembly.Instr.push token]) := by
    calc
      afterPush.pc = state.pc + EvmYul.UInt256.ofNat 33 := by
          simp [afterPush, start,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
      _ = Assembly.Program.pcAfter pre + EvmYul.UInt256.ofNat 33 := by
          rw [hPc]
      _ = EvmYul.UInt256.ofNat
            (Assembly.Program.byteLength pre + 33) := by
          rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ = Assembly.Program.pcAfter (pre ++ [Assembly.Instr.push token]) := by
          simp [Assembly.Program.pcAfter,
            Assembly.Program.byteLength_append,
            Assembly.Program.byteLength, Assembly.Instr.byteSize,
            Assembly.Instr.push32Size]
  have hAfterPushStack :
      afterPush.stack = token :: args ++ suffix := by
    simp [afterPush, start, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hAfterPushRecord :
      { afterPush with stack := token :: args ++ suffix } = afterPush := by
    rw [← hAfterPushStack]
  have hFitsSink :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (pre ++ [Assembly.Instr.push token])
        (Structured.StackShuffle.sinkTopUnder args.length) := by
    exact hFits.2
  have hRestForSink :
      ∀ final : EvmYul.EVM.State,
        final.stack = args ++ token :: suffix →
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { afterPush with stack := args ++ token :: suffix } →
        final.pc =
          Assembly.Program.pcAfter
            ((pre ++ [Assembly.Instr.push token]) ++
              Structured.StackShuffle.sinkTopUnder args.length) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            ((pre ++ [Assembly.Instr.push token]) ++
              Structured.StackShuffle.sinkTopUnder args.length ++ post)
            fuel final)
          tailTrace result := by
    intro final hFinalStack hFinalErase hFinalPc
    have hFinalEraseFull :
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { state with stack := args ++ token :: suffix } := by
      calc
        Structured.Preservation.eraseControl final =
            Structured.Preservation.eraseControl
              { afterPush with stack := args ++ token :: suffix } :=
          hFinalErase
        _ =
            Structured.Preservation.eraseControl
              { state with stack := args ++ token :: suffix } := by
          simp [afterPush, start, Structured.Preservation.eraseControl,
            Assembly.eraseGas, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
    have hFinalPcFull :
        final.pc =
          Assembly.Program.pcAfter
            (pre ++
              ([Assembly.Instr.push token] ++
                Structured.StackShuffle.sinkTopUnder args.length)) := by
      simpa [List.append_assoc] using hFinalPc
    simpa [List.append_assoc] using
      hRest final hFinalStack hFinalEraseFull hFinalPcFull
  have hRestSink :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          ((pre ++ [Assembly.Instr.push token]) ++
            Structured.StackShuffle.sinkTopUnder args.length ++ post)
          ((Structured.StackShuffle.sinkTopUnder args.length).length + fuel)
          afterPush)
        tailTrace result := by
    have hPcSink :
        ({ afterPush with stack := token :: args ++ suffix } :
            EvmYul.EVM.State).pc =
          Assembly.Program.pcAfter (pre ++ [Assembly.Instr.push token]) := by
      simpa [hAfterPushRecord] using hAfterPushPc
    have hSink :=
      openRunNResult_sinkTopUnder_source_running_continue
        (state := afterPush) (args := args) (suffix := suffix)
        (token := token) (pre := pre ++ [Assembly.Instr.push token])
        (post := post) hFitsSink hPcSink hBound hRestForSink
    simpa [hAfterPushRecord, List.append_assoc] using hSink
  have hPushNoInstr :
      Assembly.Instr.usesCallCreate (Assembly.Instr.push token) = false := by
    simp [Assembly.Instr.usesCallCreate]
  have hFirst :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (pre ++ [Assembly.Instr.push token] ++
            (Structured.StackShuffle.sinkTopUnder args.length ++ post))
          (((Structured.StackShuffle.sinkTopUnder args.length).length + fuel) +
            1)
          start)
        tailTrace result := by
    exact
      openRunNResult_source_local_instr_no_call_running_continue
        (by simp [Structured.Preservation.StackShuffle.SourceLocalInstr])
        hPushNoInstr rfl hFits.1
        (by simpa [start] using hPc)
        hPushStep (by simpa [List.append_assoc] using hRestSink)
  have hFuel :
      ((Structured.StackShuffle.sinkTopUnder args.length).length + fuel) + 1 =
        ([Assembly.Instr.push token] ++
          Structured.StackShuffle.sinkTopUnder args.length).length + fuel := by
    simp
    omega
  simpa [start, hFuel, List.append_assoc] using hFirst

theorem openRunNResult_source_callEntry_after_prologue_and_jump_continue
    {source : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word} {argc retc : Nat}
    {args callerStack : EvmYul.Stack Word} {token : Word}
    {entryLabel : Assembly.Label} {entryDest : Nat}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        (([Assembly.Instr.push token] ++
          Structured.StackShuffle.sinkTopUnder args.length) ++
          [Assembly.Instr.jump entryLabel]))
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel :
      Structured.Preservation.Frame.StateRel source target tokens)
    (hSplit :
      Structured.StackFrame.splitArgs? argc source.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16)
    (hEntryLabel :
      Assembly.Program.labelPc
        (pre ++
          (([Assembly.Instr.push token] ++
            Structured.StackShuffle.sinkTopUnder args.length) ++
            [Assembly.Instr.jump entryLabel]) ++
          post)
        entryLabel = some entryDest)
    (hRest :
      ∀ afterJump : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          ((source.withEVM { source.evm with stack := args }).pushReturn
            callerStack retc)
          afterJump (token :: tokens) →
        afterJump.pc = EvmYul.UInt256.ofNat entryDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++
              (([Assembly.Instr.push token] ++
                Structured.StackShuffle.sinkTopUnder args.length) ++
                [Assembly.Instr.jump entryLabel]) ++
              post)
            fuel afterJump)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++
          (([Assembly.Instr.push token] ++
            Structured.StackShuffle.sinkTopUnder args.length) ++
            [Assembly.Instr.jump entryLabel]) ++
          post)
        ((([Assembly.Instr.push token] ++
          Structured.StackShuffle.sinkTopUnder args.length) ++
          [Assembly.Instr.jump entryLabel]).length + fuel)
        target)
      tailTrace result := by
  let prologue : Assembly.Program :=
    [Assembly.Instr.push token] ++
      Structured.StackShuffle.sinkTopUnder args.length
  let callState : Structured.RunState :=
    (source.withEVM { source.evm with stack := args }).pushReturn
      callerStack retc
  have hFitsPrologue :
      Structured.Preservation.AssemblyProgram.PCFitsFrom pre
        prologue := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.left
        (pre := pre) (first := prologue)
        (second := [Assembly.Instr.jump entryLabel])
        (by simpa [prologue, List.append_assoc] using hFits)
  have hFitsJump :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (pre ++ prologue) [Assembly.Instr.jump entryLabel] := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (pre := pre) (first := prologue)
        (second := [Assembly.Instr.jump entryLabel])
        (by simpa [prologue, List.append_assoc] using hFits)
  rcases
      Structured.Preservation.Frame.StateRel.caller_materialization_of_split
        hRel hSplit with
    ⟨callerTarget, hCaller, hTargetStack⟩
  have hTargetRecord :
      { target with stack := args ++ callerTarget } = target := by
    rw [← hTargetStack]
  have hRestForPrologue :
      ∀ final : EvmYul.EVM.State,
        final.stack = args ++ token :: callerTarget →
        Structured.Preservation.eraseControl final =
          Structured.Preservation.eraseControl
            { target with stack := args ++ token :: callerTarget } →
        final.pc =
          Assembly.Program.pcAfter (pre ++ prologue) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ prologue ++
              ([Assembly.Instr.jump entryLabel] ++ post))
            (fuel + 1) final)
          tailTrace result := by
    intro afterPrologue hFinalStack hFinalErase hFinalPc
    have hRelAfterPrologue :
        Structured.Preservation.Frame.StateRel callState afterPrologue
          (token :: tokens) := by
      refine ⟨?_, ?_⟩
      · rw [hFinalStack]
        simpa [callState, Structured.RunState.withEVM,
          Structured.RunState.pushReturn, List.append_assoc] using
          (Structured.Preservation.Frame.materializeStack_callEntry
            (args := args) (callerStack := callerStack)
            (callerTarget := callerTarget) (returns := source.returns)
            (tokens := tokens) (retc := retc) (token := token) hCaller)
      · calc
          Structured.Preservation.eraseControl afterPrologue =
              Structured.Preservation.eraseControl
                { target with stack := args ++ token :: callerTarget } :=
            hFinalErase
          _ =
              Structured.Preservation.eraseControl
                { source.evm with stack := args ++ token :: callerTarget } :=
            hRel.dataRel_replace_stack (args ++ token :: callerTarget)
          _ =
              Structured.Preservation.eraseControl
                { callState.evm with stack := afterPrologue.stack } := by
            simp [callState, Structured.RunState.withEVM,
              Structured.RunState.pushReturn, hFinalStack]
    have hJumpLabel :
        Assembly.Program.labelPc
          ((pre ++ prologue) ++ [Assembly.Instr.jump entryLabel] ++ post)
          entryLabel = some entryDest := by
      simpa [prologue, List.append_assoc] using hEntryLabel
    have hAfterJumpRel :
        Structured.Preservation.Frame.StateRel callState
          (Assembly.Source.jumpPc entryDest afterPrologue)
          (token :: tokens) := by
      refine ⟨?_, ?_⟩
      · simpa [Assembly.Source.jumpPc] using
          hRelAfterPrologue.stackRel
      · simpa [Assembly.Source.jumpPc,
          Structured.Preservation.eraseControl_with_pc] using
          hRelAfterPrologue.dataRel
    have hAfterJumpPc :
        (Assembly.Source.jumpPc entryDest afterPrologue).pc =
          EvmYul.UInt256.ofNat entryDest := by
      rfl
    have hJumpRun :=
      openRunNResult_source_jump_no_call_running_continue
        (pre := pre ++ prologue) (post := post)
        (label := entryLabel) (state := afterPrologue)
        (dest := entryDest) (fuel := fuel)
        (tailTrace := tailTrace) (result := result)
        (Structured.Preservation.AssemblyProgram.PCFitsFrom.start hFitsJump)
        hFinalPc hJumpLabel
        (by
          simpa [prologue, List.append_assoc] using
            hRest (Assembly.Source.jumpPc entryDest afterPrologue)
              hAfterJumpRel hAfterJumpPc)
    simpa [List.append_assoc] using hJumpRun
  have hPrologueRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (pre ++ prologue ++ ([Assembly.Instr.jump entryLabel] ++ post))
          (prologue.length + (fuel + 1))
          target)
        tailTrace result := by
    have hRun :=
      openRunNResult_callPrologue_source_running_continue
        (state := target) (args := args) (suffix := callerTarget)
        (token := token) (pre := pre)
        (post := [Assembly.Instr.jump entryLabel] ++ post)
        hFitsPrologue
        (by simpa [hTargetRecord] using hPc)
        hArgBound hRestForPrologue
    simpa [hTargetRecord, prologue, List.append_assoc] using hRun
  have hFuel :
      (Structured.StackShuffle.sinkTopUnder args.length).length + 1 +
          (fuel + 1) =
        (Structured.StackShuffle.sinkTopUnder args.length).length + 1 + 1 +
          fuel := by
    omega
  simpa [prologue, hFuel, List.append_assoc] using hPrologueRun

theorem openRunNResult_structured_callSite_callEntry_continue
    {program : Structured.Program} {proc : Structured.Proc}
    {bodySupply dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite} {site : Structured.CallSite}
    {source : Structured.RunState} {target : EvmYul.EVM.State}
    {args callerStack : EvmYul.Stack Word}
    {tokens : List Word} {token : Word}
    {asm : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (callSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args token site.returnLabel))
    (procSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.procSegment program
          proc bodySupply dispatchSupply sites))
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16)
    (hPc :
      target.pc = Structured.Preservation.CodeSegment.startPc callSeg)
    (hRel :
      Structured.Preservation.Frame.StateRel source target tokens)
    (hExact : Structured.Preservation.ExactLabels asm)
    (hRest :
      ∀ afterJump : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          ((source.withEVM { source.evm with stack := args }).pushReturn
            callerStack proc.retc)
          afterJump (token :: tokens) →
        afterJump.pc =
          Structured.Preservation.CodeSegment.startPc procSeg →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm fuel afterJump)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult asm
        ((Structured.Preservation.ProcedurePreservation.callJumpCode
          proc args token).length + fuel) target)
      tailTrace result := by
  let jumpCode :=
    Structured.Preservation.ProcedurePreservation.callJumpCode
      proc args token
  let returnCode : Assembly.Program :=
    [Assembly.Instr.label site.returnLabel]
  let procCode :=
    Structured.Preservation.ProcedurePreservation.procSegment program proc
      bodySupply dispatchSupply sites
  have hCallAsm :
      asm = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by
    calc
      asm =
          callSeg.pre ++
            Structured.Preservation.ProcedurePreservation.callSiteCode
              proc args token site.returnLabel ++
            callSeg.post := callSeg.hAsm
      _ = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by
            simp [jumpCode, returnCode,
              Structured.Preservation.ProcedurePreservation.callSiteCode,
              List.append_assoc]
  have hProcAsm :
      asm = procSeg.pre ++ procCode ++ procSeg.post := by
    simpa [procCode] using procSeg.hAsm
  have hCallFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom callSeg.pre
        (jumpCode ++ returnCode) := by
    simpa [jumpCode, returnCode,
      Structured.Preservation.ProcedurePreservation.callSiteCode,
      List.append_assoc] using callSeg.hFits
  have hFitsJump :
      Structured.Preservation.AssemblyProgram.PCFitsFrom callSeg.pre
        jumpCode := by
    exact
      Structured.Preservation.AssemblyProgram.PCFitsFrom.left
        (pre := callSeg.pre) (first := jumpCode) (second := returnCode)
        hCallFits
  have hEntryPcAsm :
      Assembly.Program.labelPc asm (Structured.ProcLabel.entry proc.name) =
        some (Assembly.Program.byteLength procSeg.pre) := by
    have hHere :=
      hExact.labelPc_at procSeg.pre (Structured.ProcLabel.entry proc.name)
        (Structured.Preservation.ProcedurePreservation.bodyCode program proc
            bodySupply ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc
            sites dispatchSupply ++
          procSeg.post)
        (by
          simpa [procCode,
            Structured.Preservation.ProcedurePreservation.procSegment,
            Structured.Preservation.ProcedurePreservation.bodyCode,
            Structured.Preservation.ProcedurePreservation.dispatchCode,
            List.append_assoc] using procSeg.hAsm)
    simpa using hHere
  have hEntryPcCall :
      Assembly.Program.labelPc
        (callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post)
        (Structured.ProcLabel.entry proc.name) =
        some (Assembly.Program.byteLength procSeg.pre) := by
    rw [← hCallAsm]
    exact hEntryPcAsm
  have hRun :=
    openRunNResult_source_callEntry_after_prologue_and_jump_continue
      (source := source) (target := target) (tokens := tokens)
      (argc := proc.argc) (retc := proc.retc) (args := args)
      (callerStack := callerStack) (token := token)
      (entryLabel := Structured.ProcLabel.entry proc.name)
      (entryDest := Assembly.Program.byteLength procSeg.pre)
      (pre := callSeg.pre) (post := returnCode ++ callSeg.post)
      (fuel := fuel) (tailTrace := tailTrace) (result := result)
      (by
        simpa [jumpCode,
          Structured.Preservation.ProcedurePreservation.callJumpCode,
          List.append_assoc] using hFitsJump)
      (by simpa [Structured.Preservation.CodeSegment.startPc] using hPc)
      hRel hSplit hArgBound
      (by
        simpa [jumpCode, returnCode,
          Structured.Preservation.ProcedurePreservation.callSiteCode,
          Structured.Preservation.ProcedurePreservation.callJumpCode,
          List.append_assoc] using hEntryPcCall)
      (by
        intro afterJump hAfterRel hAfterPc
        have hAfterPc' :
            afterJump.pc =
              Structured.Preservation.CodeSegment.startPc procSeg := by
          simpa [Structured.Preservation.CodeSegment.startPc,
            Assembly.Program.pcAfter] using hAfterPc
        simpa [hCallAsm, jumpCode,
          Structured.Preservation.ProcedurePreservation.callJumpCode,
          List.append_assoc] using hRest afterJump hAfterRel hAfterPc')
  simpa [hCallAsm, jumpCode, returnCode,
    Structured.Preservation.ProcedurePreservation.callJumpCode,
    Structured.Preservation.ProcedurePreservation.callSiteCode,
    List.append_assoc] using hRun

def codeSegment_procSegment_bodyCode
    {program : Structured.Program} {proc : Structured.Proc}
    {bodySupply dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite}
    {asm : Assembly.Program}
    (procSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.procSegment program
          proc bodySupply dispatchSupply sites)) :
    Structured.Preservation.CodeSegment asm
      (Structured.Preservation.ProcedurePreservation.bodyCode program proc
        bodySupply) := by
  let bodyCode :=
    Structured.Preservation.ProcedurePreservation.bodyCode program proc
      bodySupply
  let dispatchCode :=
    Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
      dispatchSupply
  let entryCode : Assembly.Program :=
    [Assembly.Instr.label (Structured.ProcLabel.entry proc.name)]
  let exitCode : Assembly.Program :=
    [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)]
  have hFitsFull :
      Structured.Preservation.AssemblyProgram.PCFitsFrom procSeg.pre
        (entryCode ++ bodyCode ++ exitCode ++ dispatchCode) := by
    simpa [entryCode, exitCode, bodyCode, dispatchCode,
      Structured.Preservation.ProcedurePreservation.procSegment,
      List.append_assoc] using procSeg.hFits
  have hFitsAfterEntry :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (procSeg.pre ++ entryCode)
        (bodyCode ++ (exitCode ++ dispatchCode)) := by
    simpa [List.append_assoc] using
      Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (pre := procSeg.pre) (first := entryCode)
        (second := bodyCode ++ exitCode ++ dispatchCode) hFitsFull
  exact
    { pre := procSeg.pre ++ entryCode
      post := exitCode ++ dispatchCode ++ procSeg.post
      hAsm := by
        simpa [entryCode, exitCode, bodyCode, dispatchCode,
          Structured.Preservation.ProcedurePreservation.procSegment,
          List.append_assoc] using procSeg.hAsm
      hFits :=
        Structured.Preservation.AssemblyProgram.PCFitsFrom.left
          (pre := procSeg.pre ++ entryCode) (first := bodyCode)
          (second := exitCode ++ dispatchCode) hFitsAfterEntry }

theorem structured_dispatch_forProc_usesCallCreate_false
    (proc : Structured.Proc) (sites : List Structured.CallSite)
    (supply : Structured.LabelSupply) :
    Assembly.Program.usesCallCreate
      (Structured.Dispatch.forProc proc sites supply).code = false :=
  Structured.CompilerFacts.dispatch_forProc_noCallCreate proc sites supply

theorem openRunNResult_source_label_running_continue
    {source : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word} {label : Assembly.Label}
    {pre post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hFit : Structured.Preservation.PCFits pre)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Structured.Preservation.Frame.StateRel source target tokens)
    (hRest :
      ∀ afterLabel : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel source afterLabel tokens →
        afterLabel.pc =
          Assembly.Program.pcAfter (pre ++ [Assembly.Instr.label label]) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ [Assembly.Instr.label label] ++ post) fuel afterLabel)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (pre ++ [Assembly.Instr.label label] ++ post) (fuel + 1) target)
      tailTrace result := by
  rcases
      Structured.Preservation.Frame.StateRel.label_stepResult_at
        (label := label) (pre := pre) (post := post)
        (source := source) (target := target) (tokens := tokens)
        hFit hPc hRel with
    ⟨afterLabel, hStep, hRelAfter, hPcAfter⟩
  have hAt :
      Assembly.Program.instrAtPc
          (pre ++ [Assembly.Instr.label label] ++ post) target.pc.toNat =
        some (Assembly.Program.byteLength pre, Assembly.Instr.label label) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post (Assembly.Instr.label label) 0
  exact
    OpenAssembly.Source.openRunNResult_current_no_call_running_continue_of_current_instr
      hAt (by simp [Assembly.Instr.usesCallCreate]) hStep
      (hRest afterLabel hRelAfter hPcAfter)

theorem openRunNResult_proc_entry_label_continue
    {program : Structured.Program} {proc : Structured.Proc}
    {bodySupply dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite}
    {source : Structured.RunState} {target : EvmYul.EVM.State}
    {tokens : List Word}
    {asm : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (procSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.procSegment program
          proc bodySupply dispatchSupply sites))
    (hPc : target.pc = Structured.Preservation.CodeSegment.startPc procSeg)
    (hRel :
      Structured.Preservation.Frame.StateRel source target tokens)
    (hRest :
      ∀ afterEntry : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel source afterEntry tokens →
        afterEntry.pc =
          Structured.Preservation.CodeSegment.startPc
            (codeSegment_procSegment_bodyCode procSeg) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm fuel afterEntry)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult asm (fuel + 1) target)
      tailTrace result := by
  let bodyCode :=
    Structured.Preservation.ProcedurePreservation.bodyCode program proc
      bodySupply
  let dispatchCode :=
    Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
      dispatchSupply
  let entryCode : Assembly.Program :=
    [Assembly.Instr.label (Structured.ProcLabel.entry proc.name)]
  let exitCode : Assembly.Program :=
    [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)]
  have hAsm :
      asm =
        procSeg.pre ++ entryCode ++ bodyCode ++ exitCode ++ dispatchCode ++
          procSeg.post := by
    simpa [entryCode, exitCode, bodyCode, dispatchCode,
      Structured.Preservation.ProcedurePreservation.procSegment,
      List.append_assoc] using procSeg.hAsm
  have hFitsEntry :
      Structured.Preservation.PCFits procSeg.pre :=
    Structured.Preservation.AssemblyProgram.PCFitsFrom.start procSeg.hFits
  have hRun :=
    openRunNResult_source_label_running_continue
      (source := source) (target := target) (tokens := tokens)
      (label := Structured.ProcLabel.entry proc.name)
      (pre := procSeg.pre)
      (post := bodyCode ++ exitCode ++ dispatchCode ++ procSeg.post)
      (fuel := fuel) (tailTrace := tailTrace) (result := result)
      hFitsEntry
      (by simpa [Structured.Preservation.CodeSegment.startPc] using hPc)
      hRel
      (by
        intro afterEntry hRelAfter hPcAfter
        have hPcAfter' :
            afterEntry.pc =
              Structured.Preservation.CodeSegment.startPc
                (codeSegment_procSegment_bodyCode procSeg) := by
          simpa [codeSegment_procSegment_bodyCode,
            Structured.Preservation.CodeSegment.startPc, entryCode,
            bodyCode, dispatchCode, exitCode] using hPcAfter
        simpa [hAsm, entryCode, exitCode, bodyCode, dispatchCode,
          List.append_assoc] using hRest afterEntry hRelAfter hPcAfter')
  simpa [hAsm, entryCode, exitCode, bodyCode, dispatchCode, List.append_assoc]
    using hRun

theorem openRunNResult_structured_callSite_body_continue
    {program : Structured.Program} {proc : Structured.Proc}
    {bodySupply dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite} {site : Structured.CallSite}
    {source : Structured.RunState} {target : EvmYul.EVM.State}
    {args callerStack : EvmYul.Stack Word}
    {tokens : List Word} {token : Word}
    {asm : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (callSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args token site.returnLabel))
    (procSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.procSegment program
          proc bodySupply dispatchSupply sites))
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16)
    (hPc :
      target.pc = Structured.Preservation.CodeSegment.startPc callSeg)
    (hRel :
      Structured.Preservation.Frame.StateRel source target tokens)
    (hExact : Structured.Preservation.ExactLabels asm)
    (hRest :
      ∀ afterEntry : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          ((source.withEVM { source.evm with stack := args }).pushReturn
            callerStack proc.retc)
          afterEntry (token :: tokens) →
        afterEntry.pc =
          Structured.Preservation.CodeSegment.startPc
            (codeSegment_procSegment_bodyCode procSeg) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm fuel afterEntry)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult asm
        ((Structured.Preservation.ProcedurePreservation.callJumpCode
          proc args token).length + (fuel + 1)) target)
      tailTrace result := by
  exact
    openRunNResult_structured_callSite_callEntry_continue
      (program := program) (proc := proc) (bodySupply := bodySupply)
      (dispatchSupply := dispatchSupply) (sites := sites) (site := site)
      (source := source) (target := target) (args := args)
      (callerStack := callerStack) (tokens := tokens) (token := token)
      (asm := asm) (fuel := fuel + 1) (tailTrace := tailTrace)
      (result := result) callSeg procSeg hSplit hArgBound hPc hRel hExact
      (by
        intro afterJump hAfterRel hAfterPc
        exact
          openRunNResult_proc_entry_label_continue
            (procSeg := procSeg) hAfterPc hAfterRel hRest)

theorem openRunNResult_exit_label_then_dispatch_continue
    {proc : Structured.Proc}
    {dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite}
    {site : Structured.CallSite} {returnDest : Nat}
    {bodyState returned : Structured.RunState}
    {stack : EvmYul.Stack Word} {frame : Structured.ReturnDest}
    {target : EvmYul.EVM.State} {tokens : List Word} {token : Word}
    {preExit post : Assembly.Program}
    {fuel : Nat} {tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hReturns : bodyState.returns = frame :: returned.returns)
    (hRetc : bodyState.evm.stack.length = proc.retc)
    (hMem :
      site ∈ sites.filter (Structured.CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (Structured.CallSite.forProc proc.name)).map
        Structured.CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hFitsExit :
      Structured.Preservation.AssemblyProgram.PCFitsFrom preExit
        [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)])
    (hFitsDispatch :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)])
        (Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
          dispatchSupply))
    (hPc : target.pc = Assembly.Program.pcAfter preExit)
    (hRel :
      Structured.Preservation.Frame.StateRel bodyState target
        (token :: tokens))
    (hExact :
      Structured.Preservation.ExactLabels
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        site.returnLabel = some returnDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          (returned.withEVM { bodyState.evm with stack := stack })
          final tokens →
        final.pc = EvmYul.UInt256.ofNat returnDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (preExit ++
              [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
              Structured.Preservation.ProcedurePreservation.dispatchCode proc
                sites dispatchSupply ++ post)
            fuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        (returnDispatchSelectedTableFuel proc.retc
          (sites.filter (Structured.CallSite.forProc proc.name)) site fuel + 1)
        target)
      tailTrace result := by
  let dcode :=
    Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
      dispatchSupply
  have hSourceEq :
      returned.withEVM { bodyState.evm with stack := stack } =
        { bodyState with
          evm :=
            { bodyState.evm with
              stack := bodyState.evm.stack ++ frame.callerStack }
          returns := returned.returns } :=
    Structured.Preservation.Frame.CallFacts.returned_with_attached_eq hAttach
  have hRun :=
    openRunNResult_source_label_running_continue
      (source := bodyState) (target := target)
      (tokens := token :: tokens)
      (label := Structured.ProcLabel.exit proc.name)
      (pre := preExit) (post := dcode ++ post)
      (fuel := returnDispatchSelectedTableFuel proc.retc
        (sites.filter (Structured.CallSite.forProc proc.name)) site fuel)
      (tailTrace := tailTrace) (result := result)
      (Structured.Preservation.AssemblyProgram.PCFitsFrom.start hFitsExit)
      hPc hRel
      (by
        intro afterExit hAfterRel hAfterPc
        have hDispatch :=
          openRunNResult_forProc_selected_source_running_continue
            (proc := proc) (sites := sites) (supply := dispatchSupply)
            (site := site) (returnDest := returnDest)
            (pre := preExit ++
              [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)])
            (post := post) (callee := bodyState) (target := afterExit)
            (tokens := tokens) (token := token) (frame := frame)
            (returns := returned.returns) (fuel := fuel)
            (tailTrace := tailTrace) (result := result)
            hMem hNoDup hToken hRetc
            (by simpa [dcode,
              Structured.Preservation.ProcedurePreservation.dispatchCode]
              using hFitsDispatch)
            hAfterPc hAfterRel hReturns hBound
            (by simpa [dcode,
              Structured.Preservation.ProcedurePreservation.dispatchCode,
              List.append_assoc] using hExact)
            (by simpa [dcode,
              Structured.Preservation.ProcedurePreservation.dispatchCode,
              List.append_assoc] using hReturnLabel)
            (by
              intro final hRelFinal hPcFinal
              have hRelFinal' :
                  Structured.Preservation.Frame.StateRel
                    (returned.withEVM
                      { bodyState.evm with stack := stack })
                    final tokens := by
                simpa [hSourceEq] using hRelFinal
              simpa [dcode,
                Structured.Preservation.ProcedurePreservation.dispatchCode,
                List.append_assoc] using
                hRest final hRelFinal' hPcFinal)
        simpa [dcode,
          Structured.Preservation.ProcedurePreservation.dispatchCode,
          List.append_assoc] using hDispatch)
  simpa [dcode, Structured.Preservation.ProcedurePreservation.dispatchCode,
    List.append_assoc] using hRun

theorem openRunNResult_body_regular_then_exit_dispatch_continue
    {proc : Structured.Proc}
    {dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite}
    {site : Structured.CallSite} {returnDest : Nat}
    {bodyCtx : Structured.CompileContext}
    {bodyState returned : Structured.RunState}
    {stack : EvmYul.Stack Word} {frame : Structured.ReturnDest}
    {entryTarget afterBody : EvmYul.EVM.State}
    {tokens : List Word} {token : Word}
    {preExit post : Assembly.Program}
    {bodyFuel tailFuel : Nat}
    {bodyTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hBodyRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (preExit ++
            [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
            Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
              dispatchSupply ++ post)
          bodyFuel entryTarget)
        bodyTrace (.ok (.running afterBody)))
    (hBodyRel :
      Structured.Preservation.CompiledOutcomeRel
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        bodyCtx (Assembly.Program.pcAfter preExit)
        (Structured.Outcome.regular bodyState)
        (.running afterBody) (token :: tokens))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hReturns : bodyState.returns = frame :: returned.returns)
    (hRetc : bodyState.evm.stack.length = proc.retc)
    (hMem :
      site ∈ sites.filter (Structured.CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (Structured.CallSite.forProc proc.name)).map
        Structured.CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hFitsExit :
      Structured.Preservation.AssemblyProgram.PCFitsFrom preExit
        [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)])
    (hFitsDispatch :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)])
        (Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
          dispatchSupply))
    (hExact :
      Structured.Preservation.ExactLabels
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        site.returnLabel = some returnDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          (returned.withEVM { bodyState.evm with stack := stack })
          final tokens →
        final.pc = EvmYul.UInt256.ofNat returnDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (preExit ++
              [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
              Structured.Preservation.ProcedurePreservation.dispatchCode proc
                sites dispatchSupply ++ post)
            tailFuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        (bodyFuel +
          (returnDispatchSelectedTableFuel proc.retc
            (sites.filter (Structured.CallSite.forProc proc.name)) site
            tailFuel + 1))
        entryTarget)
      (bodyTrace ++ tailTrace) result := by
  rcases hBodyRel with ⟨hRelAfterBody, hPcAfterBody⟩
  have hTail :=
    openRunNResult_exit_label_then_dispatch_continue
      (proc := proc) (dispatchSupply := dispatchSupply) (sites := sites)
      (site := site) (returnDest := returnDest)
      (bodyState := bodyState) (returned := returned)
      (stack := stack) (frame := frame) (target := afterBody)
      (tokens := tokens) (token := token) (preExit := preExit)
      (post := post) (fuel := tailFuel) (tailTrace := tailTrace)
      (result := result) hAttach hReturns hRetc hMem hNoDup hToken hBound
      hFitsExit hFitsDispatch hPcAfterBody hRelAfterBody hExact hReturnLabel
      hRest
  exact
    OpenAssembly.Source.openRunNResult_resolves_running_continue
      hBodyRun hTail

theorem openRunNResult_body_leave_then_exit_dispatch_continue
    {proc : Structured.Proc}
    {dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite}
    {site : Structured.CallSite} {returnDest : Nat}
    {bodyCtx : Structured.CompileContext}
    {bodyState returned : Structured.RunState}
    {stack : EvmYul.Stack Word} {frame : Structured.ReturnDest}
    {entryTarget afterBody : EvmYul.EVM.State}
    {tokens : List Word} {token : Word}
    {preExit post : Assembly.Program}
    {bodyFuel tailFuel : Nat}
    {bodyTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (hBodyRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (preExit ++
            [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
            Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
              dispatchSupply ++ post)
          bodyFuel entryTarget)
        bodyTrace (.ok (.running afterBody)))
    (hBodyRel :
      Structured.Preservation.CompiledOutcomeRel
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        bodyCtx (Assembly.Program.pcAfter preExit)
        (Structured.Outcome.leave bodyState)
        (.running afterBody) (token :: tokens))
    (hCtxLeave :
      bodyCtx.leaveLabel? = some (Structured.ProcLabel.exit proc.name))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hReturns : bodyState.returns = frame :: returned.returns)
    (hRetc : bodyState.evm.stack.length = proc.retc)
    (hMem :
      site ∈ sites.filter (Structured.CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (Structured.CallSite.forProc proc.name)).map
        Structured.CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hFitsExit :
      Structured.Preservation.AssemblyProgram.PCFitsFrom preExit
        [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)])
    (hFitsDispatch :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)])
        (Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
          dispatchSupply))
    (hExact :
      Structured.Preservation.ExactLabels
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post))
    (hReturnLabel :
      Assembly.Program.labelPc
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        site.returnLabel = some returnDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          (returned.withEVM { bodyState.evm with stack := stack })
          final tokens →
        final.pc = EvmYul.UInt256.ofNat returnDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (preExit ++
              [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
              Structured.Preservation.ProcedurePreservation.dispatchCode proc
                sites dispatchSupply ++ post)
            tailFuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        (bodyFuel +
          (returnDispatchSelectedTableFuel proc.retc
            (sites.filter (Structured.CallSite.forProc proc.name)) site
            tailFuel + 1))
        entryTarget)
      (bodyTrace ++ tailTrace) result := by
  rcases hBodyRel with
    ⟨label, dest, hLeaveLabel, hLabelPc, hRelAfterBody, hPcAfterBody⟩
  rw [hCtxLeave] at hLeaveLabel
  cases hLeaveLabel
  have hExitPc :
      Assembly.Program.labelPc
        (preExit ++
          [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)] ++
          Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
            dispatchSupply ++ post)
        (Structured.ProcLabel.exit proc.name) =
          some (Assembly.Program.byteLength preExit) := by
    have hHere :=
      hExact.labelPc_at preExit
        (Structured.ProcLabel.exit proc.name)
        (Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
          dispatchSupply ++ post)
        (by simp [List.append_assoc])
    simpa [List.append_assoc] using hHere
  rw [hExitPc] at hLabelPc
  cases hLabelPc
  have hPcAfterBody' :
      afterBody.pc = Assembly.Program.pcAfter preExit := by
    simpa [Assembly.Program.pcAfter] using hPcAfterBody
  have hTail :=
    openRunNResult_exit_label_then_dispatch_continue
      (proc := proc) (dispatchSupply := dispatchSupply) (sites := sites)
      (site := site) (returnDest := returnDest)
      (bodyState := bodyState) (returned := returned)
      (stack := stack) (frame := frame) (target := afterBody)
      (tokens := tokens) (token := token) (preExit := preExit)
      (post := post) (fuel := tailFuel) (tailTrace := tailTrace)
      (result := result) hAttach hReturns hRetc hMem hNoDup hToken hBound
      hFitsExit hFitsDispatch hPcAfterBody' hRelAfterBody hExact hReturnLabel
      hRest
  exact
    OpenAssembly.Source.openRunNResult_resolves_running_continue
      hBodyRun hTail

theorem openRunNResult_callSite_body_regular_then_exit_dispatch_continue
    {program : Structured.Program} {proc : Structured.Proc}
    {bodySupply dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite} {site : Structured.CallSite}
    {returnDest : Nat} {bodyCtx : Structured.CompileContext}
    {source bodyState returned : Structured.RunState}
    {target afterBody : EvmYul.EVM.State}
    {args callerStack stack : EvmYul.Stack Word}
    {frame : Structured.ReturnDest}
    {tokens : List Word} {token : Word}
    {asm : Assembly.Program}
    {bodyFuel tailFuel : Nat}
    {bodyTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (callSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args token site.returnLabel))
    (procSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.procSegment program
          proc bodySupply dispatchSupply sites))
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16)
    (hPc :
      target.pc = Structured.Preservation.CodeSegment.startPc callSeg)
    (hRel :
      Structured.Preservation.Frame.StateRel source target tokens)
    (hBodyRun :
      ∀ entryTarget : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          ((source.withEVM { source.evm with stack := args }).pushReturn
            callerStack proc.retc)
          entryTarget (token :: tokens) →
        entryTarget.pc =
          Structured.Preservation.CodeSegment.startPc
            (codeSegment_procSegment_bodyCode procSeg) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm bodyFuel entryTarget)
          bodyTrace (.ok (.running afterBody)))
    (hBodyRel :
      Structured.Preservation.CompiledOutcomeRel asm bodyCtx
        (Structured.Preservation.CodeSegment.fallthroughPc
          (codeSegment_procSegment_bodyCode procSeg))
        (Structured.Outcome.regular bodyState) (.running afterBody)
        (token :: tokens))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hReturns : bodyState.returns = frame :: returned.returns)
    (hRetc : bodyState.evm.stack.length = proc.retc)
    (hMem :
      site ∈ sites.filter (Structured.CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (Structured.CallSite.forProc proc.name)).map
        Structured.CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hExact : Structured.Preservation.ExactLabels asm)
    (hReturnLabel :
      Assembly.Program.labelPc asm site.returnLabel = some returnDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          (returned.withEVM { bodyState.evm with stack := stack })
          final tokens →
        final.pc = EvmYul.UInt256.ofNat returnDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm tailFuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult asm
        ((Structured.Preservation.ProcedurePreservation.callJumpCode
          proc args token).length +
          ((bodyFuel +
            (returnDispatchSelectedTableFuel proc.retc
              (sites.filter (Structured.CallSite.forProc proc.name)) site
              tailFuel + 1)) + 1))
        target)
      (bodyTrace ++ tailTrace) result := by
  let bodySeg := codeSegment_procSegment_bodyCode procSeg
  let bodyCode :=
    Structured.Preservation.ProcedurePreservation.bodyCode program proc
      bodySupply
  let dispatchCode :=
    Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
      dispatchSupply
  let entryCode : Assembly.Program :=
    [Assembly.Instr.label (Structured.ProcLabel.entry proc.name)]
  let exitCode : Assembly.Program :=
    [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)]
  let preExit := procSeg.pre ++ entryCode ++ bodyCode
  let expandedAsm := preExit ++ exitCode ++ dispatchCode ++ procSeg.post
  have hAsmExpanded : asm = expandedAsm := by
    simpa [expandedAsm, preExit, entryCode, exitCode, bodyCode, dispatchCode,
      Structured.Preservation.ProcedurePreservation.procSegment,
      List.append_assoc] using procSeg.hAsm
  have hFitsFull :
      Structured.Preservation.AssemblyProgram.PCFitsFrom procSeg.pre
        (entryCode ++ bodyCode ++ exitCode ++ dispatchCode) := by
    simpa [entryCode, exitCode, bodyCode, dispatchCode,
      Structured.Preservation.ProcedurePreservation.procSegment,
      List.append_assoc] using procSeg.hFits
  have hFitsFull' :
      Structured.Preservation.AssemblyProgram.PCFitsFrom procSeg.pre
        ((entryCode ++ bodyCode) ++ (exitCode ++ dispatchCode)) := by
    simpa [List.append_assoc] using hFitsFull
  have hFitsAfterBody :
      Structured.Preservation.AssemblyProgram.PCFitsFrom preExit
        (exitCode ++ dispatchCode) := by
    simpa [preExit, List.append_assoc] using
      Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (pre := procSeg.pre) (first := entryCode ++ bodyCode)
        (second := exitCode ++ dispatchCode) hFitsFull'
  have hFitsExit :
      Structured.Preservation.AssemblyProgram.PCFitsFrom preExit exitCode :=
    Structured.Preservation.AssemblyProgram.PCFitsFrom.left hFitsAfterBody
  have hFitsDispatch :
      Structured.Preservation.AssemblyProgram.PCFitsFrom (preExit ++ exitCode)
        dispatchCode :=
    Structured.Preservation.AssemblyProgram.PCFitsFrom.right hFitsAfterBody
  have hExactExpanded :
      Structured.Preservation.ExactLabels expandedAsm :=
    Structured.Preservation.ExactLabels.cast_asm hAsmExpanded hExact
  have hReturnLabelExpanded :
      Assembly.Program.labelPc expandedAsm site.returnLabel = some returnDest := by
    rw [← hAsmExpanded]
    exact hReturnLabel
  have hFallthrough :
      Structured.Preservation.CodeSegment.fallthroughPc bodySeg =
        Assembly.Program.pcAfter preExit := by
    simp [bodySeg, codeSegment_procSegment_bodyCode,
      Structured.Preservation.CodeSegment.fallthroughPc,
      preExit, entryCode, bodyCode, List.append_assoc]
  have hBodyRelPc :
      Structured.Preservation.CompiledOutcomeRel asm bodyCtx
        (Assembly.Program.pcAfter preExit)
        (Structured.Outcome.regular bodyState) (.running afterBody)
        (token :: tokens) := by
    simpa [hFallthrough] using hBodyRel
  have hBodyRelExpanded :
      Structured.Preservation.CompiledOutcomeRel expandedAsm bodyCtx
        (Assembly.Program.pcAfter preExit)
        (Structured.Outcome.regular bodyState) (.running afterBody)
        (token :: tokens) := by
    simpa [← hAsmExpanded] using hBodyRelPc
  exact
    openRunNResult_structured_callSite_body_continue
      (program := program) (proc := proc) (bodySupply := bodySupply)
      (dispatchSupply := dispatchSupply) (sites := sites) (site := site)
      (source := source) (target := target) (args := args)
      (callerStack := callerStack) (tokens := tokens) (token := token)
      (asm := asm)
      (fuel :=
        bodyFuel +
          (returnDispatchSelectedTableFuel proc.retc
            (sites.filter (Structured.CallSite.forProc proc.name)) site
            tailFuel + 1))
      (tailTrace := bodyTrace ++ tailTrace) (result := result)
      callSeg procSeg hSplit hArgBound hPc hRel hExact
      (by
        intro entryTarget hEntryRel hEntryPc
        have hBodyRunExpanded :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult expandedAsm bodyFuel
                entryTarget)
              bodyTrace (.ok (.running afterBody)) := by
          simpa [← hAsmExpanded] using
            hBodyRun entryTarget hEntryRel hEntryPc
        have hTail :=
          openRunNResult_body_regular_then_exit_dispatch_continue
            (proc := proc) (dispatchSupply := dispatchSupply)
            (sites := sites) (site := site) (returnDest := returnDest)
            (bodyCtx := bodyCtx) (bodyState := bodyState)
            (returned := returned) (stack := stack) (frame := frame)
            (entryTarget := entryTarget) (afterBody := afterBody)
            (tokens := tokens) (token := token) (preExit := preExit)
            (post := procSeg.post) (bodyFuel := bodyFuel)
            (tailFuel := tailFuel) (bodyTrace := bodyTrace)
            (tailTrace := tailTrace) (result := result)
            (by
              simpa [expandedAsm, exitCode] using hBodyRunExpanded)
            (by
              simpa [expandedAsm, exitCode, dispatchCode] using
                hBodyRelExpanded)
            hAttach hReturns hRetc hMem hNoDup hToken hBound
            (by simpa [exitCode] using hFitsExit)
            (by simpa [exitCode, dispatchCode] using hFitsDispatch)
            (by simpa [expandedAsm, exitCode, dispatchCode] using
              hExactExpanded)
            (by simpa [expandedAsm, exitCode, dispatchCode] using
              hReturnLabelExpanded)
            (by
              intro final hFinalRel hFinalPc
              have hTailRun := hRest final hFinalRel hFinalPc
              have hTailRunExpanded :
                  OpenExternal.OpenResultResolves
                    (OpenAssembly.Source.openRunNResult expandedAsm tailFuel
                      final)
                    tailTrace result := by
                rw [← hAsmExpanded]
                exact hTailRun
              simpa [expandedAsm, exitCode, dispatchCode, List.append_assoc]
                using hTailRunExpanded)
        have hTailExpanded :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult expandedAsm
                (bodyFuel +
                  (returnDispatchSelectedTableFuel proc.retc
                    (sites.filter (Structured.CallSite.forProc proc.name)) site
                    tailFuel + 1))
                entryTarget)
              (bodyTrace ++ tailTrace) result := by
          simpa [expandedAsm, exitCode, dispatchCode, List.append_assoc]
            using hTail
        rw [← hAsmExpanded] at hTailExpanded
        exact hTailExpanded)

theorem openRunNResult_callSite_body_leave_then_exit_dispatch_continue
    {program : Structured.Program} {proc : Structured.Proc}
    {bodySupply dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite} {site : Structured.CallSite}
    {returnDest : Nat} {bodyCtx : Structured.CompileContext}
    {source bodyState returned : Structured.RunState}
    {target afterBody : EvmYul.EVM.State}
    {args callerStack stack : EvmYul.Stack Word}
    {frame : Structured.ReturnDest}
    {tokens : List Word} {token : Word}
    {asm : Assembly.Program}
    {bodyFuel tailFuel : Nat}
    {bodyTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (callSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args token site.returnLabel))
    (procSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.procSegment program
          proc bodySupply dispatchSupply sites))
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16)
    (hPc :
      target.pc = Structured.Preservation.CodeSegment.startPc callSeg)
    (hRel :
      Structured.Preservation.Frame.StateRel source target tokens)
    (hBodyRun :
      ∀ entryTarget : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          ((source.withEVM { source.evm with stack := args }).pushReturn
            callerStack proc.retc)
          entryTarget (token :: tokens) →
        entryTarget.pc =
          Structured.Preservation.CodeSegment.startPc
            (codeSegment_procSegment_bodyCode procSeg) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm bodyFuel entryTarget)
          bodyTrace (.ok (.running afterBody)))
    (hBodyRel :
      Structured.Preservation.CompiledOutcomeRel asm bodyCtx
        (Structured.Preservation.CodeSegment.fallthroughPc
          (codeSegment_procSegment_bodyCode procSeg))
        (Structured.Outcome.leave bodyState) (.running afterBody)
        (token :: tokens))
    (hCtxLeave :
      bodyCtx.leaveLabel? = some (Structured.ProcLabel.exit proc.name))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hReturns : bodyState.returns = frame :: returned.returns)
    (hRetc : bodyState.evm.stack.length = proc.retc)
    (hMem :
      site ∈ sites.filter (Structured.CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (Structured.CallSite.forProc proc.name)).map
        Structured.CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hExact : Structured.Preservation.ExactLabels asm)
    (hReturnLabel :
      Assembly.Program.labelPc asm site.returnLabel = some returnDest)
    (hRest :
      ∀ final : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          (returned.withEVM { bodyState.evm with stack := stack })
          final tokens →
        final.pc = EvmYul.UInt256.ofNat returnDest →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm tailFuel final)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult asm
        ((Structured.Preservation.ProcedurePreservation.callJumpCode
          proc args token).length +
          ((bodyFuel +
            (returnDispatchSelectedTableFuel proc.retc
              (sites.filter (Structured.CallSite.forProc proc.name)) site
              tailFuel + 1)) + 1))
        target)
      (bodyTrace ++ tailTrace) result := by
  let bodySeg := codeSegment_procSegment_bodyCode procSeg
  let bodyCode :=
    Structured.Preservation.ProcedurePreservation.bodyCode program proc
      bodySupply
  let dispatchCode :=
    Structured.Preservation.ProcedurePreservation.dispatchCode proc sites
      dispatchSupply
  let entryCode : Assembly.Program :=
    [Assembly.Instr.label (Structured.ProcLabel.entry proc.name)]
  let exitCode : Assembly.Program :=
    [Assembly.Instr.label (Structured.ProcLabel.exit proc.name)]
  let preExit := procSeg.pre ++ entryCode ++ bodyCode
  let expandedAsm := preExit ++ exitCode ++ dispatchCode ++ procSeg.post
  have hAsmExpanded : asm = expandedAsm := by
    simpa [expandedAsm, preExit, entryCode, exitCode, bodyCode, dispatchCode,
      Structured.Preservation.ProcedurePreservation.procSegment,
      List.append_assoc] using procSeg.hAsm
  have hFitsFull :
      Structured.Preservation.AssemblyProgram.PCFitsFrom procSeg.pre
        (entryCode ++ bodyCode ++ exitCode ++ dispatchCode) := by
    simpa [entryCode, exitCode, bodyCode, dispatchCode,
      Structured.Preservation.ProcedurePreservation.procSegment,
      List.append_assoc] using procSeg.hFits
  have hFitsFull' :
      Structured.Preservation.AssemblyProgram.PCFitsFrom procSeg.pre
        ((entryCode ++ bodyCode) ++ (exitCode ++ dispatchCode)) := by
    simpa [List.append_assoc] using hFitsFull
  have hFitsAfterBody :
      Structured.Preservation.AssemblyProgram.PCFitsFrom preExit
        (exitCode ++ dispatchCode) := by
    simpa [preExit, List.append_assoc] using
      Structured.Preservation.AssemblyProgram.PCFitsFrom.right
        (pre := procSeg.pre) (first := entryCode ++ bodyCode)
        (second := exitCode ++ dispatchCode) hFitsFull'
  have hFitsExit :
      Structured.Preservation.AssemblyProgram.PCFitsFrom preExit exitCode :=
    Structured.Preservation.AssemblyProgram.PCFitsFrom.left hFitsAfterBody
  have hFitsDispatch :
      Structured.Preservation.AssemblyProgram.PCFitsFrom (preExit ++ exitCode)
        dispatchCode :=
    Structured.Preservation.AssemblyProgram.PCFitsFrom.right hFitsAfterBody
  have hExactExpanded :
      Structured.Preservation.ExactLabels expandedAsm :=
    Structured.Preservation.ExactLabels.cast_asm hAsmExpanded hExact
  have hReturnLabelExpanded :
      Assembly.Program.labelPc expandedAsm site.returnLabel = some returnDest := by
    rw [← hAsmExpanded]
    exact hReturnLabel
  have hFallthrough :
      Structured.Preservation.CodeSegment.fallthroughPc bodySeg =
        Assembly.Program.pcAfter preExit := by
    simp [bodySeg, codeSegment_procSegment_bodyCode,
      Structured.Preservation.CodeSegment.fallthroughPc,
      preExit, entryCode, bodyCode, List.append_assoc]
  have hBodyRelPc :
      Structured.Preservation.CompiledOutcomeRel asm bodyCtx
        (Assembly.Program.pcAfter preExit)
        (Structured.Outcome.leave bodyState) (.running afterBody)
        (token :: tokens) := by
    simpa [hFallthrough] using hBodyRel
  have hBodyRelExpanded :
      Structured.Preservation.CompiledOutcomeRel expandedAsm bodyCtx
        (Assembly.Program.pcAfter preExit)
        (Structured.Outcome.leave bodyState) (.running afterBody)
        (token :: tokens) := by
    simpa [← hAsmExpanded] using hBodyRelPc
  exact
    openRunNResult_structured_callSite_body_continue
      (program := program) (proc := proc) (bodySupply := bodySupply)
      (dispatchSupply := dispatchSupply) (sites := sites) (site := site)
      (source := source) (target := target) (args := args)
      (callerStack := callerStack) (tokens := tokens) (token := token)
      (asm := asm)
      (fuel :=
        bodyFuel +
          (returnDispatchSelectedTableFuel proc.retc
            (sites.filter (Structured.CallSite.forProc proc.name)) site
            tailFuel + 1))
      (tailTrace := bodyTrace ++ tailTrace) (result := result)
      callSeg procSeg hSplit hArgBound hPc hRel hExact
      (by
        intro entryTarget hEntryRel hEntryPc
        have hBodyRunExpanded :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult expandedAsm bodyFuel
                entryTarget)
              bodyTrace (.ok (.running afterBody)) := by
          simpa [← hAsmExpanded] using
            hBodyRun entryTarget hEntryRel hEntryPc
        have hTail :=
          openRunNResult_body_leave_then_exit_dispatch_continue
            (proc := proc) (dispatchSupply := dispatchSupply)
            (sites := sites) (site := site) (returnDest := returnDest)
            (bodyCtx := bodyCtx) (bodyState := bodyState)
            (returned := returned) (stack := stack) (frame := frame)
            (entryTarget := entryTarget) (afterBody := afterBody)
            (tokens := tokens) (token := token) (preExit := preExit)
            (post := procSeg.post) (bodyFuel := bodyFuel)
            (tailFuel := tailFuel) (bodyTrace := bodyTrace)
            (tailTrace := tailTrace) (result := result)
            (by
              simpa [expandedAsm, exitCode] using hBodyRunExpanded)
            (by
              simpa [expandedAsm, exitCode, dispatchCode] using
                hBodyRelExpanded)
            hCtxLeave hAttach hReturns hRetc hMem hNoDup hToken hBound
            (by simpa [exitCode] using hFitsExit)
            (by simpa [exitCode, dispatchCode] using hFitsDispatch)
            (by simpa [expandedAsm, exitCode, dispatchCode] using
              hExactExpanded)
            (by simpa [expandedAsm, exitCode, dispatchCode] using
              hReturnLabelExpanded)
            (by
              intro final hFinalRel hFinalPc
              have hTailRun := hRest final hFinalRel hFinalPc
              have hTailRunExpanded :
                  OpenExternal.OpenResultResolves
                    (OpenAssembly.Source.openRunNResult expandedAsm tailFuel
                      final)
                    tailTrace result := by
                rw [← hAsmExpanded]
                exact hTailRun
              simpa [expandedAsm, exitCode, dispatchCode, List.append_assoc]
                using hTailRunExpanded)
        have hTailExpanded :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult expandedAsm
                (bodyFuel +
                  (returnDispatchSelectedTableFuel proc.retc
                    (sites.filter (Structured.CallSite.forProc proc.name)) site
                    tailFuel + 1))
                entryTarget)
              (bodyTrace ++ tailTrace) result := by
          simpa [expandedAsm, exitCode, dispatchCode, List.append_assoc]
            using hTail
        rw [← hAsmExpanded] at hTailExpanded
        exact hTailExpanded)

theorem evmState_with_stack_eq_self
    {state : EvmYul.EVM.State} {stack : OpenExternal.Stack}
    (hStack : state.stack = stack) :
    ({ state with stack := stack } : EvmYul.EVM.State) = state := by
  cases state
  simp at hStack ⊢
  exact hStack.symm

theorem compilerPrimitiveOpenCall?_resume_vars
    {compiler : Objects.Source.State}
    {kind : OpenExternal.CallKind} {values : List Word}
    {call : OpenExternal.OpenCall (Objects.Source.State × List Word)}
    (hCall :
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some call)
    (response : OpenExternal.CallResponse) :
    (call.resume response).1.vars = compiler.vars := by
  unfold
    Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
      at hCall
  cases hPrimitive :
      OpenExternal.CallKind.primitiveSharedOpenCall?
        compiler.shared kind values with
  | none =>
      simp [hPrimitive] at hCall
  | some primitiveCall =>
      simp [hPrimitive] at hCall
      rcases hCall with rfl
      simp [Locals.Source.State.withShared]

theorem compilerOpenPrimitive_eval_resolves_callKind_ok_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    {values : List Word}
    {compilerCall :
      OpenExternal.OpenCall (Objects.Source.State × List Word)}
    {trace : OpenExternal.OpenTrace}
    {result : Objects.Source.State × List Word}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (hCall :
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some compilerCall)
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        trace (.ok result)) :
    ∃ response : OpenExternal.CallResponse,
      trace = [{ site := compilerCall.site, response := response }] ∧
        result = compilerCall.resume response := by
  have hSuspend :
      Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values =
        .call
          { site := compilerCall.site
            resume := fun response =>
              .done (.ok (compilerCall.resume response)) } :=
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_suspends_of_basicOp
      hKind hCall
  rw [hSuspend] at hResolve
  cases hResolve with
  | call hTail =>
      cases hTail
      exact ⟨_, rfl, rfl⟩

theorem compilerOpenPrimitive_call_stepAtResult
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (kind : OpenExternal.CallKind)
    (operands : OpenExternal.CallOperands)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc : Nat) :
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind (kind.args operands).reverse =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall?
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State) kind =
        some evmCall ∧
      OpenExternal.OpenCallRel
        (fun _ => True)
        (Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          baseStack) compilerCall evmCall ∧
      ∀ response : OpenExternal.CallResponse,
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim kind.toBasicOp compiler (kind.args operands).reverse)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openStepAtResult program pc
            (.prim kind.toBasicOp.toPrimOp)
            ({ evmState with stack := kind.args operands ++ baseStack }
              : EvmYul.EVM.State))
          [{ site := compilerCall.site, response := response }]
          (.ok
            (.running (EvmYul.EVM.State.incrPC
              (evmCall.resume response)))) ∧
        CompilerPrimitiveEVMInstructionResultRel baseStack
          (compilerCall.resume response)
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response))) := by
  rcases
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCallRel_evmOpenCall_of_args
        (compiler := compiler) (state := evmState) hShared kind operands
        baseStack with
    ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel⟩
  refine ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel, ?_⟩
  intro response
  have hSourceSuspend :
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval prim
          kind.toBasicOp compiler (kind.args operands).reverse =
        .call
          { site := compilerCall.site
            resume := fun response =>
              .done (.ok (compilerCall.resume response)) } :=
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_suspends_toBasicOp
      kind hCompilerCall
  have hSource :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim kind.toBasicOp compiler (kind.args operands).reverse)
        [{ site := compilerCall.site, response := response }]
        (.ok (compilerCall.resume response)) := by
    rw [hSourceSuspend]
    exact OpenExternal.OpenResultResolves.call
      OpenExternal.OpenResultResolves.done
  have hTargetRaw :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc
          (.prim kind.toBasicOp.toPrimOp)
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State))
        [{ site := evmCall.site, response := response }]
        (.ok
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response)))) :=
    OpenAssembly.Source.openStepAtResult_resolves_prim_call
      (program := program) (pc := pc) (op := kind.toBasicOp.toPrimOp)
      (state := { evmState with stack := kind.args operands ++ baseStack })
      (kind := kind) (call := evmCall)
      (callKind_ofEVMOperation_toBasicOp_toPrimOp kind) hEVMCall response
  have hTarget :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc
          (.prim kind.toBasicOp.toPrimOp)
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State))
        [{ site := compilerCall.site, response := response }]
        (.ok
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response)))) := by
    simpa [hCallRel.sameSite] using hTargetRaw
  have hResponseRel :
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack (compilerCall.resume response) (evmCall.resume response) :=
    OpenExternal.OpenCallRel.preserves_response hCallRel response trivial
  exact
    ⟨hSource, hTarget,
      CompilerPrimitiveEVMInstructionResultRel.running_incrPC hResponseRel⟩

theorem compilerOpenPrimitive_no_callCreate_stepAtResult
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc : Nat)
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.prim op.toPrimOp)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        [] (.ok (.running evmAfter)) ∧
      CompilerPrimitiveEVMInstructionResultRel baseStack
        (compiler.withShared sharedAfter, valuesAfter)
        (.running evmAfter) := by
  let state : EvmYul.EVM.State :=
    { evmState with stack := values.reverse ++ baseStack }
  have hStateShared : state.toSharedState = compiler.shared := by
    simpa [state] using hShared
  have hStateStack : state.stack = values.reverse ++ baseStack := by
    simp [state]
  rcases
      hPrim.eval_step_exists
        (op := op) (shared := compiler.shared)
        (shared' := sharedAfter) (values := values)
        (values' := valuesAfter) (evm := state)
        (baseStack := baseStack) hEval hStateShared hStateStack with
    ⟨evmAfter, hStep, hAfterShared, hAfterStack⟩
  have hSource :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) :=
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_resolves_closed_ok_of_not_callKind
      (Reference.SourceBridgeFacts.CompilerOpen.Primitive.callKind_none_of_no_callCreate
        hNoCallCreate)
      hEval
  have hTargetStep :
      Assembly.Source.stepAtResult program pc (.prim op.toPrimOp) state =
        .ok (.running evmAfter) := by
    have hTargetInstr :
        Assembly.Target.stepInstr
          (Assembly.TargetInstr.prim op.toPrimOp) state =
          .ok evmAfter := by
      simpa [Structured.BasicOp.step] using hStep
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      hTargetInstr, basicOp_toPrimOp_haltKind?_none op]
  have hTarget :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.prim op.toPrimOp)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        [] (.ok (.running evmAfter)) := by
    simpa [state] using
      OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
        (program := program) (pc := pc) (op := op.toPrimOp)
          (state := state) hNoCallCreate hTargetStep
  have hRel :
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack (compiler.withShared sharedAfter, valuesAfter) evmAfter := by
    exact
      ⟨by simpa [Locals.Source.State.withShared] using hAfterShared,
        hAfterStack⟩
  exact ⟨evmAfter, hSource, hTarget, hRel⟩

theorem compilerOpenPrimitive_no_callCreate_stepAtResult_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc : Nat)
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.prim op.toPrimOp)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        [] (.ok (.running evmAfter)) ∧
      CompilerPrimitiveEVMInstructionResultRel baseStack
        (compiler.withShared sharedAfter, valuesAfter)
        (.running evmAfter) ∧
      evmAfter.pc =
        ({ evmState with stack := values.reverse ++ baseStack }
          : EvmYul.EVM.State).pc + EvmYul.UInt256.ofNat 1 := by
  let state : EvmYul.EVM.State :=
    { evmState with stack := values.reverse ++ baseStack }
  have hStateShared : state.toSharedState = compiler.shared := by
    simpa [state] using hShared
  have hStateStack : state.stack = values.reverse ++ baseStack := by
    simp [state]
  rcases
      hPrim.eval_step_exists
        (op := op) (shared := compiler.shared)
        (shared' := sharedAfter) (values := values)
        (values' := valuesAfter) (evm := state)
        (baseStack := baseStack) hEval hStateShared hStateStack with
    ⟨evmAfter, hStep, hAfterShared, hAfterStack⟩
  have hSource :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) :=
    Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_resolves_closed_ok_of_not_callKind
      (Reference.SourceBridgeFacts.CompilerOpen.Primitive.callKind_none_of_no_callCreate
        hNoCallCreate)
      hEval
  have hTargetStep :
      Assembly.Source.stepAtResult program pc (.prim op.toPrimOp) state =
        .ok (.running evmAfter) := by
    have hTargetInstr :
        Assembly.Target.stepInstr
          (Assembly.TargetInstr.prim op.toPrimOp) state =
          .ok evmAfter := by
      simpa [Structured.BasicOp.step] using hStep
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      hTargetInstr, basicOp_toPrimOp_haltKind?_none op]
  have hTarget :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.prim op.toPrimOp)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        [] (.ok (.running evmAfter)) := by
    simpa [state] using
      OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
        (program := program) (pc := pc) (op := op.toPrimOp)
        (state := state) hNoCallCreate hTargetStep
  have hRel :
      Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
        baseStack (compiler.withShared sharedAfter, valuesAfter) evmAfter := by
    exact
      ⟨by simpa [Locals.Source.State.withShared] using hAfterShared,
        hAfterStack⟩
  have hPc :
      evmAfter.pc = state.pc + EvmYul.UInt256.ofNat 1 :=
    basicOp_no_callCreate_step_pc hNoCallCreate hStep
  exact ⟨evmAfter, hSource, hTarget, hRel, by simpa [state] using hPc⟩

theorem compilerOpenPrimitive_no_callCreate_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program
          (({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      CompilerPrimitiveEVMInstructionResultRel baseStack
        (compiler.withShared sharedAfter, valuesAfter)
        (.running evmAfter) ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1)
            ({ evmState with stack := values.reverse ++ baseStack }
              : EvmYul.EVM.State))
          tailTrace result := by
  rcases
      compilerOpenPrimitive_no_callCreate_stepAtResult
        (prim := prim) hPrim (compiler := compiler)
        (evmState := evmState) hShared op hNoCallCreate values baseStack
        program pc hEval with
    ⟨evmAfter, hSource, hTargetStep, hRel⟩
  refine ⟨evmAfter, hSource, hRel, ?_⟩
  intro tailTrace result hRest
  have hTargetRun :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program (fuel + 1)
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State))
        ([] ++ tailTrace) result :=
    OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
      (program := program) (fuel := fuel)
      (state := ({ evmState with stack := values.reverse ++ baseStack }
        : EvmYul.EVM.State))
      (mid := evmAfter) (pc := pc) (instr := .prim op.toPrimOp)
      hAt hTargetStep hRest
  simpa using hTargetRun

theorem compilerOpenPrimitive_call_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    (kind : OpenExternal.CallKind)
    (operands : OpenExternal.CallOperands)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program
          (({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim kind.toBasicOp.toPrimOp)) :
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind (kind.args operands).reverse =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall?
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State) kind =
        some evmCall ∧
      OpenExternal.OpenCallRel
        (fun _ => True)
        (Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          baseStack) compilerCall evmCall ∧
      ∀ (response : OpenExternal.CallResponse)
        {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel
            (EvmYul.EVM.State.incrPC (evmCall.resume response)))
          tailTrace result →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim kind.toBasicOp compiler (kind.args operands).reverse)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1)
            ({ evmState with stack := kind.args operands ++ baseStack }
              : EvmYul.EVM.State))
          ({ site := compilerCall.site, response := response } :: tailTrace)
          result ∧
        CompilerPrimitiveEVMInstructionResultRel baseStack
          (compilerCall.resume response)
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response))) := by
  rcases
      compilerOpenPrimitive_call_stepAtResult
        (prim := prim) (compiler := compiler) (evmState := evmState)
        hShared kind operands baseStack program pc with
    ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel, hStep⟩
  refine ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel, ?_⟩
  intro response tailTrace result hRest
  rcases hStep response with ⟨hSource, _hStepTarget, hResultRel⟩
  have hTargetRaw :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program (fuel + 1)
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State))
        ({ site := evmCall.site, response := response } :: tailTrace)
        result :=
    OpenAssembly.Source.openRunNResult_current_prim_call_continue
      (program := program)
      (state := ({ evmState with stack := kind.args operands ++ baseStack }
        : EvmYul.EVM.State))
      (fuel := fuel) (pc := pc) (op := kind.toBasicOp.toPrimOp)
      (kind := kind) (call := evmCall)
      hAt (callKind_ofEVMOperation_toBasicOp_toPrimOp kind) hEVMCall
      response hRest
  have hTarget :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program (fuel + 1)
          ({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State))
        ({ site := compilerCall.site, response := response } :: tailTrace)
        result := by
    simpa [hCallRel.sameSite] using hTargetRaw
  exact ⟨hSource, hTarget, hResultRel⟩

theorem compilerOpenPrimitive_callKind_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {evmState : EvmYul.EVM.State}
    (hShared : evmState.toSharedState = compiler.shared)
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (baseStack : OpenExternal.Stack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program
          (({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim op.toPrimOp)) :
    ∃ operands : OpenExternal.CallOperands,
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      values = (kind.args operands).reverse ∧
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall?
          ({ evmState with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State) kind =
        some evmCall ∧
      OpenExternal.OpenCallRel
        (fun _ => True)
        (Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          baseStack) compilerCall evmCall ∧
      ∀ (response : OpenExternal.CallResponse)
        {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel
            (EvmYul.EVM.State.incrPC (evmCall.resume response)))
          tailTrace result →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim op compiler values)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1)
            ({ evmState with stack := values.reverse ++ baseStack }
              : EvmYul.EVM.State))
          ({ site := compilerCall.site, response := response } :: tailTrace)
          result ∧
        CompilerPrimitiveEVMInstructionResultRel baseStack
          (compilerCall.resume response)
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response))) := by
  have hOp : op = kind.toBasicOp :=
    basicOp_eq_toBasicOp_of_callKind hKind
  subst op
  have hLen : values.length = kind.inputArity := by
    simpa using hValuesLen
  rcases
      OpenExternal.CallKind.exists_operands_of_reverse_args_length
        kind hLen with
    ⟨operands, hValues⟩
  subst values
  have hAtCall :
      Assembly.Program.instrAtPc program
          (({ evmState with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim kind.toBasicOp.toPrimOp) := by
    simpa [List.reverse_reverse] using hAt
  rcases
      compilerOpenPrimitive_call_openRunNResult_continue
        (prim := prim) (compiler := compiler) (evmState := evmState)
        hShared kind operands baseStack program pc fuel hAtCall with
    ⟨compilerCall, evmCall, hCompilerCall, hEVMCall, hCallRel, hCont⟩
  refine
    ⟨operands, compilerCall, evmCall, rfl, ?_, ?_, hCallRel, ?_⟩
  · simpa using hCompilerCall
  · simpa [List.reverse_reverse] using hEVMCall
  · intro response tailTrace result hRest
    rcases hCont response hRest with
      ⟨hSource, hTarget, hResultRel⟩
    exact
      ⟨hSource, by simpa [List.reverse_reverse] using hTarget,
        hResultRel⟩

theorem compilerOpenPrimitive_no_callCreate_state_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (hShared : state.toSharedState = compiler.shared)
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (baseStack : OpenExternal.Stack)
    (hStack : state.stack = values.reverse ++ baseStack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      CompilerPrimitiveEVMInstructionResultRel baseStack
        (compiler.withShared sharedAfter, valuesAfter)
        (.running evmAfter) ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          tailTrace result := by
  have hStateEq :
      ({ state with stack := values.reverse ++ baseStack }
        : EvmYul.EVM.State) = state :=
    evmState_with_stack_eq_self hStack
  have hAt' :
      Assembly.Program.instrAtPc program
          (({ state with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim op.toPrimOp) := by
    simpa [hStateEq] using hAt
  rcases
      compilerOpenPrimitive_no_callCreate_openRunNResult_continue
        (prim := prim) hPrim (compiler := compiler)
        (evmState := state) hShared op hNoCallCreate values baseStack
        program pc fuel hAt' hEval with
    ⟨evmAfter, hSource, hRel, hCont⟩
  refine ⟨evmAfter, hSource, hRel, ?_⟩
  intro tailTrace result hRest
  simpa [hStateEq] using hCont hRest

theorem compilerOpenPrimitive_callKind_state_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (hShared : state.toSharedState = compiler.shared)
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (baseStack : OpenExternal.Stack)
    (hStack : state.stack = values.reverse ++ baseStack)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp)) :
    ∃ operands : OpenExternal.CallOperands,
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      values = (kind.args operands).reverse ∧
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall? state kind =
        some evmCall ∧
      OpenExternal.OpenCallRel
        (fun _ => True)
        (Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          baseStack) compilerCall evmCall ∧
      ∀ (response : OpenExternal.CallResponse)
        {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel
            (EvmYul.EVM.State.incrPC (evmCall.resume response)))
          tailTrace result →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim op compiler values)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          ({ site := compilerCall.site, response := response } :: tailTrace)
          result ∧
        CompilerPrimitiveEVMInstructionResultRel baseStack
          (compilerCall.resume response)
          (.running (EvmYul.EVM.State.incrPC
            (evmCall.resume response))) := by
  have hStateEq :
      ({ state with stack := values.reverse ++ baseStack }
        : EvmYul.EVM.State) = state :=
    evmState_with_stack_eq_self hStack
  have hAt' :
      Assembly.Program.instrAtPc program
          (({ state with stack := values.reverse ++ baseStack }
            : EvmYul.EVM.State).pc.toNat) =
        some (pc, Assembly.Instr.prim op.toPrimOp) := by
    simpa [hStateEq] using hAt
  rcases
      compilerOpenPrimitive_callKind_openRunNResult_continue
        (prim := prim) (compiler := compiler) (evmState := state)
        hShared hKind values hValuesLen baseStack program pc fuel hAt' with
    ⟨operands, compilerCall, evmCall, hValues, hCompilerCall,
      hEVMCall, hCallRel, hCont⟩
  refine
    ⟨operands, compilerCall, evmCall, hValues, hCompilerCall, ?_,
      hCallRel, ?_⟩
  · simpa [hStateEq] using hEVMCall
  · intro response tailTrace result hRest
    rcases hCont response hRest with
      ⟨hSource, hTarget, hResultRel⟩
    exact ⟨hSource, by simpa [hStateEq] using hTarget, hResultRel⟩

theorem compilerOpenPrimitive_no_callCreate_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      Locals.SourceLowering.StackPrefixRel layout
        (compiler.withShared sharedAfter) (valuesAfter.reverse ++ stackPrefix)
        evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          tailTrace result := by
  rcases hPrefixRel with
    ⟨hShared, storeBase, hStack, hStoreRel⟩
  have hStackState : state.stack = values.reverse ++
      (stackPrefix ++ storeBase) := by
    rw [hStack]
    simp [List.append_assoc]
  rcases
      compilerOpenPrimitive_no_callCreate_state_openRunNResult_continue
        (prim := prim) hPrim (compiler := compiler) (state := state)
        hShared op hNoCallCreate values (stackPrefix ++ storeBase)
        hStackState program pc fuel hAt hEval with
    ⟨evmAfter, hSource, hResultRel, hCont⟩
  have hAfterPrefix :
      Locals.SourceLowering.StackPrefixRel layout
        (compiler.withShared sharedAfter) (valuesAfter.reverse ++ stackPrefix)
        evmAfter := by
    rcases hResultRel with ⟨hAfterShared, hAfterStack⟩
    refine ⟨?_, storeBase, ?_, ?_⟩
    · simpa [Locals.Source.State.withShared] using hAfterShared
    · rw [hAfterStack]
      simp [List.append_assoc]
    · simpa [Locals.Source.State.withShared] using hStoreRel
  exact ⟨evmAfter, hSource, hAfterPrefix, hCont⟩

theorem compilerOpenPrimitive_no_callCreate_stackPrefix_openRunNResult_continue_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (op : Structured.BasicOp)
    (hNoCallCreate : op.toPrimOp.isCallCreate = false)
    (values : List Word)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {sharedAfter : EvmYul.SharedState .EVM}
    {valuesAfter : List Word}
    (hEval :
      prim.eval op compiler.shared values = .ok (sharedAfter, valuesAfter)) :
    ∃ evmAfter : EvmYul.EVM.State,
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        [] (.ok (compiler.withShared sharedAfter, valuesAfter)) ∧
      Locals.SourceLowering.StackPrefixRel layout
        (compiler.withShared sharedAfter) (valuesAfter.reverse ++ stackPrefix)
        evmAfter ∧
      evmAfter.pc = state.pc + EvmYul.UInt256.ofNat 1 ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          tailTrace result := by
  rcases hPrefixRel with
    ⟨hShared, storeBase, hStack, hStoreRel⟩
  have hStackState : state.stack = values.reverse ++
      (stackPrefix ++ storeBase) := by
    rw [hStack]
    simp [List.append_assoc]
  have hStateEq :
      ({ state with stack := values.reverse ++ (stackPrefix ++ storeBase) }
        : EvmYul.EVM.State) = state :=
    evmState_with_stack_eq_self hStackState
  rcases
      compilerOpenPrimitive_no_callCreate_stepAtResult_pc
        (prim := prim) hPrim (compiler := compiler) (evmState := state)
        hShared op hNoCallCreate values (stackPrefix ++ storeBase)
        program pc hEval with
    ⟨evmAfter, hSource, hTargetStep, hResultRel, hPc⟩
  have hAfterPrefix :
      Locals.SourceLowering.StackPrefixRel layout
        (compiler.withShared sharedAfter) (valuesAfter.reverse ++ stackPrefix)
        evmAfter := by
    rcases hResultRel with ⟨hAfterShared, hAfterStack⟩
    refine ⟨?_, storeBase, ?_, ?_⟩
    · simpa [Locals.Source.State.withShared] using hAfterShared
    · rw [hAfterStack]
      simp [List.append_assoc]
    · simpa [Locals.Source.State.withShared] using hStoreRel
  refine ⟨evmAfter, hSource, hAfterPrefix, ?_, ?_⟩
  · simpa [hStateEq] using hPc
  · intro tailTrace result hRest
    have hTargetStepState :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openStepAtResult program pc
            (.prim op.toPrimOp) state)
          [] (.ok (.running evmAfter)) := by
      simpa [hStateEq] using hTargetStep
    simpa using
      OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
        (program := program) (fuel := fuel) (state := state)
        (mid := evmAfter) (pc := pc) (instr := .prim op.toPrimOp)
        hAt hTargetStepState hRest

theorem compilerOpenPrimitive_callKind_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp} {kind : OpenExternal.CallKind}
    (hKind : OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp)) :
    ∃ operands : OpenExternal.CallOperands,
    ∃ compilerCall :
        OpenExternal.OpenCall (Objects.Source.State × List Word),
    ∃ evmCall : OpenExternal.OpenCall EvmYul.EVM.State,
      values = (kind.args operands).reverse ∧
      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
          compiler kind values =
        some compilerCall ∧
      OpenExternal.CallKind.evmOpenCall? state kind =
        some evmCall ∧
      (∀ response : OpenExternal.CallResponse,
        Locals.SourceLowering.StackPrefixRel layout
          (compilerCall.resume response).1
          ((compilerCall.resume response).2.reverse ++ stackPrefix)
          (EvmYul.EVM.State.incrPC (evmCall.resume response))) ∧
      ∀ (response : OpenExternal.CallResponse)
        {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel
            (EvmYul.EVM.State.incrPC (evmCall.resume response)))
          tailTrace result →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
            prim op compiler values)
          [{ site := compilerCall.site, response := response }]
          (.ok (compilerCall.resume response)) ∧
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          ({ site := compilerCall.site, response := response } :: tailTrace)
          result := by
  rcases hPrefixRel with
    ⟨hShared, storeBase, hStack, hStoreRel⟩
  have hStackState : state.stack = values.reverse ++
      (stackPrefix ++ storeBase) := by
    rw [hStack]
    simp [List.append_assoc]
  rcases
      compilerOpenPrimitive_callKind_state_openRunNResult_continue
        (prim := prim) (compiler := compiler) (state := state)
        hShared hKind values hValuesLen (stackPrefix ++ storeBase)
        hStackState program pc fuel hAt with
    ⟨operands, compilerCall, evmCall, hValues, hCompilerCall,
      hEVMCall, hCallRel, hCont⟩
  have hResponsePrefix :
      ∀ response : OpenExternal.CallResponse,
        Locals.SourceLowering.StackPrefixRel layout
          (compilerCall.resume response).1
          ((compilerCall.resume response).2.reverse ++ stackPrefix)
          (EvmYul.EVM.State.incrPC (evmCall.resume response)) := by
    intro response
    have hResponseRel :
        Reference.SourceBridgeFacts.SourceStateRel.CompilerPrimitiveEVMResultRel
          (stackPrefix ++ storeBase) (compilerCall.resume response)
          (evmCall.resume response) :=
      OpenExternal.OpenCallRel.preserves_response hCallRel response trivial
    rcases hResponseRel with ⟨hResponseShared, hResponseStack⟩
    have hVars :
        (compilerCall.resume response).1.vars = compiler.vars :=
      compilerPrimitiveOpenCall?_resume_vars hCompilerCall response
    refine ⟨?_, storeBase, ?_, ?_⟩
    · simpa [EvmYul.EVM.State.incrPC] using hResponseShared
    · simpa [EvmYul.EVM.State.incrPC, List.append_assoc] using
        hResponseStack
    · simpa [hVars] using hStoreRel
  refine
    ⟨operands, compilerCall, evmCall, hValues, hCompilerCall, hEVMCall,
      hResponsePrefix, ?_⟩
  intro response tailTrace result hRest
  rcases hCont response hRest with
    ⟨hSource, hTarget, _hResultRel⟩
  exact ⟨hSource, hTarget⟩

theorem compilerOpenPrimitive_stackPrefix_openRunNResult_continue_of_resolves_ok
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (op : Structured.BasicOp)
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  cases hKind : OpenExternal.CallKind.ofBasicOp? op with
  | none =>
      have hNoCallCreate :
          op.toPrimOp.isCallCreate = false := by
        rcases hSupported with hNoCallCreate | ⟨kind, hSome⟩
        · exact hNoCallCreate
        · rw [hKind] at hSome
          cases hSome
      rw [Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_of_not_callKind
        hKind] at hResolve
      cases hEval : prim.eval op compiler.shared values with
      | error err =>
          simp [hEval] at hResolve
          cases hResolve
      | ok primResult =>
          rcases primResult with ⟨sharedAfter, valuesAfter'⟩
          simp [hEval] at hResolve
          cases hResolve
          rcases
              compilerOpenPrimitive_no_callCreate_stackPrefix_openRunNResult_continue
                (prim := prim) hPrim (layout := layout)
                (compiler := compiler) (state := state)
                op hNoCallCreate values stackPrefix hPrefixRel
                program pc fuel hAt hEval with
            ⟨evmAfter, _hSource, hAfterPrefix, hCont⟩
          refine ⟨evmAfter, hAfterPrefix, ?_⟩
          intro tailTrace result hRest
          simpa using hCont hRest
  | some kind =>
      rcases
          compilerOpenPrimitive_callKind_stackPrefix_openRunNResult_continue
            (prim := prim) (layout := layout) (compiler := compiler)
            (state := state) hKind values hValuesLen stackPrefix
            hPrefixRel program pc fuel hAt with
        ⟨operands, compilerCall, evmCall, hValues, hCompilerCall,
          _hEVMCall, hResponsePrefix, hCont⟩
      rcases
          compilerOpenPrimitive_eval_resolves_callKind_ok_inv
            (prim := prim) (compiler := compiler) hKind hCompilerCall
            hResolve with
        ⟨response, hTrace, hResult⟩
      have hCompilerAfter :
          compilerAfter = (compilerCall.resume response).1 := by
        simpa using congrArg Prod.fst hResult
      have hValuesAfter :
          valuesAfter = (compilerCall.resume response).2 := by
        simpa using congrArg Prod.snd hResult
      refine
        ⟨EvmYul.EVM.State.incrPC (evmCall.resume response),
          ?_, ?_⟩
      · simpa [hCompilerAfter, hValuesAfter] using
          hResponsePrefix response
      intro tailTrace result hRest
      rcases hCont response hRest with
        ⟨_hSource, hTarget⟩
      simpa [hTrace] using hTarget

theorem compilerOpenPrimitive_stackPrefix_openRunNResult_continue_pc_of_resolves_ok
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (op : Structured.BasicOp)
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (values : List Word)
    (hValuesLen :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (stackPrefix : List Word)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler
        (values.reverse ++ stackPrefix) state)
    (program : Assembly.Program) (pc fuel : Nat)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc = state.pc + EvmYul.UInt256.ofNat 1 ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  cases hKind : OpenExternal.CallKind.ofBasicOp? op with
  | none =>
      have hNoCallCreate :
          op.toPrimOp.isCallCreate = false := by
        rcases hSupported with hNoCallCreate | ⟨kind, hSome⟩
        · exact hNoCallCreate
        · rw [hKind] at hSome
          cases hSome
      rw [Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval_of_not_callKind
        hKind] at hResolve
      cases hEval : prim.eval op compiler.shared values with
      | error err =>
          simp [hEval] at hResolve
          cases hResolve
      | ok primResult =>
          rcases primResult with ⟨sharedAfter, valuesAfter'⟩
          simp [hEval] at hResolve
          cases hResolve
          rcases
              compilerOpenPrimitive_no_callCreate_stackPrefix_openRunNResult_continue_pc
                (prim := prim) hPrim (layout := layout)
                (compiler := compiler) (state := state)
                op hNoCallCreate values stackPrefix hPrefixRel
                program pc fuel hAt hEval with
            ⟨evmAfter, _hSource, hAfterPrefix, hAfterPc, hCont⟩
          refine ⟨evmAfter, hAfterPrefix, hAfterPc, ?_⟩
          intro tailTrace result hRest
          simpa using hCont hRest
  | some kind =>
      rcases
          compilerOpenPrimitive_callKind_stackPrefix_openRunNResult_continue
            (prim := prim) (layout := layout) (compiler := compiler)
            (state := state) hKind values hValuesLen stackPrefix
            hPrefixRel program pc fuel hAt with
        ⟨operands, compilerCall, evmCall, hValues, hCompilerCall,
          hEVMCall, hResponsePrefix, hCont⟩
      rcases
          compilerOpenPrimitive_eval_resolves_callKind_ok_inv
            (prim := prim) (compiler := compiler) hKind hCompilerCall
            hResolve with
        ⟨response, hTrace, hResult⟩
      have hCompilerAfter :
          compilerAfter = (compilerCall.resume response).1 := by
        simpa using congrArg Prod.fst hResult
      have hValuesAfter :
          valuesAfter = (compilerCall.resume response).2 := by
        simpa using congrArg Prod.snd hResult
      have hAfterPc :
          (EvmYul.EVM.State.incrPC (evmCall.resume response)).pc =
            state.pc + EvmYul.UInt256.ofNat 1 := by
        simp [EvmYul.EVM.State.incrPC,
          evmOpenCall?_resume_pc hEVMCall response]
      refine
        ⟨EvmYul.EVM.State.incrPC (evmCall.resume response),
          ?_, hAfterPc, ?_⟩
      · simpa [hCompilerAfter, hValuesAfter] using
          hResponsePrefix response
      intro tailTrace result hRest
      rcases hCont response hRest with
        ⟨_hSource, hTarget⟩
      simpa [hTrace] using hTarget

theorem compilerOpenPrimitive_eval_resolves_ok_length
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {compiler compilerAfter : Objects.Source.State}
    {op : Structured.BasicOp} {values valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval
          prim op compiler values)
        trace (.ok (compilerAfter, valuesAfter))) :
    valuesAfter.length = Expressions.Structured.BasicOp.outputs op := by
  unfold Reference.SourceBridgeFacts.CompilerOpen.Primitive.eval at hResolve
  cases hOpen :
      Reference.SourceBridgeFacts.CompilerOpen.Primitive.openCall?
        compiler op values with
  | none =>
      simp [hOpen] at hResolve
      cases hEval : prim.eval op compiler.shared values with
      | error err =>
          simp [hEval] at hResolve
          cases hResolve
      | ok primResult =>
          rcases primResult with ⟨sharedAfter, valuesAfter'⟩
          simp [hEval] at hResolve
          cases hResolve
          exact hPrim.eval_length hEval
  | some call =>
      simp [hOpen] at hResolve
      cases hResolve with
      | @call call' response _trace _result hTail =>
          cases hCallResult : call.resume response with
          | error err =>
              simp [hCallResult] at hTail
              cases hTail
          | ok resultPair =>
              rcases resultPair with ⟨compilerAfter', valuesAfter'⟩
              simp [hCallResult] at hTail
              cases hTail
              unfold
                Reference.SourceBridgeFacts.CompilerOpen.Primitive.openCall?
                at hOpen
              cases hKind : OpenExternal.CallKind.ofBasicOp? op with
              | none =>
                  simp [hKind] at hOpen
              | some kind =>
                  cases hCompilerCall :
                      Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
                        compiler kind values with
                  | none =>
                      simp [hKind, hCompilerCall] at hOpen
                  | some compilerCall =>
                      simp [hKind, hCompilerCall] at hOpen
                      rcases hOpen with rfl
                      have hOp : op = kind.toBasicOp :=
                        basicOp_eq_toBasicOp_of_callKind hKind
                      cases hOp
                      have hPairEq :
                          compilerCall.resume response =
                            (compilerAfter, valuesAfter) :=
                        Except.ok.inj hCallResult
                      have hResumeLen :
                          (compilerCall.resume response).2.length = 1 := by
                        unfold
                          Reference.SourceBridgeFacts.SourceStateRel.compilerPrimitiveOpenCall?
                          at hCompilerCall
                        cases hPrimitiveCall :
                            OpenExternal.CallKind.primitiveSharedOpenCall?
                              compiler.shared kind values with
                        | none =>
                            simp [hPrimitiveCall] at hCompilerCall
                        | some primitiveCall =>
                            simp [hPrimitiveCall] at hCompilerCall
                            rcases hCompilerCall with rfl
                            unfold
                              OpenExternal.CallKind.primitiveSharedOpenCall?
                              at hPrimitiveCall
                            cases hSite :
                                OpenExternal.CallKind.primitiveCallSite?
                                  compiler.shared kind values with
                            | none =>
                                simp [hSite] at hPrimitiveCall
                            | some site =>
                                simp [hSite] at hPrimitiveCall
                                rcases hPrimitiveCall with rfl
                                simp
                      simpa [hPairEq,
                        OpenExternal.CallKind.outputs_toBasicOp] using
                        hResumeLen

mutual
  theorem compilerOpenLocalsExpr_eval_resolves_ok_length_of_sourceOwned
      {prim : Objects.Source.PrimitiveSemantics}
      (hPrim : Locals.SourceLowering.PrimitiveSound prim) :
      ∀ {results : Nat} {expr : Locals.Expr results}
        {compiler compilerAfter : Objects.Source.State}
        {valuesAfter : List Word} {trace : OpenExternal.OpenTrace},
        Locals.Source.Expr.SourceOwned expr →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
            prim expr compiler)
          trace (.ok (compilerAfter, valuesAfter)) →
        valuesAfter.length = results := by
    intro results expr compiler compilerAfter valuesAfter trace hOwned hResolve
    cases expr with
    | lit value =>
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
        cases hResolve
        simp
    | var name =>
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
        cases hLookup : compiler.vars name with
        | none =>
            simp [hLookup, Reference.SourceBridgeFacts.CompilerOpen.invalid]
              at hResolve
            cases hResolve
        | some value =>
            simp [hLookup] at hResolve
            cases hResolve
            simp
    | code code =>
        simp [Locals.Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
        simp [Locals.Source.Expr.SourceOwned] at hOwned
        rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
          hArgsError | hArgsOk
        · rcases hArgsError with ⟨err, _hArgs, hResult⟩
          cases hResult
        · rcases hArgsOk with
            ⟨argsTrace, primTrace, argResult, _hTrace, _hResolveArgs,
              hResolvePrim⟩
          rcases argResult with ⟨compilerAfterArgs, argValues⟩
          exact
            compilerOpenPrimitive_eval_resolves_ok_length
              (prim := prim) hPrim hResolvePrim

  theorem compilerOpenLocalsExprSeq_eval_resolves_ok_length_of_sourceOwned
      {prim : Objects.Source.PrimitiveSemantics}
      (hPrim : Locals.SourceLowering.PrimitiveSound prim) :
      ∀ {results : Nat} {exprs : Locals.ExprSeq results}
        {compiler compilerAfter : Objects.Source.State}
        {valuesAfter : List Word} {trace : OpenExternal.OpenTrace},
        Locals.Source.ExprSeq.SourceOwned exprs →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim exprs compiler)
          trace (.ok (compilerAfter, valuesAfter)) →
        valuesAfter.length = results := by
    intro results exprs compiler compilerAfter valuesAfter trace hOwned hResolve
    cases exprs with
    | nil =>
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
        cases hResolve
        simp
    | @cons left right head tail =>
        simp [Locals.Source.ExprSeq.SourceOwned] at hOwned
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
        rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
          hHeadError | hHeadOk
        · rcases hHeadError with ⟨err, _hHead, hResult⟩
          cases hResult
        · rcases hHeadOk with
            ⟨headTrace, tailAndDoneTrace, headResult, _hTrace,
              hResolveHead, hResolveTailBind⟩
          rcases headResult with ⟨compilerAfterHead, headValues⟩
          rcases OpenExternal.OpenResultResolves.bind_inv hResolveTailBind with
            hTailError | hTailOk
          · rcases hTailError with ⟨err, _hTail, hResult⟩
            cases hResult
          · rcases hTailOk with
              ⟨tailTrace, doneTrace, tailResult, _hTailAndDoneTrace,
                hResolveTail, hResolveDone⟩
            rcases tailResult with ⟨compilerAfterTail, tailValues⟩
            cases hResolveDone
            have hHeadLen :
                headValues.length = left :=
              compilerOpenLocalsExpr_eval_resolves_ok_length_of_sourceOwned
                hPrim hHeadOwned hResolveHead
            have hTailLen :
                tailValues.length = right :=
              compilerOpenLocalsExprSeq_eval_resolves_ok_length_of_sourceOwned
                hPrim hTailOwned hResolveTail
            simp [hHeadLen, hTailLen]
end

theorem compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_of_args
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (primitiveTailFuel expressionFuel : Nat)
    (hArgsLength :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        argValues.length = Expressions.Structured.BasicOp.inputs op)
    (hArgsSound :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        ∃ evmAfterArgs : EvmYul.EVM.State,
        ∃ pc : Nat,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterArgs
            (argValues.reverse ++ stackPrefix) evmAfterArgs ∧
          Assembly.Program.instrAtPc program evmAfterArgs.pc.toNat =
            some (pc, Assembly.Instr.prim op.toPrimOp) ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program
                (primitiveTailFuel + 1) evmAfterArgs)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program expressionFuel state)
              (argsTrace ++ tailTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.prim op args) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program primitiveTailFuel
            evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program expressionFuel state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hArgsError | hArgsOk
  · rcases hArgsError with ⟨err, _hArgs, hResult⟩
    cases hResult
  · rcases hArgsOk with
      ⟨argsTrace, primTrace, argResult, hTrace, hResolveArgs,
        hResolvePrim⟩
    rcases argResult with ⟨compilerAfterArgs, argValues⟩
    rcases hArgsSound hResolveArgs with
      ⟨evmAfterArgs, pc, hArgsPrefix, hAt, hArgsCont⟩
    have hArgValuesLen :
        argValues.length = Expressions.Structured.BasicOp.inputs op :=
      hArgsLength hResolveArgs
    rcases
        compilerOpenPrimitive_stackPrefix_openRunNResult_continue_of_resolves_ok
          (prim := prim) hPrim (layout := layout)
          (compiler := compilerAfterArgs) (compilerAfter := compilerAfter)
          (state := evmAfterArgs) op hSupported argValues hArgValuesLen
          stackPrefix hArgsPrefix program pc primitiveTailFuel hAt
          hResolvePrim with
      ⟨evmAfter, hAfterPrefix, hPrimCont⟩
    refine ⟨evmAfter, hAfterPrefix, ?_⟩
    intro tailTrace result hRest
    have hPrimitiveAndTail :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (primitiveTailFuel + 1) evmAfterArgs)
          (primTrace ++ tailTrace) result :=
      hPrimCont hRest
    have hFull := hArgsCont hPrimitiveAndTail
    subst trace
    simpa [List.append_assoc] using hFull

theorem compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_fallthrough_of_args
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (primitiveTailFuel expressionFuel : Nat)
    (finalFallthroughPc : Word)
    (hArgsLength :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        argValues.length = Expressions.Structured.BasicOp.inputs op)
    (hArgsSound :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        ∃ evmAfterArgs : EvmYul.EVM.State,
        ∃ pc : Nat,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterArgs
            (argValues.reverse ++ stackPrefix) evmAfterArgs ∧
          Assembly.Program.instrAtPc program evmAfterArgs.pc.toNat =
            some (pc, Assembly.Instr.prim op.toPrimOp) ∧
          evmAfterArgs.pc + EvmYul.UInt256.ofNat 1 =
            finalFallthroughPc ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program
                (primitiveTailFuel + 1) evmAfterArgs)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program expressionFuel state)
              (argsTrace ++ tailTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.prim op args) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc = finalFallthroughPc ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program primitiveTailFuel
            evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program expressionFuel state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hArgsError | hArgsOk
  · rcases hArgsError with ⟨err, _hArgs, hResult⟩
    cases hResult
  · rcases hArgsOk with
      ⟨argsTrace, primTrace, argResult, hTrace, hResolveArgs,
        hResolvePrim⟩
    rcases argResult with ⟨compilerAfterArgs, argValues⟩
    rcases hArgsSound hResolveArgs with
      ⟨evmAfterArgs, pc, hArgsPrefix, hAt, hArgsFallthrough,
        hArgsCont⟩
    have hArgValuesLen :
        argValues.length = Expressions.Structured.BasicOp.inputs op :=
      hArgsLength hResolveArgs
    rcases
        compilerOpenPrimitive_stackPrefix_openRunNResult_continue_pc_of_resolves_ok
          (prim := prim) hPrim (layout := layout)
          (compiler := compilerAfterArgs) (compilerAfter := compilerAfter)
          (state := evmAfterArgs) op hSupported argValues hArgValuesLen
          stackPrefix hArgsPrefix program pc primitiveTailFuel hAt
          hResolvePrim with
      ⟨evmAfter, hAfterPrefix, hAfterPc, hPrimCont⟩
    refine ⟨evmAfter, hAfterPrefix, ?_, ?_⟩
    · exact hAfterPc.trans hArgsFallthrough
    · intro tailTrace result hRest
      have hPrimitiveAndTail :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program
              (primitiveTailFuel + 1) evmAfterArgs)
            (primTrace ++ tailTrace) result :=
        hPrimCont hRest
      have hFull := hArgsCont hPrimitiveAndTail
      subst trace
      simpa [List.append_assoc] using hFull

theorem compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_of_sourceOwned_args
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    (hArgsOwned : Locals.Source.ExprSeq.SourceOwned args)
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (primitiveTailFuel expressionFuel : Nat)
    (hArgsSound :
      ∀ {argsTrace : OpenExternal.OpenTrace}
        {compilerAfterArgs : Objects.Source.State} {argValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim args compiler)
          argsTrace (.ok (compilerAfterArgs, argValues)) →
        ∃ evmAfterArgs : EvmYul.EVM.State,
        ∃ pc : Nat,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterArgs
            (argValues.reverse ++ stackPrefix) evmAfterArgs ∧
          Assembly.Program.instrAtPc program evmAfterArgs.pc.toNat =
            some (pc, Assembly.Instr.prim op.toPrimOp) ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program
                (primitiveTailFuel + 1) evmAfterArgs)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program expressionFuel state)
              (argsTrace ++ tailTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.prim op args) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program primitiveTailFuel
            evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program expressionFuel state)
          (trace ++ tailTrace) result :=
  compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_of_args
    (prim := prim) hPrim (layout := layout) (compiler := compiler)
    (compilerAfter := compilerAfter) (state := state) (op := op)
    (args := args) hSupported stackPrefix program primitiveTailFuel
    expressionFuel
    (fun hResolveArgs =>
      compilerOpenLocalsExprSeq_eval_resolves_ok_length_of_sourceOwned
        hPrim hArgsOwned hResolveArgs)
    hArgsSound hResolve

theorem compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode_args
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.prim op args) = some code)
    (hArgsOwned : Locals.Source.ExprSeq.SourceOwned args)
    (hSupported :
      op.toPrimOp.isCallCreate = false ∨
        ∃ kind : OpenExternal.CallKind,
          OpenExternal.CallKind.ofBasicOp? op = some kind)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (primitiveTailFuel expressionFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hArgsSound :
      ∀ {argsCode : Structured.Code},
        Locals.ExprSeq.compileCode ctx offset args = some argsCode →
        (argsSegment :
          Structured.Preservation.CodeSegment program argsCode.toAssembly) →
        state.pc =
          Structured.Preservation.CodeSegment.startPc argsSegment →
        ∀ {argsTrace : OpenExternal.OpenTrace}
          {compilerAfterArgs : Objects.Source.State}
          {argValues : List Word},
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
              prim args compiler)
            argsTrace (.ok (compilerAfterArgs, argValues)) →
          ∃ evmAfterArgs : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfterArgs
              (argValues.reverse ++ stackPrefix) evmAfterArgs ∧
            evmAfterArgs.pc =
              Structured.Preservation.CodeSegment.fallthroughPc
                argsSegment ∧
            ∀ {tailTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program
                  (primitiveTailFuel + 1) evmAfterArgs)
                tailTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program expressionFuel
                  state)
                (argsTrace ++ tailTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.prim op args) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program primitiveTailFuel
            evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program expressionFuel state)
          (trace ++ tailTrace) result := by
  rcases localsExpr_compileCode_prim_inv hCompile with
    ⟨argsCode, hArgsCompile, hCode⟩
  have hAssemblyCode :
      code.toAssembly =
        argsCode.toAssembly ++ [Assembly.Instr.prim op.toPrimOp] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let appendSegment :
      Structured.Preservation.CodeSegment program
        (argsCode.toAssembly ++ [Assembly.Instr.prim op.toPrimOp]) :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  let argsSegment :
      Structured.Preservation.CodeSegment program argsCode.toAssembly :=
    Structured.Preservation.CodeSegment.left appendSegment
  let primSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim op.toPrimOp] :=
    Structured.Preservation.CodeSegment.right appendSegment
  have hArgsPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc argsSegment := by
    simpa [argsSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hPrimStart :
      Structured.Preservation.CodeSegment.startPc primSegment =
        Structured.Preservation.CodeSegment.fallthroughPc argsSegment :=
    codeSegment_right_startPc_eq_left_fallthroughPc appendSegment
  have hPrimFallSegment :
      Structured.Preservation.CodeSegment.fallthroughPc primSegment =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    simp [primSegment, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc,
      hAssemblyCode, List.append_assoc]
  have hPrimFall :
      Structured.Preservation.CodeSegment.fallthroughPc primSegment =
        Structured.Preservation.CodeSegment.startPc primSegment +
          EvmYul.UInt256.ofNat 1 := by
    simpa [Assembly.Instr.byteSize] using
      codeSegment_fallthroughPc_singleton primSegment
  exact
    compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_fallthrough_of_args
      (prim := prim) hPrim (layout := layout) (compiler := compiler)
      (compilerAfter := compilerAfter) (state := state) (op := op)
      (args := args) hSupported stackPrefix program primitiveTailFuel
      expressionFuel
      (Structured.Preservation.CodeSegment.fallthroughPc segment)
      (fun hResolveArgs =>
        compilerOpenLocalsExprSeq_eval_resolves_ok_length_of_sourceOwned
          hPrim hArgsOwned hResolveArgs)
      (fun {argsTrace compilerAfterArgs argValues} hResolveArgs => by
        rcases hArgsSound hArgsCompile argsSegment hArgsPc hResolveArgs with
          ⟨evmAfterArgs, hArgsPrefix, hArgsAfterPc, hArgsCont⟩
        have hAtPrimPc :
            evmAfterArgs.pc =
              Structured.Preservation.CodeSegment.startPc primSegment := by
          rw [hArgsAfterPc]
          exact hPrimStart.symm
        have hAt :
            Assembly.Program.instrAtPc program evmAfterArgs.pc.toNat =
              some
                ((Structured.Preservation.CodeSegment.startPc
                    primSegment).toNat,
                  Assembly.Instr.prim op.toPrimOp) := by
          simpa [hAtPrimPc] using
            codeSegment_instrAtPc_start_cons primSegment
        have hArgsFall :
            evmAfterArgs.pc + EvmYul.UInt256.ofNat 1 =
              Structured.Preservation.CodeSegment.fallthroughPc
                segment := by
          rw [hAtPrimPc]
          rw [← hPrimFall]
          exact hPrimFallSegment
        exact
          ⟨evmAfterArgs,
            (Structured.Preservation.CodeSegment.startPc primSegment).toNat,
            hArgsPrefix, hAt, hArgsFall, hArgsCont⟩)
      hResolve

theorem compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (value : Word)
    (stackPrefix : List Word)
    (program : Assembly.Program) (pc fuel : Nat)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.push value))
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.lit value) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  cases hResolve
  rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  let evmAfter :=
    state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33)
  have hStep :
      Assembly.Source.stepAtResult program pc (.push value) state =
        .ok (.running evmAfter) := by
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      Assembly.Instr.haltKind?, Assembly.Target.stepInstr, evmAfter]
  have hOpenStep :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program pc (.push value) state)
        [] (.ok (.running evmAfter)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_non_prim
      (program := program) (pc := pc) (instr := .push value)
      (state := state) (result := .running evmAfter)
      (by intro op hEq; cases hEq) hStep
  refine ⟨evmAfter, ?_, ?_⟩
  · constructor
    · simpa [evmAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · refine ⟨baseStack, ?_, hStackRel⟩
      simp [evmAfter, hStack, EvmYul.Stack.push,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  · intro tailTrace result hRest
    simpa using
      OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
        (program := program) (fuel := fuel) (state := state)
        (mid := evmAfter) (pc := pc) (instr := .push value)
        hAt hOpenStep hRest

theorem compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {value : Word}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.lit value) = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.lit value) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  have hCode :
      code = [Structured.BasicInstr.push value] :=
    localsExpr_compileCode_lit_eq hCompile
  have hAssemblyCode :
      code.toAssembly = [Assembly.Instr.push value] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let pushSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.push value] :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  have hPcPush :
      state.pc =
        Structured.Preservation.CodeSegment.startPc pushSegment := by
    simpa [pushSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat,
            Assembly.Instr.push value) := by
    simpa [hPcPush] using codeSegment_instrAtPc_start_cons pushSegment
  exact
    compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue
      (prim := prim) (layout := layout) (compiler := compiler)
      (compilerAfter := compilerAfter) (state := state) value stackPrefix
      program
      ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
      fuel hPrefixRel hAt hResolve

theorem compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {value : Word}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.lit value) = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.lit value) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  have hCode :
      code = [Structured.BasicInstr.push value] :=
    localsExpr_compileCode_lit_eq hCompile
  have hAssemblyCode :
      code.toAssembly = [Assembly.Instr.push value] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let pushSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.push value] :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  have hPcPush :
      state.pc =
        Structured.Preservation.CodeSegment.startPc pushSegment := by
    simpa [pushSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat,
            Assembly.Instr.push value) := by
    simpa [hPcPush] using codeSegment_instrAtPc_start_cons pushSegment
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  cases hResolve
  rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  let evmAfter :=
    state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33)
  have hStep :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
          (.push value) state =
        .ok (.running evmAfter) := by
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      Assembly.Instr.haltKind?, Assembly.Target.stepInstr, evmAfter]
  have hOpenStep :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
          (.push value) state)
        [] (.ok (.running evmAfter)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_non_prim
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
      (instr := .push value)
      (state := state) (result := .running evmAfter)
      (by intro op hEq; cases hEq) hStep
  have hAfterPc :
      evmAfter.pc =
        Structured.Preservation.CodeSegment.startPc pushSegment +
          EvmYul.UInt256.ofNat 33 := by
    simp [evmAfter, hPcPush, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hFallPush :
      Structured.Preservation.CodeSegment.fallthroughPc pushSegment =
        Structured.Preservation.CodeSegment.startPc pushSegment +
          EvmYul.UInt256.ofNat 33 := by
    simpa [Assembly.Instr.byteSize, Assembly.Instr.push32Size] using
      codeSegment_fallthroughPc_singleton pushSegment
  have hFallSegment :
      Structured.Preservation.CodeSegment.fallthroughPc pushSegment =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    simp [pushSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc, hAssemblyCode]
  refine ⟨evmAfter, ?_, ?_, ?_⟩
  · constructor
    · simpa [evmAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · refine ⟨baseStack, ?_, hStackRel⟩
      simp [evmAfter, hStack, EvmYul.Stack.push,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  · rw [hFallSegment.symm, hFallPush]
    exact hAfterPc
  · intro tailTrace result hRest
    simpa using
      OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
        (program := program) (fuel := fuel) (state := state)
        (mid := evmAfter)
        (pc := (Structured.Preservation.CodeSegment.startPc pushSegment).toNat)
        (instr := .push value)
        hAt hOpenStep hRest

theorem compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name} {idx offset : Nat} {op : Structured.BasicOp}
    (hName : layout[idx]? = some name)
    (stackPrefix : List Word)
    (hPrefixLen : stackPrefix.length = offset)
    (hBound : offset + idx + 1 ≤ 16)
    (hDup : Locals.StackOp.dup? (offset + idx + 1) = some op)
    (program : Assembly.Program) (pc fuel : Nat)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, Assembly.Instr.prim op.toPrimOp))
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.var name) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  cases hLookup : compiler.vars name with
  | none =>
      simp [hLookup, Reference.SourceBridgeFacts.CompilerOpen.invalid] at hResolve
      cases hResolve
  | some value =>
      simp [hLookup] at hResolve
      cases hResolve
      rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
      have hBaseAt : baseStack[idx]? = some value := by
        have hLookupBase := hStackRel.2 hName
        simpa [hLookup] using hLookupBase
      subst offset
      have hStackAt :
          state.stack[stackPrefix.length + idx]? = some value := by
        rw [hStack]
        rw [List.getElem?_append_right]
        · simpa using hBaseAt
        · simp
      let evmAfter := state.replaceStackAndIncrPC (value :: state.stack)
      let depth := stackPrefix.length + (idx + 1)
      have hDupDepth : Locals.StackOp.dup? depth = some op := by
        simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hDup
      have hNoCallCreate : op.toPrimOp.isCallCreate = false :=
        Locals.CompilerFacts.StackOp.dup?_not_callCreate depth hDupDepth
      have hDupValue :
          EvmYul.dup depth state = .ok evmAfter := by
        have hDupValue' :=
          Locals.Direct.evm_dup_succ_get? (state := state)
            (idx := stackPrefix.length + idx) hStackAt
        simpa [depth, evmAfter, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hDupValue'
      have hStepOp : Structured.BasicOp.step op state = .ok evmAfter := by
        have hOne : 1 ≤ depth := by
          unfold depth
          omega
        have hDepthBound : depth ≤ 16 := by
          simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hBound
        rcases
            Locals.Direct.stackOp_dup?_step_eq_dup
              (n := depth) hOne hDepthBound state with
          ⟨op', hDup', hStepEq⟩
        have hOp : op = op' := by
          rw [hDupDepth] at hDup'
          cases hDup'
          rfl
        rw [hOp, hStepEq]
        exact hDupValue
      have hStepAt :
          Assembly.Source.stepAt program pc (.prim op.toPrimOp) state =
            .ok evmAfter := by
        simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using hStepOp
      have hStepResult :
          Assembly.Source.stepAtResult program pc (.prim op.toPrimOp) state =
            .ok (.running evmAfter) := by
        simp [Assembly.Source.stepAtResult, hStepAt,
          basicOp_toPrimOp_haltKind?_none op]
      have hOpenStep :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openStepAtResult program pc
              (.prim op.toPrimOp) state)
            [] (.ok (.running evmAfter)) :=
        OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
          (program := program) (pc := pc) (op := op.toPrimOp)
          (state := state) (result := .running evmAfter)
          hNoCallCreate hStepResult
      refine ⟨evmAfter, ?_, ?_⟩
      · constructor
        · simpa [evmAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hShared
        · refine ⟨baseStack, ?_, hStackRel⟩
          simp [evmAfter, hStack, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
      · intro tailTrace result hRest
        simpa using
          OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
            (program := program) (fuel := fuel) (state := state)
            (mid := evmAfter) (pc := pc) (instr := .prim op.toPrimOp)
            hAt hOpenStep hRest

theorem compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.var name) = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout offset
      (.var name))
    (stackPrefix : List Word)
    (hPrefixLen : stackPrefix.length = offset)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.var name) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  rcases localsExpr_compileCode_var_inv hCompile with
    ⟨depth, op, hDepth, hDup, hCode⟩
  rcases hAccess with ⟨idx, hName, hBound⟩
  have hDepthIdx :
      Locals.Layout.lookupDepth? name ctx.layout = some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  rw [hDepthIdx] at hDepth
  cases hDepth
  have hDupIdx :
      Locals.StackOp.dup? (offset + idx + 1) = some op := by
    simpa [Nat.add_assoc] using hDup
  have hAssemblyCode :
      code.toAssembly = [Assembly.Instr.prim op.toPrimOp] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let opSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim op.toPrimOp] :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  have hPcOp :
      state.pc =
        Structured.Preservation.CodeSegment.startPc opSegment := by
    simpa [opSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc opSegment).toNat,
            Assembly.Instr.prim op.toPrimOp) := by
    simpa [hPcOp] using codeSegment_instrAtPc_start_cons opSegment
  exact
    compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue
      (prim := prim) (layout := layout) (compiler := compiler)
      (compilerAfter := compilerAfter) (state := state) (name := name)
      (idx := idx) (offset := offset) (op := op) hName stackPrefix
      hPrefixLen hBound hDupIdx program
      ((Structured.Preservation.CodeSegment.startPc opSegment).toNat)
      fuel hPrefixRel hAt hResolve

theorem compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name}
    {code : Structured.Code}
    (hCompile :
      Locals.Expr.compileCode ctx offset (.var name) = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout offset
      (.var name))
    (stackPrefix : List Word)
    (hPrefixLen : stackPrefix.length = offset)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim (.var name) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (fuel + 1) state)
          (trace ++ tailTrace) result := by
  rcases localsExpr_compileCode_var_inv hCompile with
    ⟨depth, op, hDepth, hDup, hCode⟩
  rcases hAccess with ⟨idx, hName, hBound⟩
  have hDepthIdx :
      Locals.Layout.lookupDepth? name ctx.layout = some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  rw [hDepthIdx] at hDepth
  cases hDepth
  have hDupIdx :
      Locals.StackOp.dup? (offset + idx + 1) = some op := by
    simpa [Nat.add_assoc] using hDup
  have hAssemblyCode :
      code.toAssembly = [Assembly.Instr.prim op.toPrimOp] := by
    simp [hCode, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let opSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim op.toPrimOp] :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  have hPcOp :
      state.pc =
        Structured.Preservation.CodeSegment.startPc opSegment := by
    simpa [opSegment, Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc opSegment).toNat,
            Assembly.Instr.prim op.toPrimOp) := by
    simpa [hPcOp] using codeSegment_instrAtPc_start_cons opSegment
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval] at hResolve
  cases hLookup : compiler.vars name with
  | none =>
      simp [hLookup, Reference.SourceBridgeFacts.CompilerOpen.invalid] at hResolve
      cases hResolve
  | some value =>
      simp [hLookup] at hResolve
      cases hResolve
      rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
      have hBaseAt : baseStack[idx]? = some value := by
        have hLookupBase := hStackRel.2 hName
        simpa [hLookup] using hLookupBase
      subst offset
      have hStackAt :
          state.stack[stackPrefix.length + idx]? = some value := by
        rw [hStack]
        rw [List.getElem?_append_right]
        · simpa using hBaseAt
        · simp
      let evmAfter := state.replaceStackAndIncrPC (value :: state.stack)
      let depth := stackPrefix.length + (idx + 1)
      have hDupDepth : Locals.StackOp.dup? depth = some op := by
        simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hDupIdx
      have hNoCallCreate : op.toPrimOp.isCallCreate = false :=
        Locals.CompilerFacts.StackOp.dup?_not_callCreate depth hDupDepth
      have hDupValue :
          EvmYul.dup depth state = .ok evmAfter := by
        have hDupValue' :=
          Locals.Direct.evm_dup_succ_get? (state := state)
            (idx := stackPrefix.length + idx) hStackAt
        simpa [depth, evmAfter, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hDupValue'
      have hStepOp : Structured.BasicOp.step op state = .ok evmAfter := by
        have hOne : 1 ≤ depth := by
          unfold depth
          omega
        have hDepthBound : depth ≤ 16 := by
          simpa [depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hBound
        rcases
            Locals.Direct.stackOp_dup?_step_eq_dup
              (n := depth) hOne hDepthBound state with
          ⟨op', hDup', hStepEq⟩
        have hOp : op = op' := by
          rw [hDupDepth] at hDup'
          cases hDup'
          rfl
        rw [hOp, hStepEq]
        exact hDupValue
      have hStepAt :
          Assembly.Source.stepAt program
              ((Structured.Preservation.CodeSegment.startPc opSegment).toNat)
              (.prim op.toPrimOp) state =
            .ok evmAfter := by
        simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using hStepOp
      have hStepResult :
          Assembly.Source.stepAtResult program
              ((Structured.Preservation.CodeSegment.startPc opSegment).toNat)
              (.prim op.toPrimOp) state =
            .ok (.running evmAfter) := by
        simp [Assembly.Source.stepAtResult, hStepAt,
          basicOp_toPrimOp_haltKind?_none op]
      have hOpenStep :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openStepAtResult program
              ((Structured.Preservation.CodeSegment.startPc opSegment).toNat)
              (.prim op.toPrimOp) state)
            [] (.ok (.running evmAfter)) :=
        OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
          (program := program)
          (pc := (Structured.Preservation.CodeSegment.startPc opSegment).toNat)
          (op := op.toPrimOp)
          (state := state) (result := .running evmAfter)
          hNoCallCreate hStepResult
      have hAfterPc :
          evmAfter.pc =
            Structured.Preservation.CodeSegment.startPc opSegment +
              EvmYul.UInt256.ofNat 1 := by
        simp [evmAfter, hPcOp, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hFallOp :
          Structured.Preservation.CodeSegment.fallthroughPc opSegment =
            Structured.Preservation.CodeSegment.startPc opSegment +
              EvmYul.UInt256.ofNat 1 := by
        simpa [Assembly.Instr.byteSize] using
          codeSegment_fallthroughPc_singleton opSegment
      have hFallSegment :
          Structured.Preservation.CodeSegment.fallthroughPc opSegment =
            Structured.Preservation.CodeSegment.fallthroughPc segment := by
        simp [opSegment, Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hAssemblyCode]
      refine ⟨evmAfter, ?_, ?_, ?_⟩
      · constructor
        · simpa [evmAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hShared
        · refine ⟨baseStack, ?_, hStackRel⟩
          simp [evmAfter, hStack, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
      · rw [hFallSegment.symm, hFallOp]
        exact hAfterPc
      · intro tailTrace result hRest
        simpa using
          OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
            (program := program) (fuel := fuel) (state := state)
            (mid := evmAfter)
            (pc := (Structured.Preservation.CodeSegment.startPc opSegment).toNat)
            (instr := .prim op.toPrimOp)
            hAt hOpenStep hRest

theorem compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim Locals.ExprSeq.nil compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel state)
          (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
  cases hResolve
  refine ⟨state, ?_, ?_⟩
  · simpa using hPrefixRel
  · intro tailTrace result hRest
    simpa using hRest

theorem compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset Locals.ExprSeq.nil = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (_segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (_hPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc _segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim Locals.ExprSeq.nil compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel state)
          (trace ++ tailTrace) result := by
  have hCode : code = [] :=
    localsExprSeq_compileCode_nil_eq hCompile
  exact
    compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue
      (prim := prim) (layout := layout) (compiler := compiler)
      (compilerAfter := compilerAfter) (state := state) stackPrefix program
      fuel hPrefixRel hResolve

theorem compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset Locals.ExprSeq.nil = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program) (fuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix state)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim Locals.ExprSeq.nil compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program fuel state)
          (trace ++ tailTrace) result := by
  have hCode : code = [] :=
    localsExprSeq_compileCode_nil_eq hCompile
  have hFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment =
        Structured.Preservation.CodeSegment.startPc segment := by
    rcases segment with ⟨pre, post, hAsm, hFits⟩
    simp [Structured.Preservation.CodeSegment.fallthroughPc,
      Structured.Preservation.CodeSegment.startPc, hCode,
      Structured.Code.toAssembly]
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
  cases hResolve
  refine ⟨state, ?_, ?_, ?_⟩
  · simpa using hPrefixRel
  · simpa [hFall] using hPc
  · intro tailTrace result hRest
    simpa using hRest

theorem compilerOpenLocalsExprSeq_cons_stackPrefix_openRunNResult_continue_of_head_tail
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {left right : Nat}
    {head : Locals.Expr left}
    {tail : Locals.ExprSeq right}
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (finalTailFuel tailFuel seqFuel : Nat)
    (hHeadSound :
      ∀ {headTrace : OpenExternal.OpenTrace}
        {compilerAfterHead : Objects.Source.State}
        {headValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
            prim head compiler)
          headTrace (.ok (compilerAfterHead, headValues)) →
        ∃ evmAfterHead : EvmYul.EVM.State,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
            (headValues.reverse ++ stackPrefix) evmAfterHead ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program seqFuel state)
              (headTrace ++ tailTrace) result)
    (hTailSound :
      ∀ {compilerAfterHead compilerAfterTail : Objects.Source.State}
        {headValues tailValues : List Word}
        {evmAfterHead : EvmYul.EVM.State}
        {tailTrace : OpenExternal.OpenTrace},
        Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
          (headValues.reverse ++ stackPrefix) evmAfterHead →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim tail compilerAfterHead)
          tailTrace (.ok (compilerAfterTail, tailValues)) →
        ∃ evmAfterTail : EvmYul.EVM.State,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterTail
            (tailValues.reverse ++ headValues.reverse ++ stackPrefix)
            evmAfterTail ∧
          ∀ {restTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program finalTailFuel
                evmAfterTail)
              restTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              (tailTrace ++ restTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim (Locals.ExprSeq.cons head tail) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      ∀ {restTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program finalTailFuel evmAfter)
          restTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program seqFuel state)
          (trace ++ restTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailAndDoneTrace, headResult, hTrace, hResolveHead,
        hResolveTailBind⟩
    rcases headResult with ⟨compilerAfterHead, headValues⟩
    rcases OpenExternal.OpenResultResolves.bind_inv hResolveTailBind with
      hTailError | hTailOk
    · rcases hTailError with ⟨err, _hTail, hResult⟩
      cases hResult
    · rcases hTailOk with
        ⟨tailTrace, doneTrace, tailResult, hTailAndDoneTrace,
          hResolveTail, hResolveDone⟩
      rcases tailResult with ⟨compilerAfterTail, tailValues⟩
      cases hResolveDone
      rcases hHeadSound hResolveHead with
        ⟨evmAfterHead, hHeadRel, hHeadCont⟩
      rcases hTailSound hHeadRel hResolveTail with
        ⟨evmAfterTail, hTailRel, hTailCont⟩
      refine ⟨evmAfterTail, ?_, ?_⟩
      · simpa [List.reverse_append, List.append_assoc] using hTailRel
      · intro restTrace result hRest
        have hTailAndRest :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              (tailTrace ++ restTrace) result :=
          hTailCont hRest
        have hFull := hHeadCont hTailAndRest
        subst tailAndDoneTrace
        subst trace
        simpa [List.append_assoc] using hFull

theorem compilerOpenLocalsExprSeq_cons_stackPrefix_openRunNResult_continue_fallthrough_of_head_tail
    {prim : Objects.Source.PrimitiveSemantics}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {left right : Nat}
    {head : Locals.Expr left}
    {tail : Locals.ExprSeq right}
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (finalTailFuel tailFuel seqFuel : Nat)
    (headFallthroughPc tailStartPc finalFallthroughPc : Word)
    (hHeadToTail : headFallthroughPc = tailStartPc)
    (hHeadSound :
      ∀ {headTrace : OpenExternal.OpenTrace}
        {compilerAfterHead : Objects.Source.State}
        {headValues : List Word},
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
            prim head compiler)
          headTrace (.ok (compilerAfterHead, headValues)) →
        ∃ evmAfterHead : EvmYul.EVM.State,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
            (headValues.reverse ++ stackPrefix) evmAfterHead ∧
          evmAfterHead.pc = headFallthroughPc ∧
          ∀ {tailTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              tailTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program seqFuel state)
              (headTrace ++ tailTrace) result)
    (hTailSound :
      ∀ {compilerAfterHead compilerAfterTail : Objects.Source.State}
        {headValues tailValues : List Word}
        {evmAfterHead : EvmYul.EVM.State}
        {tailTrace : OpenExternal.OpenTrace},
        Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
          (headValues.reverse ++ stackPrefix) evmAfterHead →
        evmAfterHead.pc = tailStartPc →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
            prim tail compilerAfterHead)
          tailTrace (.ok (compilerAfterTail, tailValues)) →
        ∃ evmAfterTail : EvmYul.EVM.State,
          Locals.SourceLowering.StackPrefixRel layout compilerAfterTail
            (tailValues.reverse ++ headValues.reverse ++ stackPrefix)
            evmAfterTail ∧
          evmAfterTail.pc = finalFallthroughPc ∧
          ∀ {restTrace : OpenExternal.OpenTrace}
            {result : Except EVMException Assembly.StepResult},
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program finalTailFuel
                evmAfterTail)
              restTrace result →
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              (tailTrace ++ restTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim (Locals.ExprSeq.cons head tail) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc = finalFallthroughPc ∧
      ∀ {restTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program finalTailFuel evmAfter)
          restTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program seqFuel state)
          (trace ++ restTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailAndDoneTrace, headResult, hTrace, hResolveHead,
        hResolveTailBind⟩
    rcases headResult with ⟨compilerAfterHead, headValues⟩
    rcases OpenExternal.OpenResultResolves.bind_inv hResolveTailBind with
      hTailError | hTailOk
    · rcases hTailError with ⟨err, _hTail, hResult⟩
      cases hResult
    · rcases hTailOk with
        ⟨tailTrace, doneTrace, tailResult, hTailAndDoneTrace,
          hResolveTail, hResolveDone⟩
      rcases tailResult with ⟨compilerAfterTail, tailValues⟩
      cases hResolveDone
      rcases hHeadSound hResolveHead with
        ⟨evmAfterHead, hHeadRel, hHeadPc, hHeadCont⟩
      have hAtTail : evmAfterHead.pc = tailStartPc := by
        simpa [hHeadToTail] using hHeadPc
      rcases hTailSound hHeadRel hAtTail hResolveTail with
        ⟨evmAfterTail, hTailRel, hTailPc, hTailCont⟩
      refine ⟨evmAfterTail, ?_, hTailPc, ?_⟩
      · simpa [List.reverse_append, List.append_assoc] using hTailRel
      · intro restTrace result hRest
        have hTailAndRest :
            OpenExternal.OpenResultResolves
              (OpenAssembly.Source.openRunNResult program tailFuel
                evmAfterHead)
              (tailTrace ++ restTrace) result :=
          hTailCont hRest
        have hFull := hHeadCont hTailAndRest
        subst tailAndDoneTrace
        subst trace
        simpa [List.append_assoc] using hFull

theorem compilerOpenLocalsExprSeq_cons_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode_head_tail
    {prim : Objects.Source.PrimitiveSemantics}
    {ctx : Locals.Ctx} {offset : Nat}
    {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {left right : Nat}
    {head : Locals.Expr left}
    {tail : Locals.ExprSeq right}
    {code : Structured.Code}
    (hCompile :
      Locals.ExprSeq.compileCode ctx offset
        (Locals.ExprSeq.cons head tail) = some code)
    (stackPrefix : List Word)
    (program : Assembly.Program)
    (finalTailFuel tailFuel seqFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hHeadSound :
      ∀ {headCode : Structured.Code},
        Locals.Expr.compileCode ctx offset head = some headCode →
        (headSegment :
          Structured.Preservation.CodeSegment program headCode.toAssembly) →
        state.pc =
          Structured.Preservation.CodeSegment.startPc headSegment →
        ∀ {headTrace : OpenExternal.OpenTrace}
          {compilerAfterHead : Objects.Source.State}
          {headValues : List Word},
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
              prim head compiler)
            headTrace (.ok (compilerAfterHead, headValues)) →
          ∃ evmAfterHead : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
              (headValues.reverse ++ stackPrefix) evmAfterHead ∧
            evmAfterHead.pc =
              Structured.Preservation.CodeSegment.fallthroughPc
                headSegment ∧
            ∀ {tailTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program tailFuel
                  evmAfterHead)
                tailTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program seqFuel state)
                (headTrace ++ tailTrace) result)
    (hTailSound :
      ∀ {tailCode : Structured.Code},
        Locals.ExprSeq.compileCode ctx (offset + left) tail =
          some tailCode →
        (tailSegment :
          Structured.Preservation.CodeSegment program tailCode.toAssembly) →
        ∀ {compilerAfterHead compilerAfterTail : Objects.Source.State}
          {headValues tailValues : List Word}
          {evmAfterHead : EvmYul.EVM.State}
          {tailTrace : OpenExternal.OpenTrace},
          evmAfterHead.pc =
            Structured.Preservation.CodeSegment.startPc tailSegment →
          Locals.SourceLowering.StackPrefixRel layout compilerAfterHead
            (headValues.reverse ++ stackPrefix) evmAfterHead →
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
              prim tail compilerAfterHead)
            tailTrace (.ok (compilerAfterTail, tailValues)) →
          ∃ evmAfterTail : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfterTail
              (tailValues.reverse ++ headValues.reverse ++ stackPrefix)
              evmAfterTail ∧
            evmAfterTail.pc =
              Structured.Preservation.CodeSegment.fallthroughPc
                tailSegment ∧
            ∀ {restTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program finalTailFuel
                  evmAfterTail)
                restTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program tailFuel
                  evmAfterHead)
                (tailTrace ++ restTrace) result)
    {valuesAfter : List Word}
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
          prim (Locals.ExprSeq.cons head tail) compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {restTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program finalTailFuel evmAfter)
          restTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program seqFuel state)
          (trace ++ restTrace) result := by
  rcases localsExprSeq_compileCode_cons_inv hCompile with
    ⟨headCode, tailCode, hHeadCompile, hTailCompile, hCode⟩
  have hAssemblyCode :
      code.toAssembly = headCode.toAssembly ++ tailCode.toAssembly := by
    simp [hCode, Structured.Code.toAssembly]
  let appendSegment :
      Structured.Preservation.CodeSegment program
        (headCode.toAssembly ++ tailCode.toAssembly) :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  let headSegment :
      Structured.Preservation.CodeSegment program headCode.toAssembly :=
    Structured.Preservation.CodeSegment.left appendSegment
  let tailSegment :
      Structured.Preservation.CodeSegment program tailCode.toAssembly :=
    Structured.Preservation.CodeSegment.right appendSegment
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    simpa [headSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hHeadToTail :
      Structured.Preservation.CodeSegment.fallthroughPc headSegment =
        Structured.Preservation.CodeSegment.startPc tailSegment := by
    exact
      (codeSegment_right_startPc_eq_left_fallthroughPc
        appendSegment).symm
  have hTailFallSegment :
      Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    simp [tailSegment, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc,
      hAssemblyCode, List.append_assoc]
  rcases
      compilerOpenLocalsExprSeq_cons_stackPrefix_openRunNResult_continue_fallthrough_of_head_tail
        (prim := prim) (layout := layout) (compiler := compiler)
        (compilerAfter := compilerAfter) (state := state)
        (left := left) (right := right) (head := head) (tail := tail)
        stackPrefix program finalTailFuel tailFuel seqFuel
        (Structured.Preservation.CodeSegment.fallthroughPc headSegment)
        (Structured.Preservation.CodeSegment.startPc tailSegment)
        (Structured.Preservation.CodeSegment.fallthroughPc tailSegment)
        hHeadToTail
        (fun {headTrace compilerAfterHead headValues} hResolveHead =>
          hHeadSound hHeadCompile headSegment hHeadPc hResolveHead)
        (fun {compilerAfterHead compilerAfterTail headValues tailValues
              evmAfterHead tailTrace}
            hHeadRel hAtTail hResolveTail =>
          hTailSound hTailCompile tailSegment hAtTail hHeadRel
            hResolveTail)
        hResolve with
    ⟨evmAfter, hRel, hPcTail, hCont⟩
  refine ⟨evmAfter, hRel, ?_, hCont⟩
  simpa [hTailFallSegment] using hPcTail

mutual
  theorem compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
      {prim : Objects.Source.PrimitiveSemantics}
      (hPrim : Locals.SourceLowering.PrimitiveSound prim) :
      ∀ {results : Nat} {expr : Locals.Expr results}
        {ctx : Locals.Ctx} {offset : Nat} {layout : List Name}
        {compiler compilerAfter : Objects.Source.State}
        {state : EvmYul.EVM.State} {code : Structured.Code},
        Locals.Source.Expr.SourceOwned expr →
        LocalsExprOpenSupported expr →
        Locals.SourceLowering.Expr.Accessible layout offset expr →
        Locals.Expr.compileCode ctx offset expr = some code →
        ctx.layout = layout →
        layout.Nodup →
        (stackPrefix : List Word) →
        stackPrefix.length = offset →
        (program : Assembly.Program) →
        (tailFuel : Nat) →
        (segment :
          Structured.Preservation.CodeSegment program code.toAssembly) →
        state.pc = Structured.Preservation.CodeSegment.startPc segment →
        Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix
          state →
        ∀ {valuesAfter : List Word} {trace : OpenExternal.OpenTrace},
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
              prim expr compiler)
            trace (.ok (compilerAfter, valuesAfter)) →
          ∃ evmAfter : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfter
              (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
            evmAfter.pc =
              Structured.Preservation.CodeSegment.fallthroughPc segment ∧
            ∀ {tailTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program tailFuel
                  evmAfter)
                tailTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program
                  (code.length + tailFuel) state)
                (trace ++ tailTrace) result := by
    intro results expr
    cases expr with
    | lit value =>
        intro ctx offset layout compiler compilerAfter state code
          _hOwned _hSupported _hAccess hCompile _hCtxLayout _hNoDup
          stackPrefix _hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        rcases
            compilerOpenLocalsExpr_lit_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
              (prim := prim) (ctx := ctx) (offset := offset)
              (layout := layout) (compiler := compiler)
              (compilerAfter := compilerAfter) (state := state)
              (value := value) hCompile stackPrefix program tailFuel
              segment hPc hPrefixRel hResolve with
          ⟨evmAfter, hRel, hAfterPc, hCont⟩
        refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
        intro tailTrace result hRest
        have hCode :
            code = [Structured.BasicInstr.push value] :=
          localsExpr_compileCode_lit_eq hCompile
        have hFuel : tailFuel + 1 = code.length + tailFuel := by
          simp [hCode, Nat.add_comm]
        simpa [hFuel] using hCont hRest
    | var name =>
        intro ctx offset layout compiler compilerAfter state code
          _hOwned _hSupported hAccess hCompile hCtxLayout hNoDup
          stackPrefix hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        rcases
            compilerOpenLocalsExpr_var_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
              (prim := prim) (ctx := ctx) (offset := offset)
              (layout := layout) (compiler := compiler)
              (compilerAfter := compilerAfter) (state := state)
              (name := name) hCompile hCtxLayout hNoDup hAccess
              stackPrefix hPrefixLen program tailFuel segment hPc
              hPrefixRel hResolve with
          ⟨evmAfter, hRel, hAfterPc, hCont⟩
        refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
        intro tailTrace result hRest
        rcases localsExpr_compileCode_var_inv hCompile with
          ⟨depth, op, _hDepth, _hDup, hCode⟩
        have hFuel : tailFuel + 1 = code.length + tailFuel := by
          simp [hCode, Nat.add_comm]
        simpa [hFuel] using hCont hRest
    | code code' =>
        intro ctx offset layout compiler compilerAfter state code
          hOwned _hSupported _hAccess _hCompile _hCtxLayout _hNoDup
          stackPrefix _hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        simp [Locals.Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        intro ctx offset layout compiler compilerAfter state code
          hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          stackPrefix hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        have hArgsOwned : Locals.Source.ExprSeq.SourceOwned args := by
          simpa [Locals.Source.Expr.SourceOwned] using hOwned
        simp [LocalsExprOpenSupported] at hSupported
        rcases hSupported with ⟨hArgsSupported, hOpSupported⟩
        rcases
            compilerOpenLocalsExpr_prim_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode_args
              (prim := prim) hPrim (ctx := ctx) (offset := offset)
              (layout := layout) (compiler := compiler)
              (compilerAfter := compilerAfter) (state := state)
              (op := op) (args := args) hCompile hArgsOwned hOpSupported
              stackPrefix program tailFuel (code.length + tailFuel)
              segment hPc
              (fun {argsCode} hArgsCompile argsSegment hArgsPc
                  {argsTrace compilerAfterArgs argValues}
                  hResolveArgs => by
                rcases
                    compilerOpenLocalsExprSeq_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
                      hPrim hArgsOwned hArgsSupported hAccess
                      hArgsCompile hCtxLayout hNoDup stackPrefix
                      hPrefixLen program (tailFuel + 1) argsSegment
                      hArgsPc hPrefixRel hResolveArgs with
                  ⟨evmAfterArgs, hArgsRel, hArgsAfterPc, hArgsCont⟩
                refine ⟨evmAfterArgs, hArgsRel, hArgsAfterPc, ?_⟩
                intro tailTrace result hRest
                have hFuel :
                    argsCode.length + (tailFuel + 1) =
                      code.length + tailFuel := by
                  rcases localsExpr_compileCode_prim_inv hCompile with
                    ⟨argsCode', hArgsCompile', hCode⟩
                  rw [hArgsCompile] at hArgsCompile'
                  cases hArgsCompile'
                  simp [hCode, Nat.add_comm, Nat.add_left_comm]
                simpa [hFuel] using hArgsCont hRest)
              hResolve with
          ⟨evmAfter, hRel, hAfterPc, hCont⟩
        exact ⟨evmAfter, hRel, hAfterPc, hCont⟩

  theorem compilerOpenLocalsExprSeq_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
      {prim : Objects.Source.PrimitiveSemantics}
      (hPrim : Locals.SourceLowering.PrimitiveSound prim) :
      ∀ {results : Nat} {exprs : Locals.ExprSeq results}
        {ctx : Locals.Ctx} {offset : Nat} {layout : List Name}
        {compiler compilerAfter : Objects.Source.State}
        {state : EvmYul.EVM.State} {code : Structured.Code},
        Locals.Source.ExprSeq.SourceOwned exprs →
        LocalsExprSeqOpenSupported exprs →
        Locals.SourceLowering.ExprSeq.Accessible layout offset exprs →
        Locals.ExprSeq.compileCode ctx offset exprs = some code →
        ctx.layout = layout →
        layout.Nodup →
        (stackPrefix : List Word) →
        stackPrefix.length = offset →
        (program : Assembly.Program) →
        (tailFuel : Nat) →
        (segment :
          Structured.Preservation.CodeSegment program code.toAssembly) →
        state.pc = Structured.Preservation.CodeSegment.startPc segment →
        Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix
          state →
        ∀ {valuesAfter : List Word} {trace : OpenExternal.OpenTrace},
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
              prim exprs compiler)
            trace (.ok (compilerAfter, valuesAfter)) →
          ∃ evmAfter : EvmYul.EVM.State,
            Locals.SourceLowering.StackPrefixRel layout compilerAfter
              (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
            evmAfter.pc =
              Structured.Preservation.CodeSegment.fallthroughPc segment ∧
            ∀ {tailTrace : OpenExternal.OpenTrace}
              {result : Except EVMException Assembly.StepResult},
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program tailFuel
                  evmAfter)
                tailTrace result →
              OpenExternal.OpenResultResolves
                (OpenAssembly.Source.openRunNResult program
                  (code.length + tailFuel) state)
                (trace ++ tailTrace) result := by
    intro results exprs
    cases exprs with
    | nil =>
        intro ctx offset layout compiler compilerAfter state code
          _hOwned _hSupported _hAccess hCompile _hCtxLayout _hNoDup
          stackPrefix _hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        rcases
            compilerOpenLocalsExprSeq_nil_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
              (prim := prim) (ctx := ctx) (offset := offset)
              (layout := layout) (compiler := compiler)
              (compilerAfter := compilerAfter) (state := state)
              hCompile stackPrefix program tailFuel segment hPc hPrefixRel
              hResolve with
          ⟨evmAfter, hRel, hAfterPc, hCont⟩
        refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
        intro tailTrace result hRest
        have hCode : code = [] :=
          localsExprSeq_compileCode_nil_eq hCompile
        simpa [hCode] using hCont hRest
    | @cons left right head tail =>
        intro ctx offset layout compiler compilerAfter state code
          hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          stackPrefix hPrefixLen program tailFuel segment hPc hPrefixRel
          valuesAfter trace hResolve
        simp [Locals.Source.ExprSeq.SourceOwned] at hOwned
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        simp [LocalsExprSeqOpenSupported] at hSupported
        rcases hSupported with ⟨hHeadSupported, hTailSupported⟩
        simp [Locals.SourceLowering.ExprSeq.Accessible] at hAccess
        rcases hAccess with ⟨hHeadAccess, hTailAccess⟩
        rcases localsExprSeq_compileCode_cons_inv hCompile with
          ⟨headCode, tailCode, hHeadCompile, hTailCompile, hCode⟩
        have hAssemblyCode :
            code.toAssembly =
              headCode.toAssembly ++ tailCode.toAssembly := by
          simp [hCode, Structured.Code.toAssembly]
        let appendSegment :
            Structured.Preservation.CodeSegment program
              (headCode.toAssembly ++ tailCode.toAssembly) :=
          Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
        let headSegment :
            Structured.Preservation.CodeSegment program
              headCode.toAssembly :=
          Structured.Preservation.CodeSegment.left appendSegment
        let tailSegment :
            Structured.Preservation.CodeSegment program
              tailCode.toAssembly :=
          Structured.Preservation.CodeSegment.right appendSegment
        have hHeadPc :
            state.pc =
              Structured.Preservation.CodeSegment.startPc headSegment := by
          simpa [headSegment, appendSegment,
            Structured.Preservation.CodeSegment.left,
            Structured.Preservation.CodeSegment.cast_code,
            Structured.Preservation.CodeSegment.startPc] using hPc
        have hHeadToTail :
            Structured.Preservation.CodeSegment.fallthroughPc headSegment =
              Structured.Preservation.CodeSegment.startPc tailSegment :=
          (codeSegment_right_startPc_eq_left_fallthroughPc appendSegment).symm
        have hTailFallSegment :
            Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
              Structured.Preservation.CodeSegment.fallthroughPc segment := by
          simp [tailSegment, appendSegment,
            Structured.Preservation.CodeSegment.right,
            Structured.Preservation.CodeSegment.cast_code,
            Structured.Preservation.CodeSegment.fallthroughPc,
            hAssemblyCode, List.append_assoc]
        rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq] at hResolve
        rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
          hHeadError | hHeadOk
        · rcases hHeadError with ⟨err, _hHead, hResult⟩
          cases hResult
        · rcases hHeadOk with
            ⟨headTrace, tailAndDoneTrace, headResult, hTrace,
              hResolveHead, hResolveTailBind⟩
          rcases headResult with ⟨compilerAfterHead, headValues⟩
          rcases OpenExternal.OpenResultResolves.bind_inv
              hResolveTailBind with
            hTailError | hTailOk
          · rcases hTailError with ⟨err, _hTail, hResult⟩
            cases hResult
          · rcases hTailOk with
              ⟨tailTrace, doneTrace, tailResult, hTailAndDoneTrace,
                hResolveTail, hResolveDone⟩
            rcases tailResult with ⟨compilerAfterTail, tailValues⟩
            cases hResolveDone
            rcases
                compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
                  hPrim hHeadOwned hHeadSupported hHeadAccess
                  hHeadCompile hCtxLayout hNoDup stackPrefix hPrefixLen
                  program (tailCode.length + tailFuel) headSegment
                  hHeadPc hPrefixRel hResolveHead with
              ⟨evmAfterHead, hHeadRel, hHeadAfterPc, hHeadCont⟩
            have hHeadLen :
                headValues.length = left :=
              compilerOpenLocalsExpr_eval_resolves_ok_length_of_sourceOwned
                hPrim hHeadOwned hResolveHead
            have hTailPrefixLen :
                (headValues.reverse ++ stackPrefix).length =
                  offset + left := by
              simp [List.length_reverse, hHeadLen, hPrefixLen,
                Nat.add_comm]
            have hTailPc :
                evmAfterHead.pc =
                  Structured.Preservation.CodeSegment.startPc tailSegment := by
              rw [hHeadAfterPc]
              exact hHeadToTail
            rcases
                compilerOpenLocalsExprSeq_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
                  hPrim hTailOwned hTailSupported hTailAccess
                  hTailCompile hCtxLayout hNoDup
                  (headValues.reverse ++ stackPrefix) hTailPrefixLen
                  program tailFuel tailSegment hTailPc hHeadRel
                  hResolveTail with
              ⟨evmAfterTail, hTailRel, hTailAfterPc, hTailCont⟩
            refine ⟨evmAfterTail, ?_, ?_, ?_⟩
            · simpa [List.reverse_append, List.append_assoc] using
                hTailRel
            · simpa [hTailFallSegment] using hTailAfterPc
            · intro restTrace result hRest
              have hTailAndRest :
                  OpenExternal.OpenResultResolves
                    (OpenAssembly.Source.openRunNResult program
                      (tailCode.length + tailFuel) evmAfterHead)
                    (tailTrace ++ restTrace) result :=
                hTailCont hRest
              have hFull := hHeadCont hTailAndRest
              have hFuel :
                  headCode.length + (tailCode.length + tailFuel) =
                    code.length + tailFuel := by
                simp [hCode, Nat.add_assoc]
              subst tailAndDoneTrace
              subst trace
              simpa [List.append_assoc, hFuel] using hFull
end

theorem compilerOpenFunctionsArgList_openRunNResult_of_compileOpen
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {args : List (Functions.Expr 1)}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hOwned :
      Locals.Source.ExprSeq.SourceOwned (Functions.Lower.argExprs args))
    (hSupported :
      LocalsExprSeqOpenSupported (Functions.Lower.argExprs args))
    (hAccess :
      Locals.SourceLowering.ExprSeq.Accessible layout 0
        (Functions.Lower.argExprs args))
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          { stmts := Functions.Lower.evalArgs args } =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (stackPrefix : List Word)
    (hPrefixLen : stackPrefix.length = 0)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler stackPrefix
        state)
    {valuesAfter : List Word} {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.ArgList.eval
          prim args compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    finalLocalsCtx = localsCtx ∧
      ∃ targetFuel evmAfter,
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program targetFuel state)
          trace (.ok (.running evmAfter)) ∧
        Locals.SourceLowering.StackPrefixRel layout compilerAfter
          (valuesAfter.reverse ++ stackPrefix) evmAfter ∧
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
  cases args with
  | nil =>
      have hCompileNil :
          compiledStmts = [] ∧ localsCtx = finalLocalsCtx := by
        simpa [Functions.Lower.evalArgs, Locals.Block.compileOpen] using
          hCompileBlock
      rcases hCompileNil with ⟨hCompiledStmts, hFinalCtx⟩
      subst compiledStmts
      subst finalLocalsCtx
      rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.ArgList.eval]
        at hResolve
      cases hResolve
      have hFall :
          Structured.Preservation.CodeSegment.fallthroughPc segment =
            Structured.Preservation.CodeSegment.startPc segment := by
        rcases segment with ⟨pre, post, hAsm, hFits⟩
        simp [Structured.Preservation.CodeSegment.fallthroughPc,
          Structured.Preservation.CodeSegment.startPc,
          Expressions.StmtList.toStructured, Structured.Block.compileFromCtx]
      refine ⟨rfl, 0, state, ?_, ?_, ?_⟩
      · rw [OpenAssembly.Source.openRunNResult_zero]
        exact OpenExternal.OpenResultResolves.done
      · simpa using hPrefixRel
      · rw [hFall]
        exact hPc
  | cons arg rest =>
      let args' : List (Functions.Expr 1) := arg :: rest
      have hCompileCons :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  [Locals.Stmt.exprs
                    (Functions.Lower.argExprs args')] } =
            some (compiledStmts, finalLocalsCtx) := by
        simpa [Functions.Lower.evalArgs, args'] using hCompileBlock
      rcases
          localsBlock_compileOpen_exprs_cons_inv hCompileCons with
        ⟨code, restStmts, hCode, hRestCompile, hCompiledStmts⟩
      have hRest :
          restStmts = [] ∧ localsCtx = finalLocalsCtx := by
        simpa [Locals.Block.compileOpen] using hRestCompile
      rcases hRest with ⟨hRestStmts, hFinalCtx⟩
      subst restStmts
      subst finalLocalsCtx
      have hSegmentCode :
          (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured compiledStmts }
              structuredCtx supply).code =
            (Structured.Block.compileFromCtx
              { stmts :=
                  Expressions.StmtList.toStructured
                    (Locals.codeStmt code ++ []) }
              structuredCtx supply).code := by
        simp [hCompiledStmts]
      let segment' :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts :=
                  Expressions.StmtList.toStructured
                    (Locals.codeStmt code ++ []) }
              structuredCtx supply).code :=
        Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
      rcases codeSegment_expressions_codeStmt_cons_split segment' with
        ⟨headSegment, tailSegment, hHeadStart, hTailStart, hTailFall⟩
      have hSegmentStart :
          Structured.Preservation.CodeSegment.startPc segment' =
            Structured.Preservation.CodeSegment.startPc segment := by
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.startPc]
      have hSegmentFall :
          Structured.Preservation.CodeSegment.fallthroughPc segment' =
            Structured.Preservation.CodeSegment.fallthroughPc segment := by
        cases segment with
        | mk pre post hAsm hFits =>
            simp [segment', Structured.Preservation.CodeSegment.cast_code,
              Structured.Preservation.CodeSegment.fallthroughPc,
              hSegmentCode]
      have hHeadPc :
          state.pc =
            Structured.Preservation.CodeSegment.startPc headSegment := by
        rw [hPc, ← hSegmentStart, ← hHeadStart]
      have hEvalSeqResolve :
          OpenExternal.OpenResultResolves
            (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalSeq
              prim (Functions.Lower.argExprs args') compiler)
            trace (.ok (compilerAfter, valuesAfter)) :=
        Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.ArgList.eval_argExprs
          (args := args') hResolve
      rcases
          compilerOpenLocalsExprSeq_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
            hPrim hOwned hSupported hAccess hCode hCtxLayout hNoDup
            stackPrefix hPrefixLen program 0 headSegment hHeadPc
            hPrefixRel hEvalSeqResolve with
        ⟨evmAfter, hAfterRel, hAfterPc, hCont⟩
      have hDone :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program 0 evmAfter)
            [] (.ok (.running evmAfter)) := by
        rw [OpenAssembly.Source.openRunNResult_zero]
        exact OpenExternal.OpenResultResolves.done
      have hRun :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program code.length state)
            trace (.ok (.running evmAfter)) := by
        simpa using hCont hDone
      have hTailEmpty :
          Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
            Structured.Preservation.CodeSegment.startPc tailSegment := by
        rcases tailSegment with ⟨pre, post, hAsm, hFits⟩
        simp [Structured.Preservation.CodeSegment.fallthroughPc,
          Structured.Preservation.CodeSegment.startPc,
          Expressions.StmtList.toStructured, Structured.Block.compileFromCtx]
      have hAfterPcFull :
          evmAfter.pc =
            Structured.Preservation.CodeSegment.fallthroughPc segment := by
        calc
          evmAfter.pc =
              Structured.Preservation.CodeSegment.fallthroughPc
                headSegment := hAfterPc
          _ = Structured.Preservation.CodeSegment.startPc tailSegment :=
              hTailStart.symm
          _ = Structured.Preservation.CodeSegment.fallthroughPc tailSegment :=
              hTailEmpty.symm
          _ = Structured.Preservation.CodeSegment.fallthroughPc segment' :=
              hTailFall
          _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
              hSegmentFall
      exact ⟨rfl, code.length, evmAfter, hRun, hAfterRel, hAfterPcFull⟩

theorem stackPrefixRel_singleton_to_cons_insert
    {layout : List Name} {source : Objects.Source.State}
    {evm : EvmYul.EVM.State} {name : Name} {value : Word}
    (hFresh : name ∉ layout)
    (hRel :
      Locals.SourceLowering.StackPrefixRel layout source [value] evm) :
    Locals.SourceLowering.StackPrefixRel (name :: layout)
      (source.insert name value) [] evm := by
  rcases hRel with ⟨hShared, baseStack, hStack, hStore⟩
  refine ⟨by simpa [Locals.Source.State.insert] using hShared,
    value :: baseStack, ?_, ?_⟩
  · simp [hStack]
  · simpa [Locals.Source.State.insert] using
      (Locals.SourceLowering.StackStoreRel.cons_insert
        (layout := layout) (store := source.vars)
        (stack := baseStack) (name := name) (value := value)
        hFresh hStore)

theorem compilerOpenLocalsExpr_zero_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {expr : Locals.Expr 0}
    {ctx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {valuesAfter : List Word} {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim expr compiler)
        trace (.ok (compilerAfter, valuesAfter))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout compilerAfter []
        evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (trace ++ tailTrace) result := by
  rcases
      compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
        hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
        [] rfl program tailFuel segment hPc hPrefixRel hResolve with
    ⟨evmAfter, hRel, hAfterPc, hCont⟩
  have hValuesLen :
      valuesAfter.length = 0 :=
    compilerOpenLocalsExpr_eval_resolves_ok_length_of_sourceOwned
      hPrim hOwned hResolve
  have hValuesNil : valuesAfter = [] := by
    cases valuesAfter with
    | nil => rfl
    | cons _ _ =>
        simp at hValuesLen
  refine ⟨evmAfter, ?_, hAfterPc, hCont⟩
  simpa [hValuesNil] using hRel

theorem compilerOpenLocalsExpr_evalOne_resolves_ok_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {results : Nat} {expr : Locals.Expr results}
    {compiler compilerAfter : Objects.Source.State}
    {value : Word} {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalOne
          prim expr compiler)
        trace (.ok (compilerAfter, value))) :
    OpenExternal.OpenResultResolves
      (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
        prim expr compiler)
      trace (.ok (compilerAfter, [value])) := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalOne] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterEval, values⟩
    cases values with
    | nil =>
        simp [Reference.SourceBridgeFacts.CompilerOpen.invalid] at hDone
        cases hDone
    | cons head tail =>
        cases tail with
        | nil =>
            simp at hDone
            cases hDone
            subst trace
            simpa using hEval
        | cons second rest =>
            simp [Reference.SourceBridgeFacts.CompilerOpen.invalid] at hDone
            cases hDone

theorem compilerOpenLocalsExpr_one_insert_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {expr : Locals.Expr 1}
    {ctx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    {name : Name} {value : Word}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim expr compiler)
        trace (.ok (compilerAfter, [value]))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel (name :: layout)
        (compilerAfter.insert name value) [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (trace ++ tailTrace) result := by
  rcases
      compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
        hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
        [] rfl program tailFuel segment hPc hPrefixRel hResolve with
    ⟨evmAfter, hRel, hAfterPc, hCont⟩
  refine ⟨evmAfter, ?_, hAfterPc, hCont⟩
  exact stackPrefixRel_singleton_to_cons_insert hFresh (by simpa using hRel)

theorem compilerOpenLocalsExpr_evalOne_insert_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {expr : Locals.Expr 1}
    {ctx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    {name : Name} {value : Word}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalOne
          prim expr compiler)
        trace (.ok (compilerAfter, value))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel (name :: layout)
        (compilerAfter.insert name value) [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (trace ++ tailTrace) result := by
  exact
    compilerOpenLocalsExpr_one_insert_openRunNResult_continue_fallthrough_of_compileCode
      hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup hFresh
      program tailFuel segment hPc hPrefixRel
      (compilerOpenLocalsExpr_evalOne_resolves_ok_inv hResolve)

theorem compilerOpenAssignTail_stackPrefix_openRunNResult_continue_fallthrough
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name} {idx : Nat} {value : Word}
    {swapOp : Structured.BasicOp}
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout source [value] state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        ([Assembly.Instr.prim swapOp.toPrimOp] ++
          [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp]))
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout
        (source.withVars (Locals.Source.Store.insert source.vars name value))
        [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (2 + tailFuel) state)
          tailTrace result := by
  rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStoreRel⟩
  rcases Locals.SourceLowering.StackStoreRel.lookup_value hStoreRel hName with
    ⟨oldAtIdx, hOld, _hOldStore⟩
  let swappedEVM :=
    state.replaceStackAndIncrPC
      (oldAtIdx :: baseStack.take idx ++ [value] ++
        baseStack.drop (idx + 1))
  let finalStack :=
    baseStack.take idx ++ value :: baseStack.drop (idx + 1)
  let finalEVM := swappedEVM.replaceStackAndIncrPC finalStack
  let swapSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim swapOp.toPrimOp] :=
    Structured.Preservation.CodeSegment.left segment
  let popSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp] :=
    Structured.Preservation.CodeSegment.right segment
  have hPcSwap :
      state.pc =
        Structured.Preservation.CodeSegment.startPc swapSegment := by
    simpa [swapSegment, Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAtSwap :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat,
            Assembly.Instr.prim swapOp.toPrimOp) := by
    simpa [hPcSwap] using codeSegment_instrAtPc_start_cons swapSegment
  have hSwapRun :
      EvmYul.swap (idx + 1) state = .ok swappedEVM := by
    simpa [swappedEVM, hStack] using
      (Locals.SourceLowering.Assignment.evm_swap_assign_get?
        (state := state) (locals := baseStack) (idx := idx)
        (old := oldAtIdx) (value := value)
        (by simpa using hStack) hOld)
  have hSwapStep :
      Structured.BasicOp.step swapOp state = .ok swappedEVM := by
    rcases
        Locals.SourceLowering.Assignment.stackOp_swap?_step_eq_swap
          (n := idx + 1) (by omega) hBound state with
      ⟨op', hSwap', hStepEq⟩
    have hOp : swapOp = op' := by
      rw [hSwap] at hSwap'
      cases hSwap'
      rfl
    rw [hOp, hStepEq]
    exact hSwapRun
  have hSwapNoCall :
      swapOp.toPrimOp.isCallCreate = false :=
    Locals.CompilerFacts.StackOp.swap?_not_callCreate (idx + 1) hSwap
  have hSwapStepAt :
      Assembly.Source.stepAt program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state =
        .ok swappedEVM := by
    simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using
      hSwapStep
  have hSwapStepResult :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state =
        .ok (.running swappedEVM) := by
    simp [Assembly.Source.stepAtResult, hSwapStepAt,
      basicOp_toPrimOp_haltKind?_none swapOp]
  have hOpenSwap :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state)
        [] (.ok (.running swappedEVM)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
      (op := swapOp.toPrimOp) (state := state)
      (result := .running swappedEVM) hSwapNoCall hSwapStepResult
  have hSwapPc :
      swappedEVM.pc =
        Structured.Preservation.CodeSegment.startPc popSegment := by
    have hStepPc :
        swappedEVM.pc = state.pc + EvmYul.UInt256.ofNat 1 :=
      basicOp_no_callCreate_step_pc hSwapNoCall hSwapStep
    have hSwapFall :
        Structured.Preservation.CodeSegment.fallthroughPc swapSegment =
          Structured.Preservation.CodeSegment.startPc swapSegment +
            EvmYul.UInt256.ofNat 1 := by
      simpa [Structured.BasicInstr.toAssembly, Structured.BasicOp.toPrimOp,
        Assembly.Instr.byteSize] using
        codeSegment_fallthroughPc_singleton swapSegment
    have hPopStart :
        Structured.Preservation.CodeSegment.startPc popSegment =
          Structured.Preservation.CodeSegment.fallthroughPc swapSegment :=
      codeSegment_right_startPc_eq_left_fallthroughPc segment
    rw [hStepPc, hPcSwap, hPopStart, hSwapFall]
  have hAtPop :
      Assembly.Program.instrAtPc program swappedEVM.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat,
            Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp) := by
    simpa [hSwapPc] using codeSegment_instrAtPc_start_cons popSegment
  have hPopStep :
      Structured.BasicOp.step Structured.BasicOp.pop swappedEVM =
        .ok finalEVM := by
    simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimStep.run, Assembly.PrimOp.continuingStep?,
      EvmYul.Stack.pop, swappedEVM, finalEVM, finalStack,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, List.append_assoc]
  have hPopStepAt :
      Assembly.Source.stepAt program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM =
        .ok finalEVM := by
    simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using
      hPopStep
  have hPopStepResult :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM =
        .ok (.running finalEVM) := by
    simp [Assembly.Source.stepAtResult, hPopStepAt,
      basicOp_toPrimOp_haltKind?_none Structured.BasicOp.pop]
  have hOpenPop :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM)
        [] (.ok (.running finalEVM)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc popSegment).toNat)
      (op := Structured.BasicOp.pop.toPrimOp) (state := swappedEVM)
      (result := .running finalEVM) rfl hPopStepResult
  have hFinalPc :
      finalEVM.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    have hStepPc :
        finalEVM.pc = swappedEVM.pc + EvmYul.UInt256.ofNat 1 :=
      basicOp_no_callCreate_step_pc (op := Structured.BasicOp.pop) rfl hPopStep
    have hPopFall :
        Structured.Preservation.CodeSegment.fallthroughPc popSegment =
          Structured.Preservation.CodeSegment.startPc popSegment +
            EvmYul.UInt256.ofNat 1 := by
      simpa [Structured.BasicInstr.toAssembly, Structured.BasicOp.toPrimOp,
        Assembly.Instr.byteSize] using
        codeSegment_fallthroughPc_singleton popSegment
    have hPopFallSegment :
        Structured.Preservation.CodeSegment.fallthroughPc popSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      simp [popSegment, Structured.Preservation.CodeSegment.right,
        Structured.Preservation.CodeSegment.fallthroughPc]
    rw [hStepPc, hSwapPc, ← hPopFall, hPopFallSegment]
  refine ⟨finalEVM, ?_, hFinalPc, ?_⟩
  · refine ⟨?_, finalStack, ?_, ?_⟩
    · simpa [finalEVM, swappedEVM, Locals.Source.State.withVars,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · simp [finalEVM, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, finalStack]
    · simpa [finalStack, Locals.Source.State.withVars] using
        (Locals.SourceLowering.StackStoreRel.assign
          (layout := layout) (store := source.vars)
          (stack := baseStack) (name := name) (value := value)
          (idx := idx) hNoDup hName hStoreRel)
  · intro tailFuel tailTrace result hRest
    have hPopAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (tailFuel + 1)
            swappedEVM)
          tailTrace result := by
      simpa using
        OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
          (program := program) (fuel := tailFuel) (state := swappedEVM)
          (mid := finalEVM)
          (pc := (Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (instr := .prim Structured.BasicOp.pop.toPrimOp)
          hAtPop hOpenPop hRest
    have hSwapAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program ((tailFuel + 1) + 1)
            state)
          tailTrace result := by
      simpa using
        OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
          (program := program) (fuel := tailFuel + 1) (state := state)
          (mid := swappedEVM)
          (pc := (Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (instr := .prim swapOp.toPrimOp)
          hAtSwap hOpenSwap hPopAndRest
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSwapAndRest

theorem compilerOpenAssignTopWithOffset_stackPrefix_openRunNResult_continue_fallthrough
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name} {idx offset : Nat} {value : Word}
    {restValues : List Word} {swapOp : Structured.BasicOp}
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hPrefixLen : restValues.length = offset)
    (hBound : offset + idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (offset + (idx + 1)) = some swapOp)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout source (value :: restValues)
        state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        ([Assembly.Instr.prim swapOp.toPrimOp] ++
          [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp]))
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout
        (source.withVars (Locals.Source.Store.insert source.vars name value))
        restValues evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (2 + tailFuel) state)
          tailTrace result := by
  rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStoreRel⟩
  rcases Locals.SourceLowering.StackStoreRel.lookup_value hStoreRel hName with
    ⟨oldAtIdx, hOld, _hOldStore⟩
  let restValuesBase := restValues ++ baseStack
  have hRestValuesOld :
      restValuesBase[offset + idx]? = some oldAtIdx := by
    subst restValuesBase
    rw [← hPrefixLen]
    exact
      (Locals.StackLowering.getElem?_append_right_add restValues baseStack idx).trans
        hOld
  let swappedEVM :=
    state.replaceStackAndIncrPC
      (oldAtIdx :: restValues ++ baseStack.take idx ++ [value] ++
        baseStack.drop (idx + 1))
  let finalStack :=
    restValues ++ baseStack.take idx ++ value :: baseStack.drop (idx + 1)
  let finalEVM := swappedEVM.replaceStackAndIncrPC finalStack
  let swapSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim swapOp.toPrimOp] :=
    Structured.Preservation.CodeSegment.left segment
  let popSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp] :=
    Structured.Preservation.CodeSegment.right segment
  have hPcSwap :
      state.pc =
        Structured.Preservation.CodeSegment.startPc swapSegment := by
    simpa [swapSegment, Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAtSwap :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat,
            Assembly.Instr.prim swapOp.toPrimOp) := by
    simpa [hPcSwap] using codeSegment_instrAtPc_start_cons swapSegment
  have hStackRestValues :
      state.stack = value :: restValuesBase := by
    subst restValuesBase
    simpa [List.append_assoc] using hStack
  have hSwapRunRaw :
      EvmYul.swap (offset + idx + 1) state =
        .ok
          (state.replaceStackAndIncrPC
            (oldAtIdx :: restValuesBase.take (offset + idx) ++ [value] ++
              restValuesBase.drop (offset + idx + 1))) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Locals.SourceLowering.Assignment.evm_swap_assign_get?
        (state := state) (locals := restValuesBase) (idx := offset + idx)
        (old := oldAtIdx) (value := value) hStackRestValues hRestValuesOld)
  have hTakeRestValues :
      restValuesBase.take (offset + idx) =
        restValues ++ baseStack.take idx := by
    subst restValuesBase
    rw [← hPrefixLen]
    simp [List.take_append]
  have hDropRestValues :
      restValuesBase.drop (offset + idx + 1) =
        baseStack.drop (idx + 1) := by
    subst restValuesBase
    rw [← hPrefixLen]
    simp [List.drop_append, Nat.add_assoc]
  have hSwapRun :
      EvmYul.swap (offset + idx + 1) state = .ok swappedEVM := by
    simpa [swappedEVM, hTakeRestValues, hDropRestValues, List.append_assoc]
      using hSwapRunRaw
  have hSwapStep :
      Structured.BasicOp.step swapOp state = .ok swappedEVM := by
    rcases
        Locals.SourceLowering.Assignment.stackOp_swap?_step_eq_swap
          (n := offset + (idx + 1)) (by omega) hBound state with
      ⟨op', hSwap', hStepEq⟩
    have hOp : swapOp = op' := by
      rw [hSwap] at hSwap'
      cases hSwap'
      rfl
    rw [hOp, hStepEq]
    simpa [Nat.add_assoc] using hSwapRun
  have hSwapNoCall :
      swapOp.toPrimOp.isCallCreate = false :=
    Locals.CompilerFacts.StackOp.swap?_not_callCreate
      (offset + (idx + 1)) hSwap
  have hSwapStepAt :
      Assembly.Source.stepAt program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state =
        .ok swappedEVM := by
    simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using
      hSwapStep
  have hSwapStepResult :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state =
        .ok (.running swappedEVM) := by
    simp [Assembly.Source.stepAtResult, hSwapStepAt,
      basicOp_toPrimOp_haltKind?_none swapOp]
  have hOpenSwap :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state)
        [] (.ok (.running swappedEVM)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
      (op := swapOp.toPrimOp) (state := state)
      (result := .running swappedEVM) hSwapNoCall hSwapStepResult
  have hSwapPc :
      swappedEVM.pc =
        Structured.Preservation.CodeSegment.startPc popSegment := by
    have hStepPc :
        swappedEVM.pc = state.pc + EvmYul.UInt256.ofNat 1 :=
      basicOp_no_callCreate_step_pc hSwapNoCall hSwapStep
    have hSwapFall :
        Structured.Preservation.CodeSegment.fallthroughPc swapSegment =
          Structured.Preservation.CodeSegment.startPc swapSegment +
            EvmYul.UInt256.ofNat 1 := by
      simpa [Structured.BasicInstr.toAssembly, Structured.BasicOp.toPrimOp,
        Assembly.Instr.byteSize] using
        codeSegment_fallthroughPc_singleton swapSegment
    have hPopStart :
        Structured.Preservation.CodeSegment.startPc popSegment =
          Structured.Preservation.CodeSegment.fallthroughPc swapSegment :=
      codeSegment_right_startPc_eq_left_fallthroughPc segment
    rw [hStepPc, hPcSwap, hPopStart, hSwapFall]
  have hAtPop :
      Assembly.Program.instrAtPc program swappedEVM.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat,
            Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp) := by
    simpa [hSwapPc] using codeSegment_instrAtPc_start_cons popSegment
  have hPopStep :
      Structured.BasicOp.step Structured.BasicOp.pop swappedEVM =
        .ok finalEVM := by
    simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimStep.run, Assembly.PrimOp.continuingStep?,
      EvmYul.Stack.pop, swappedEVM, finalEVM, finalStack,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, List.append_assoc]
  have hPopStepAt :
      Assembly.Source.stepAt program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM =
        .ok finalEVM := by
    simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using
      hPopStep
  have hPopStepResult :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM =
        .ok (.running finalEVM) := by
    simp [Assembly.Source.stepAtResult, hPopStepAt,
      basicOp_toPrimOp_haltKind?_none Structured.BasicOp.pop]
  have hOpenPop :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM)
        [] (.ok (.running finalEVM)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc popSegment).toNat)
      (op := Structured.BasicOp.pop.toPrimOp) (state := swappedEVM)
      (result := .running finalEVM) rfl hPopStepResult
  have hFinalPc :
      finalEVM.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    have hStepPc :
        finalEVM.pc = swappedEVM.pc + EvmYul.UInt256.ofNat 1 :=
      basicOp_no_callCreate_step_pc (op := Structured.BasicOp.pop) rfl hPopStep
    have hPopFall :
        Structured.Preservation.CodeSegment.fallthroughPc popSegment =
          Structured.Preservation.CodeSegment.startPc popSegment +
            EvmYul.UInt256.ofNat 1 := by
      simpa [Structured.BasicInstr.toAssembly, Structured.BasicOp.toPrimOp,
        Assembly.Instr.byteSize] using
        codeSegment_fallthroughPc_singleton popSegment
    have hPopFallSegment :
        Structured.Preservation.CodeSegment.fallthroughPc popSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      simp [popSegment, Structured.Preservation.CodeSegment.right,
        Structured.Preservation.CodeSegment.fallthroughPc]
    rw [hStepPc, hSwapPc, ← hPopFall, hPopFallSegment]
  refine ⟨finalEVM, ?_, hFinalPc, ?_⟩
  · refine ⟨?_, baseStack.take idx ++ value :: baseStack.drop (idx + 1), ?_, ?_⟩
    · simpa [finalEVM, swappedEVM, Locals.Source.State.withVars,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · simp [finalEVM, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, finalStack, List.append_assoc]
    · simpa [Locals.Source.State.withVars] using
        (Locals.SourceLowering.StackStoreRel.assign
          (layout := layout) (store := source.vars)
          (stack := baseStack) (name := name) (value := value)
          (idx := idx) hNoDup hName hStoreRel)
  · intro tailFuel tailTrace result hRest
    have hPopAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (tailFuel + 1)
            swappedEVM)
          tailTrace result := by
      simpa using
        OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
          (program := program) (fuel := tailFuel) (state := swappedEVM)
          (mid := finalEVM)
          (pc := (Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (instr := .prim Structured.BasicOp.pop.toPrimOp)
          hAtPop hOpenPop hRest
    have hSwapAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program ((tailFuel + 1) + 1)
            state)
          tailTrace result := by
      simpa using
        OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
          (program := program) (fuel := tailFuel + 1) (state := state)
          (mid := swappedEVM)
          (pc := (Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (instr := .prim swapOp.toPrimOp)
          hAtSwap hOpenSwap hPopAndRest
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSwapAndRest

def StackPrefixSuffixRel (layout : List Name) (source : Objects.Source.State)
    (stackPrefix suffix : List Word) (evm : EvmYul.EVM.State) : Prop :=
  evm.toSharedState = source.shared ∧
    ∃ baseStack : EvmYul.Stack Word,
      evm.stack = stackPrefix ++ baseStack ++ suffix ∧
        Locals.SourceLowering.StackStoreRel layout source.vars baseStack

def StackPrefixSuffixErasedRel (layout : List Name)
    (source : Objects.Source.State) (stackPrefix suffix : List Word)
    (evm : EvmYul.EVM.State) : Prop :=
  Structured.Preservation.eraseControl evm =
      Structured.Preservation.eraseControl
        { evm with toSharedState := source.shared } ∧
    ∃ baseStack : EvmYul.Stack Word,
      evm.stack = stackPrefix ++ baseStack ++ suffix ∧
        Locals.SourceLowering.StackStoreRel layout source.vars baseStack

namespace StackPrefixSuffixErasedRel

theorem exactWithTargetShared
    {layout : List Name} {source : Objects.Source.State}
    {stackPrefix suffix : List Word} {evm : EvmYul.EVM.State}
    (hRel :
      StackPrefixSuffixErasedRel layout source stackPrefix suffix evm) :
    StackPrefixSuffixRel layout
      { source with shared := evm.toSharedState } stackPrefix suffix evm := by
  rcases hRel with ⟨_hErase, baseStack, hStack, hStoreRel⟩
  exact ⟨rfl, baseStack, hStack, by simpa using hStoreRel⟩

theorem of_exactWithTargetShared
    {layout : List Name} {source : Objects.Source.State}
    {stackPrefix suffix : List Word} {start evm : EvmYul.EVM.State}
    (hErase :
      Structured.Preservation.eraseControl start =
        Structured.Preservation.eraseControl
          { start with toSharedState := source.shared })
    (hRel :
      StackPrefixSuffixRel layout
        { source with shared := start.toSharedState } stackPrefix suffix evm) :
    StackPrefixSuffixErasedRel layout source stackPrefix suffix evm := by
  rcases hRel with ⟨hShared, baseStack, hStack, hStoreRel⟩
  refine ⟨?_, baseStack, hStack, by simpa using hStoreRel⟩
  cases start
  cases evm
  simp [Structured.Preservation.eraseControl, Assembly.eraseGas] at hErase hShared ⊢
  cases hShared
  exact hErase

theorem of_frameStateRel_stateRel
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State} {base : Locals.RunState}
    {target : EvmYul.EVM.State} {values tokens : List Word}
    (hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns source base)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel
        (base.withEVM
          { base.evm with stack := values.reverse ++ base.evm.stack })
        target tokens) :
    ∃ suffix,
      StackPrefixSuffixErasedRel layout source values.reverse suffix target := by
  rcases hBaseRel with ⟨hLowerRel, _hReturns⟩
  rcases hLowerRel with ⟨hBaseShared, hStoreRel⟩
  rcases hFrameRel.hidden_suffix with
    ⟨suffix, hTargetStack, _hMaterialize⟩
  refine ⟨suffix, ?_⟩
  refine ⟨?_, base.evm.stack, ?_, hStoreRel⟩
  · calc
      Structured.Preservation.eraseControl target =
          Structured.Preservation.eraseControl
            { (base.withEVM
                { base.evm with stack := values.reverse ++ base.evm.stack }).evm with
              stack := target.stack } := hFrameRel.dataRel
      _ = Structured.Preservation.eraseControl
            { target with toSharedState := source.shared } := by
          cases target
          cases base
          cases source
          cases hBaseShared
          simp [Structured.RunState.withEVM,
            Structured.Preservation.eraseControl, Assembly.eraseGas]
  · calc
      target.stack =
          (base.withEVM
            { base.evm with stack := values.reverse ++ base.evm.stack }).evm.stack ++
            suffix := hTargetStack
      _ = (values.reverse ++ base.evm.stack) ++ suffix := by
            simp [Structured.RunState.withEVM]
      _ = values.reverse ++ base.evm.stack ++ suffix := by
            simp [List.append_assoc]

theorem of_attached_returnedFrameStateRel_stateRel
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {sourceBeforeCall sourceAfterCall : Objects.Source.State}
    {base bodyState returned : Locals.RunState}
    {target : EvmYul.EVM.State}
    {values tokens stack : List Word} {frame : Structured.ReturnDest}
    (hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns sourceBeforeCall
        base)
    (hVars : sourceAfterCall.vars = sourceBeforeCall.vars)
    (hReturned :
      Functions.SourceDirect.ReturnedStackRel (frame :: hiddenReturns)
        sourceAfterCall values bodyState)
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hFrameStack : frame.callerStack = base.evm.stack)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel
        (returned.withEVM { bodyState.evm with stack := stack })
        target tokens) :
    ∃ suffix,
      StackPrefixSuffixErasedRel layout sourceAfterCall values.reverse suffix
        target := by
  rcases hBaseRel with ⟨hLowerRel, _hReturns⟩
  rcases hLowerRel with ⟨_hBaseShared, hStoreRel⟩
  rcases hReturned with ⟨hReturnedShared, hReturnedStack, _hReturnedReturns⟩
  rcases hFrameRel.hidden_suffix with
    ⟨suffix, hTargetStack, _hMaterialize⟩
  have hStoreRelAfter :
      Locals.SourceLowering.StackStoreRel layout sourceAfterCall.vars
        base.evm.stack := by
    simpa [hVars] using hStoreRel
  have hAttachedStack :
      stack = values.reverse ++ base.evm.stack := by
    have hStackEq :=
      Structured.Preservation.Frame.StackFrameFacts.attachReturns?_eq hAttach
    calc
      stack = bodyState.evm.stack ++ frame.callerStack := hStackEq
      _ = values.reverse ++ frame.callerStack := by
            rw [hReturnedStack]
      _ = values.reverse ++ base.evm.stack := by
            rw [hFrameStack]
  refine ⟨suffix, ?_⟩
  refine ⟨?_, base.evm.stack, ?_, hStoreRelAfter⟩
  · calc
      Structured.Preservation.eraseControl target =
          Structured.Preservation.eraseControl
            { (returned.withEVM
                { bodyState.evm with stack := stack }).evm with
              stack := target.stack } := hFrameRel.dataRel
      _ = Structured.Preservation.eraseControl
            { target with toSharedState := sourceAfterCall.shared } := by
          cases target
          cases bodyState
          cases returned
          cases sourceAfterCall
          cases hReturnedShared
          simp [Structured.RunState.withEVM,
            Structured.Preservation.eraseControl, Assembly.eraseGas]
  · calc
      target.stack = stack ++ suffix := by
            simpa [Structured.RunState.withEVM] using hTargetStack
      _ = (values.reverse ++ base.evm.stack) ++ suffix := by
            rw [hAttachedStack]
      _ = values.reverse ++ base.evm.stack ++ suffix := by
            simp [List.append_assoc]

end StackPrefixSuffixErasedRel

theorem sourceDirect_prefixedStateRel_splitArgs_callerBase
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State} {callSource : Locals.RunState}
    {args : EvmYul.Stack Word} {argc : Nat}
    (hRel :
      Functions.SourceDirect.PrefixedStateRel layout hiddenReturns source args
        callSource)
    (hArgc : argc = args.length) :
    ∃ callerBase : Locals.RunState,
      Structured.StackFrame.splitArgs? argc callSource.evm.stack =
        some (args, callerBase.evm.stack) ∧
      Functions.SourceDirect.StateRel layout hiddenReturns source
        callerBase ∧
      callSource.evm.stack = args ++ callerBase.evm.stack := by
  rcases hRel with ⟨hShared, baseStack, hStack, hStoreRel, hReturns⟩
  let callerBase : Locals.RunState :=
    callSource.withEVM { callSource.evm with stack := baseStack }
  have hCallerStack : callerBase.evm.stack = baseStack := by
    simp [callerBase, Structured.RunState.withEVM]
  have hSplit :
      Structured.StackFrame.splitArgs? argc callSource.evm.stack =
        some (args, callerBase.evm.stack) := by
    unfold Structured.StackFrame.splitArgs?
    have hLe : argc ≤ callSource.evm.stack.length := by
      rw [hStack, hArgc]
      simp
    rw [if_pos hLe]
    have hTake :
        List.take argc (args ++ baseStack) = args := by
      simp [hArgc]
    have hDrop :
        List.drop argc (args ++ baseStack) = baseStack := by
      simp [hArgc]
    simp [hStack, hTake, hDrop, hCallerStack]
  have hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns source
        callerBase := by
    constructor
    · constructor
      · simpa [callerBase, Structured.RunState.withEVM] using hShared
      · simpa [callerBase, Structured.RunState.withEVM] using hStoreRel
    · simpa [callerBase, Structured.RunState.withEVM] using hReturns
  exact ⟨callerBase, hSplit, hBaseRel, by simpa [hCallerStack] using hStack⟩

theorem sourceDirect_prefixedStateRel_of_stackPrefixRel
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State} {stackPrefix : List Word}
    {evm : EvmYul.EVM.State}
    (hRel :
      Locals.SourceLowering.StackPrefixRel layout source stackPrefix evm) :
    Functions.SourceDirect.PrefixedStateRel layout hiddenReturns source
      stackPrefix { evm := evm, returns := hiddenReturns } := by
  rcases hRel with ⟨hShared, baseStack, hStack, hStoreRel⟩
  exact ⟨hShared, baseStack, hStack, hStoreRel, rfl⟩

theorem sourceDirect_prefixedStateRel_splitArgs_callerBase_withShared
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State} {callSource : Locals.RunState}
    {args : EvmYul.Stack Word} {argc : Nat}
    (sharedAfterCall : EvmYul.SharedState .EVM)
    (hRel :
      Functions.SourceDirect.PrefixedStateRel layout hiddenReturns source args
        callSource)
    (hArgc : argc = args.length) :
    ∃ callerBase : Locals.RunState,
      Structured.StackFrame.splitArgs? argc callSource.evm.stack =
        some (args, callerBase.evm.stack) ∧
      Functions.SourceDirect.StateRel layout hiddenReturns
        (source.withShared sharedAfterCall) callerBase ∧
      callSource.evm.stack = args ++ callerBase.evm.stack := by
  rcases hRel with ⟨_hShared, baseStack, hStack, hStoreRel, hReturns⟩
  let callerBase : Locals.RunState :=
    callSource.withEVM
      { callSource.evm with toSharedState := sharedAfterCall, stack := baseStack }
  have hCallerStack : callerBase.evm.stack = baseStack := by
    simp [callerBase, Structured.RunState.withEVM]
  have hSplit :
      Structured.StackFrame.splitArgs? argc callSource.evm.stack =
        some (args, callerBase.evm.stack) := by
    unfold Structured.StackFrame.splitArgs?
    have hLe : argc ≤ callSource.evm.stack.length := by
      rw [hStack, hArgc]
      simp
    rw [if_pos hLe]
    have hTake :
        List.take argc (args ++ baseStack) = args := by
      simp [hArgc]
    have hDrop :
        List.drop argc (args ++ baseStack) = baseStack := by
      simp [hArgc]
    simp [hStack, hTake, hDrop, hCallerStack]
  have hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns
        (source.withShared sharedAfterCall) callerBase := by
    constructor
    · constructor
      · simp [callerBase, Structured.RunState.withEVM,
          Locals.Source.State.withShared]
      · simpa [callerBase, Structured.RunState.withEVM] using hStoreRel
    · simpa [callerBase, Structured.RunState.withEVM] using hReturns
  exact ⟨callerBase, hSplit, hBaseRel, by simpa [hCallerStack] using hStack⟩

theorem sourceDirect_stackPrefixRel_callSource_parts_withShared
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State} {args : EvmYul.Stack Word}
    {evm : EvmYul.EVM.State} {argc : Nat}
    (sharedAfterCall : EvmYul.SharedState .EVM)
    (hRel :
      Locals.SourceLowering.StackPrefixRel layout source args evm)
    (hArgc : argc = args.length) :
    ∃ callSource callerBase : Locals.RunState,
      callSource.evm = evm ∧
      callSource.returns = hiddenReturns ∧
      Structured.StackFrame.splitArgs? argc callSource.evm.stack =
        some (args, callerBase.evm.stack) ∧
      Functions.SourceDirect.PrefixedStateRel layout hiddenReturns source args
        callSource ∧
      Functions.SourceDirect.StateRel layout hiddenReturns
        (source.withShared sharedAfterCall) callerBase ∧
      callSource.evm.stack = args ++ callerBase.evm.stack := by
  let callSource : Locals.RunState :=
    { evm := evm, returns := hiddenReturns }
  have hPrefix :
      Functions.SourceDirect.PrefixedStateRel layout hiddenReturns source args
        callSource := by
    simpa [callSource] using
      (sourceDirect_prefixedStateRel_of_stackPrefixRel
        (hiddenReturns := hiddenReturns) hRel)
  rcases
      sourceDirect_prefixedStateRel_splitArgs_callerBase_withShared
        sharedAfterCall hPrefix hArgc with
    ⟨callerBase, hSplit, hBaseRel, hStack⟩
  exact
    ⟨callSource, callerBase, by simp [callSource], by simp [callSource],
      hSplit, hPrefix, hBaseRel, hStack⟩

theorem compilerOpenFunctionsArgList_callSource_parts_withShared_of_compileOpen
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {args : List (Functions.Expr 1)}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {valuesAfter : List Word} {argc : Nat}
    (sharedAfterCall : EvmYul.SharedState .EVM)
    (hOwned :
      Locals.Source.ExprSeq.SourceOwned (Functions.Lower.argExprs args))
    (hSupported :
      LocalsExprSeqOpenSupported (Functions.Lower.argExprs args))
    (hAccess :
      Locals.SourceLowering.ExprSeq.Accessible layout 0
        (Functions.Lower.argExprs args))
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          { stmts := Functions.Lower.evalArgs args } =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.ArgList.eval
          prim args compiler)
        trace (.ok (compilerAfter, valuesAfter)))
    (hArgc : argc = valuesAfter.length) :
    finalLocalsCtx = localsCtx ∧
      ∃ targetFuel evmAfter callSource callerBase,
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program targetFuel state)
          trace (.ok (.running evmAfter)) ∧
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment ∧
        callSource.evm = evmAfter ∧
        callSource.returns = [] ∧
        Structured.Preservation.Frame.StateRel callSource evmAfter [] ∧
        Structured.StackFrame.splitArgs? argc callSource.evm.stack =
          some (valuesAfter.reverse, callerBase.evm.stack) ∧
        Functions.SourceDirect.PrefixedStateRel layout [] compilerAfter
          valuesAfter.reverse callSource ∧
        Functions.SourceDirect.StateRel layout []
          (compilerAfter.withShared sharedAfterCall) callerBase ∧
        callSource.evm.stack =
          valuesAfter.reverse ++ callerBase.evm.stack := by
  rcases
      compilerOpenFunctionsArgList_openRunNResult_of_compileOpen
        hPrim hOwned hSupported hAccess hCompileBlock hCtxLayout hNoDup []
        rfl program segment hPc hPrefixRel hResolve with
    ⟨hFinalCtx, targetFuel, evmAfter, hRun, hArgRel, hAfterPc⟩
  let callSource : Locals.RunState := { evm := evmAfter, returns := [] }
  have hArgRel' :
      Locals.SourceLowering.StackPrefixRel layout compilerAfter
        valuesAfter.reverse evmAfter := by
    simpa using hArgRel
  have hPrefix :
      Functions.SourceDirect.PrefixedStateRel layout [] compilerAfter
        valuesAfter.reverse callSource := by
    simpa [callSource] using
      (sourceDirect_prefixedStateRel_of_stackPrefixRel
        (hiddenReturns := []) hArgRel')
  have hArgc' : argc = (valuesAfter.reverse).length := by
    simpa using hArgc
  rcases
      sourceDirect_prefixedStateRel_splitArgs_callerBase_withShared
        sharedAfterCall hPrefix hArgc' with
    ⟨callerBase, hSplit, hBaseRel, hStack⟩
  have hFrame :
      Structured.Preservation.Frame.StateRel callSource evmAfter [] := by
    simpa [callSource, Structured.RunState.initial] using
      (Structured.Preservation.Frame.stateRel_initial evmAfter)
  refine ⟨hFinalCtx, targetFuel, evmAfter, callSource, callerBase, hRun,
    hAfterPc, by simp [callSource], by simp [callSource], hFrame, hSplit,
    hPrefix, hBaseRel, hStack⟩

theorem sourceDirect_returnedStackRel_of_shared_eq
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Objects.Source.State}
    {values : List Word} {target : Locals.RunState}
    (hRel :
      Functions.SourceDirect.ReturnedStackRel hiddenReturns source values
        target)
    (hShared : source.shared = source'.shared) :
    Functions.SourceDirect.ReturnedStackRel hiddenReturns source' values
      target := by
  rcases hRel with ⟨hTargetShared, hStack, hReturns⟩
  exact ⟨hTargetShared.trans hShared, hStack, hReturns⟩

theorem sourceDirect_returnedStackRel_attach_parts
    {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State}
    {values : List Word} {bodyState : Locals.RunState}
    {frame : Structured.ReturnDest}
    (hRel :
      Functions.SourceDirect.ReturnedStackRel (frame :: hiddenReturns)
        source values bodyState)
    (hLen : values.length = frame.retc) :
    ∃ returned : Locals.RunState, ∃ stack : EvmYul.Stack Word,
      stack = values.reverse ++ frame.callerStack ∧
        Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
          some stack ∧
        bodyState.returns = frame :: returned.returns ∧
        bodyState.evm.stack.length = frame.retc := by
  rcases hRel with ⟨_hShared, hStack, hReturns⟩
  let returned : Locals.RunState := { bodyState with returns := hiddenReturns }
  let stack : EvmYul.Stack Word := values.reverse ++ frame.callerStack
  refine ⟨returned, stack, rfl, ?_, ?_, ?_⟩
  · cases frame with
    | mk callerStack retc =>
        simp [stack, Structured.StackFrame.attachReturns?, hStack, hLen]
  · simpa [returned] using hReturns
  · calc
      bodyState.evm.stack.length = values.reverse.length := by
        rw [hStack]
      _ = values.length := by simp
      _ = frame.retc := hLen

theorem sourceDirect_returnedStackRel_callSite_parts
    {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State}
    {values : List Word} {bodyState callerBase : Locals.RunState}
    {frame : Structured.ReturnDest} {proc : Structured.Proc}
    (hRel :
      Functions.SourceDirect.ReturnedStackRel (frame :: hiddenReturns)
        source values bodyState)
    (hValuesLen : values.length = proc.retc)
    (hFrameRetc : frame.retc = proc.retc)
    (hFrameStack : frame.callerStack = callerBase.evm.stack) :
    ∃ returned : Locals.RunState, ∃ stack : EvmYul.Stack Word,
      stack = values.reverse ++ callerBase.evm.stack ∧
        Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
          some stack ∧
        bodyState.returns = frame :: returned.returns ∧
        bodyState.evm.stack.length = proc.retc ∧
        frame.callerStack = callerBase.evm.stack := by
  have hLen : values.length = frame.retc :=
    hValuesLen.trans hFrameRetc.symm
  rcases sourceDirect_returnedStackRel_attach_parts hRel hLen with
    ⟨returned, stack, hStack, hAttach, hReturns, hRetc⟩
  refine ⟨returned, stack, ?_, hAttach, hReturns, ?_, hFrameStack⟩
  · calc
      stack = values.reverse ++ frame.callerStack := hStack
      _ = values.reverse ++ callerBase.evm.stack := by
        rw [hFrameStack]
  · exact hRetc.trans hFrameRetc

theorem sourceOpen_callPostState_withShared_parts
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx ctxFinal : Functions.Source.Ctx}
    {tailFuel : Nat} {rest : List Functions.Stmt}
    {sourceAfterArgs : Objects.Source.State}
    {sharedAfterCall : EvmYul.SharedState .EVM}
    {targets : List Name} {values : List Word}
    {returnStore : Functions.Source.Store}
    {sourceOutcome : Functions.Source.Outcome}
    {tailTrace : OpenExternal.OpenTrace}
    (hAssign :
      Functions.Source.Store.assignMany targets values sourceAfterArgs.vars =
        some returnStore)
    (hTail :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim program ctx tailFuel { stmts := rest }
          { shared := sharedAfterCall, vars := returnStore })
        tailTrace (.ok (sourceOutcome, ctxFinal))) :
    (sourceAfterArgs.withShared sharedAfterCall).vars = sourceAfterArgs.vars ∧
      Functions.Source.Store.assignMany targets values
          (sourceAfterArgs.withShared sharedAfterCall).vars =
        some returnStore ∧
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim program ctx tailFuel { stmts := rest }
          ((sourceAfterArgs.withShared sharedAfterCall).withVars returnStore))
        tailTrace (.ok (sourceOutcome, ctxFinal)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Locals.Source.State.withShared]
  · simpa [Locals.Source.State.withShared] using hAssign
  · simpa [Locals.Source.State.withShared, Locals.Source.State.withVars] using
      hTail

theorem compilerOpenAssignTopWithOffset_stackPrefixSuffix_openRunNResult_continue_fallthrough
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {name : Name} {idx offset : Nat} {value : Word}
    {restValues suffix : List Word} {swapOp : Structured.BasicOp}
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hPrefixLen : restValues.length = offset)
    (hBound : offset + idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (offset + (idx + 1)) = some swapOp)
    (hPrefixRel :
      StackPrefixSuffixRel layout source (value :: restValues) suffix state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        ([Assembly.Instr.prim swapOp.toPrimOp] ++
          [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp]))
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ evmAfter : EvmYul.EVM.State,
      StackPrefixSuffixRel layout
        (source.withVars (Locals.Source.Store.insert source.vars name value))
        restValues suffix evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (2 + tailFuel) state)
          tailTrace result := by
  rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStoreRel⟩
  rcases Locals.SourceLowering.StackStoreRel.lookup_value hStoreRel hName with
    ⟨oldAtIdx, hOld, _hOldStore⟩
  let localsWithSuffix := baseStack ++ suffix
  have hLocalWithSuffix :
      localsWithSuffix[idx]? = some oldAtIdx := by
    have hIdxLt : idx < baseStack.length := by
      exact (List.getElem?_eq_some_iff.mp hOld).1
    simp [localsWithSuffix, List.getElem?_append_left hIdxLt, hOld]
  let swappedEVM :=
    state.replaceStackAndIncrPC
      (oldAtIdx :: restValues ++ localsWithSuffix.take idx ++ [value] ++
        localsWithSuffix.drop (idx + 1))
  let finalStackRaw :=
    restValues ++ localsWithSuffix.take idx ++ value ::
      localsWithSuffix.drop (idx + 1)
  let finalBaseStack :=
    baseStack.take idx ++ value :: baseStack.drop (idx + 1)
  let finalEVM := swappedEVM.replaceStackAndIncrPC finalStackRaw
  let swapSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim swapOp.toPrimOp] :=
    Structured.Preservation.CodeSegment.left segment
  let popSegment :
      Structured.Preservation.CodeSegment program
        [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp] :=
    Structured.Preservation.CodeSegment.right segment
  have hPcSwap :
      state.pc =
        Structured.Preservation.CodeSegment.startPc swapSegment := by
    simpa [swapSegment, Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hAtSwap :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat,
            Assembly.Instr.prim swapOp.toPrimOp) := by
    simpa [hPcSwap] using codeSegment_instrAtPc_start_cons swapSegment
  have hStackRestValues :
      state.stack = value :: restValues ++ localsWithSuffix := by
    simp [localsWithSuffix, hStack, List.append_assoc]
  have hSwapRunRaw :
      EvmYul.swap (restValues.length + idx + 1) state =
        .ok swappedEVM := by
    simpa [swappedEVM, Nat.add_assoc] using
      (Functions.SourceDirect.Assignment.evm_swap_assign_get?_with_prefix
        (state := state) (stackPrefix := restValues)
        (locals := localsWithSuffix) (idx := idx) (old := oldAtIdx)
        (value := value) hStackRestValues hLocalWithSuffix)
  have hSwapRun :
      EvmYul.swap (offset + idx + 1) state = .ok swappedEVM := by
    simpa [hPrefixLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hSwapRunRaw
  have hSwapStep :
      Structured.BasicOp.step swapOp state = .ok swappedEVM := by
    rcases
        Locals.SourceLowering.Assignment.stackOp_swap?_step_eq_swap
          (n := offset + (idx + 1)) (by omega) hBound state with
      ⟨op', hSwap', hStepEq⟩
    have hOp : swapOp = op' := by
      rw [hSwap] at hSwap'
      cases hSwap'
      rfl
    rw [hOp, hStepEq]
    simpa [Nat.add_assoc] using hSwapRun
  have hSwapNoCall :
      swapOp.toPrimOp.isCallCreate = false :=
    Locals.CompilerFacts.StackOp.swap?_not_callCreate
      (offset + (idx + 1)) hSwap
  have hSwapStepAt :
      Assembly.Source.stepAt program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state =
        .ok swappedEVM := by
    simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using
      hSwapStep
  have hSwapStepResult :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state =
        .ok (.running swappedEVM) := by
    simp [Assembly.Source.stepAtResult, hSwapStepAt,
      basicOp_toPrimOp_haltKind?_none swapOp]
  have hOpenSwap :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (.prim swapOp.toPrimOp) state)
        [] (.ok (.running swappedEVM)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
      (op := swapOp.toPrimOp) (state := state)
      (result := .running swappedEVM) hSwapNoCall hSwapStepResult
  have hSwapPc :
      swappedEVM.pc =
        Structured.Preservation.CodeSegment.startPc popSegment := by
    have hStepPc :
        swappedEVM.pc = state.pc + EvmYul.UInt256.ofNat 1 :=
      basicOp_no_callCreate_step_pc hSwapNoCall hSwapStep
    have hSwapFall :
        Structured.Preservation.CodeSegment.fallthroughPc swapSegment =
          Structured.Preservation.CodeSegment.startPc swapSegment +
            EvmYul.UInt256.ofNat 1 := by
      simpa [Structured.BasicInstr.toAssembly, Structured.BasicOp.toPrimOp,
        Assembly.Instr.byteSize] using
        codeSegment_fallthroughPc_singleton swapSegment
    have hPopStart :
        Structured.Preservation.CodeSegment.startPc popSegment =
          Structured.Preservation.CodeSegment.fallthroughPc swapSegment :=
      codeSegment_right_startPc_eq_left_fallthroughPc segment
    rw [hStepPc, hPcSwap, hPopStart, hSwapFall]
  have hAtPop :
      Assembly.Program.instrAtPc program swappedEVM.pc.toNat =
        some
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat,
            Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp) := by
    simpa [hSwapPc] using codeSegment_instrAtPc_start_cons popSegment
  have hPopStep :
      Structured.BasicOp.step Structured.BasicOp.pop swappedEVM =
        .ok finalEVM := by
    simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimStep.run, Assembly.PrimOp.continuingStep?,
      EvmYul.Stack.pop, swappedEVM, finalEVM, finalStackRaw,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, List.append_assoc]
  have hPopStepAt :
      Assembly.Source.stepAt program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM =
        .ok finalEVM := by
    simpa [Assembly.Source.stepAt, Structured.BasicOp.step] using
      hPopStep
  have hPopStepResult :
      Assembly.Source.stepAtResult program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM =
        .ok (.running finalEVM) := by
    simp [Assembly.Source.stepAtResult, hPopStepAt,
      basicOp_toPrimOp_haltKind?_none Structured.BasicOp.pop]
  have hOpenPop :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openStepAtResult program
          ((Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (.prim Structured.BasicOp.pop.toPrimOp) swappedEVM)
        [] (.ok (.running finalEVM)) :=
    OpenAssembly.Source.openStepAtResult_resolves_closed_of_prim_no_callCreate
      (program := program)
      (pc := (Structured.Preservation.CodeSegment.startPc popSegment).toNat)
      (op := Structured.BasicOp.pop.toPrimOp) (state := swappedEVM)
      (result := .running finalEVM) rfl hPopStepResult
  have hFinalPc :
      finalEVM.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    have hStepPc :
        finalEVM.pc = swappedEVM.pc + EvmYul.UInt256.ofNat 1 :=
      basicOp_no_callCreate_step_pc (op := Structured.BasicOp.pop) rfl hPopStep
    have hPopFall :
        Structured.Preservation.CodeSegment.fallthroughPc popSegment =
          Structured.Preservation.CodeSegment.startPc popSegment +
            EvmYul.UInt256.ofNat 1 := by
      simpa [Structured.BasicInstr.toAssembly, Structured.BasicOp.toPrimOp,
        Assembly.Instr.byteSize] using
        codeSegment_fallthroughPc_singleton popSegment
    have hPopFallSegment :
        Structured.Preservation.CodeSegment.fallthroughPc popSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      simp [popSegment, Structured.Preservation.CodeSegment.right,
        Structured.Preservation.CodeSegment.fallthroughPc]
    rw [hStepPc, hSwapPc, ← hPopFall, hPopFallSegment]
  have hFinalStackShape :
      finalStackRaw = restValues ++ finalBaseStack ++ suffix := by
    have hIdxLt : idx < baseStack.length :=
      (List.getElem?_eq_some_iff.mp hOld).1
    have hIdxLe : idx ≤ baseStack.length := Nat.le_of_lt hIdxLt
    have hIdxSuccLe : idx + 1 ≤ baseStack.length := by omega
    have hTake :
        localsWithSuffix.take idx = baseStack.take idx := by
      simpa [localsWithSuffix] using
        (List.take_append_of_le_length (l₁ := baseStack) (l₂ := suffix)
          hIdxLe)
    have hDrop :
        localsWithSuffix.drop (idx + 1) =
          baseStack.drop (idx + 1) ++ suffix := by
      simpa [localsWithSuffix] using
        (List.drop_append_of_le_length (l₁ := baseStack) (l₂ := suffix)
          hIdxSuccLe)
    simp [finalStackRaw, finalBaseStack, hTake, hDrop, List.append_assoc]
  refine ⟨finalEVM, ?_, hFinalPc, ?_⟩
  · refine ⟨?_, finalBaseStack, ?_, ?_⟩
    · simpa [finalEVM, swappedEVM, Locals.Source.State.withVars,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · simp [finalEVM, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hFinalStackShape]
    · simpa [finalBaseStack, Locals.Source.State.withVars] using
        (Locals.SourceLowering.StackStoreRel.assign
          (layout := layout) (store := source.vars)
          (stack := baseStack) (name := name) (value := value)
          (idx := idx) hNoDup hName hStoreRel)
  · intro tailFuel tailTrace result hRest
    have hPopAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (tailFuel + 1)
            swappedEVM)
          tailTrace result := by
      simpa using
        OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
          (program := program) (fuel := tailFuel) (state := swappedEVM)
          (mid := finalEVM)
          (pc := (Structured.Preservation.CodeSegment.startPc popSegment).toNat)
          (instr := .prim Structured.BasicOp.pop.toPrimOp)
          hAtPop hOpenPop hRest
    have hSwapAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program ((tailFuel + 1) + 1)
            state)
          tailTrace result := by
      simpa using
        OpenAssembly.Source.openRunNResult_current_stepAt_running_continue
          (program := program) (fuel := tailFuel + 1) (state := state)
          (mid := swappedEVM)
          (pc := (Structured.Preservation.CodeSegment.startPc swapSegment).toNat)
          (instr := .prim swapOp.toPrimOp)
          hAtSwap hOpenSwap hPopAndRest
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSwapAndRest

theorem compilerOpenFunctionsAssignReturnedTopsRev_stackPrefix_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {names : List Name} {values : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ names →
        ∃ idx, layout[idx]? = some name ∧ names.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany names values source.vars = some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTopsRev names } =
        some (compiledStmts, finalCtx))
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout source values state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ assignFuel evmAfter,
      Locals.SourceLowering.StackPrefixRel layout
        (source.withVars store') [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (assignFuel + tailFuel) state)
          tailTrace result := by
  induction names generalizing values source state store' compiledStmts
      finalCtx supply with
  | nil =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
          subst store'
          have hCompiled' :
              compiledStmts = [] ∧ ctx = finalCtx := by
            simpa [Functions.Lower.assignReturnedTopsRev,
              Locals.Block.compileOpen] using hCompileBlock
          have hCompiled :
              compiledStmts = [] ∧ finalCtx = ctx :=
            ⟨hCompiled'.1, hCompiled'.2.symm⟩
          rcases hCompiled with ⟨hCompiledStmts, _hFinalCtx⟩
          have hFallthrough :
              state.pc =
                Structured.Preservation.CodeSegment.fallthroughPc segment := by
            have hSegmentCode :
                (Structured.Block.compileFromCtx
                    { stmts := Expressions.StmtList.toStructured compiledStmts }
                    structuredCtx supply).code = [] := by
              simp [hCompiledStmts, Expressions.StmtList.toStructured,
                Structured.Block.compileFromCtx]
            let emptySegment :
                Structured.Preservation.CodeSegment program [] :=
              Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
            have hEmpty :
                Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
                  Structured.Preservation.CodeSegment.startPc emptySegment :=
              codeSegment_fallthroughPc_empty emptySegment
            have hStart :
                Structured.Preservation.CodeSegment.startPc emptySegment =
                  Structured.Preservation.CodeSegment.startPc segment := by
              simp [emptySegment, Structured.Preservation.CodeSegment.cast_code,
                Structured.Preservation.CodeSegment.startPc]
            have hFall :
                Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
                  Structured.Preservation.CodeSegment.fallthroughPc segment := by
              cases segment with
              | mk pre post hAsm hFits =>
                  simp [emptySegment,
                    Structured.Preservation.CodeSegment.cast_code,
                    Structured.Preservation.CodeSegment.fallthroughPc,
                    hSegmentCode]
            calc
              state.pc = Structured.Preservation.CodeSegment.startPc segment :=
                hPc
              _ = Structured.Preservation.CodeSegment.startPc emptySegment :=
                hStart.symm
              _ = Structured.Preservation.CodeSegment.fallthroughPc emptySegment :=
                hEmpty.symm
              _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
                hFall
          refine ⟨0, state, ?_, hFallthrough, ?_⟩
          · simpa [Locals.Source.State.withVars] using hPrefixRel
          · intro tailFuel tailTrace result hRest
            simpa using hRest
      | cons value valuesTail =>
          simp [Functions.Source.Store.assignMany] at hAssign
  | cons name rest ih =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
      | cons value valuesTail =>
          unfold Functions.Source.Store.assignMany at hAssign
          cases hContains : source.vars.contains name with
          | false =>
              simp [hContains] at hAssign
          | true =>
              simp [hContains] at hAssign
              unfold Functions.Lower.assignReturnedTopsRev at hCompileBlock
              unfold Locals.Block.compileOpen at hCompileBlock
              cases hDepth :
                  Locals.Layout.lookupDepth? name ctx.layout with
              | none =>
                  simp [Locals.Stmt.compile, hDepth] at hCompileBlock
              | some depth =>
                  cases hSwap :
                      Locals.StackOp.swap? (rest.length + depth) with
                  | none =>
                      simp [Locals.Stmt.compile, hDepth, hSwap]
                        at hCompileBlock
                  | some swapOp =>
                      cases hRestCompile :
                          Locals.Block.compileOpen ctx
                            { stmts :=
                                Functions.Lower.assignReturnedTopsRev rest } with
                      | none =>
                          simp [Locals.Stmt.compile, hDepth, hSwap,
                            hRestCompile] at hCompileBlock
                      | some restResult =>
                          rcases restResult with ⟨restStmts, restCtx⟩
                          simp [Locals.Stmt.compile, hDepth, hSwap,
                            hRestCompile] at hCompileBlock
                          rcases hCompileBlock with
                            ⟨hCompiledStmts, hFinalCtx⟩
                          subst finalCtx
                          rcases hTargets (name := name) (by simp) with
                            ⟨idx, hName, hHeadBoundAll⟩
                          have hHeadBound :
                              rest.length + idx + 1 ≤ 16 := by
                            have hHeadBound' :
                                (name :: rest).length + idx ≤ 16 :=
                              hHeadBoundAll
                            simpa [Nat.add_assoc, Nat.add_comm,
                              Nat.add_left_comm] using hHeadBound'
                          have hDepthExpected :
                              Locals.Layout.lookupDepth? name ctx.layout =
                                some (idx + 1) := by
                            simpa [hCtxLayout] using
                              (Locals.Layout.lookupDepth?_of_get?_nodup hName
                                hNoDup)
                          have hDepthEq : depth = idx + 1 := by
                            rw [hDepthExpected] at hDepth
                            cases hDepth
                            rfl
                          subst depth
                          have hValuesTailLen :
                              valuesTail.length = rest.length :=
                            Functions.Source.Store.assignMany_length hAssign
                          have hTargetsRest :
                              ∀ {restName : Name}, restName ∈ rest →
                                ∃ idx,
                                  layout[idx]? = some restName ∧
                                    rest.length + idx ≤ 16 := by
                            intro restName hMem
                            rcases hTargets (name := restName)
                                (by simp [hMem]) with
                              ⟨restIdx, hRestName, hRestBoundAll⟩
                            refine ⟨restIdx, hRestName, ?_⟩
                            have hRestBoundAll' :
                                rest.length + restIdx + 1 ≤ 16 := by
                              simpa [Nat.add_assoc, Nat.add_comm,
                                Nat.add_left_comm] using hRestBoundAll
                            omega
                          have hSegmentCode :
                              (Structured.Block.compileFromCtx
                                  { stmts :=
                                      Expressions.StmtList.toStructured
                                        compiledStmts }
                                  structuredCtx supply).code =
                                (Structured.Block.compileFromCtx
                                  { stmts :=
                                      Expressions.StmtList.toStructured
                                        (Locals.codeStmt
                                          [Structured.BasicInstr.op swapOp,
                                            Structured.BasicInstr.op
                                              Structured.BasicOp.pop] ++
                                          restStmts) }
                                  structuredCtx supply).code := by
                            simp [hCompiledStmts]
                          let segment' :
                              Structured.Preservation.CodeSegment program
                                (Structured.Block.compileFromCtx
                                  { stmts :=
                                      Expressions.StmtList.toStructured
                                        (Locals.codeStmt
                                          [Structured.BasicInstr.op swapOp,
                                            Structured.BasicInstr.op
                                              Structured.BasicOp.pop] ++
                                          restStmts) }
                                  structuredCtx supply).code :=
                            Structured.Preservation.CodeSegment.cast_code
                              hSegmentCode segment
                          rcases codeSegment_expressions_codeStmt_cons_split
                              segment' with
                            ⟨headSegmentRaw, tailSegment, hHeadStart,
                              hTailStart, hTailFall⟩
                          have hSegmentStart :
                              Structured.Preservation.CodeSegment.startPc
                                  segment' =
                                Structured.Preservation.CodeSegment.startPc
                                  segment := by
                            simp [segment',
                              Structured.Preservation.CodeSegment.cast_code,
                              Structured.Preservation.CodeSegment.startPc]
                          have hSegmentFall :
                              Structured.Preservation.CodeSegment.fallthroughPc
                                  segment' =
                                Structured.Preservation.CodeSegment.fallthroughPc
                                  segment := by
                            cases segment with
                            | mk pre post hAsm hFits =>
                                simp [segment',
                                  Structured.Preservation.CodeSegment.cast_code,
                                  Structured.Preservation.CodeSegment.fallthroughPc,
                                  hSegmentCode]
                          have hHeadPc :
                              state.pc =
                                Structured.Preservation.CodeSegment.startPc
                                  headSegmentRaw := by
                            rw [hPc, ← hSegmentStart, ← hHeadStart]
                          have hHeadAssembly :
                              Structured.Code.toAssembly
                                [Structured.BasicInstr.op swapOp,
                                  Structured.BasicInstr.op
                                    Structured.BasicOp.pop] =
                                  [Assembly.Instr.prim swapOp.toPrimOp] ++
                                  [Assembly.Instr.prim
                                    Structured.BasicOp.pop.toPrimOp] := by
                            rfl
                          let headSegment :
                              Structured.Preservation.CodeSegment program
                                ([Assembly.Instr.prim swapOp.toPrimOp] ++
                                  [Assembly.Instr.prim
                                    Structured.BasicOp.pop.toPrimOp]) :=
                            Structured.Preservation.CodeSegment.cast_code
                              hHeadAssembly headSegmentRaw
                          have hHeadPc' :
                              state.pc =
                                Structured.Preservation.CodeSegment.startPc
                                  headSegment := by
                            simpa [headSegment,
                              Structured.Preservation.CodeSegment.cast_code,
                              Structured.Preservation.CodeSegment.startPc]
                              using hHeadPc
                          rcases
                              compilerOpenAssignTopWithOffset_stackPrefix_openRunNResult_continue_fallthrough
                                (layout := layout) (source := source)
                                (state := state) (name := name) (idx := idx)
                                (offset := rest.length) (value := value)
                                (restValues := valuesTail) (swapOp := swapOp)
                                hNoDup hName hValuesTailLen hHeadBound
                                (by simpa [Nat.add_assoc] using hSwap)
                                hPrefixRel program headSegment hHeadPc' with
                            ⟨evmAfterHead, hHeadRel, hHeadAfterPc,
                              hHeadCont⟩
                          have hTailPc :
                              evmAfterHead.pc =
                                Structured.Preservation.CodeSegment.startPc
                                  tailSegment := by
                            have hHeadFall :
                                Structured.Preservation.CodeSegment.fallthroughPc
                                    headSegment =
                                  Structured.Preservation.CodeSegment.fallthroughPc
                                    headSegmentRaw := by
                              cases headSegmentRaw with
                              | mk pre post hAsm hFits =>
                                  simp [headSegment,
                                    Structured.Preservation.CodeSegment.cast_code,
                                    Structured.Preservation.CodeSegment.fallthroughPc,
                                    hHeadAssembly]
                            rw [hHeadAfterPc, hHeadFall]
                            exact hTailStart.symm
                          rcases
                              ih (values := valuesTail)
                                (source :=
                                  source.withVars
                                    (Locals.Source.Store.insert source.vars
                                      name value))
                                (state := evmAfterHead) (store' := store')
                                (compiledStmts := restStmts)
                                (finalCtx := restCtx) (supply := supply)
                                hTargetsRest hAssign hRestCompile hHeadRel
                                tailSegment hTailPc with
                            ⟨restFuel, evmAfter, hRestRel, hRestAfterPc,
                              hRestCont⟩
                          have hTailFallFull :
                              Structured.Preservation.CodeSegment.fallthroughPc
                                  tailSegment =
                                Structured.Preservation.CodeSegment.fallthroughPc
                                  segment := by
                            calc
                              Structured.Preservation.CodeSegment.fallthroughPc
                                  tailSegment =
                                Structured.Preservation.CodeSegment.fallthroughPc
                                  segment' := hTailFall
                              _ =
                                Structured.Preservation.CodeSegment.fallthroughPc
                                  segment := hSegmentFall
                          refine ⟨2 + restFuel, evmAfter, hRestRel, ?_, ?_⟩
                          · rw [hRestAfterPc]
                            exact hTailFallFull
                          · intro tailFuel tailTrace result hTailRun
                            have hRestAndTail :
                                OpenExternal.OpenResultResolves
                                  (OpenAssembly.Source.openRunNResult program
                                    (restFuel + tailFuel) evmAfterHead)
                                  tailTrace result :=
                              hRestCont hTailRun
                            have hFull := hHeadCont hRestAndTail
                            simpa [Nat.add_assoc] using hFull

theorem compilerOpenFunctionsAssignReturnedTops_stackPrefix_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {values : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values source.vars =
        some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (compiledStmts, finalCtx))
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout source values.reverse state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ assignFuel evmAfter,
      Locals.SourceLowering.StackPrefixRel layout
        (source.withVars store') [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (assignFuel + tailFuel) state)
          tailTrace result := by
  have hAssignReverse :
      Functions.Source.Store.assignMany targets.reverse values.reverse
          source.vars =
        some store' :=
    Functions.Source.Store.assignMany_reverse_of_run hAssign hTargetsNoDup
  have hTargetsReverse :
      ∀ {name : Name}, name ∈ targets.reverse →
        ∃ idx, layout[idx]? = some name ∧
          targets.reverse.length + idx ≤ 16 := by
    intro name hMem
    rcases hTargets (name := name) (by simpa using hMem) with
      ⟨idx, hName, hBound⟩
    exact ⟨idx, hName, by simpa using hBound⟩
  exact
    compilerOpenFunctionsAssignReturnedTopsRev_stackPrefix_openRunNResult_continue_fallthrough_of_compileOpen
      (layout := layout) (source := source) (state := state) (ctx := ctx)
      (finalCtx := finalCtx) (names := targets.reverse)
      (values := values.reverse) (store' := store')
      (compiledStmts := compiledStmts) (structuredCtx := structuredCtx)
      (supply := supply) hCtxLayout hNoDup hTargetsReverse hAssignReverse
      (by simpa [Functions.Lower.assignReturnedTops] using hCompileBlock)
      hPrefixRel program segment hPc

theorem compilerOpenFunctionsAssignReturnedTopsRev_stackPrefixSuffix_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {names : List Name} {values suffix : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ names →
        ∃ idx, layout[idx]? = some name ∧ names.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany names values source.vars = some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTopsRev names } =
        some (compiledStmts, finalCtx))
    (hPrefixRel :
      StackPrefixSuffixRel layout source values suffix state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ assignFuel evmAfter,
      assignFuel = 2 * names.length ∧
      StackPrefixSuffixRel layout (source.withVars store') [] suffix evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (assignFuel + tailFuel) state)
          tailTrace result := by
  induction names generalizing values source state store' compiledStmts
      finalCtx supply with
  | nil =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
          subst store'
          have hCompiled' :
              compiledStmts = [] ∧ ctx = finalCtx := by
            simpa [Functions.Lower.assignReturnedTopsRev,
              Locals.Block.compileOpen] using hCompileBlock
          have hCompiled :
              compiledStmts = [] ∧ finalCtx = ctx :=
            ⟨hCompiled'.1, hCompiled'.2.symm⟩
          rcases hCompiled with ⟨hCompiledStmts, _hFinalCtx⟩
          have hFallthrough :
              state.pc =
                Structured.Preservation.CodeSegment.fallthroughPc segment := by
            have hSegmentCode :
                (Structured.Block.compileFromCtx
                    { stmts := Expressions.StmtList.toStructured compiledStmts }
                    structuredCtx supply).code = [] := by
              simp [hCompiledStmts, Expressions.StmtList.toStructured,
                Structured.Block.compileFromCtx]
            let emptySegment :
                Structured.Preservation.CodeSegment program [] :=
              Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
            have hEmpty :
                Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
                  Structured.Preservation.CodeSegment.startPc emptySegment :=
              codeSegment_fallthroughPc_empty emptySegment
            have hStart :
                Structured.Preservation.CodeSegment.startPc emptySegment =
                  Structured.Preservation.CodeSegment.startPc segment := by
              simp [emptySegment, Structured.Preservation.CodeSegment.cast_code,
                Structured.Preservation.CodeSegment.startPc]
            have hFall :
                Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
                  Structured.Preservation.CodeSegment.fallthroughPc segment := by
              cases segment with
              | mk pre post hAsm hFits =>
                  simp [emptySegment,
                    Structured.Preservation.CodeSegment.cast_code,
                    Structured.Preservation.CodeSegment.fallthroughPc,
                    hSegmentCode]
            calc
              state.pc = Structured.Preservation.CodeSegment.startPc segment :=
                hPc
              _ = Structured.Preservation.CodeSegment.startPc emptySegment :=
                hStart.symm
              _ = Structured.Preservation.CodeSegment.fallthroughPc emptySegment :=
                hEmpty.symm
              _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
                hFall
          refine ⟨0, state, by simp, ?_, hFallthrough, ?_⟩
          · simpa [Locals.Source.State.withVars] using hPrefixRel
          · intro tailFuel tailTrace result hRest
            simpa using hRest
      | cons value valuesTail =>
          simp [Functions.Source.Store.assignMany] at hAssign
  | cons name rest ih =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
      | cons value valuesTail =>
          unfold Functions.Source.Store.assignMany at hAssign
          cases hContains : source.vars.contains name with
          | false =>
              simp [hContains] at hAssign
          | true =>
              simp [hContains] at hAssign
              unfold Functions.Lower.assignReturnedTopsRev at hCompileBlock
              unfold Locals.Block.compileOpen at hCompileBlock
              cases hDepth :
                  Locals.Layout.lookupDepth? name ctx.layout with
              | none =>
                  simp [Locals.Stmt.compile, hDepth] at hCompileBlock
              | some depth =>
                  cases hSwap :
                      Locals.StackOp.swap? (rest.length + depth) with
                  | none =>
                      simp [Locals.Stmt.compile, hDepth, hSwap]
                        at hCompileBlock
                  | some swapOp =>
                      cases hRestCompile :
                          Locals.Block.compileOpen ctx
                            { stmts :=
                                Functions.Lower.assignReturnedTopsRev rest } with
                      | none =>
                          simp [Locals.Stmt.compile, hDepth, hSwap,
                            hRestCompile] at hCompileBlock
                      | some restResult =>
                          rcases restResult with ⟨restStmts, restCtx⟩
                          simp [Locals.Stmt.compile, hDepth, hSwap,
                            hRestCompile] at hCompileBlock
                          rcases hCompileBlock with
                            ⟨hCompiledStmts, hFinalCtx⟩
                          subst finalCtx
                          rcases hTargets (name := name) (by simp) with
                            ⟨idx, hName, hHeadBoundAll⟩
                          have hHeadBound :
                              rest.length + idx + 1 ≤ 16 := by
                            have hHeadBound' :
                                (name :: rest).length + idx ≤ 16 :=
                              hHeadBoundAll
                            simpa [Nat.add_assoc, Nat.add_comm,
                              Nat.add_left_comm] using hHeadBound'
                          have hDepthExpected :
                              Locals.Layout.lookupDepth? name ctx.layout =
                                some (idx + 1) := by
                            simpa [hCtxLayout] using
                              (Locals.Layout.lookupDepth?_of_get?_nodup hName
                                hNoDup)
                          have hDepthEq : depth = idx + 1 := by
                            rw [hDepthExpected] at hDepth
                            cases hDepth
                            rfl
                          subst depth
                          have hValuesTailLen :
                              valuesTail.length = rest.length :=
                            Functions.Source.Store.assignMany_length hAssign
                          have hTargetsRest :
                              ∀ {restName : Name}, restName ∈ rest →
                                ∃ idx,
                                  layout[idx]? = some restName ∧
                                    rest.length + idx ≤ 16 := by
                            intro restName hMem
                            rcases hTargets (name := restName)
                                (by simp [hMem]) with
                              ⟨restIdx, hRestName, hRestBoundAll⟩
                            refine ⟨restIdx, hRestName, ?_⟩
                            have hRestBoundAll' :
                                rest.length + restIdx + 1 ≤ 16 := by
                              simpa [Nat.add_assoc, Nat.add_comm,
                                Nat.add_left_comm] using hRestBoundAll
                            omega
                          have hSegmentCode :
                              (Structured.Block.compileFromCtx
                                  { stmts :=
                                      Expressions.StmtList.toStructured
                                        compiledStmts }
                                  structuredCtx supply).code =
                                (Structured.Block.compileFromCtx
                                  { stmts :=
                                      Expressions.StmtList.toStructured
                                        (Locals.codeStmt
                                          [Structured.BasicInstr.op swapOp,
                                            Structured.BasicInstr.op
                                              Structured.BasicOp.pop] ++
                                          restStmts) }
                                  structuredCtx supply).code := by
                            simp [hCompiledStmts]
                          let segment' :
                              Structured.Preservation.CodeSegment program
                                (Structured.Block.compileFromCtx
                                  { stmts :=
                                      Expressions.StmtList.toStructured
                                        (Locals.codeStmt
                                          [Structured.BasicInstr.op swapOp,
                                            Structured.BasicInstr.op
                                              Structured.BasicOp.pop] ++
                                          restStmts) }
                                  structuredCtx supply).code :=
                            Structured.Preservation.CodeSegment.cast_code
                              hSegmentCode segment
                          rcases codeSegment_expressions_codeStmt_cons_split
                              segment' with
                            ⟨headSegmentRaw, tailSegment, hHeadStart,
                              hTailStart, hTailFall⟩
                          have hSegmentStart :
                              Structured.Preservation.CodeSegment.startPc
                                  segment' =
                                Structured.Preservation.CodeSegment.startPc
                                  segment := by
                            simp [segment',
                              Structured.Preservation.CodeSegment.cast_code,
                              Structured.Preservation.CodeSegment.startPc]
                          have hSegmentFall :
                              Structured.Preservation.CodeSegment.fallthroughPc
                                  segment' =
                                Structured.Preservation.CodeSegment.fallthroughPc
                                  segment := by
                            cases segment with
                            | mk pre post hAsm hFits =>
                                simp [segment',
                                  Structured.Preservation.CodeSegment.cast_code,
                                  Structured.Preservation.CodeSegment.fallthroughPc,
                                  hSegmentCode]
                          have hHeadPc :
                              state.pc =
                                Structured.Preservation.CodeSegment.startPc
                                  headSegmentRaw := by
                            rw [hPc, ← hSegmentStart, ← hHeadStart]
                          have hHeadAssembly :
                              Structured.Code.toAssembly
                                [Structured.BasicInstr.op swapOp,
                                  Structured.BasicInstr.op
                                    Structured.BasicOp.pop] =
                                  [Assembly.Instr.prim swapOp.toPrimOp] ++
                                  [Assembly.Instr.prim
                                    Structured.BasicOp.pop.toPrimOp] := by
                            rfl
                          let headSegment :
                              Structured.Preservation.CodeSegment program
                                ([Assembly.Instr.prim swapOp.toPrimOp] ++
                                  [Assembly.Instr.prim
                                    Structured.BasicOp.pop.toPrimOp]) :=
                            Structured.Preservation.CodeSegment.cast_code
                              hHeadAssembly headSegmentRaw
                          have hHeadPc' :
                              state.pc =
                                Structured.Preservation.CodeSegment.startPc
                                  headSegment := by
                            simpa [headSegment,
                              Structured.Preservation.CodeSegment.cast_code,
                              Structured.Preservation.CodeSegment.startPc]
                              using hHeadPc
                          rcases
                              compilerOpenAssignTopWithOffset_stackPrefixSuffix_openRunNResult_continue_fallthrough
                                (layout := layout) (source := source)
                                (state := state) (name := name) (idx := idx)
                                (offset := rest.length) (value := value)
                                (restValues := valuesTail)
                                (suffix := suffix) (swapOp := swapOp)
                                hNoDup hName hValuesTailLen hHeadBound
                                (by simpa [Nat.add_assoc] using hSwap)
                                hPrefixRel program headSegment hHeadPc' with
                            ⟨evmAfterHead, hHeadRel, hHeadAfterPc,
                              hHeadCont⟩
                          have hTailPc :
                              evmAfterHead.pc =
                                Structured.Preservation.CodeSegment.startPc
                                  tailSegment := by
                            have hHeadFall :
                                Structured.Preservation.CodeSegment.fallthroughPc
                                    headSegment =
                                  Structured.Preservation.CodeSegment.fallthroughPc
                                    headSegmentRaw := by
                              cases headSegmentRaw with
                              | mk pre post hAsm hFits =>
                                  simp [headSegment,
                                    Structured.Preservation.CodeSegment.cast_code,
                                    Structured.Preservation.CodeSegment.fallthroughPc,
                                    hHeadAssembly]
                            rw [hHeadAfterPc, hHeadFall]
                            exact hTailStart.symm
                          rcases
                              ih (values := valuesTail)
                                (source :=
                                  source.withVars
                                    (Locals.Source.Store.insert source.vars
                                      name value))
                                (state := evmAfterHead) (store' := store')
                                (compiledStmts := restStmts)
                                (finalCtx := restCtx) (supply := supply)
                                hTargetsRest hAssign hRestCompile hHeadRel
                                tailSegment hTailPc with
                            ⟨restFuel, evmAfter, hRestFuel, hRestRel,
                              hRestAfterPc, hRestCont⟩
                          have hTailFallFull :
                              Structured.Preservation.CodeSegment.fallthroughPc
                                  tailSegment =
                                Structured.Preservation.CodeSegment.fallthroughPc
                                  segment := by
                            calc
                              Structured.Preservation.CodeSegment.fallthroughPc
                                  tailSegment =
                                Structured.Preservation.CodeSegment.fallthroughPc
                                  segment' := hTailFall
                              _ =
                                Structured.Preservation.CodeSegment.fallthroughPc
                                  segment := hSegmentFall
                          refine
                            ⟨2 + restFuel, evmAfter, ?_, hRestRel, ?_, ?_⟩
                          · rw [hRestFuel]
                            simp [Nat.mul_succ, Nat.add_comm]
                          · rw [hRestAfterPc]
                            exact hTailFallFull
                          · intro tailFuel tailTrace result hTailRun
                            have hRestAndTail :
                                OpenExternal.OpenResultResolves
                                  (OpenAssembly.Source.openRunNResult program
                                    (restFuel + tailFuel) evmAfterHead)
                                  tailTrace result :=
                              hRestCont hTailRun
                            have hFull := hHeadCont hRestAndTail
                            simpa [Nat.add_assoc] using hFull

theorem compilerOpenFunctionsAssignReturnedTops_stackPrefixSuffix_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {values suffix : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values source.vars =
        some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (compiledStmts, finalCtx))
    (hPrefixRel :
      StackPrefixSuffixRel layout source values.reverse suffix state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ assignFuel evmAfter,
      assignFuel = 2 * targets.length ∧
      StackPrefixSuffixRel layout (source.withVars store') [] suffix evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (assignFuel + tailFuel) state)
          tailTrace result := by
  have hAssignReverse :
      Functions.Source.Store.assignMany targets.reverse values.reverse
          source.vars =
        some store' :=
    Functions.Source.Store.assignMany_reverse_of_run hAssign hTargetsNoDup
  have hTargetsReverse :
      ∀ {name : Name}, name ∈ targets.reverse →
        ∃ idx, layout[idx]? = some name ∧
          targets.reverse.length + idx ≤ 16 := by
    intro name hMem
    rcases hTargets (name := name) (by simpa using hMem) with
      ⟨idx, hName, hBound⟩
    exact ⟨idx, hName, by simpa using hBound⟩
  rcases
      compilerOpenFunctionsAssignReturnedTopsRev_stackPrefixSuffix_openRunNResult_continue_fallthrough_of_compileOpen
        (layout := layout) (source := source) (state := state) (ctx := ctx)
        (finalCtx := finalCtx) (names := targets.reverse)
        (values := values.reverse) (suffix := suffix) (store' := store')
        (compiledStmts := compiledStmts) (structuredCtx := structuredCtx)
        (supply := supply) hCtxLayout hNoDup hTargetsReverse hAssignReverse
        (by simpa [Functions.Lower.assignReturnedTops] using hCompileBlock)
        hPrefixRel program segment hPc with
    ⟨assignFuel, evmAfter, hFuel, hRel, hAfterPc, hCont⟩
  exact
    ⟨assignFuel, evmAfter, by simpa using hFuel, hRel, hAfterPc, hCont⟩

theorem compilerOpenFunctionsAssignReturnedTopsRev_stackPrefixSuffixErased_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {names : List Name} {values suffix : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ names →
        ∃ idx, layout[idx]? = some name ∧ names.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany names values source.vars = some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTopsRev names } =
        some (compiledStmts, finalCtx))
    (hPrefixRel :
      StackPrefixSuffixErasedRel layout source values suffix state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ assignFuel evmAfter,
      assignFuel = 2 * names.length ∧
      StackPrefixSuffixErasedRel layout (source.withVars store') [] suffix
        evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (assignFuel + tailFuel) state)
          tailTrace result := by
  let sourceExact : Objects.Source.State :=
    { source with shared := state.toSharedState }
  have hExactPrefix :
      StackPrefixSuffixRel layout sourceExact values suffix state := by
    simpa [sourceExact] using
      StackPrefixSuffixErasedRel.exactWithTargetShared hPrefixRel
  have hAssignExact :
      Functions.Source.Store.assignMany names values sourceExact.vars =
        some store' := by
    simpa [sourceExact] using hAssign
  rcases
      compilerOpenFunctionsAssignReturnedTopsRev_stackPrefixSuffix_openRunNResult_continue_fallthrough_of_compileOpen
        (layout := layout) (source := sourceExact) (state := state)
        (ctx := ctx) (finalCtx := finalCtx) (names := names)
        (values := values) (suffix := suffix) (store' := store')
        (compiledStmts := compiledStmts) (structuredCtx := structuredCtx)
        (supply := supply) hCtxLayout hNoDup hTargets hAssignExact
        hCompileBlock hExactPrefix program segment hPc with
    ⟨assignFuel, evmAfter, hFuel, hExactAfter, hAfterPc, hCont⟩
  have hEraseFinal :
      Structured.Preservation.eraseControl state =
        Structured.Preservation.eraseControl
          { state with toSharedState := (source.withVars store').shared } := by
    simpa [Locals.Source.State.withVars] using hPrefixRel.1
  have hErasedAfter :
      StackPrefixSuffixErasedRel layout (source.withVars store') [] suffix
        evmAfter := by
    exact
      StackPrefixSuffixErasedRel.of_exactWithTargetShared
        (source := source.withVars store') (start := state)
        hEraseFinal
        (by
          simpa [sourceExact, Locals.Source.State.withVars] using hExactAfter)
  exact ⟨assignFuel, evmAfter, hFuel, hErasedAfter, hAfterPc, hCont⟩

theorem compilerOpenFunctionsAssignReturnedTops_stackPrefixSuffixErased_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {source : Objects.Source.State}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {values suffix : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values source.vars =
        some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (compiledStmts, finalCtx))
    (hPrefixRel :
      StackPrefixSuffixErasedRel layout source values.reverse suffix state)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ assignFuel evmAfter,
      assignFuel = 2 * targets.length ∧
      StackPrefixSuffixErasedRel layout (source.withVars store') [] suffix
        evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (assignFuel + tailFuel) state)
          tailTrace result := by
  let sourceExact : Objects.Source.State :=
    { source with shared := state.toSharedState }
  have hExactPrefix :
      StackPrefixSuffixRel layout sourceExact values.reverse suffix state := by
    simpa [sourceExact] using
      StackPrefixSuffixErasedRel.exactWithTargetShared hPrefixRel
  have hAssignExact :
      Functions.Source.Store.assignMany targets values sourceExact.vars =
        some store' := by
    simpa [sourceExact] using hAssign
  rcases
      compilerOpenFunctionsAssignReturnedTops_stackPrefixSuffix_openRunNResult_continue_fallthrough_of_compileOpen
        (layout := layout) (source := sourceExact) (state := state)
        (ctx := ctx) (finalCtx := finalCtx) (targets := targets)
        (values := values) (suffix := suffix) (store' := store')
        (compiledStmts := compiledStmts) (structuredCtx := structuredCtx)
        (supply := supply) hCtxLayout hNoDup hTargetsNoDup hTargets
        hAssignExact hCompileBlock hExactPrefix program segment hPc with
    ⟨assignFuel, evmAfter, hFuel, hExactAfter, hAfterPc, hCont⟩
  have hEraseFinal :
      Structured.Preservation.eraseControl state =
        Structured.Preservation.eraseControl
          { state with toSharedState := (source.withVars store').shared } := by
    simpa [Locals.Source.State.withVars] using hPrefixRel.1
  have hErasedAfter :
      StackPrefixSuffixErasedRel layout (source.withVars store') [] suffix
        evmAfter := by
    exact
      StackPrefixSuffixErasedRel.of_exactWithTargetShared
        (source := source.withVars store') (start := state)
        hEraseFinal
        (by
          simpa [sourceExact, Locals.Source.State.withVars] using hExactAfter)
  exact ⟨assignFuel, evmAfter, hFuel, hErasedAfter, hAfterPc, hCont⟩

theorem compilerOpenFunctionsAssignReturnedTops_frameStateRel_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State} {base : Locals.RunState}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {values tokens : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values source.vars =
        some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (compiledStmts, finalCtx))
    (hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns source base)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel
        (base.withEVM
          { base.evm with stack := values.reverse ++ base.evm.stack })
        state tokens)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment) :
    ∃ assignFuel evmAfter suffix,
      assignFuel = 2 * targets.length ∧
      StackPrefixSuffixErasedRel layout (source.withVars store') [] suffix
        evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (assignFuel + tailFuel) state)
          tailTrace result := by
  rcases
      StackPrefixSuffixErasedRel.of_frameStateRel_stateRel
        (layout := layout) (hiddenReturns := hiddenReturns)
        (source := source) (base := base) (target := state)
        (values := values) (tokens := tokens) hBaseRel hFrameRel with
    ⟨suffix, hPrefixRel⟩
  rcases
      compilerOpenFunctionsAssignReturnedTops_stackPrefixSuffixErased_openRunNResult_continue_fallthrough_of_compileOpen
        (layout := layout) (source := source) (state := state)
        (ctx := ctx) (finalCtx := finalCtx) (targets := targets)
        (values := values) (suffix := suffix) (store' := store')
        (compiledStmts := compiledStmts) (structuredCtx := structuredCtx)
        (supply := supply) hCtxLayout hNoDup hTargetsNoDup hTargets
        hAssign hCompileBlock hPrefixRel program segment hPc with
    ⟨assignFuel, evmAfter, hFuel, hAfterRel, hAfterPc, hCont⟩
  exact ⟨assignFuel, evmAfter, suffix, hFuel, hAfterRel, hAfterPc, hCont⟩

theorem compilerOpenFunctionsAssignReturnedTops_returnLabel_frameStateRel_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {source : Objects.Source.State} {base : Locals.RunState}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {values tokens : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {label : Assembly.Label} {pre post : Assembly.Program}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values source.vars =
        some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (compiledStmts, finalCtx))
    (hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns source base)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel
        (base.withEVM
          { base.evm with stack := values.reverse ++ base.evm.stack })
        state tokens)
    (hFit : Structured.Preservation.PCFits pre)
    (segment :
      Structured.Preservation.CodeSegment
        (pre ++ [Assembly.Instr.label label] ++ post)
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Assembly.Program.pcAfter pre)
    (hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment =
        Assembly.Program.pcAfter (pre ++ [Assembly.Instr.label label])) :
    ∃ labelAssignFuel evmAfter suffix,
      labelAssignFuel = 2 * targets.length + 1 ∧
      StackPrefixSuffixErasedRel layout (source.withVars store') [] suffix
        evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ [Assembly.Instr.label label] ++ post)
            tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ [Assembly.Instr.label label] ++ post)
            (labelAssignFuel + tailFuel) state)
          tailTrace result := by
  let returnSource :=
    base.withEVM
      { base.evm with stack := values.reverse ++ base.evm.stack }
  rcases
      Structured.Preservation.Frame.StateRel.label_stepResult_at
        (label := label) (pre := pre) (post := post)
        (source := returnSource) (target := state) (tokens := tokens)
        hFit hPc hFrameRel with
    ⟨afterLabel, hLabelStep, hRelAfterLabel, hPcAfterLabel⟩
  have hAt :
      Assembly.Program.instrAtPc
          (pre ++ [Assembly.Instr.label label] ++ post) state.pc.toNat =
        some (Assembly.Program.byteLength pre, Assembly.Instr.label label) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post (Assembly.Instr.label label) 0
  have hAssignPc :
      afterLabel.pc = Structured.Preservation.CodeSegment.startPc segment := by
    rw [hPcAfterLabel, hSegmentStart]
  rcases
      compilerOpenFunctionsAssignReturnedTops_frameStateRel_openRunNResult_continue_fallthrough_of_compileOpen
        (layout := layout) (hiddenReturns := hiddenReturns)
        (source := source) (base := base) (state := afterLabel)
        (ctx := ctx) (finalCtx := finalCtx) (targets := targets)
        (values := values) (tokens := tokens) (store' := store')
        (compiledStmts := compiledStmts) (structuredCtx := structuredCtx)
        (supply := supply) hCtxLayout hNoDup hTargetsNoDup hTargets
        hAssign hCompileBlock hBaseRel hRelAfterLabel
        (program := pre ++ [Assembly.Instr.label label] ++ post)
        segment hAssignPc with
    ⟨assignFuel, evmAfter, suffix, hFuel, hAfterRel, hAfterPc, hAssignCont⟩
  refine ⟨assignFuel + 1, evmAfter, suffix, ?_, hAfterRel, hAfterPc, ?_⟩
  · omega
  intro tailFuel tailTrace result hTail
  have hAssignRun := hAssignCont hTail
  have hFull :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (pre ++ [Assembly.Instr.label label] ++ post)
          ((assignFuel + tailFuel) + 1) state)
        tailTrace result :=
    OpenAssembly.Source.openRunNResult_current_no_call_running_continue_of_current_instr
      hAt (by simp [Assembly.Instr.usesCallCreate]) hLabelStep hAssignRun
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFull

theorem compilerOpenFunctionsAssignReturnedTops_returnLabel_attachedFrameStateRel_openRunNResult_continue_fallthrough_of_compileOpen
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {sourceBeforeCall sourceAfterCall : Objects.Source.State}
    {base bodyState returned : Locals.RunState}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {values tokens stack : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {frame : Structured.ReturnDest}
    {label : Assembly.Label} {pre post : Assembly.Program}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values sourceAfterCall.vars =
        some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (compiledStmts, finalCtx))
    (hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns sourceBeforeCall
        base)
    (hVars : sourceAfterCall.vars = sourceBeforeCall.vars)
    (hReturned :
      Functions.SourceDirect.ReturnedStackRel (frame :: hiddenReturns)
        sourceAfterCall values bodyState)
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hFrameStack : frame.callerStack = base.evm.stack)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel
        (returned.withEVM { bodyState.evm with stack := stack })
        state tokens)
    (hFit : Structured.Preservation.PCFits pre)
    (segment :
      Structured.Preservation.CodeSegment
        (pre ++ [Assembly.Instr.label label] ++ post)
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Assembly.Program.pcAfter pre)
    (hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment =
        Assembly.Program.pcAfter (pre ++ [Assembly.Instr.label label])) :
    ∃ labelAssignFuel evmAfter suffix,
      labelAssignFuel = 2 * targets.length + 1 ∧
      StackPrefixSuffixErasedRel layout (sourceAfterCall.withVars store') []
        suffix evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ [Assembly.Instr.label label] ++ post)
            tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult
            (pre ++ [Assembly.Instr.label label] ++ post)
            (labelAssignFuel + tailFuel) state)
          tailTrace result := by
  let returnSource :=
    returned.withEVM { bodyState.evm with stack := stack }
  rcases
      Structured.Preservation.Frame.StateRel.label_stepResult_at
        (label := label) (pre := pre) (post := post)
        (source := returnSource) (target := state) (tokens := tokens)
        hFit hPc hFrameRel with
    ⟨afterLabel, hLabelStep, hRelAfterLabel, hPcAfterLabel⟩
  have hAt :
      Assembly.Program.instrAtPc
          (pre ++ [Assembly.Instr.label label] ++ post) state.pc.toNat =
        some (Assembly.Program.byteLength pre, Assembly.Instr.label label) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post (Assembly.Instr.label label) 0
  have hAssignPc :
      afterLabel.pc = Structured.Preservation.CodeSegment.startPc segment := by
    rw [hPcAfterLabel, hSegmentStart]
  rcases
      StackPrefixSuffixErasedRel.of_attached_returnedFrameStateRel_stateRel
        (layout := layout) (hiddenReturns := hiddenReturns)
        (sourceBeforeCall := sourceBeforeCall)
        (sourceAfterCall := sourceAfterCall)
        (base := base) (bodyState := bodyState)
        (returned := returned) (target := afterLabel) (values := values)
        (tokens := tokens) (stack := stack) (frame := frame)
        hBaseRel hVars hReturned hAttach hFrameStack hRelAfterLabel with
    ⟨suffix, hPrefixRel⟩
  rcases
      compilerOpenFunctionsAssignReturnedTops_stackPrefixSuffixErased_openRunNResult_continue_fallthrough_of_compileOpen
        (layout := layout) (source := sourceAfterCall) (state := afterLabel)
        (ctx := ctx) (finalCtx := finalCtx) (targets := targets)
        (values := values) (suffix := suffix) (store' := store')
        (compiledStmts := compiledStmts) (structuredCtx := structuredCtx)
        (supply := supply) hCtxLayout hNoDup hTargetsNoDup hTargets
        hAssign hCompileBlock hPrefixRel
        (program := pre ++ [Assembly.Instr.label label] ++ post)
        segment hAssignPc with
    ⟨assignFuel, evmAfter, hFuel, hAfterRel, hAfterPc, hAssignCont⟩
  refine ⟨assignFuel + 1, evmAfter, suffix, ?_, hAfterRel, hAfterPc, ?_⟩
  · omega
  intro tailFuel tailTrace result hTail
  have hAssignRun := hAssignCont hTail
  have hFull :
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult
          (pre ++ [Assembly.Instr.label label] ++ post)
          ((assignFuel + tailFuel) + 1) state)
        tailTrace result :=
    OpenAssembly.Source.openRunNResult_current_no_call_running_continue_of_current_instr
      hAt (by simp [Assembly.Instr.usesCallCreate]) hLabelStep hAssignRun
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFull

theorem compilerOpenFunctionsAssignReturnedTops_callSiteReturn_attachedFrameStateRel_openRunNResult_continue_of_compileOpen
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {sourceBeforeCall sourceAfterCall : Objects.Source.State}
    {base bodyState returned : Locals.RunState}
    {state : EvmYul.EVM.State} {ctx finalCtx : Locals.Ctx}
    {targets : List Name} {values tokens stack : List Word}
    {store' : Functions.Source.Store}
    {compiledStmts : List Expressions.Stmt}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {frame : Structured.ReturnDest}
    {proc : Structured.Proc} {site : Structured.CallSite}
    {args : EvmYul.Stack Word} {token : Word}
    {asm : Assembly.Program} {returnDest : Nat}
    (callSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args token site.returnLabel))
    (assignSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hAssignStart :
      Structured.Preservation.CodeSegment.startPc assignSegment =
        Structured.Preservation.CodeSegment.fallthroughPc callSeg)
    (hExact : Structured.Preservation.ExactLabels asm)
    (hReturnLabel :
      Assembly.Program.labelPc asm site.returnLabel = some returnDest)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values sourceAfterCall.vars =
        some store')
    (hCompileBlock :
      Locals.Block.compileOpen ctx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (compiledStmts, finalCtx))
    (hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns sourceBeforeCall
        base)
    (hVars : sourceAfterCall.vars = sourceBeforeCall.vars)
    (hReturned :
      Functions.SourceDirect.ReturnedStackRel (frame :: hiddenReturns)
        sourceAfterCall values bodyState)
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hFrameStack : frame.callerStack = base.evm.stack)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel
        (returned.withEVM { bodyState.evm with stack := stack })
        state tokens)
    (hPc : state.pc = EvmYul.UInt256.ofNat returnDest) :
    ∃ labelAssignFuel evmAfter suffix,
      labelAssignFuel = 2 * targets.length + 1 ∧
      StackPrefixSuffixErasedRel layout (sourceAfterCall.withVars store') []
        suffix evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc assignSegment ∧
      ∀ {tailFuel : Nat} {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm
            (labelAssignFuel + tailFuel) state)
          tailTrace result := by
  let jumpCode :=
    Structured.Preservation.ProcedurePreservation.callJumpCode proc args token
  let returnCode : Assembly.Program := [Assembly.Instr.label site.returnLabel]
  let expandedAsm := callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post
  have hCallAsm : asm = expandedAsm := by
    calc
      asm =
          callSeg.pre ++
            Structured.Preservation.ProcedurePreservation.callSiteCode
              proc args token site.returnLabel ++
            callSeg.post := callSeg.hAsm
      _ = expandedAsm := by
            simp [expandedAsm, jumpCode, returnCode,
              Structured.Preservation.ProcedurePreservation.callSiteCode,
              List.append_assoc]
  have hCallFits :
      Structured.Preservation.AssemblyProgram.PCFitsFrom callSeg.pre
        (jumpCode ++ returnCode) := by
    simpa [jumpCode, returnCode,
      Structured.Preservation.ProcedurePreservation.callSiteCode,
      List.append_assoc] using callSeg.hFits
  have hFitsAfterJump :
      Structured.Preservation.AssemblyProgram.PCFitsFrom
        (callSeg.pre ++ jumpCode) returnCode :=
    Structured.Preservation.AssemblyProgram.PCFitsFrom.right
      (pre := callSeg.pre) (first := jumpCode) (second := returnCode)
      hCallFits
  have hReturnDest :
      returnDest = Assembly.Program.byteLength (callSeg.pre ++ jumpCode) := by
    have hHere :
        Assembly.Program.labelPc asm site.returnLabel =
          some (Assembly.Program.byteLength (callSeg.pre ++ jumpCode)) := by
      have hHereExpanded :=
        hExact.labelPc_at (callSeg.pre ++ jumpCode) site.returnLabel
          callSeg.post
          (by
            simpa [expandedAsm, jumpCode, returnCode] using hCallAsm)
      simpa [expandedAsm, jumpCode, returnCode] using hHereExpanded
    rw [hReturnLabel] at hHere
    cases hHere
    rfl
  have hPc' :
      state.pc = Assembly.Program.pcAfter (callSeg.pre ++ jumpCode) := by
    simpa [Assembly.Program.pcAfter, hReturnDest] using hPc
  let assignSegmentExpanded :
      Structured.Preservation.CodeSegment expandedAsm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_asm hCallAsm assignSegment
  have hAssignFallthrough :
      Structured.Preservation.CodeSegment.fallthroughPc assignSegmentExpanded =
        Structured.Preservation.CodeSegment.fallthroughPc assignSegment := by
    cases assignSegment with
    | mk pre post hAsm hFits =>
        simp [assignSegmentExpanded,
          Structured.Preservation.CodeSegment.cast_asm,
          Structured.Preservation.CodeSegment.fallthroughPc]
  have hAssignSegmentStart :
      Structured.Preservation.CodeSegment.startPc assignSegmentExpanded =
        Assembly.Program.pcAfter
          ((callSeg.pre ++ jumpCode) ++ [Assembly.Instr.label site.returnLabel]) := by
    calc
      Structured.Preservation.CodeSegment.startPc assignSegmentExpanded =
          Structured.Preservation.CodeSegment.startPc assignSegment := by
            simp [assignSegmentExpanded,
              Structured.Preservation.CodeSegment.cast_asm,
              Structured.Preservation.CodeSegment.startPc]
      _ = Structured.Preservation.CodeSegment.fallthroughPc callSeg :=
            hAssignStart
      _ = Assembly.Program.pcAfter
            (callSeg.pre ++
              Structured.Preservation.ProcedurePreservation.callSiteCode
                proc args token site.returnLabel) := by
            rfl
      _ = Assembly.Program.pcAfter
            ((callSeg.pre ++ jumpCode) ++
              [Assembly.Instr.label site.returnLabel]) := by
            simp [jumpCode,
              Structured.Preservation.ProcedurePreservation.callSiteCode,
              List.append_assoc]
  rcases
      compilerOpenFunctionsAssignReturnedTops_returnLabel_attachedFrameStateRel_openRunNResult_continue_fallthrough_of_compileOpen
        (layout := layout) (hiddenReturns := hiddenReturns)
        (sourceBeforeCall := sourceBeforeCall)
        (sourceAfterCall := sourceAfterCall)
        (base := base) (bodyState := bodyState)
        (returned := returned) (state := state) (ctx := ctx)
        (finalCtx := finalCtx) (targets := targets) (values := values)
        (tokens := tokens) (stack := stack) (store' := store')
        (compiledStmts := compiledStmts) (structuredCtx := structuredCtx)
        (supply := supply) (frame := frame) (label := site.returnLabel)
        (pre := callSeg.pre ++ jumpCode) (post := callSeg.post)
        hCtxLayout hNoDup hTargetsNoDup hTargets hAssign hCompileBlock
        hBaseRel hVars hReturned hAttach hFrameStack hFrameRel
        (Structured.Preservation.AssemblyProgram.PCFitsFrom.start
          hFitsAfterJump)
        assignSegmentExpanded hPc' hAssignSegmentStart with
    ⟨labelAssignFuel, evmAfter, suffix, hFuel, hAfterRel, hAfterPc, hCont⟩
  refine ⟨labelAssignFuel, evmAfter, suffix, hFuel, hAfterRel, ?_, ?_⟩
  · simpa [hAssignFallthrough] using hAfterPc
  · intro tailFuel tailTrace result hTail
    have hTailExpanded :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult expandedAsm tailFuel evmAfter)
          tailTrace result := by
      simpa [← hCallAsm] using hTail
    have hRunExpanded := hCont hTailExpanded
    have hRunExpanded' :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult expandedAsm
            (labelAssignFuel + tailFuel) state)
          tailTrace result := by
      simpa [expandedAsm, jumpCode, returnCode, List.append_assoc] using
        hRunExpanded
    simpa [← hCallAsm] using hRunExpanded'

theorem openRunNResult_callSite_body_regular_then_return_assign_continue
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {sourceBeforeCall sourceAfterCall : Objects.Source.State}
    {callSource callerBase bodyState returned : Locals.RunState}
    {program : Structured.Program} {proc : Structured.Proc}
    {bodySupply dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite} {site : Structured.CallSite}
    {returnDest : Nat} {bodyCtx : Structured.CompileContext}
    {target afterBody : EvmYul.EVM.State}
    {args callerStack stack : EvmYul.Stack Word}
    {frame : Structured.ReturnDest}
    {tokens : List Word} {token : Word}
    {asm : Assembly.Program}
    {targets : List Name} {values : List Word}
    {store' : Functions.Source.Store}
    {assignStmts : List Expressions.Stmt}
    {assignFinalCtx : Locals.Ctx} {assignCtx : Locals.Ctx}
    {assignStructuredCtx : Structured.CompileContext}
    {assignSupply : Structured.LabelSupply}
    {bodyFuel tailFuel : Nat}
    {bodyTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (callSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args token site.returnLabel))
    (procSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.procSegment program
          proc bodySupply dispatchSupply sites))
    (assignSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured assignStmts }
          assignStructuredCtx assignSupply).code)
    (hAssignStart :
      Structured.Preservation.CodeSegment.startPc assignSegment =
        Structured.Preservation.CodeSegment.fallthroughPc callSeg)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc callSource.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16)
    (hPc :
      target.pc = Structured.Preservation.CodeSegment.startPc callSeg)
    (hCallRel :
      Structured.Preservation.Frame.StateRel callSource target tokens)
    (hBodyRun :
      ∀ entryTarget : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          ((callSource.withEVM { callSource.evm with stack := args }).pushReturn
            callerStack proc.retc)
          entryTarget (token :: tokens) →
        entryTarget.pc =
          Structured.Preservation.CodeSegment.startPc
            (codeSegment_procSegment_bodyCode procSeg) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm bodyFuel entryTarget)
          bodyTrace (.ok (.running afterBody)))
    (hBodyRel :
      Structured.Preservation.CompiledOutcomeRel asm bodyCtx
        (Structured.Preservation.CodeSegment.fallthroughPc
          (codeSegment_procSegment_bodyCode procSeg))
        (Structured.Outcome.regular bodyState) (.running afterBody)
        (token :: tokens))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hReturns : bodyState.returns = frame :: returned.returns)
    (hRetc : bodyState.evm.stack.length = proc.retc)
    (hMem :
      site ∈ sites.filter (Structured.CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (Structured.CallSite.forProc proc.name)).map
        Structured.CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hExact : Structured.Preservation.ExactLabels asm)
    (hReturnLabel :
      Assembly.Program.labelPc asm site.returnLabel = some returnDest)
    (hCtxLayout : assignCtx.layout = layout)
    (hLayoutNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values sourceAfterCall.vars =
        some store')
    (hCompileAssign :
      Locals.Block.compileOpen assignCtx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (assignStmts, assignFinalCtx))
    (hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns sourceBeforeCall
        callerBase)
    (hVars : sourceAfterCall.vars = sourceBeforeCall.vars)
    (hReturned :
      Functions.SourceDirect.ReturnedStackRel (frame :: hiddenReturns)
        sourceAfterCall values bodyState)
    (hFrameStack : frame.callerStack = callerBase.evm.stack)
    (hTail :
      ∀ evmAfter suffix,
        StackPrefixSuffixErasedRel layout (sourceAfterCall.withVars store')
          [] suffix evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc assignSegment →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm tailFuel evmAfter)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult asm
        ((Structured.Preservation.ProcedurePreservation.callJumpCode
          proc args token).length +
          ((bodyFuel +
            (returnDispatchSelectedTableFuel proc.retc
              (sites.filter (Structured.CallSite.forProc proc.name)) site
              ((2 * targets.length + 1) + tailFuel) + 1)) + 1))
        target)
      (bodyTrace ++ tailTrace) result := by
  exact
    openRunNResult_callSite_body_regular_then_exit_dispatch_continue
      (program := program) (proc := proc) (bodySupply := bodySupply)
      (dispatchSupply := dispatchSupply) (sites := sites) (site := site)
      (returnDest := returnDest) (bodyCtx := bodyCtx)
      (source := callSource) (bodyState := bodyState) (returned := returned)
      (target := target) (afterBody := afterBody) (args := args)
      (callerStack := callerStack) (stack := stack) (frame := frame)
      (tokens := tokens) (token := token) (asm := asm)
      (bodyFuel := bodyFuel)
      (tailFuel := (2 * targets.length + 1) + tailFuel)
      (bodyTrace := bodyTrace) (tailTrace := tailTrace) (result := result)
      callSeg procSeg hSplit hArgBound hPc hCallRel hBodyRun hBodyRel
      hAttach hReturns hRetc hMem hNoDup hToken hBound hExact hReturnLabel
      (by
        intro final hFinalRel hFinalPc
        rcases
            compilerOpenFunctionsAssignReturnedTops_callSiteReturn_attachedFrameStateRel_openRunNResult_continue_of_compileOpen
              (layout := layout) (hiddenReturns := hiddenReturns)
              (sourceBeforeCall := sourceBeforeCall)
              (sourceAfterCall := sourceAfterCall) (base := callerBase)
              (bodyState := bodyState) (returned := returned)
              (state := final) (ctx := assignCtx)
              (finalCtx := assignFinalCtx) (targets := targets)
              (values := values) (tokens := tokens) (stack := stack)
              (store' := store') (compiledStmts := assignStmts)
              (structuredCtx := assignStructuredCtx)
              (supply := assignSupply) (frame := frame)
              (proc := proc) (site := site) (args := args) (token := token)
              (asm := asm) (returnDest := returnDest)
              callSeg assignSegment hAssignStart hExact hReturnLabel
              hCtxLayout hLayoutNoDup hTargetsNoDup hTargets hAssign
              hCompileAssign hBaseRel hVars hReturned hAttach hFrameStack
              hFinalRel hFinalPc with
          ⟨labelAssignFuel, evmAfter, suffix, hFuel, hAfterRel, hAfterPc,
            hCont⟩
        have hTailRun := hTail evmAfter suffix hAfterRel hAfterPc
        have hRun := hCont hTailRun
        simpa [hFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hRun)

theorem openRunNResult_callSite_body_leave_then_return_assign_continue
    {layout : List Name} {hiddenReturns : List Structured.ReturnDest}
    {sourceBeforeCall sourceAfterCall : Objects.Source.State}
    {callSource callerBase bodyState returned : Locals.RunState}
    {program : Structured.Program} {proc : Structured.Proc}
    {bodySupply dispatchSupply : Structured.LabelSupply}
    {sites : List Structured.CallSite} {site : Structured.CallSite}
    {returnDest : Nat} {bodyCtx : Structured.CompileContext}
    {target afterBody : EvmYul.EVM.State}
    {args callerStack stack : EvmYul.Stack Word}
    {frame : Structured.ReturnDest}
    {tokens : List Word} {token : Word}
    {asm : Assembly.Program}
    {targets : List Name} {values : List Word}
    {store' : Functions.Source.Store}
    {assignStmts : List Expressions.Stmt}
    {assignFinalCtx : Locals.Ctx} {assignCtx : Locals.Ctx}
    {assignStructuredCtx : Structured.CompileContext}
    {assignSupply : Structured.LabelSupply}
    {bodyFuel tailFuel : Nat}
    {bodyTrace tailTrace : OpenExternal.OpenTrace}
    {result : Except EVMException Assembly.StepResult}
    (callSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.callSiteCode
          proc args token site.returnLabel))
    (procSeg :
      Structured.Preservation.CodeSegment asm
        (Structured.Preservation.ProcedurePreservation.procSegment program
          proc bodySupply dispatchSupply sites))
    (assignSegment :
      Structured.Preservation.CodeSegment asm
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured assignStmts }
          assignStructuredCtx assignSupply).code)
    (hAssignStart :
      Structured.Preservation.CodeSegment.startPc assignSegment =
        Structured.Preservation.CodeSegment.fallthroughPc callSeg)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc callSource.evm.stack =
        some (args, callerStack))
    (hArgBound : args.length ≤ 16)
    (hPc :
      target.pc = Structured.Preservation.CodeSegment.startPc callSeg)
    (hCallRel :
      Structured.Preservation.Frame.StateRel callSource target tokens)
    (hBodyRun :
      ∀ entryTarget : EvmYul.EVM.State,
        Structured.Preservation.Frame.StateRel
          ((callSource.withEVM { callSource.evm with stack := args }).pushReturn
            callerStack proc.retc)
          entryTarget (token :: tokens) →
        entryTarget.pc =
          Structured.Preservation.CodeSegment.startPc
            (codeSegment_procSegment_bodyCode procSeg) →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm bodyFuel entryTarget)
          bodyTrace (.ok (.running afterBody)))
    (hBodyRel :
      Structured.Preservation.CompiledOutcomeRel asm bodyCtx
        (Structured.Preservation.CodeSegment.fallthroughPc
          (codeSegment_procSegment_bodyCode procSeg))
        (Structured.Outcome.leave bodyState) (.running afterBody)
        (token :: tokens))
    (hCtxLeave :
      bodyCtx.leaveLabel? = some (Structured.ProcLabel.exit proc.name))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hReturns : bodyState.returns = frame :: returned.returns)
    (hRetc : bodyState.evm.stack.length = proc.retc)
    (hMem :
      site ∈ sites.filter (Structured.CallSite.forProc proc.name))
    (hNoDup :
      ((sites.filter (Structured.CallSite.forProc proc.name)).map
        Structured.CallSite.token).Nodup)
    (hToken : site.token = token)
    (hBound : proc.retc < 16)
    (hExact : Structured.Preservation.ExactLabels asm)
    (hReturnLabel :
      Assembly.Program.labelPc asm site.returnLabel = some returnDest)
    (hCtxLayout : assignCtx.layout = layout)
    (hLayoutNoDup : layout.Nodup)
    (hTargetsNoDup : targets.Nodup)
    (hTargets :
      ∀ {name : Name}, name ∈ targets →
        ∃ idx, layout[idx]? = some name ∧ targets.length + idx ≤ 16)
    (hAssign :
      Functions.Source.Store.assignMany targets values sourceAfterCall.vars =
        some store')
    (hCompileAssign :
      Locals.Block.compileOpen assignCtx
          { stmts := Functions.Lower.assignReturnedTops targets } =
        some (assignStmts, assignFinalCtx))
    (hBaseRel :
      Functions.SourceDirect.StateRel layout hiddenReturns sourceBeforeCall
        callerBase)
    (hVars : sourceAfterCall.vars = sourceBeforeCall.vars)
    (hReturned :
      Functions.SourceDirect.ReturnedStackRel (frame :: hiddenReturns)
        sourceAfterCall values bodyState)
    (hFrameStack : frame.callerStack = callerBase.evm.stack)
    (hTail :
      ∀ evmAfter suffix,
        StackPrefixSuffixErasedRel layout (sourceAfterCall.withVars store')
          [] suffix evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc assignSegment →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm tailFuel evmAfter)
          tailTrace result) :
    OpenExternal.OpenResultResolves
      (OpenAssembly.Source.openRunNResult asm
        ((Structured.Preservation.ProcedurePreservation.callJumpCode
          proc args token).length +
          ((bodyFuel +
            (returnDispatchSelectedTableFuel proc.retc
              (sites.filter (Structured.CallSite.forProc proc.name)) site
              ((2 * targets.length + 1) + tailFuel) + 1)) + 1))
        target)
      (bodyTrace ++ tailTrace) result := by
  exact
    openRunNResult_callSite_body_leave_then_exit_dispatch_continue
      (program := program) (proc := proc) (bodySupply := bodySupply)
      (dispatchSupply := dispatchSupply) (sites := sites) (site := site)
      (returnDest := returnDest) (bodyCtx := bodyCtx)
      (source := callSource) (bodyState := bodyState) (returned := returned)
      (target := target) (afterBody := afterBody) (args := args)
      (callerStack := callerStack) (stack := stack) (frame := frame)
      (tokens := tokens) (token := token) (asm := asm)
      (bodyFuel := bodyFuel)
      (tailFuel := (2 * targets.length + 1) + tailFuel)
      (bodyTrace := bodyTrace) (tailTrace := tailTrace) (result := result)
      callSeg procSeg hSplit hArgBound hPc hCallRel hBodyRun hBodyRel
      hCtxLeave hAttach hReturns hRetc hMem hNoDup hToken hBound hExact
      hReturnLabel
      (by
        intro final hFinalRel hFinalPc
        rcases
            compilerOpenFunctionsAssignReturnedTops_callSiteReturn_attachedFrameStateRel_openRunNResult_continue_of_compileOpen
              (layout := layout) (hiddenReturns := hiddenReturns)
              (sourceBeforeCall := sourceBeforeCall)
              (sourceAfterCall := sourceAfterCall) (base := callerBase)
              (bodyState := bodyState) (returned := returned)
              (state := final) (ctx := assignCtx)
              (finalCtx := assignFinalCtx) (targets := targets)
              (values := values) (tokens := tokens) (stack := stack)
              (store' := store') (compiledStmts := assignStmts)
              (structuredCtx := assignStructuredCtx)
              (supply := assignSupply) (frame := frame)
              (proc := proc) (site := site) (args := args) (token := token)
              (asm := asm) (returnDest := returnDest)
              callSeg assignSegment hAssignStart hExact hReturnLabel
              hCtxLayout hLayoutNoDup hTargetsNoDup hTargets hAssign
              hCompileAssign hBaseRel hVars hReturned hAttach hFrameStack
              hFinalRel hFinalPc with
          ⟨labelAssignFuel, evmAfter, suffix, hFuel, hAfterRel, hAfterPc,
            hCont⟩
        have hTailRun := hTail evmAfter suffix hAfterRel hAfterPc
        have hRun := hCont hTailRun
        simpa [hFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hRun)

theorem compilerOpenLocalsExpr_evalOne_assign_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {expr : Locals.Expr 1}
    {ctx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {valueCode : Structured.Code}
    {name : Name} {idx : Nat} {value : Word}
    {swapOp : Structured.BasicOp}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some valueCode)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.evalOne
          prim expr compiler)
        trace (.ok (compilerAfter, value))) :
    ∃ evmAfter : EvmYul.EVM.State,
      Locals.SourceLowering.StackPrefixRel layout
        (compilerAfter.withVars
          (Locals.Source.Store.insert compilerAfter.vars name value))
        [] evmAfter ∧
      evmAfter.pc =
        Structured.Preservation.CodeSegment.fallthroughPc segment ∧
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {result : Except EVMException Assembly.StepResult},
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
          tailTrace result →
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            ((valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]).length +
              tailFuel) state)
          (trace ++ tailTrace) result := by
  let assignTail : Structured.Code :=
    [Structured.BasicInstr.op swapOp,
      Structured.BasicInstr.op Structured.BasicOp.pop]
  have hAssemblyCode :
      (valueCode ++ assignTail).toAssembly =
        valueCode.toAssembly ++ assignTail.toAssembly := by
    simp [assignTail, Structured.Code.toAssembly]
  let appendSegment :
      Structured.Preservation.CodeSegment program
        (valueCode.toAssembly ++ assignTail.toAssembly) :=
    Structured.Preservation.CodeSegment.cast_code hAssemblyCode segment
  let valueSegment :
      Structured.Preservation.CodeSegment program valueCode.toAssembly :=
    Structured.Preservation.CodeSegment.left appendSegment
  let tailSegmentRaw :
      Structured.Preservation.CodeSegment program assignTail.toAssembly :=
    Structured.Preservation.CodeSegment.right appendSegment
  have hTailAssembly :
      assignTail.toAssembly =
        [Assembly.Instr.prim swapOp.toPrimOp] ++
          [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp] := by
    simp [assignTail, Structured.Code.toAssembly,
      Structured.BasicInstr.toAssembly]
  let tailSegment :
      Structured.Preservation.CodeSegment program
        ([Assembly.Instr.prim swapOp.toPrimOp] ++
          [Assembly.Instr.prim Structured.BasicOp.pop.toPrimOp]) :=
    Structured.Preservation.CodeSegment.cast_code hTailAssembly
      tailSegmentRaw
  have hValuePc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc valueSegment := by
    simpa [valueSegment, appendSegment,
      Structured.Preservation.CodeSegment.left,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hPc
  have hValueToTail :
      Structured.Preservation.CodeSegment.fallthroughPc valueSegment =
        Structured.Preservation.CodeSegment.startPc tailSegment := by
    have hRaw :
        Structured.Preservation.CodeSegment.startPc tailSegmentRaw =
          Structured.Preservation.CodeSegment.fallthroughPc valueSegment :=
      codeSegment_right_startPc_eq_left_fallthroughPc appendSegment
    simpa [tailSegment, tailSegmentRaw,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc] using hRaw.symm
  have hTailFallSegment :
      Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    simp [tailSegment, tailSegmentRaw, appendSegment,
      Structured.Preservation.CodeSegment.right,
      Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.fallthroughPc,
      hAssemblyCode, hTailAssembly, assignTail]
  have hResolveEval :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.LocalsExpr.eval
          prim expr compiler)
        trace (.ok (compilerAfter, [value])) :=
    compilerOpenLocalsExpr_evalOne_resolves_ok_inv hResolve
  rcases
      compilerOpenLocalsExpr_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
        hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
        [] rfl program (2 + tailFuel) valueSegment hValuePc
        hPrefixRel hResolveEval with
    ⟨evmAfterValue, hValueRel, hValuePcAfter, hValueCont⟩
  have hTailPc :
      evmAfterValue.pc =
        Structured.Preservation.CodeSegment.startPc tailSegment := by
    rw [hValuePcAfter]
    exact hValueToTail
  rcases
      compilerOpenAssignTail_stackPrefix_openRunNResult_continue_fallthrough
        (layout := layout) (source := compilerAfter)
        (state := evmAfterValue) (name := name) (idx := idx)
        (value := value) (swapOp := swapOp)
        hNoDup hName hBound hSwap (by simpa using hValueRel)
        program tailSegment hTailPc with
    ⟨evmAfterAssign, hAssignRel, hAssignPc, hAssignCont⟩
  refine ⟨evmAfterAssign, hAssignRel, ?_, ?_⟩
  · simpa [hTailFallSegment] using hAssignPc
  · intro tailTrace result hRest
    have hTailAndRest :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program (2 + tailFuel)
            evmAfterValue)
          tailTrace result :=
      hAssignCont hRest
    have hFull := hValueCont hTailAndRest
    have hFuel :
        valueCode.length + (2 + tailFuel) =
          (valueCode ++
            [Structured.BasicInstr.op swapOp,
              Structured.BasicInstr.op Structured.BasicOp.pop]).length +
            tailFuel := by
      simp [Nat.add_assoc]
    simpa [hFuel] using hFull

theorem compilerOpenFunctionsStmt_expr_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {expr : Functions.Expr 0}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 expr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.expr expr) compiler)
        trace (.ok (Functions.Source.Outcome.regular compilerAfter,
          ctxAfter))) :
    ctxAfter = sourceCtx ∧
      ∃ evmAfter : EvmYul.EVM.State,
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter ∧
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment ∧
        ∀ {tailTrace : OpenExternal.OpenTrace}
          {result : Except EVMException Assembly.StepResult},
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace result →
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program
              (code.length + tailFuel) state)
            (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterEval, valuesAfter⟩
    cases hDone
    subst trace
    constructor
    · rfl
    · rcases
        compilerOpenLocalsExpr_zero_stackPrefix_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          program tailFuel segment hPc hPrefixRel hEval with
        ⟨evmAfter, hRel, hAfterPc, hCont⟩
      refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
      intro tailTrace result hRest
      have hFull := hCont hRest
      simpa [List.append_assoc] using hFull

theorem compilerOpenFunctionsStmt_let_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.let_ name valueExpr)
          compiler)
        trace (.ok (Functions.Source.Outcome.regular compilerAfter,
          ctxAfter))) :
    ctxAfter = { sourceCtx with scope := name :: sourceCtx.scope } ∧
      ∃ evmAfter : EvmYul.EVM.State,
        Locals.SourceLowering.StackPrefixRel (name :: layout)
          compilerAfter [] evmAfter ∧
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment ∧
        ∀ {tailTrace : OpenExternal.OpenTrace}
          {result : Except EVMException Assembly.StepResult},
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace result →
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program
              (code.length + tailFuel) state)
            (trace ++ tailTrace) result := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterValue, value⟩
    cases hDone
    subst trace
    constructor
    · rfl
    · rcases
        compilerOpenLocalsExpr_evalOne_insert_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup hFresh
          program tailFuel segment hPc hPrefixRel hEval with
        ⟨evmAfter, hRel, hAfterPc, hCont⟩
      refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
      intro tailTrace result hRest
      have hFull := hCont hRest
      simpa [List.append_assoc] using hFull

theorem compilerOpenFunctionsStmt_assign_openRunNResult_continue_fallthrough_of_compileCode
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler compilerAfter : Objects.Source.State}
    {state : EvmYul.EVM.State} {valueCode : Structured.Code}
    {idx : Nat} {swapOp : Structured.BasicOp}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr =
      some valueCode)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.assign name valueExpr)
          compiler)
        trace (.ok (Functions.Source.Outcome.regular compilerAfter,
          ctxAfter))) :
    ctxAfter = sourceCtx ∧
      ∃ evmAfter : EvmYul.EVM.State,
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter ∧
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment ∧
        ∀ {tailTrace : OpenExternal.OpenTrace}
          {result : Except EVMException Assembly.StepResult},
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace result →
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program
              ((valueCode ++
                [Structured.BasicInstr.op swapOp,
                  Structured.BasicInstr.op Structured.BasicOp.pop]).length +
                tailFuel) state)
            (trace ++ tailTrace) result := by
  have hContains : compiler.vars.contains name = true := by
    rcases hPrefixRel with ⟨_hShared, baseStack, _hStack, hStoreRel⟩
    exact Locals.SourceLowering.StackStoreRel.contains_of_layout
      hStoreRel hName
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  simp [hContains] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterValue, value⟩
    cases hDone
    subst trace
    constructor
    · rfl
    · rcases
        compilerOpenLocalsExpr_evalOne_assign_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hName hBound hSwap program tailFuel segment hPc hPrefixRel
          hEval with
        ⟨evmAfter, hRel, hAfterPc, hCont⟩
      refine ⟨evmAfter, hRel, hAfterPc, ?_⟩
      intro tailTrace result hRest
      have hFull := hCont hRest
      simpa [List.append_assoc] using hFull

theorem compilerOpenFunctionsStmt_expr_resolves_ok_regular_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {expr : Functions.Expr 0}
    {compiler : Objects.Source.State}
    {trace : OpenExternal.OpenTrace}
    {outcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.expr expr) compiler)
        trace (.ok (outcome, ctxAfter))) :
    ∃ compilerAfter : Objects.Source.State,
      outcome = Functions.Source.Outcome.regular compilerAfter ∧
        ctxAfter = sourceCtx := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfter, valuesAfter⟩
    cases hDone
    exact ⟨compilerAfter, rfl, rfl⟩

theorem compilerOpenFunctionsStmt_let_resolves_ok_regular_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {compiler : Objects.Source.State}
    {trace : OpenExternal.OpenTrace}
    {outcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.let_ name valueExpr)
          compiler)
        trace (.ok (outcome, ctxAfter))) :
    ∃ compilerAfter : Objects.Source.State,
      outcome = Functions.Source.Outcome.regular compilerAfter ∧
        ctxAfter = { sourceCtx with scope := name :: sourceCtx.scope } := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hEvalError | hEvalOk
  · rcases hEvalError with ⟨err, _hEval, hResult⟩
    cases hResult
  · rcases hEvalOk with
      ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
    rcases evalResult with ⟨compilerAfterValue, value⟩
    cases hDone
    exact ⟨compilerAfterValue.insert name value, rfl, rfl⟩

theorem compilerOpenFunctionsStmt_assign_resolves_ok_regular_inv
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {compiler : Objects.Source.State}
    {trace : OpenExternal.OpenTrace}
    {outcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run
          prim programSource sourceCtx sourceFuel (.assign name valueExpr)
          compiler)
        trace (.ok (outcome, ctxAfter))) :
    ∃ compilerAfter : Objects.Source.State,
      outcome = Functions.Source.Outcome.regular compilerAfter ∧
        ctxAfter = sourceCtx := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Stmt.run] at hResolve
  cases hContains : compiler.vars.contains name with
  | false =>
      simp [hContains, Reference.SourceBridgeFacts.CompilerOpen.invalid] at hResolve
      cases hResolve
  | true =>
      simp [hContains] at hResolve
      rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
        hEvalError | hEvalOk
      · rcases hEvalError with ⟨err, _hEval, hResult⟩
        cases hResult
      · rcases hEvalOk with
          ⟨evalTrace, doneTrace, evalResult, hTrace, hEval, hDone⟩
        rcases evalResult with ⟨compilerAfterValue, value⟩
        cases hDone
        exact
          ⟨compilerAfterValue.withVars
              (Locals.Source.Store.insert compilerAfterValue.vars name
                value),
            rfl, rfl⟩

theorem compilerOpenFunctionsBlock_expr_cons_openRunNResult_of_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 expr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .expr expr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_expr_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_expr_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          program tailFuel segment hPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, _hAfterPc, hHeadCont⟩
    rcases hTail hRel hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine ⟨code.length + tailFuel, targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_let_cons_openRunNResult_of_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel (name :: layout)
          compilerAfter [] evmAfter →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .let_ name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_let_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_let_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hFresh program tailFuel segment hPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, _hAfterPc, hHeadCont⟩
    rcases hTail hRel hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine ⟨code.length + tailFuel, targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_assign_cons_openRunNResult_of_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {valueCode : Structured.Code}
    {idx : Nat} {swapOp : Structured.BasicOp}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr =
      some valueCode)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .assign name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_assign_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_assign_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hName hBound hSwap program tailFuel segment hPc hPrefixRel
          hHead with
      ⟨_hCtx, evmAfter, hRel, _hAfterPc, hHeadCont⟩
    rcases hTail hRel hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine
      ⟨(valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).length +
          tailFuel,
        targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_expr_cons_openRunNResult_of_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 expr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .expr expr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_expr_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_expr_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          program tailFuel segment hPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    rcases hTail hRel hAfterPc hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine ⟨code.length + tailFuel, targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_let_cons_openRunNResult_of_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {code : Structured.Code}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr = some code)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program code.toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel (name :: layout)
          compilerAfter [] evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .let_ name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_let_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_let_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hFresh program tailFuel segment hPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    rcases hTail hRel hAfterPc hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine ⟨code.length + tailFuel, targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_assign_cons_openRunNResult_of_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx : Locals.Ctx} {layout : List Name}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State} {valueCode : Structured.Code}
    {idx : Nat} {swapOp : Structured.BasicOp}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompile : Locals.Expr.compileCode localsCtx 0 valueExpr =
      some valueCode)
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (idx + 1) = some swapOp)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).toAssembly)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc segment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .assign name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_assign_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_assign_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCompile hCtxLayout hNoDup
          hName hBound hSwap program tailFuel segment hPc hPrefixRel
          hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    rcases hTail hRel hAfterPc hRest with
      ⟨targetResult, hTailRun, hOutcomeRel⟩
    refine
      ⟨(valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).length +
          tailFuel,
        targetResult, ?_, hOutcomeRel⟩
    exact hHeadCont hTailRun

theorem compilerOpenFunctionsBlock_expr_cons_openRunNResult_of_compileOpen_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .expr expr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .expr expr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_expr_cons_inv hCompileBlock with
    ⟨code, restStmts, hCode, hRestCompile, hCompiledStmts⟩
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, _hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  have hTailForHead :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult := by
    intro tailTrace sourceOutcome tailCtxAfter compilerAfter evmAfter
      hRel hAfterPc hRest
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    exact hTail tailSegment hRestCompile hRel hTailPc hRest
  exact
    compilerOpenFunctionsBlock_expr_cons_openRunNResult_of_tail_pc
      hPrim hOwned hSupported hAccess hCode hCtxLayout hNoDup program
      tailFuel headSegment hHeadPc hPrefixRel hTailForHead hResolve

theorem compilerOpenFunctionsBlock_let_cons_openRunNResult_of_compileOpen_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .let_ name valueExpr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen
          (localsCtx.withLayout (name :: localsCtx.layout))
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel (name :: layout) compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .let_ name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_let_cons_inv hCompileBlock with
    ⟨code, restStmts, hCode, hRestCompile, hCompiledStmts⟩
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, _hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  have hTailForHead :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel (name :: layout) compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult := by
    intro tailTrace sourceOutcome tailCtxAfter compilerAfter evmAfter
      hRel hAfterPc hRest
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    exact hTail tailSegment hRestCompile hRel hTailPc hRest
  exact
    compilerOpenFunctionsBlock_let_cons_openRunNResult_of_tail_pc
      hPrim hOwned hSupported hAccess hCode hCtxLayout hNoDup hFresh
      program tailFuel headSegment hHeadPc hPrefixRel hTailForHead hResolve

theorem compilerOpenFunctionsBlock_assign_cons_openRunNResult_of_compileOpen_tail_pc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {idx : Nat}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .assign name valueExpr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (program : Assembly.Program)
    (tailFuel : Nat)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {ResultRel : Functions.Source.Outcome → Assembly.StepResult → Prop}
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .assign name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      ResultRel sourceOutcome targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_assign_cons_inv hCompileBlock with
    ⟨depth, valueCode, swapOp, restStmts, hDepth, hValue, hSwap,
      hRestCompile, hCompiledStmts⟩
  have hDepthExpected :
      Locals.Layout.lookupDepth? name localsCtx.layout =
        some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  have hDepthEq : depth = idx + 1 := by
    rw [hDepthExpected] at hDepth
    cases hDepth
    rfl
  subst depth
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt
                  (valueCode ++
                    [Structured.BasicInstr.op swapOp,
                      Structured.BasicInstr.op Structured.BasicOp.pop]) ++
                  restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt
                  (valueCode ++
                    [Structured.BasicInstr.op swapOp,
                      Structured.BasicInstr.op Structured.BasicOp.pop]) ++
                  restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, _hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  have hTailForHead :
      ∀ {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.fallthroughPc headSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program tailFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          ResultRel sourceOutcome targetResult := by
    intro tailTrace sourceOutcome tailCtxAfter compilerAfter evmAfter
      hRel hAfterPc hRest
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    exact hTail tailSegment hRestCompile hRel hTailPc hRest
  exact
    compilerOpenFunctionsBlock_assign_cons_openRunNResult_of_tail_pc
      hPrim hOwned hSupported hAccess hValue hCtxLayout hNoDup hName
      hBound hSwap program tailFuel headSegment hHeadPc hPrefixRel
      hTailForHead hResolve

def FunctionsBlockCompiledOutcomeRel
    (asm : Assembly.Program) (ctx : Structured.CompileContext)
    (fallthroughPc : Word) (returns layout : List Name)
    (hiddenReturns : List Structured.ReturnDest) (tokens : List Word)
    (source : Functions.Source.Outcome)
    (target : Assembly.StepResult) : Prop :=
  ∃ direct : Locals.Outcome,
    Functions.SourceDirect.BlockScopedOutcomeRel returns layout hiddenReturns
      source direct ∧
    Structured.Preservation.CompiledOutcomeRel asm ctx fallthroughPc direct
      target tokens

namespace FunctionsBlockCompiledOutcomeRel

theorem cast_fallthrough
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {pc₁ pc₂ : Word} {returns layout : List Name}
    {hiddenReturns : List Structured.ReturnDest} {tokens : List Word}
    {source : Functions.Source.Outcome} {target : Assembly.StepResult}
    (hPc : pc₁ = pc₂)
    (hRel :
      FunctionsBlockCompiledOutcomeRel asm ctx pc₁ returns layout
        hiddenReturns tokens source target) :
    FunctionsBlockCompiledOutcomeRel asm ctx pc₂ returns layout
      hiddenReturns tokens source target := by
  simpa [hPc] using hRel

theorem regular_nil
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {returns layout : List Name}
    {source : Objects.Source.State} {target : EvmYul.EVM.State}
    (hRel :
      Locals.SourceLowering.StackPrefixRel layout source [] target)
    (hPc : target.pc = fallthroughPc) :
    FunctionsBlockCompiledOutcomeRel asm ctx fallthroughPc returns layout
      [] [] (Functions.Source.Outcome.regular source)
      (.running target) := by
  let directState : Structured.RunState := Structured.RunState.initial target
  have hLocal :
      Locals.SourceLowering.StateRel layout source directState := by
    exact
      Locals.SourceLowering.StackPrefixRel.to_stateRel_nil
        (target := directState)
        (by simpa [directState, Structured.RunState.initial] using hRel)
  have hDirectState :
      Functions.SourceDirect.StateRel layout [] source directState := by
    exact ⟨hLocal, rfl⟩
  refine
    ⟨Locals.Outcome.regular directState,
      Functions.SourceDirect.BlockScopedOutcomeRel.regular hDirectState,
      ?_⟩
  exact
    Structured.Preservation.CompiledOutcomeRel.regular
      (Structured.Preservation.Frame.stateRel_initial target) hPc

end FunctionsBlockCompiledOutcomeRel

theorem functionsBlock_toLocals_compileOpen_nil_inv
    {returns : List Name} {ctx finalCtx : Locals.Ctx}
    {compiledStmts : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx
          (Functions.Block.toLocals returns { stmts := [] }) =
        some (compiledStmts, finalCtx)) :
    compiledStmts = [] ∧ finalCtx = ctx := by
  have h :
      compiledStmts = [] ∧ ctx = finalCtx := by
    simpa [Functions.Block.toLocals, Functions.StmtList.toLocals,
      Locals.Block.compileOpen] using hCompile
  exact ⟨h.1, h.2.symm⟩

theorem compilerOpenFunctionsBlock_nil_openRunNResult_of_compileOpen
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := [] }) =
        some (compiledStmts, finalLocalsCtx))
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx sourceFuel { stmts := [] } compiler)
        trace (.ok (sourceOutcome, ctxAfter))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOutcomeRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        returns layout [] [] sourceOutcome targetResult := by
  rcases functionsBlock_toLocals_compileOpen_nil_inv hCompileBlock with
    ⟨hCompiledStmts, _hFinalCtx⟩
  cases sourceFuel with
  | zero =>
      rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen]
        at hResolve
      cases hResolve
  | succ sourceFuel' =>
      rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen]
        at hResolve
      cases hResolve
      have hFallthrough :
          state.pc =
            Structured.Preservation.CodeSegment.fallthroughPc segment := by
        have hSegmentCode :
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured compiledStmts }
              structuredCtx supply).code = [] := by
          simp [hCompiledStmts, Expressions.StmtList.toStructured,
            Structured.Block.compileFromCtx]
        let emptySegment :
            Structured.Preservation.CodeSegment program [] :=
          Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
        have hEmpty :
            Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
              Structured.Preservation.CodeSegment.startPc emptySegment :=
          codeSegment_fallthroughPc_empty emptySegment
        have hStart :
            Structured.Preservation.CodeSegment.startPc emptySegment =
              Structured.Preservation.CodeSegment.startPc segment := by
          simp [emptySegment, Structured.Preservation.CodeSegment.cast_code,
            Structured.Preservation.CodeSegment.startPc]
        have hFall :
            Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
              Structured.Preservation.CodeSegment.fallthroughPc segment := by
          cases segment with
          | mk pre post hAsm hFits =>
              simp [emptySegment,
                Structured.Preservation.CodeSegment.cast_code,
                Structured.Preservation.CodeSegment.fallthroughPc,
                hSegmentCode]
        calc
          state.pc = Structured.Preservation.CodeSegment.startPc segment := hPc
          _ = Structured.Preservation.CodeSegment.startPc emptySegment :=
            hStart.symm
          _ = Structured.Preservation.CodeSegment.fallthroughPc emptySegment :=
            hEmpty.symm
          _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
            hFall
      refine ⟨0, .running state, ?_, ?_⟩
      · exact OpenExternal.OpenResultResolves.done
      · exact
          FunctionsBlockCompiledOutcomeRel.regular_nil
            (asm := program) (ctx := structuredCtx) (returns := returns)
            (layout := layout) hPrefixRel hFallthrough

def FunctionsBlockCompiledOpenResultRel
    (asm : Assembly.Program) (ctx : Structured.CompileContext)
    (fallthroughPc : Word) (retc : Nat) (returns : List Name)
    (hiddenReturns : List Structured.ReturnDest) (tokens : List Word)
    (source : Functions.Source.Outcome × Functions.Source.Ctx)
    (targetCtx : Locals.Ctx) (target : Assembly.StepResult) : Prop :=
  ∃ direct : Locals.Outcome,
    Functions.SourceDirect.BlockOpenResultRel retc returns hiddenReturns
      source (direct, targetCtx) ∧
    Structured.Preservation.CompiledOutcomeRel asm ctx fallthroughPc direct
      target tokens

namespace FunctionsBlockCompiledOpenResultRel

theorem cast_fallthrough
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {pc₁ pc₂ : Word} {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest} {tokens : List Word}
    {source : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetCtx : Locals.Ctx} {target : Assembly.StepResult}
    (hPc : pc₁ = pc₂)
    (hRel :
      FunctionsBlockCompiledOpenResultRel asm ctx pc₁ retc returns
        hiddenReturns tokens source targetCtx target) :
    FunctionsBlockCompiledOpenResultRel asm ctx pc₂ retc returns
      hiddenReturns tokens source targetCtx target := by
  simpa [hPc] using hRel

theorem regular_nil
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {retc : Nat} {returns : List Name}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {source : Objects.Source.State} {target : EvmYul.EVM.State}
    (hCtx :
      Functions.SourceDirect.CtxRel retc sourceCtx targetCtx)
    (hRel :
      Locals.SourceLowering.StackPrefixRel targetCtx.layout source []
        target)
    (hPc : target.pc = fallthroughPc) :
    FunctionsBlockCompiledOpenResultRel asm ctx fallthroughPc retc
      returns [] [] (Functions.Source.Outcome.regular source, sourceCtx)
      targetCtx (.running target) := by
  let directState : Structured.RunState := Structured.RunState.initial target
  have hLocal :
      Locals.SourceLowering.StateRel targetCtx.layout source
        directState := by
    exact
      Locals.SourceLowering.StackPrefixRel.to_stateRel_nil
        (target := directState)
        (by simpa [directState, Structured.RunState.initial] using hRel)
  have hDirectState :
      Functions.SourceDirect.StateRel targetCtx.layout [] source
        directState := by
    exact ⟨hLocal, rfl⟩
  refine
    ⟨Locals.Outcome.regular directState,
      Functions.SourceDirect.BlockOpenResultRel.regular hCtx
        hDirectState,
      ?_⟩
  exact
    Structured.Preservation.CompiledOutcomeRel.regular
      (Structured.Preservation.Frame.stateRel_initial target) hPc

theorem to_compiledOutcomeRel
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest} {tokens : List Word}
    {source : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetCtx : Locals.Ctx} {target : Assembly.StepResult}
    (hRel :
      FunctionsBlockCompiledOpenResultRel asm ctx fallthroughPc retc
        returns hiddenReturns tokens source targetCtx target) :
    FunctionsBlockCompiledOutcomeRel asm ctx fallthroughPc returns
      targetCtx.layout hiddenReturns tokens source.1 target := by
  rcases hRel with ⟨direct, hOpen, hCompiled⟩
  refine ⟨direct, ?_, hCompiled⟩
  rcases source with ⟨sourceOutcome, sourceCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases direct with
      | mk directState directMode =>
          cases sourceMode <;> cases directMode <;>
            simp [Functions.SourceDirect.BlockOpenResultRel,
              Functions.SourceDirect.BlockScopedOutcomeRel] at hOpen ⊢
          all_goals exact hOpen.1

theorem source_regular_running_compiledOutcomeRel
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest} {tokens : List Word}
    {source : Objects.Source.State} {sourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx} {target : Assembly.StepResult}
    (hRel :
      FunctionsBlockCompiledOpenResultRel asm ctx fallthroughPc retc returns
        hiddenReturns tokens
        (Functions.Source.Outcome.regular source, sourceCtx) targetCtx
        target) :
    ∃ bodyState afterBody,
      target = .running afterBody ∧
        Structured.Preservation.CompiledOutcomeRel asm ctx fallthroughPc
          (Structured.Outcome.regular bodyState) (.running afterBody)
          tokens := by
  rcases hRel with ⟨direct, hOpen, hCompiled⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockOpenResultRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Functions.Source.Outcome.regular,
          Locals.Source.Outcome.regular] at hOpen
      · cases target with
        | running afterBody =>
            exact ⟨directState, afterBody, rfl, hCompiled⟩
        | halted halt =>
            simp [Structured.Preservation.CompiledOutcomeRel] at hCompiled

theorem source_regular_running_stateRel_compiledOutcomeRel
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest} {tokens : List Word}
    {source : Objects.Source.State} {sourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx} {target : Assembly.StepResult}
    (hRel :
      FunctionsBlockCompiledOpenResultRel asm ctx fallthroughPc retc returns
        hiddenReturns tokens
        (Functions.Source.Outcome.regular source, sourceCtx) targetCtx
        target) :
    ∃ bodyState afterBody,
      target = .running afterBody ∧
        Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
          bodyState ∧
        Structured.Preservation.CompiledOutcomeRel asm ctx fallthroughPc
          (Structured.Outcome.regular bodyState) (.running afterBody)
          tokens := by
  rcases hRel with ⟨direct, hOpen, hCompiled⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockOpenResultRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Functions.Source.Outcome.regular,
          Locals.Source.Outcome.regular] at hOpen
      · cases target with
        | running afterBody =>
            exact ⟨directState, afterBody, rfl, hOpen.1, hCompiled⟩
        | halted halt =>
            simp [Structured.Preservation.CompiledOutcomeRel] at hCompiled

theorem source_regular_running_return_cleanup_parts
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest} {tokens : List Word}
    {source : Objects.Source.State} {sourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx} {target : Assembly.StepResult}
    {values : List Word}
    (hRel :
      FunctionsBlockCompiledOpenResultRel asm ctx fallthroughPc retc returns
        hiddenReturns tokens
        (Functions.Source.Outcome.regular source, sourceCtx) targetCtx
        target)
    (hAccess :
      Functions.SourceDirect.ReturnValuesRel.Accessible targetCtx.layout 0
        returns)
    (hLookup :
      Functions.Source.Store.lookupMany returns source.vars = some values)
    (hNoDup : targetCtx.layout.Nodup)
    (hReturnsLen : returns.length = targetCtx.leaveRetc)
    (hRetcBound : targetCtx.leaveRetc ≤ 16) :
    ∃ bodyState afterBody stateAfterReturns returnedState,
      target = .running afterBody ∧
        Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
          bodyState ∧
        Functions.SourceDirect.ReturnValuesRel targetCtx.layout source
          bodyState returns values ∧
        Functions.Direct.pushReturns targetCtx returns bodyState =
          .ok stateAfterReturns ∧
        Locals.Direct.Ctx.runCleanupToPreserving targetCtx
          targetCtx.leaveRetc 0 stateAfterReturns =
          .ok returnedState ∧
        Functions.SourceDirect.ReturnedStackRel hiddenReturns source values
          returnedState ∧
        Structured.Preservation.CompiledOutcomeRel asm ctx fallthroughPc
          (Structured.Outcome.regular bodyState) (.running afterBody)
          tokens := by
  rcases source_regular_running_stateRel_compiledOutcomeRel hRel with
    ⟨bodyState, afterBody, hTarget, hStateRel, hCompiled⟩
  have hValues :
      Functions.SourceDirect.ReturnValuesRel targetCtx.layout source
        bodyState returns values :=
    Functions.SourceDirect.ReturnValuesRel.of_stateRel_lookupMany_accessible
      hAccess hLookup hStateRel
  rcases
      Functions.SourceDirect.ReturnValuesRel.pushCleanup_returnedStack
        (layout := targetCtx.layout) (hiddenReturns := hiddenReturns)
        (source := source) (target := bodyState) (ctx := targetCtx)
        (returns := returns) (values := values)
        rfl hNoDup hReturnsLen hRetcBound hValues hStateRel with
    ⟨stateAfterReturns, returnedState, hPush, hCleanup, hReturned⟩
  exact
    ⟨bodyState, afterBody, stateAfterReturns, returnedState, hTarget,
      hStateRel, hValues, hPush, hCleanup, hReturned, hCompiled⟩

theorem source_leave_running_compiledOutcomeRel
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest} {tokens : List Word}
    {source : Objects.Source.State} {sourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx} {target : Assembly.StepResult}
    (hRel :
      FunctionsBlockCompiledOpenResultRel asm ctx fallthroughPc retc returns
        hiddenReturns tokens
        (Functions.Source.Outcome.leave source, sourceCtx) targetCtx
        target) :
    ∃ bodyState afterBody,
      target = .running afterBody ∧
        Structured.Preservation.CompiledOutcomeRel asm ctx fallthroughPc
          (Structured.Outcome.leave bodyState) (.running afterBody)
          tokens := by
  rcases hRel with ⟨direct, hOpen, hCompiled⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.BlockOpenResultRel,
          Functions.SourceDirect.StmtOutcomeRel,
          Functions.Source.Outcome.leave,
          Locals.Source.Outcome.leave] at hOpen
      · cases target with
        | running afterBody =>
            exact ⟨directState, afterBody, rfl, hCompiled⟩
        | halted halt =>
            simp [Structured.Preservation.CompiledOutcomeRel] at hCompiled

theorem source_leave_running_returnedStackRel_compiledOutcomeRel
    {asm : Assembly.Program} {ctx : Structured.CompileContext}
    {fallthroughPc : Word} {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest} {tokens : List Word}
    {source : Objects.Source.State} {sourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx} {target : Assembly.StepResult}
    (hRel :
      FunctionsBlockCompiledOpenResultRel asm ctx fallthroughPc retc returns
        hiddenReturns tokens
        (Functions.Source.Outcome.leave source, sourceCtx) targetCtx
        target) :
    ∃ values bodyState afterBody,
      target = .running afterBody ∧
        Functions.Source.Store.lookupMany returns source.vars = some values ∧
        Functions.SourceDirect.ReturnedStackRel hiddenReturns source values
          bodyState ∧
        Structured.Preservation.CompiledOutcomeRel asm ctx fallthroughPc
          (Structured.Outcome.leave bodyState) (.running afterBody)
          tokens := by
  rcases hRel with ⟨direct, hOpen, hCompiled⟩
  rcases
      Functions.SourceDirect.BlockOpenResultRel.outcomeRel_of_nonregular
        hOpen
        (by
          simp [Functions.Source.Outcome.leave,
            Locals.Source.Outcome.leave]) with
    ⟨_outcomeLayout, hOutcome⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.SourceDirect.StmtOutcomeRel,
          Functions.Source.Outcome.leave,
          Locals.Source.Outcome.leave] at hOutcome
      · rcases hOutcome with ⟨values, hLookup, hReturned⟩
        cases target with
        | running afterBody =>
            exact ⟨values, directState, afterBody, rfl, hLookup, hReturned,
              hCompiled⟩
        | halted halt =>
            simp [Structured.Preservation.CompiledOutcomeRel] at hCompiled

end FunctionsBlockCompiledOpenResultRel

theorem compilerOpenFunctionsBlock_nil_openRunNResult_openResultRel_of_compileOpen
    {prim : Objects.Source.PrimitiveSemantics}
    {programSource : Functions.Program}
    {sourceCtx ctxAfter : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {retc : Nat} {returns : List Name}
    {localsCtx finalLocalsCtx : Locals.Ctx}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hCtxRel :
      Functions.SourceDirect.CtxRel retc sourceCtx localsCtx)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := [] }) =
        some (compiledStmts, finalLocalsCtx))
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel localsCtx.layout compiler []
        state)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx sourceFuel { stmts := [] } compiler)
        trace (.ok (sourceOutcome, ctxAfter))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOpenResultRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        retc returns [] [] (sourceOutcome, ctxAfter) finalLocalsCtx
        targetResult := by
  rcases functionsBlock_toLocals_compileOpen_nil_inv hCompileBlock with
    ⟨hCompiledStmts, hFinalCtx⟩
  subst finalLocalsCtx
  cases sourceFuel with
  | zero =>
      rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen]
        at hResolve
      cases hResolve
  | succ sourceFuel' =>
      rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen]
        at hResolve
      cases hResolve
      have hFallthrough :
          state.pc =
            Structured.Preservation.CodeSegment.fallthroughPc segment := by
        have hSegmentCode :
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured compiledStmts }
              structuredCtx supply).code = [] := by
          simp [hCompiledStmts, Expressions.StmtList.toStructured,
            Structured.Block.compileFromCtx]
        let emptySegment :
            Structured.Preservation.CodeSegment program [] :=
          Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
        have hEmpty :
            Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
              Structured.Preservation.CodeSegment.startPc emptySegment :=
          codeSegment_fallthroughPc_empty emptySegment
        have hStart :
            Structured.Preservation.CodeSegment.startPc emptySegment =
              Structured.Preservation.CodeSegment.startPc segment := by
          simp [emptySegment, Structured.Preservation.CodeSegment.cast_code,
            Structured.Preservation.CodeSegment.startPc]
        have hFall :
            Structured.Preservation.CodeSegment.fallthroughPc emptySegment =
              Structured.Preservation.CodeSegment.fallthroughPc segment := by
          cases segment with
          | mk pre post hAsm hFits =>
              simp [emptySegment,
                Structured.Preservation.CodeSegment.cast_code,
                Structured.Preservation.CodeSegment.fallthroughPc,
                hSegmentCode]
        calc
          state.pc = Structured.Preservation.CodeSegment.startPc segment := hPc
          _ = Structured.Preservation.CodeSegment.startPc emptySegment :=
            hStart.symm
          _ = Structured.Preservation.CodeSegment.fallthroughPc emptySegment :=
            hEmpty.symm
          _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
            hFall
      refine ⟨0, .running state, ?_, ?_⟩
      · exact OpenExternal.OpenResultResolves.done
      · exact
          FunctionsBlockCompiledOpenResultRel.regular_nil
            (asm := program) (ctx := structuredCtx) (retc := retc)
            (returns := returns) hCtxRel hPrefixRel hFallthrough

theorem compilerOpenFunctionsBlock_expr_cons_openRunNResult_compiledOutcomeRel_of_compileOpen_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .expr expr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetFuel targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program targetFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          FunctionsBlockCompiledOutcomeRel program structuredCtx
            (Structured.Preservation.CodeSegment.fallthroughPc tailSegment)
            returns layout [] [] sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .expr expr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOutcomeRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        returns layout [] [] sourceOutcome targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_expr_cons_inv hCompileBlock with
    ⟨code, restStmts, hCode, hRestCompile, hCompiledStmts⟩
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hSegmentFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment' =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    cases segment with
    | mk pre post hAsm hFits =>
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hSegmentCode]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_expr_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_expr_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCode hCtxLayout hNoDup
          program 0 headSegment hHeadPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    have hHeadRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program code.length state)
          headTrace (.ok (.running evmAfter)) := by
      have hDone :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program 0 evmAfter)
            [] (.ok (.running evmAfter)) := by
        rw [OpenAssembly.Source.openRunNResult_zero]
        exact OpenExternal.OpenResultResolves.done
      have hFull := hHeadCont hDone
      simpa using hFull
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    rcases hTail tailSegment hRestCompile hRel hTailPc hRest with
      ⟨tailFuel, targetResult, hTailRun, hOutcomeRel⟩
    have hTargetRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (headTrace ++ tailTrace) (.ok targetResult) :=
      OpenAssembly.Source.openRunNResult_resolves_running_continue
        hHeadRun hTailRun
    have hTailFallFull :
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      calc
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
            Structured.Preservation.CodeSegment.fallthroughPc segment' :=
          hTailFall
        _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
          hSegmentFall
    exact
      ⟨code.length + tailFuel, targetResult, hTargetRun,
        FunctionsBlockCompiledOutcomeRel.cast_fallthrough
          hTailFallFull hOutcomeRel⟩

theorem compilerOpenFunctionsBlock_assign_cons_openRunNResult_compiledOutcomeRel_of_compileOpen_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {returns : List Name}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {idx : Nat}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .assign name valueExpr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetFuel targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program targetFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          FunctionsBlockCompiledOutcomeRel program structuredCtx
            (Structured.Preservation.CodeSegment.fallthroughPc tailSegment)
            returns layout [] [] sourceOutcome targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .assign name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOutcomeRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        returns layout [] [] sourceOutcome targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_assign_cons_inv hCompileBlock with
    ⟨depth, valueCode, swapOp, restStmts, hDepth, hValue, hSwap,
      hRestCompile, hCompiledStmts⟩
  have hDepthExpected :
      Locals.Layout.lookupDepth? name localsCtx.layout =
        some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  have hDepthEq : depth = idx + 1 := by
    rw [hDepthExpected] at hDepth
    cases hDepth
    rfl
  subst depth
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt
                  (valueCode ++
                    [Structured.BasicInstr.op swapOp,
                      Structured.BasicInstr.op Structured.BasicOp.pop]) ++
                  restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt
                  (valueCode ++
                    [Structured.BasicInstr.op swapOp,
                      Structured.BasicInstr.op Structured.BasicOp.pop]) ++
                  restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hSegmentFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment' =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    cases segment with
    | mk pre post hAsm hFits =>
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hSegmentCode]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_assign_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_assign_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hValue hCtxLayout hNoDup
          hName hBound hSwap program 0 headSegment hHeadPc hPrefixRel
          hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    have hHeadRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]).length
            state)
          headTrace (.ok (.running evmAfter)) := by
      have hDone :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program 0 evmAfter)
            [] (.ok (.running evmAfter)) := by
        rw [OpenAssembly.Source.openRunNResult_zero]
        exact OpenExternal.OpenResultResolves.done
      have hFull := hHeadCont hDone
      simpa using hFull
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    rcases hTail tailSegment hRestCompile hRel hTailPc hRest with
      ⟨tailFuel, targetResult, hTailRun, hOutcomeRel⟩
    have hTargetRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            ((valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]).length +
              tailFuel) state)
          (headTrace ++ tailTrace) (.ok targetResult) :=
      OpenAssembly.Source.openRunNResult_resolves_running_continue
        hHeadRun hTailRun
    have hTailFallFull :
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      calc
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
            Structured.Preservation.CodeSegment.fallthroughPc segment' :=
          hTailFall
        _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
          hSegmentFall
    exact
      ⟨(valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).length +
          tailFuel,
        targetResult, hTargetRun,
        FunctionsBlockCompiledOutcomeRel.cast_fallthrough
          hTailFallFull hOutcomeRel⟩

theorem compilerOpenFunctionsBlock_let_cons_openRunNResult_compiledOpenResultRel_of_compileOpen_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {retc : Nat} {returns : List Name}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .let_ name valueExpr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hFresh : name ∉ layout)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen
          (localsCtx.withLayout (name :: localsCtx.layout))
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel (name :: layout)
          compilerAfter [] evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource
            { sourceCtx with scope := name :: sourceCtx.scope }
            sourceFuel { stmts := rest } compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetFuel targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program targetFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          FunctionsBlockCompiledOpenResultRel program structuredCtx
            (Structured.Preservation.CodeSegment.fallthroughPc tailSegment)
            retc returns [] [] (sourceOutcome, tailCtxAfter) tailFinalCtx
            targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .let_ name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOpenResultRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        retc returns [] [] (sourceOutcome, ctxFinal) finalLocalsCtx
        targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_let_cons_inv hCompileBlock with
    ⟨code, restStmts, hCode, hRestCompile, hCompiledStmts⟩
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hSegmentFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment' =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    cases segment with
    | mk pre post hAsm hFits =>
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hSegmentCode]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_let_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_let_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCode hCtxLayout hNoDup hFresh
          program 0 headSegment hHeadPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    have hHeadRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program code.length state)
          headTrace (.ok (.running evmAfter)) := by
      have hDone :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program 0 evmAfter)
            [] (.ok (.running evmAfter)) := by
        rw [OpenAssembly.Source.openRunNResult_zero]
        exact OpenExternal.OpenResultResolves.done
      have hFull := hHeadCont hDone
      simpa using hFull
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    rcases hTail tailSegment hRestCompile hRel hTailPc hRest with
      ⟨tailFuel, targetResult, hTailRun, hOpenRel⟩
    have hTargetRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (headTrace ++ tailTrace) (.ok targetResult) :=
      OpenAssembly.Source.openRunNResult_resolves_running_continue
        hHeadRun hTailRun
    have hTailFallFull :
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      calc
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
            Structured.Preservation.CodeSegment.fallthroughPc segment' :=
          hTailFall
        _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
          hSegmentFall
    exact
      ⟨code.length + tailFuel, targetResult, hTargetRun,
        FunctionsBlockCompiledOpenResultRel.cast_fallthrough
          hTailFallFull hOpenRel⟩

theorem compilerOpenFunctionsBlock_expr_cons_openRunNResult_compiledOpenResultRel_of_compileOpen_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {retc : Nat} {returns : List Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hSupported : LocalsExprOpenSupported expr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 expr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .expr expr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetFuel targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program targetFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          FunctionsBlockCompiledOpenResultRel program structuredCtx
            (Structured.Preservation.CodeSegment.fallthroughPc tailSegment)
            retc returns [] [] (sourceOutcome, tailCtxAfter) tailFinalCtx
            targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .expr expr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOpenResultRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        retc returns [] [] (sourceOutcome, ctxFinal) finalLocalsCtx
        targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_expr_cons_inv hCompileBlock with
    ⟨code, restStmts, hCode, hRestCompile, hCompiledStmts⟩
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt code ++ restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hSegmentFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment' =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    cases segment with
    | mk pre post hAsm hFits =>
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hSegmentCode]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_expr_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_expr_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hCode hCtxLayout hNoDup
          program 0 headSegment hHeadPc hPrefixRel hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    have hHeadRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program code.length state)
          headTrace (.ok (.running evmAfter)) := by
      have hDone :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program 0 evmAfter)
            [] (.ok (.running evmAfter)) := by
        rw [OpenAssembly.Source.openRunNResult_zero]
        exact OpenExternal.OpenResultResolves.done
      have hFull := hHeadCont hDone
      simpa using hFull
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    rcases hTail tailSegment hRestCompile hRel hTailPc hRest with
      ⟨tailFuel, targetResult, hTailRun, hOpenRel⟩
    have hTargetRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (code.length + tailFuel) state)
          (headTrace ++ tailTrace) (.ok targetResult) :=
      OpenAssembly.Source.openRunNResult_resolves_running_continue
        hHeadRun hTailRun
    have hTailFallFull :
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      calc
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
            Structured.Preservation.CodeSegment.fallthroughPc segment' :=
          hTailFall
        _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
          hSegmentFall
    exact
      ⟨code.length + tailFuel, targetResult, hTargetRun,
        FunctionsBlockCompiledOpenResultRel.cast_fallthrough
          hTailFallFull hOpenRel⟩

theorem compilerOpenFunctionsBlock_assign_cons_openRunNResult_compiledOpenResultRel_of_compileOpen_tail
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {retc : Nat} {returns : List Name}
    {name : Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    {idx : Nat}
    (hOwned : Locals.Source.Expr.SourceOwned valueExpr)
    (hSupported : LocalsExprOpenSupported valueExpr)
    (hAccess : Locals.SourceLowering.Expr.Accessible layout 0 valueExpr)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns
            { stmts := .assign name valueExpr :: rest }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    (hTail :
      ∀ {tailStmts : List Expressions.Stmt}
        {tailFinalCtx : Locals.Ctx}
        {tailTrace : OpenExternal.OpenTrace}
        {sourceOutcome : Functions.Source.Outcome}
        {tailCtxAfter : Functions.Source.Ctx}
        {compilerAfter : Objects.Source.State}
        {evmAfter : EvmYul.EVM.State},
        (tailSegment :
          Structured.Preservation.CodeSegment program
            (Structured.Block.compileFromCtx
              { stmts := Expressions.StmtList.toStructured tailStmts }
              structuredCtx supply).code) →
        Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := rest }) =
          some (tailStmts, tailFinalCtx) →
        Locals.SourceLowering.StackPrefixRel layout compilerAfter []
          evmAfter →
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment →
        OpenExternal.OpenResultResolves
          (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
            prim programSource sourceCtx sourceFuel { stmts := rest }
            compilerAfter)
          tailTrace (.ok (sourceOutcome, tailCtxAfter)) →
        ∃ targetFuel targetResult,
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program targetFuel evmAfter)
            tailTrace (.ok targetResult) ∧
          FunctionsBlockCompiledOpenResultRel program structuredCtx
            (Structured.Preservation.CodeSegment.fallthroughPc tailSegment)
            retc returns [] [] (sourceOutcome, tailCtxAfter) tailFinalCtx
            targetResult)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx (sourceFuel + 1)
          { stmts := .assign name valueExpr :: rest } compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOpenResultRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        retc returns [] [] (sourceOutcome, ctxFinal) finalLocalsCtx
        targetResult := by
  rcases
      functionsBlock_toLocals_compileOpen_assign_cons_inv hCompileBlock with
    ⟨depth, valueCode, swapOp, restStmts, hDepth, hValue, hSwap,
      hRestCompile, hCompiledStmts⟩
  have hDepthExpected :
      Locals.Layout.lookupDepth? name localsCtx.layout =
        some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  have hDepthEq : depth = idx + 1 := by
    rw [hDepthExpected] at hDepth
    cases hDepth
    rfl
  subst depth
  have hSegmentCode :
      (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code =
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt
                  (valueCode ++
                    [Structured.BasicInstr.op swapOp,
                      Structured.BasicInstr.op Structured.BasicOp.pop]) ++
                  restStmts) }
          structuredCtx supply).code := by
    simp [hCompiledStmts]
  let segment' :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt
                  (valueCode ++
                    [Structured.BasicInstr.op swapOp,
                      Structured.BasicInstr.op Structured.BasicOp.pop]) ++
                  restStmts) }
          structuredCtx supply).code :=
    Structured.Preservation.CodeSegment.cast_code hSegmentCode segment
  rcases codeSegment_expressions_codeStmt_cons_split segment' with
    ⟨headSegment, tailSegment, hHeadStart, hTailStart, hTailFall⟩
  have hSegmentStart :
      Structured.Preservation.CodeSegment.startPc segment' =
        Structured.Preservation.CodeSegment.startPc segment := by
    simp [segment', Structured.Preservation.CodeSegment.cast_code,
      Structured.Preservation.CodeSegment.startPc]
  have hSegmentFall :
      Structured.Preservation.CodeSegment.fallthroughPc segment' =
        Structured.Preservation.CodeSegment.fallthroughPc segment := by
    cases segment with
    | mk pre post hAsm hFits =>
        simp [segment', Structured.Preservation.CodeSegment.cast_code,
          Structured.Preservation.CodeSegment.fallthroughPc, hSegmentCode]
  have hHeadPc :
      state.pc =
        Structured.Preservation.CodeSegment.startPc headSegment := by
    rw [hPc, ← hSegmentStart, ← hHeadStart]
  rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen] at hResolve
  rcases OpenExternal.OpenResultResolves.bind_inv hResolve with
    hHeadError | hHeadOk
  · rcases hHeadError with ⟨err, _hHead, hResult⟩
    cases hResult
  · rcases hHeadOk with
      ⟨headTrace, tailTrace, stmtResult, hTrace, hHead, hRest⟩
    rcases stmtResult with ⟨headOutcome, ctxAfterHead⟩
    rcases
      compilerOpenFunctionsStmt_assign_resolves_ok_regular_inv hHead with
      ⟨compilerAfter, hOutcome, hCtxAfterHead⟩
    subst headOutcome
    subst ctxAfterHead
    subst trace
    simp [Functions.Source.Outcome.regular,
      Locals.Source.Outcome.regular] at hRest
    rcases
        compilerOpenFunctionsStmt_assign_openRunNResult_continue_fallthrough_of_compileCode
          hPrim hOwned hSupported hAccess hValue hCtxLayout hNoDup
          hName hBound hSwap program 0 headSegment hHeadPc hPrefixRel
          hHead with
      ⟨_hCtx, evmAfter, hRel, hAfterPc, hHeadCont⟩
    have hHeadRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            (valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]).length
            state)
          headTrace (.ok (.running evmAfter)) := by
      have hDone :
          OpenExternal.OpenResultResolves
            (OpenAssembly.Source.openRunNResult program 0 evmAfter)
            [] (.ok (.running evmAfter)) := by
        rw [OpenAssembly.Source.openRunNResult_zero]
        exact OpenExternal.OpenResultResolves.done
      have hFull := hHeadCont hDone
      simpa using hFull
    have hTailPc :
        evmAfter.pc =
          Structured.Preservation.CodeSegment.startPc tailSegment := by
      rw [hAfterPc]
      exact hTailStart.symm
    rcases hTail tailSegment hRestCompile hRel hTailPc hRest with
      ⟨tailFuel, targetResult, hTailRun, hOpenRel⟩
    have hTargetRun :
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult program
            ((valueCode ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op Structured.BasicOp.pop]).length +
              tailFuel) state)
          (headTrace ++ tailTrace) (.ok targetResult) :=
      OpenAssembly.Source.openRunNResult_resolves_running_continue
        hHeadRun hTailRun
    have hTailFallFull :
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
          Structured.Preservation.CodeSegment.fallthroughPc segment := by
      calc
        Structured.Preservation.CodeSegment.fallthroughPc tailSegment =
            Structured.Preservation.CodeSegment.fallthroughPc segment' :=
          hTailFall
        _ = Structured.Preservation.CodeSegment.fallthroughPc segment :=
          hSegmentFall
    exact
      ⟨(valueCode ++
          [Structured.BasicInstr.op swapOp,
            Structured.BasicInstr.op Structured.BasicOp.pop]).length +
          tailFuel,
        targetResult, hTargetRun,
        FunctionsBlockCompiledOpenResultRel.cast_fallthrough
          hTailFallFull hOpenRel⟩

def FunctionsStmtListRegularOpenSupported (layout : List Name) :
    List Functions.Stmt → Prop
  | [] => True
  | .expr expr :: rest =>
      Locals.Source.Expr.SourceOwned expr ∧
        LocalsExprOpenSupported expr ∧
          Locals.SourceLowering.Expr.Accessible layout 0 expr ∧
            FunctionsStmtListRegularOpenSupported layout rest
  | .let_ name valueExpr :: rest =>
      Locals.Source.Expr.SourceOwned valueExpr ∧
        LocalsExprOpenSupported valueExpr ∧
          Locals.SourceLowering.Expr.Accessible layout 0 valueExpr ∧
            name ∉ layout ∧
              FunctionsStmtListRegularOpenSupported (name :: layout) rest
  | .assign name valueExpr :: rest =>
      Locals.Source.Expr.SourceOwned valueExpr ∧
        LocalsExprOpenSupported valueExpr ∧
          Locals.SourceLowering.Expr.Accessible layout 0 valueExpr ∧
            (∃ idx, layout[idx]? = some name ∧ idx + 1 ≤ 16) ∧
              FunctionsStmtListRegularOpenSupported layout rest
  | _ :: _ => False

theorem compilerOpenFunctionsBlock_regular_openRunNResult_compiledOpenResultRel_of_compileOpen
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {programSource : Functions.Program}
    {sourceCtx ctxFinal : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {retc : Nat} {returns : List Name}
    {stmts : List Functions.Stmt}
    {localsCtx finalLocalsCtx : Locals.Ctx} {layout : List Name}
    {compiledStmts : List Expressions.Stmt}
    {compiler : Objects.Source.State}
    {state : EvmYul.EVM.State}
    {structuredCtx : Structured.CompileContext}
    {supply : Structured.LabelSupply}
    (hSupported : FunctionsStmtListRegularOpenSupported layout stmts)
    (hCtxRel :
      Functions.SourceDirect.CtxRel retc sourceCtx localsCtx)
    (hCompileBlock :
      Locals.Block.compileOpen localsCtx
          (Functions.Block.toLocals returns { stmts := stmts }) =
        some (compiledStmts, finalLocalsCtx))
    (hCtxLayout : localsCtx.layout = layout)
    (hNoDup : layout.Nodup)
    (program : Assembly.Program)
    (segment :
      Structured.Preservation.CodeSegment program
        (Structured.Block.compileFromCtx
          { stmts := Expressions.StmtList.toStructured compiledStmts }
          structuredCtx supply).code)
    (hPc :
      state.pc = Structured.Preservation.CodeSegment.startPc segment)
    (hPrefixRel :
      Locals.SourceLowering.StackPrefixRel layout compiler [] state)
    {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    (hResolve :
      OpenExternal.OpenResultResolves
        (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          prim programSource sourceCtx sourceFuel { stmts := stmts }
          compiler)
        trace (.ok (sourceOutcome, ctxFinal))) :
    ∃ targetFuel targetResult,
      OpenExternal.OpenResultResolves
        (OpenAssembly.Source.openRunNResult program targetFuel state)
        trace (.ok targetResult) ∧
      FunctionsBlockCompiledOpenResultRel program structuredCtx
        (Structured.Preservation.CodeSegment.fallthroughPc segment)
        retc returns [] [] (sourceOutcome, ctxFinal) finalLocalsCtx
        targetResult := by
  induction stmts generalizing sourceCtx localsCtx finalLocalsCtx layout
      compiledStmts compiler state sourceFuel ctxFinal trace
      sourceOutcome with
  | nil =>
      exact
        compilerOpenFunctionsBlock_nil_openRunNResult_openResultRel_of_compileOpen
          (retc := retc) (returns := returns) hCtxRel hCompileBlock
          program segment hPc
          (by simpa [hCtxLayout] using hPrefixRel) hResolve
  | cons stmt rest ih =>
      cases sourceFuel with
      | zero =>
          rw [Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen]
            at hResolve
          cases hResolve
      | succ sourceFuel' =>
          cases stmt with
          | expr expr =>
              rcases hSupported with
                ⟨hOwned, hOpenSupported, hAccess, hRestSupported⟩
              exact
                compilerOpenFunctionsBlock_expr_cons_openRunNResult_compiledOpenResultRel_of_compileOpen_tail
                  hPrim hOwned hOpenSupported hAccess hCompileBlock
                  hCtxLayout hNoDup program segment hPc hPrefixRel
                  (hTail := by
                    intro tailStmts tailFinalCtx tailTrace sourceOutcome
                      tailCtxAfter compilerAfter evmAfter tailSegment
                      hRestCompile hRel hTailPc hRestResolve
                    exact
                      ih (sourceCtx := sourceCtx)
                        (ctxFinal := tailCtxAfter)
                        (sourceFuel := sourceFuel')
                        (localsCtx := localsCtx)
                        (finalLocalsCtx := tailFinalCtx)
                        (layout := layout)
                        (compiledStmts := tailStmts)
                        (compiler := compilerAfter)
                        (state := evmAfter)
                        (trace := tailTrace)
                        (sourceOutcome := sourceOutcome)
                        hRestSupported hCtxRel hRestCompile hCtxLayout
                        hNoDup tailSegment hTailPc hRel hRestResolve)
                  hResolve
          | let_ name valueExpr =>
              rcases hSupported with
                ⟨hOwned, hOpenSupported, hAccess, hFresh,
                  hRestSupported⟩
              have hCtxLayoutTail :
                  (localsCtx.withLayout (name :: localsCtx.layout)).layout =
                    name :: layout := by
                simp [Locals.Ctx.withLayout, hCtxLayout]
              have hNoDupTail : (name :: layout).Nodup := by
                simp [hFresh, hNoDup]
              exact
                compilerOpenFunctionsBlock_let_cons_openRunNResult_compiledOpenResultRel_of_compileOpen_tail
                  hPrim hOwned hOpenSupported hAccess hCompileBlock
                  hCtxLayout hNoDup hFresh program segment hPc hPrefixRel
                  (hTail := by
                    intro tailStmts tailFinalCtx tailTrace sourceOutcome
                      tailCtxAfter compilerAfter evmAfter tailSegment
                      hRestCompile hRel hTailPc hRestResolve
                    exact
                      ih
                        (sourceCtx :=
                          { sourceCtx with
                            scope := name :: sourceCtx.scope })
                        (ctxFinal := tailCtxAfter)
                        (sourceFuel := sourceFuel')
                        (localsCtx :=
                          localsCtx.withLayout
                            (name :: localsCtx.layout))
                        (finalLocalsCtx := tailFinalCtx)
                        (layout := name :: layout)
                        (compiledStmts := tailStmts)
                        (compiler := compilerAfter)
                        (state := evmAfter)
                        (trace := tailTrace)
                        (sourceOutcome := sourceOutcome)
                        hRestSupported
                        (Functions.SourceDirect.CtxRel.withScopeCons
                          hCtxRel)
                        hRestCompile hCtxLayoutTail hNoDupTail
                        tailSegment hTailPc hRel hRestResolve)
                  hResolve
          | assign name valueExpr =>
              rcases hSupported with
                ⟨hOwned, hOpenSupported, hAccess, hLookup,
                  hRestSupported⟩
              rcases hLookup with ⟨idx, hName, hBound⟩
              exact
                compilerOpenFunctionsBlock_assign_cons_openRunNResult_compiledOpenResultRel_of_compileOpen_tail
                  hPrim hOwned hOpenSupported hAccess hCompileBlock
                  hCtxLayout hNoDup hName hBound program segment hPc
                  hPrefixRel
                  (hTail := by
                    intro tailStmts tailFinalCtx tailTrace sourceOutcome
                      tailCtxAfter compilerAfter evmAfter tailSegment
                      hRestCompile hRel hTailPc hRestResolve
                    exact
                      ih (sourceCtx := sourceCtx)
                        (ctxFinal := tailCtxAfter)
                        (sourceFuel := sourceFuel')
                        (localsCtx := localsCtx)
                        (finalLocalsCtx := tailFinalCtx)
                        (layout := layout)
                        (compiledStmts := tailStmts)
                        (compiler := compilerAfter)
                        (state := evmAfter)
                        (trace := tailTrace)
                        (sourceOutcome := sourceOutcome)
                        hRestSupported hCtxRel hRestCompile hCtxLayout
                        hNoDup tailSegment hTailPc hRel hRestResolve)
                  hResolve
          | block body =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | if_ cond body =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | switch scrutinee cases defaultBody =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | for_ init cond post body =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | brk =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | cont =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | leave =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | call targets functionName args =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | terminal kind =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported
          | terminalArgs kind args =>
              simp [FunctionsStmtListRegularOpenSupported] at hSupported

def FunctionsBlockToAssemblySourceOpenSoundAt
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (asm : Assembly.Program)
    (ctx : Functions.Source.Ctx) (sourceFuel : Nat)
    (block : Functions.Block) (sourceInitial : Objects.Source.State)
    (evmInitial : EvmYul.EVM.State) : Prop :=
  ∀ {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    {ctxAfter : Functions.Source.Ctx},
    OpenExternal.OpenResultResolves
      (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
        prim program ctx sourceFuel block sourceInitial)
      trace (.ok (sourceOutcome, ctxAfter)) →
      ∃ targetFuel targetResult,
        OpenExternal.OpenResultResolves
          (OpenAssembly.Source.openRunNResult asm targetFuel evmInitial)
          trace (.ok targetResult) ∧
        Functions.Source.WholeProgramOutcomeRel sourceOutcome targetResult

def FunctionsBlockToCompiledOpenSoundAt
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (asm : Assembly.Program)
    (ctx : Functions.Source.Ctx) (sourceFuel : Nat)
    (block : Functions.Block) (sourceInitial : Objects.Source.State)
    (evmInitial : EvmYul.EVM.State) : Prop :=
  ∀ {trace : OpenExternal.OpenTrace}
    {sourceOutcome : Functions.Source.Outcome}
    {ctxAfter : Functions.Source.Ctx},
    OpenExternal.OpenResultResolves
      (Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
        prim program ctx sourceFuel block sourceInitial)
      trace (.ok (sourceOutcome, ctxAfter)) →
      ∃ targetFuel targetResult,
        OpenExternal.OpenResultResolves
          (OpenAssembly.Compiled.openRunNResult asm targetFuel evmInitial)
          trace (.ok targetResult) ∧
        Functions.Source.WholeProgramOutcomeRel sourceOutcome targetResult

namespace FunctionsBlockToAssemblySourceOpenSoundAt

theorem to_compiled
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {ctx : Functions.Source.Ctx} {sourceFuel : Nat}
    {block : Functions.Block} {sourceInitial : Objects.Source.State}
    {evmInitial : EvmYul.EVM.State}
    (hCompile : Assembly.compile? asm = some target)
    (hSound :
      FunctionsBlockToAssemblySourceOpenSoundAt prim program asm ctx
        sourceFuel block sourceInitial evmInitial) :
    FunctionsBlockToCompiledOpenSoundAt prim program asm ctx sourceFuel
      block sourceInitial evmInitial := by
  intro trace sourceOutcome ctxAfter hSource
  rcases hSound hSource with
    ⟨targetFuel, targetResult, hAssembly, hOutcome⟩
  rcases
      OpenAssembly.compile_openRunN_result_compiled_sound
        (target := target) hCompile hAssembly with
    ⟨_hAccepted, hCompiled⟩
  exact ⟨targetFuel, targetResult, hCompiled, hOutcome⟩

end FunctionsBlockToAssemblySourceOpenSoundAt

def FunctionsProgramToAssemblySourceOpenSoundAt
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (asm : Assembly.Program)
    (sourceFuel : Nat) (initial : EvmYul.EVM.State) : Prop :=
  FunctionsBlockToAssemblySourceOpenSoundAt prim program asm
    Functions.Source.Ctx.initial sourceFuel program.body
    (Functions.Source.Program.initialState initial.toSharedState) initial

def FunctionsProgramToCompiledOpenSoundAt
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (asm : Assembly.Program)
    (sourceFuel : Nat) (initial : EvmYul.EVM.State) : Prop :=
  FunctionsBlockToCompiledOpenSoundAt prim program asm
    Functions.Source.Ctx.initial sourceFuel program.body
    (Functions.Source.Program.initialState initial.toSharedState) initial

theorem FunctionsProgramToAssemblySourceOpenSoundAt.to_compiled
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {sourceFuel : Nat} {initial : EvmYul.EVM.State}
    (hCompile : Assembly.compile? asm = some target)
    (hSound :
      FunctionsProgramToAssemblySourceOpenSoundAt prim program asm
        sourceFuel initial) :
    FunctionsProgramToCompiledOpenSoundAt prim program asm sourceFuel
      initial :=
  FunctionsBlockToAssemblySourceOpenSoundAt.to_compiled hCompile hSound

end OpenLowering
end Yul
end EvmCompiler
