import EvmCompiler.Structured.Semantics
import EvmCompiler.Structured.Preservation
import EvmCompiler.Assembly.PrimSemantics

namespace EvmCompiler
namespace Structured
namespace StackResource

/--
Executable one-instruction stack effect.  `input` is the required visible stack
height and `output` is the visible height contributed after the instruction.
-/
structure Effect where
  input : Nat
  output : Nat
  deriving DecidableEq, Repr

namespace Effect

def apply? (effect : Effect) (height : Nat) : Option Nat :=
  if effect.input ≤ height then
    some (height - effect.input + effect.output)
  else
    none

theorem apply?_eq_some {effect : Effect} {height finalHeight : Nat}
    (hApply : effect.apply? height = some finalHeight) :
    finalHeight = height - effect.input + effect.output := by
  unfold apply? at hApply
  by_cases hInput : effect.input ≤ height
  · simp [hInput] at hApply
    exact hApply.symm
  · simp [hInput] at hApply

theorem apply?_shift {effect : Effect} {height finalHeight amount : Nat}
    (hApply : effect.apply? height = some finalHeight) :
    effect.apply? (height + amount) = some (finalHeight + amount) := by
  unfold apply? at hApply ⊢
  by_cases hInput : effect.input ≤ height
  · have hInputShift : effect.input ≤ height + amount := by omega
    simp [hInput, hInputShift] at hApply ⊢
    cases hApply
    omega
  · simp [hInput] at hApply

end Effect

/-- Summary of straight-line stack usage from one fixed entry height. -/
structure Summary where
  finalHeight : Nat
  peakHeight : Nat
  deriving DecidableEq, Repr

namespace Summary

def pure (height : Nat) : Summary where
  finalHeight := height
  peakHeight := height

def shift (summary : Summary) (amount : Nat) : Summary where
  finalHeight := summary.finalHeight + amount
  peakHeight := summary.peakHeight + amount

def bind? (summary : Summary) (effect : Effect) : Option Summary := do
  let finalHeight ← effect.apply? summary.finalHeight
  some
    { finalHeight := finalHeight
      peakHeight := max summary.peakHeight finalHeight }

theorem bind?_eq_some {summary next : Summary} {effect : Effect}
    (hBind : summary.bind? effect = some next) :
    next.finalHeight =
        summary.finalHeight - effect.input + effect.output ∧
      next.peakHeight = max summary.peakHeight next.finalHeight := by
  unfold bind? at hBind
  cases hApply : effect.apply? summary.finalHeight with
  | none =>
      simp [hApply] at hBind
  | some finalHeight =>
      simp [hApply] at hBind
      cases hBind
      exact ⟨Effect.apply?_eq_some hApply, rfl⟩

theorem pure_shift (height amount : Nat) :
    shift (pure height) amount = pure (height + amount) := by
  simp [shift, pure]

theorem bind?_shift {summary next : Summary} {effect : Effect}
    {amount : Nat}
    (hBind : summary.bind? effect = some next) :
    (summary.shift amount).bind? effect =
      some (next.shift amount) := by
  unfold bind? at hBind ⊢
  cases hApply : effect.apply? summary.finalHeight with
  | none =>
      simp [hApply] at hBind
  | some finalHeight =>
      simp [hApply] at hBind
      cases hBind
      have hApplyShift :=
        Effect.apply?_shift (amount := amount) hApply
      simp [shift, hApplyShift]

end Summary

namespace BasicOp

def effect? (op : BasicOp) : Option Effect :=
  match op.toPrimOp.continuingStep? with
  | some step =>
      some
        { input := Assembly.PrimStep.inputArity step
          output := Assembly.PrimStep.outputArity step }
  | none => none

theorem step_stack_length_of_effect?
    {op : BasicOp} {effect : Effect} {state state' : EVMState}
    (hEffect : effect? op = some effect)
    (hStep : op.step state = .ok state') :
    state'.stack.length =
      state.stack.length - effect.input + effect.output := by
  unfold effect? at hEffect
  cases hCont : op.toPrimOp.continuingStep? with
  | none =>
      simp [hCont] at hEffect
  | some step =>
      simp [hCont] at hEffect
      cases hEffect
      have hRun :
          step.run state = .ok state' := by
        simpa [BasicOp.step, Assembly.Target.stepInstr,
          Assembly.PrimOp.step_eq_continuingStep_run hCont] using hStep
      cases step with
      | dup n =>
          have hArity := Assembly.PrimStep.run_inputArity_le hRun
          have hLen := Assembly.PrimStep.run_dup_stack_length hRun
          simp [Assembly.PrimStep.inputArity] at hArity
          rw [hLen]
          simp [Assembly.PrimStep.inputArity,
            Assembly.PrimStep.outputArity]
          omega
      | swap n =>
          have hArity := Assembly.PrimStep.run_inputArity_le hRun
          have hPos : 1 ≤ n :=
            Assembly.PrimOp.continuingStep?_swap_pos hCont
          have hLen :=
            Assembly.PrimStep.run_swap_stack_length_of_pos hPos hRun
          simp [Assembly.PrimStep.inputArity] at hArity
          rw [hLen]
          simp [Assembly.PrimStep.inputArity,
            Assembly.PrimStep.outputArity]
          omega
      | invalid =>
          simp [Assembly.PrimStep.run] at hRun
      | un f | bin f | tri f | executionEnv f | machineState f | state f
      | unaryExecutionEnv f | unaryState f | pop | mload
      | binaryMachineState f | binaryMachineStateWithResult f
      | binaryState f | log0 | ternaryMachineState f | ternaryCopy f
      | returndatacopy | log1 | quaternaryCopy f | log2 | log3 | log4 =>
          have hLen :=
            Assembly.PrimStep.run_stack_length_safe
              (step := _) (state := state) (evm' := state')
              (by simp [Assembly.PrimStep.SuffixSafe]) hRun
          simpa using hLen

end BasicOp

namespace BasicInstr

def effect? : BasicInstr → Option Effect
  | .push _ => some { input := 0, output := 1 }
  | .op op => BasicOp.effect? op

theorem step_stack_length_of_effect?
    {instr : BasicInstr} {effect : Effect} {state state' : EVMState}
    (hEffect : effect? instr = some effect)
    (hStep : instr.step state = .ok state') :
    state'.stack.length =
      state.stack.length - effect.input + effect.output := by
  cases instr with
  | push value =>
      simp [effect?] at hEffect
      cases hEffect
      simp [BasicInstr.step, Assembly.Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
  | op op =>
      exact BasicOp.step_stack_length_of_effect? hEffect hStep

end BasicInstr

namespace Code

def analyzeFrom? (height : Nat) : Code → Option Summary
  | [] => some (Summary.pure height)
  | instr :: rest => do
      let effect ← BasicInstr.effect? instr
      let headSummary ← (Summary.pure height).bind? effect
      let tailSummary ← analyzeFrom? headSummary.finalHeight rest
      some
        { finalHeight := tailSummary.finalHeight
          peakHeight := max headSummary.peakHeight tailSummary.peakHeight }

def stackSafeFrom? (height reserved maxStack : Nat) (code : Code) : Bool :=
  match analyzeFrom? height code with
  | none => false
  | some summary => summary.peakHeight + reserved ≤ maxStack

def RunStackBoundedBy : Code → EVMState → Nat → Prop
  | [], state, bound => state.stack.length ≤ bound
  | instr :: rest, state, bound =>
      ∀ mid, instr.step state = .ok mid →
        mid.stack.length ≤ bound ∧ RunStackBoundedBy rest mid bound

theorem runStackBoundedBy_mono
    {code : Code} {state : EVMState} {bound bound' : Nat}
    (hBound : RunStackBoundedBy code state bound)
    (hLe : bound ≤ bound') :
    RunStackBoundedBy code state bound' := by
  induction code generalizing state with
  | nil =>
      simp [RunStackBoundedBy] at hBound ⊢
      omega
  | cons instr rest ih =>
      intro mid hStep
      rcases hBound mid hStep with ⟨hMid, hRest⟩
      exact ⟨by omega, ih hRest⟩

theorem stackSafeFrom?_eq_true
    {height reserved maxStack : Nat} {code : Code}
    (hSafe : stackSafeFrom? height reserved maxStack code = true) :
    ∃ summary,
      analyzeFrom? height code = some summary ∧
        summary.peakHeight + reserved ≤ maxStack := by
  unfold stackSafeFrom? at hSafe
  cases hAnalyze : analyzeFrom? height code with
  | none =>
      simp [hAnalyze] at hSafe
  | some summary =>
      simp [hAnalyze] at hSafe
      exact ⟨summary, rfl, hSafe⟩

theorem analyzeFrom?_final_le_peak
    {height : Nat} {code : Code} {summary : Summary}
    (hAnalyze : analyzeFrom? height code = some summary) :
    summary.finalHeight ≤ summary.peakHeight := by
  induction code generalizing height summary with
  | nil =>
      simp [analyzeFrom?] at hAnalyze
      cases hAnalyze
      simp [Summary.pure]
  | cons instr rest ih =>
      simp [analyzeFrom?] at hAnalyze
      cases hEffect : BasicInstr.effect? instr with
      | none =>
          simp [hEffect] at hAnalyze
      | some effect =>
          cases hHead :
              (Summary.pure height).bind? effect with
          | none =>
              simp [hEffect, hHead] at hAnalyze
          | some headSummary =>
              cases hTail :
                  analyzeFrom? headSummary.finalHeight rest with
              | none =>
                  simp [hEffect, hHead, hTail] at hAnalyze
              | some tailSummary =>
                  simp [hEffect, hHead, hTail] at hAnalyze
                  cases hAnalyze
                  have hTailLe := ih hTail
                  simp
                  omega

theorem analyzeFrom?_height_le_peak
    {height : Nat} {code : Code} {summary : Summary}
    (hAnalyze : analyzeFrom? height code = some summary) :
    height ≤ summary.peakHeight := by
  induction code generalizing height summary with
  | nil =>
      simp [analyzeFrom?] at hAnalyze
      cases hAnalyze
      simp [Summary.pure]
  | cons instr rest ih =>
      simp [analyzeFrom?] at hAnalyze
      cases hEffect : BasicInstr.effect? instr with
      | none =>
          simp [hEffect] at hAnalyze
      | some effect =>
          cases hHead :
              (Summary.pure height).bind? effect with
          | none =>
              simp [hEffect, hHead] at hAnalyze
          | some headSummary =>
              cases hTail :
                  analyzeFrom? headSummary.finalHeight rest with
              | none =>
                  simp [hEffect, hHead, hTail] at hAnalyze
              | some tailSummary =>
                  simp [hEffect, hHead, hTail] at hAnalyze
                  cases hAnalyze
                  have hHeadPeak := (Summary.bind?_eq_some hHead).2
                  simp [hHeadPeak, Summary.pure]

theorem analyzeFrom?_shift
    {height amount : Nat} {code : Code} {summary : Summary}
    (hAnalyze : analyzeFrom? height code = some summary) :
    analyzeFrom? (height + amount) code =
      some (summary.shift amount) := by
  induction code generalizing height summary with
  | nil =>
      simp [analyzeFrom?] at hAnalyze ⊢
      cases hAnalyze
      simp [Summary.shift, Summary.pure]
  | cons instr rest ih =>
      simp [analyzeFrom?] at hAnalyze ⊢
      cases hEffect : BasicInstr.effect? instr with
      | none =>
          simp [hEffect] at hAnalyze
      | some effect =>
          cases hHead :
              (Summary.pure height).bind? effect with
          | none =>
              simp [hEffect, hHead] at hAnalyze
          | some headSummary =>
              cases hTail :
                  analyzeFrom? headSummary.finalHeight rest with
              | none =>
                  simp [hEffect, hHead, hTail] at hAnalyze
              | some tailSummary =>
                  simp [hEffect, hHead, hTail] at hAnalyze
                  cases hAnalyze
                  have hHeadShift :
                      (Summary.pure (height + amount)).bind? effect =
                        some (headSummary.shift amount) := by
                    simpa [Summary.pure_shift] using
                      Summary.bind?_shift (amount := amount) hHead
                  have hTailShift :
                      analyzeFrom?
                          (headSummary.finalHeight + amount) rest =
                        some (tailSummary.shift amount) := by
                    exact
                      ih (height := headSummary.finalHeight)
                        (summary := tailSummary) hTail
                  simp [hHeadShift, hTailShift, Summary.shift]

theorem run_stack_length_of_analyzeFrom?
    {height : Nat} {code : Code} {summary : Summary}
    {state final : EVMState}
    (hAnalyze : analyzeFrom? height code = some summary)
    (hHeight : state.stack.length = height)
    (hRun : Code.run code state = .ok final) :
    final.stack.length = summary.finalHeight := by
  induction code generalizing height summary state final with
  | nil =>
      simp [analyzeFrom?] at hAnalyze
      cases hAnalyze
      simp [Code.run] at hRun
      cases hRun
      simpa [Summary.pure] using hHeight
  | cons instr rest ih =>
      simp [analyzeFrom?] at hAnalyze
      cases hEffect : BasicInstr.effect? instr with
      | none =>
          simp [hEffect] at hAnalyze
      | some effect =>
          cases hHead :
              (Summary.pure height).bind? effect with
          | none =>
              simp [hEffect, hHead] at hAnalyze
          | some headSummary =>
              cases hTail :
                  analyzeFrom? headSummary.finalHeight rest with
              | none =>
                  simp [hEffect, hHead, hTail] at hAnalyze
              | some tailSummary =>
                  simp [hEffect, hHead, hTail] at hAnalyze
                  cases hAnalyze
                  change
                    (do
                        let state' ← instr.step state
                        Code.run rest state') =
                      .ok final at hRun
                  cases hStep : instr.step state with
                  | error err =>
                      rw [hStep] at hRun
                      simp [Bind.bind, Except.bind] at hRun
                  | ok mid =>
                      rw [hStep] at hRun
                      have hInstrLen :=
                        BasicInstr.step_stack_length_of_effect?
                          hEffect hStep
                      have hHeadFinal :=
                        (Summary.bind?_eq_some hHead).1
                      have hMidHeight :
                          mid.stack.length = headSummary.finalHeight := by
                        rw [hInstrLen, hHeight, hHeadFinal]
                        simp [Summary.pure]
                      simpa using
                        ih (height := headSummary.finalHeight)
                          (summary := tailSummary) hTail hMidHeight hRun

theorem run_stack_bounded_of_analyzeFrom?
    {height : Nat} {code : Code} {summary : Summary}
    {state final : EVMState}
    (hAnalyze : analyzeFrom? height code = some summary)
    (hHeight : state.stack.length = height)
    (hRun : Code.run code state = .ok final) :
    RunStackBoundedBy code state summary.peakHeight := by
  induction code generalizing height summary state final with
  | nil =>
      simp [analyzeFrom?] at hAnalyze
      cases hAnalyze
      simp [RunStackBoundedBy, Summary.pure, hHeight]
  | cons instr rest ih =>
      simp [analyzeFrom?] at hAnalyze
      cases hEffect : BasicInstr.effect? instr with
      | none =>
          simp [hEffect] at hAnalyze
      | some effect =>
          cases hHead :
              (Summary.pure height).bind? effect with
          | none =>
              simp [hEffect, hHead] at hAnalyze
          | some headSummary =>
              cases hTail :
                  analyzeFrom? headSummary.finalHeight rest with
              | none =>
                  simp [hEffect, hHead, hTail] at hAnalyze
              | some tailSummary =>
                  simp [hEffect, hHead, hTail] at hAnalyze
                  cases hAnalyze
                  change
                    (do
                        let state' ← instr.step state
                        Code.run rest state') =
                      .ok final at hRun
                  cases hStep : instr.step state with
                  | error err =>
                      rw [hStep] at hRun
                      simp [Bind.bind, Except.bind] at hRun
                  | ok mid =>
                      rw [hStep] at hRun
                      have hInstrLen :=
                        BasicInstr.step_stack_length_of_effect?
                          hEffect hStep
                      have hHeadFinal :=
                        (Summary.bind?_eq_some hHead).1
                      have hHeadPeak :=
                        (Summary.bind?_eq_some hHead).2
                      have hMidHeight :
                          mid.stack.length = headSummary.finalHeight := by
                        rw [hInstrLen, hHeight, hHeadFinal]
                        simp [Summary.pure]
                      have hMidBound :
                          mid.stack.length ≤
                            max headSummary.peakHeight
                              tailSummary.peakHeight := by
                        rw [hMidHeight, hHeadPeak]
                        simp [Summary.pure]
                      have hRestBound :
                          RunStackBoundedBy rest mid
                            tailSummary.peakHeight :=
                        ih (height := headSummary.finalHeight)
                          (summary := tailSummary) hTail hMidHeight hRun
                      intro observed hObserved
                      rw [hStep] at hObserved
                      cases hObserved
                      exact
                        ⟨hMidBound,
                          runStackBoundedBy_mono hRestBound
                            (by simp)⟩

theorem runStackBoundedBy_of_analyzeFrom?
    {height : Nat} {code : Code} {summary : Summary}
    {state : EVMState}
    (hAnalyze : analyzeFrom? height code = some summary)
    (hHeight : state.stack.length = height) :
    RunStackBoundedBy code state summary.peakHeight := by
  induction code generalizing height summary state with
  | nil =>
      simp [analyzeFrom?] at hAnalyze
      cases hAnalyze
      simp [RunStackBoundedBy, Summary.pure, hHeight]
  | cons instr rest ih =>
      simp [analyzeFrom?] at hAnalyze
      cases hEffect : BasicInstr.effect? instr with
      | none =>
          simp [hEffect] at hAnalyze
      | some effect =>
          cases hHead :
              (Summary.pure height).bind? effect with
          | none =>
              simp [hEffect, hHead] at hAnalyze
          | some headSummary =>
              cases hTail :
                  analyzeFrom? headSummary.finalHeight rest with
              | none =>
                  simp [hEffect, hHead, hTail] at hAnalyze
              | some tailSummary =>
                  simp [hEffect, hHead, hTail] at hAnalyze
                  cases hAnalyze
                  intro mid hStep
                  have hInstrLen :=
                    BasicInstr.step_stack_length_of_effect?
                      hEffect hStep
                  have hHeadFinal :=
                    (Summary.bind?_eq_some hHead).1
                  have hHeadPeak :=
                    (Summary.bind?_eq_some hHead).2
                  have hMidHeight :
                      mid.stack.length = headSummary.finalHeight := by
                    rw [hInstrLen, hHeight, hHeadFinal]
                    simp [Summary.pure]
                  have hMidBound :
                      mid.stack.length ≤
                        max headSummary.peakHeight tailSummary.peakHeight := by
                    rw [hMidHeight, hHeadPeak]
                    simp [Summary.pure]
                  have hRestBound :
                      RunStackBoundedBy rest mid tailSummary.peakHeight :=
                    ih (height := headSummary.finalHeight)
                      (summary := tailSummary) hTail hMidHeight
                  exact
                    ⟨hMidBound,
                      runStackBoundedBy_mono hRestBound (by simp)⟩

theorem source_runResult_stackBoundPoints_of_relAt
    {code : Code} {pre post : Assembly.Program}
    {source target source' : EVMState} {bound : Nat}
    (hSafe : Preservation.Code.RunnerSafe code)
    (hFits : Preservation.Code.PCFitsFrom pre code)
    (hRel :
      Preservation.RelAt (Assembly.Program.pcAfter pre) target source)
    (hRun : Code.run code source = .ok source')
    (hBound : RunStackBoundedBy code target bound)
    (hInitial : target.stack.length ≤ bound) :
    Preservation.ARunResultPoints
      (pre ++ code.toAssembly ++ post)
      (fun state => state.stack.length ≤ bound)
      target
      (fun result =>
        match result with
        | .running target' =>
            Preservation.RelAt
              (Assembly.Program.pcAfter (pre ++ code.toAssembly))
              target' source'
        | .halted _ => False) := by
  induction code generalizing pre source target with
  | nil =>
      simp [Code.run] at hRun
      cases hRun
      refine Preservation.ARunResultPoints.pure hInitial ?_
      simpa [Code.toAssembly, Assembly.Program.byteLength_append,
        Assembly.Program.pcAfter] using hRel
  | cons instr rest ih =>
      cases hSafe with
      | cons hInstr hRestSafe =>
          unfold Code.run at hRun
          cases hStep : instr.step source with
          | error _err =>
              rw [hStep] at hRun
              cases hRun
          | ok sourceMid =>
              rw [hStep] at hRun
              rcases hFits with ⟨hFitHere, hFitsRest⟩
              obtain ⟨targetMid, hTargetStep, hSameData⟩ :=
                hInstr.controlSafe hRel.sameData hStep
              rcases hBound targetMid hTargetStep with
                ⟨hMidBound, hRestBound⟩
              have hStepResult :
                  Assembly.Source.stepResult
                      (pre ++ Code.toAssembly (instr :: rest) ++ post)
                      target =
                    .ok (.running targetMid) := by
                rw [show
                    pre ++ Code.toAssembly (instr :: rest) ++ post =
                      pre ++ instr.toAssembly ::
                        (Code.toAssembly rest ++ post) by
                      simp [Code.toAssembly, List.append_assoc]]
                unfold Assembly.Source.stepResult
                have hAt :
                    Assembly.Program.instrAtPc
                        (pre ++ instr.toAssembly ::
                          (Code.toAssembly rest ++ post))
                        target.pc.toNat =
                      some (Assembly.Program.byteLength pre,
                        instr.toAssembly) := by
                  unfold Assembly.Program.instrAtPc
                  rw [hRel.pc_eq, hFitHere]
                  simpa using
                    Assembly.Program.instrAtPcFrom_append_boundary_cons
                      pre (Code.toAssembly rest ++ post)
                      instr.toAssembly 0
                rw [hAt]
                simp [Assembly.Source.stepAtResult,
                  Preservation.BasicInstr.source_stepAt_eq_step,
                  hTargetStep,
                  Preservation.BasicInstr.toAssembly_haltKind?_none,
                  Bind.bind, Except.bind]
              have hRelMid :
                  Preservation.RelAt
                    (Assembly.Program.pcAfter (pre ++ [instr.toAssembly]))
                    targetMid sourceMid := by
                refine ⟨?_, hSameData⟩
                calc
                  targetMid.pc
                      =
                        target.pc +
                          EvmYul.UInt256.ofNat instr.toAssembly.byteSize :=
                          hInstr.stepPC hTargetStep
                  _ =
                        Assembly.Program.pcAfter pre +
                          EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
                          rw [hRel.pc_eq]
                  _ =
                        EvmYul.UInt256.ofNat
                            (Assembly.Program.byteLength pre) +
                          EvmYul.UInt256.ofNat instr.toAssembly.byteSize := by
                          rfl
                  _ =
                        EvmYul.UInt256.ofNat
                          (Assembly.Program.byteLength pre +
                            instr.toAssembly.byteSize) := by
                          rw [Assembly.UInt256_ofNat_add]
                  _ =
                        Assembly.Program.pcAfter
                          (pre ++ [instr.toAssembly]) := by
                          simp [Assembly.Program.pcAfter,
                            Assembly.Program.byteLength_append,
                            Assembly.Program.byteLength]
              refine
                Preservation.ARunResultPoints.bind_running
                  (program := pre ++ Code.toAssembly (instr :: rest) ++ post)
                  (point := fun state => state.stack.length ≤ bound)
                  (middle := fun stateAfterInstr =>
                    Preservation.RelAt
                        (Assembly.Program.pcAfter
                          (pre ++ [instr.toAssembly]))
                        stateAfterInstr sourceMid ∧
                      stateAfterInstr.stack.length ≤ bound ∧
                      RunStackBoundedBy rest stateAfterInstr bound)
                  ?_ ?_
              · refine
                  ⟨1, .running targetMid,
                    Preservation.SourceRunResultPoints.stepRunning
                      hInitial ?_ (Preservation.SourceRunResultPoints.done
                        hMidBound),
                    ⟨hRelMid, hMidBound, hRestBound⟩⟩
                simpa [Code.toAssembly, List.append_assoc] using hStepResult
              · intro stateAfterInstr hMiddle
                rcases hMiddle with
                  ⟨hRelAfterInstr, hStackBoundAfterInstr,
                    hRestBoundAfterInstr⟩
                have hRestRun :
                    Code.run rest sourceMid = .ok source' := hRun
                simpa [Code.toAssembly, List.append_assoc] using
                  ih (pre := pre ++ [instr.toAssembly])
                    hRestSafe hFitsRest hRelAfterInstr hRestRun
                    hRestBoundAfterInstr hStackBoundAfterInstr

theorem source_runResult_stackBoundPoints_of_analyzeFrom?
    {code : Code} {pre post : Assembly.Program}
    {source target source' : EVMState}
    {height bound : Nat} {summary : Summary}
    (hSafe : Preservation.Code.RunnerSafe code)
    (hFits : Preservation.Code.PCFitsFrom pre code)
    (hRel :
      Preservation.RelAt (Assembly.Program.pcAfter pre) target source)
    (hRun : Code.run code source = .ok source')
    (hAnalyze : analyzeFrom? height code = some summary)
    (hHeight : target.stack.length = height)
    (hPeak : summary.peakHeight ≤ bound) :
    Preservation.ARunResultPoints
      (pre ++ code.toAssembly ++ post)
      (fun state => state.stack.length ≤ bound)
      target
      (fun result =>
        match result with
        | .running target' =>
            Preservation.RelAt
              (Assembly.Program.pcAfter (pre ++ code.toAssembly))
              target' source'
        | .halted _ => False) := by
  have hBound :
      RunStackBoundedBy code target bound :=
    runStackBoundedBy_mono
      (runStackBoundedBy_of_analyzeFrom? hAnalyze hHeight)
      hPeak
  have hInitial : target.stack.length ≤ bound := by
    rw [hHeight]
    exact le_trans (analyzeFrom?_height_le_peak hAnalyze) hPeak
  exact
    source_runResult_stackBoundPoints_of_relAt
      hSafe hFits hRel hRun hBound hInitial

theorem source_runResult_stackHeadroomPoints_of_analyzeFrom?
    {code : Code} {pre post : Assembly.Program}
    {source target source' : EVMState}
    {height : Nat} {summary : Summary}
    (hSafe : Preservation.Code.RunnerSafe code)
    (hFits : Preservation.Code.PCFitsFrom pre code)
    (hRel :
      Preservation.RelAt (Assembly.Program.pcAfter pre) target source)
    (hRun : Code.run code source = .ok source')
    (hAnalyze : analyzeFrom? height code = some summary)
    (hHeight : target.stack.length = height)
    (hPeakHeadroom : summary.peakHeight + 17 ≤ 1024) :
    Preservation.ARunResultPoints
      (pre ++ code.toAssembly ++ post)
      (fun state => state.stack.length + 17 ≤ 1024)
      target
      (fun result =>
        match result with
        | .running target' =>
            Preservation.RelAt
              (Assembly.Program.pcAfter (pre ++ code.toAssembly))
              target' source'
        | .halted _ => False) :=
  (source_runResult_stackBoundPoints_of_analyzeFrom?
      hSafe hFits hRel hRun hAnalyze hHeight (by rfl)).point_mono
    (fun _state hBound => by omega)

end Code

theorem primStep_run_pc {step : Assembly.PrimStep} {state mid : EVMState}
    (hRun : step.run state = .ok mid) :
    mid.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases step <;>
    simp [Assembly.PrimStep.run, EvmYul.EVM.execBinOp, EvmYul.EVM.execUnOp,
      EvmYul.EVM.execTriOp, EvmYul.EVM.executionEnvOp,
      EvmYul.EVM.unaryExecutionEnvOp, EvmYul.EVM.machineStateOp,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.EVM.binaryMachineStateOp',
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
    | contradiction
    | cases hRun
      rfl
namespace AssemblyInstr

/--
Stack effect for assembly instructions that can continue normally under
`Assembly.Source.stepAtResult`.

Terminal instructions have no running successor, while non-continuing
non-terminal primitives such as raw `PC`/CALL-family opcodes are left
unsupported by the executable checker.
-/
def runningEffect? : Assembly.Instr → Option Effect
  | .label _ => some { input := 0, output := 0 }
  | .push _ => some { input := 0, output := 1 }
  | .jump _ => some { input := 0, output := 0 }
  | .jumpi _ => some { input := 1, output := 0 }
  | .prim op =>
      match op.haltKind? with
      | some _ => none
      | none =>
          match op.continuingStep? with
          | some step =>
              some
                { input := Assembly.PrimStep.inputArity step
                  output := Assembly.PrimStep.outputArity step }
          | none => none

theorem stepAtResult_running_stack_length_of_effect?
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {effect : Effect} {state mid : EVMState}
    (hEffect : runningEffect? instr = some effect)
    (hStep :
      Assembly.Source.stepAtResult program pc instr state =
        .ok (.running mid)) :
    mid.stack.length =
      state.stack.length - effect.input + effect.output := by
  cases instr with
  | label label =>
      simp [runningEffect?] at hEffect
      cases hEffect
      simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
        Assembly.Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.incrPC]
  | push value =>
      simp [runningEffect?] at hEffect
      cases hEffect
      simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
        Assembly.Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
  | jump target =>
      simp [runningEffect?] at hEffect
      cases hEffect
      unfold Assembly.Source.stepAtResult at hStep
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.Source.stepAt, hDest, Assembly.Source.invalid,
            Bind.bind, Except.bind] at hStep
      | some dest =>
          simp [Assembly.Source.stepAt, hDest, Assembly.Source.jumpPc] at hStep
          cases hStep
          simp
  | jumpi target =>
      simp [runningEffect?] at hEffect
      cases hEffect
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            hDest, Assembly.Source.invalid, Bind.bind, Except.bind] at hStep
      | some dest =>
          simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Instr.haltKind?, hDest] at hStep
          cases hPop : state.stack.pop with
          | none =>
              simp [hPop] at hStep
              change
                (Except.error EvmYul.EVM.ExecutionException.StackUnderflow :
                  Except EVMException Assembly.StepResult) =
                  .ok (.running mid) at hStep
              cases hStep
          | some popped =>
              rcases popped with ⟨stack, cond⟩
              simp [hPop] at hStep
              cases hStep
              have hLen : state.stack.length = stack.length + 1 :=
                Assembly.PrimStep.Stack.length_of_pop_some hPop
              simp [hLen]
  | prim op =>
      unfold runningEffect? at hEffect
      cases hHalt : op.haltKind? with
      | some kind =>
          simp [hHalt] at hEffect
      | none =>
          simp [hHalt] at hEffect
          cases hCont : op.continuingStep? with
          | none =>
              simp [hCont] at hEffect
          | some step =>
              simp [hCont] at hEffect
              cases hEffect
              unfold Assembly.Source.stepAtResult at hStep
              simp [Assembly.Source.stepAt, Assembly.Instr.haltKind?,
                hHalt] at hStep
              have hRun :
                  step.run state = .ok mid := by
                have hStep' := hStep
                simp [Assembly.Target.stepInstr,
                  Assembly.PrimOp.step_eq_continuingStep_run hCont,
                  Bind.bind, Except.bind] at hStep'
                cases hRunStep : step.run state with
                | error err =>
                    rw [hRunStep] at hStep'
                    simp at hStep'
                | ok mid' =>
                    rw [hRunStep] at hStep'
                    simp at hStep'
                    cases hStep'
                    rfl
              cases step with
              | dup n =>
                  have hArity := Assembly.PrimStep.run_inputArity_le hRun
                  have hLen := Assembly.PrimStep.run_dup_stack_length hRun
                  simp [Assembly.PrimStep.inputArity] at hArity
                  rw [hLen]
                  simp [Assembly.PrimStep.inputArity,
                    Assembly.PrimStep.outputArity]
                  omega
              | swap n =>
                  have hPos : 1 ≤ n :=
                    Assembly.PrimOp.continuingStep?_swap_pos hCont
                  have hArity := Assembly.PrimStep.run_inputArity_le hRun
                  have hLen :=
                    Assembly.PrimStep.run_swap_stack_length_of_pos hPos hRun
                  simp [Assembly.PrimStep.inputArity] at hArity
                  rw [hLen]
                  simp [Assembly.PrimStep.inputArity,
                    Assembly.PrimStep.outputArity]
                  omega
              | invalid =>
                  simp [Assembly.PrimStep.run] at hRun
              | un f | bin f | tri f | executionEnv f | machineState f
              | state f | unaryExecutionEnv f | unaryState f | pop | mload
              | binaryMachineState f | binaryMachineStateWithResult f
              | binaryState f | log0 | ternaryMachineState f
              | ternaryCopy f | returndatacopy | log1 | quaternaryCopy f
              | log2 | log3 | log4 =>
                  have hLen :=
                    Assembly.PrimStep.run_stack_length_safe
                      (step := _) (state := state) (evm' := mid)
                      (by simp [Assembly.PrimStep.SuffixSafe]) hRun
                  simpa using hLen

theorem stepAtResult_running_stack_le_of_effect?
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {effect : Effect} {state mid : EVMState}
    {bound nextBound : Nat}
    (hEffect : runningEffect? instr = some effect)
    (hBound : state.stack.length ≤ bound)
    (hNext :
      bound - effect.input + effect.output ≤ nextBound)
    (hStep :
      Assembly.Source.stepAtResult program pc instr state =
        .ok (.running mid)) :
    mid.stack.length ≤ nextBound := by
  have hLen :=
    stepAtResult_running_stack_length_of_effect?
      (program := program) (pc := pc) (instr := instr)
      (effect := effect) hEffect hStep
  rw [hLen]
  have hMono :
      state.stack.length - effect.input + effect.output ≤
        bound - effect.input + effect.output := by
    exact Nat.add_le_add_right
      (Nat.sub_le_sub_right hBound effect.input) effect.output
  exact le_trans hMono hNext

theorem stepAtResult_running_of_emit_runListResult
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {emitted : List Assembly.LocatedTarget}
    {state mid : EVMState}
    (hEmit : Assembly.emitInstr? program pc instr = some emitted)
    (hRun :
      Assembly.Target.runListResult
          (emitted.map Assembly.LocatedTarget.instr) state =
        .ok (.running mid)) :
    Assembly.Source.stepAtResult program pc instr state = .ok (.running mid) := by
  cases instr with
  | label name =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      simpa [Assembly.Preservation.runListResult_single] using hRun
  | prim op =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      simpa [Assembly.Preservation.runListResult_single] using hRun
  | push value =>
      simp [Assembly.emitInstr?] at hEmit
      subst emitted
      simpa [Assembly.Preservation.runListResult_single] using hRun
  | jump target =>
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.emitInstr?, hDest] at hEmit
      | some dest =>
          simp [Assembly.emitInstr?, hDest] at hEmit
          subst emitted
          have hRun' :
              Assembly.Target.runListResult
                  [ Assembly.TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
                  , Assembly.TargetInstr.jump
                  ] state =
                .ok (.running mid) := by
            simpa using hRun
          rw [Assembly.Preservation.run_push_jump_result] at hRun'
          simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Source.jumpPc, Assembly.Instr.haltKind?, hDest] at hRun' ⊢
          exact hRun'
  | jumpi target =>
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [Assembly.emitInstr?, hDest] at hEmit
      | some dest =>
          simp [Assembly.emitInstr?, hDest] at hEmit
          subst emitted
          have hRun' :
              Assembly.Target.runListResult
                  [ Assembly.TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
                  , Assembly.TargetInstr.jumpi
                  ] state =
                .ok (.running mid) := by
            simpa using hRun
          rw [Assembly.Preservation.run_push_jumpi_result] at hRun'
          simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Instr.haltKind?, hDest] at hRun' ⊢
          cases hPop : state.stack.pop with
          | none =>
              simp [hPop] at hRun'
          | some popped =>
              rcases popped with ⟨stack, cond⟩
              simp [hPop] at hRun' ⊢
              exact hRun'

end AssemblyInstr

namespace AssemblyBounds

abbrev BoundTable := List (Word × Nat)

def lookupBound? : BoundTable → Word → Option Nat
  | [], _ => none
  | (pc, bound) :: rest, query =>
      if query = pc then
        some bound
      else
        lookupBound? rest query

def fallthroughPc (pc : Nat) (delta : Nat) : Word :=
  EvmYul.UInt256.ofNat pc + EvmYul.UInt256.ofNat delta

def jumpiFallthroughPc (pc : Nat) : Word :=
  EvmYul.UInt256.ofNat pc +
    EvmYul.UInt256.ofNat Assembly.Instr.push32Size +
      EvmYul.UInt256.ofNat 1

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
      match op.haltKind? with
      | some _ => some []
      | none =>
          match op.continuingStep? with
          | some _ => some [fallthroughPc pc 1]
          | none => none

def successorBoundOk? (table : BoundTable) (height reserved maxStack : Nat)
    (pc : Word) : Bool :=
  match lookupBound? table pc with
  | none => false
  | some bound =>
      decide (height ≤ bound) &&
        decide (bound + reserved ≤ maxStack)

def successorsBoundOk? (table : BoundTable) (height reserved maxStack : Nat) :
    List Word → Bool
  | [] => true
  | pc :: rest =>
      successorBoundOk? table height reserved maxStack pc &&
        successorsBoundOk? table height reserved maxStack rest

def instructionBoundOk? (program : Assembly.Program) (table : BoundTable)
    (reserved maxStack pc : Nat) (instr : Assembly.Instr) : Bool :=
  match lookupBound? table (EvmYul.UInt256.ofNat pc),
      AssemblyInstr.runningEffect? instr,
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

def insertMaxBound (pc : Word) (height : Nat) : BoundTable → BoundTable
  | [] => [(pc, height)]
  | (entryPc, bound) :: rest =>
      if pc = entryPc then
        (entryPc, Nat.max bound height) :: rest
      else
        (entryPc, bound) :: insertMaxBound pc height rest

def seedProgramBoundsFrom : Assembly.Program → Nat → BoundTable
  | [], pc => [(EvmYul.UInt256.ofNat pc, 0)]
  | instr :: rest, pc =>
      (EvmYul.UInt256.ofNat pc, 0) ::
        seedProgramBoundsFrom rest (pc + instr.byteSize)

def seedProgramBounds (program : Assembly.Program) : BoundTable :=
  seedProgramBoundsFrom program 0

def relaxSuccessors? (table : BoundTable) (height reserved maxStack : Nat) :
    List Word → Option (BoundTable × Bool)
  | [] => some (table, false)
  | pc :: rest =>
      if _hHeight : height + reserved ≤ maxStack then
        let old := lookupBound? table pc
        let table' := insertMaxBound pc height table
        let changed :=
          match old with
          | none => true
          | some oldHeight => oldHeight < height
        match relaxSuccessors? table' height reserved maxStack rest with
        | none => none
        | some (table'', restChanged) => some (table'', changed || restChanged)
      else
        none

def relaxInstruction? (program : Assembly.Program) (table : BoundTable)
    (reserved maxStack pc : Nat) (instr : Assembly.Instr) :
    Option (BoundTable × Bool) := do
  let bound ← lookupBound? table (EvmYul.UInt256.ofNat pc)
  if _hBound : bound + reserved ≤ maxStack then
    match AssemblyInstr.runningEffect? instr,
        runningSuccessors? program pc instr with
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

theorem instrAtPcFrom_eq_query
    {program : Assembly.Program} {base query pc : Nat}
    {instr : Assembly.Instr}
    (hAt :
      Assembly.Program.instrAtPcFrom program base query = some (pc, instr)) :
    pc = query := by
  induction program generalizing base with
  | nil =>
      simp [Assembly.Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      by_cases hEq : query = base
      · simp [Assembly.Program.instrAtPcFrom, hEq] at hAt
        exact hAt.1.symm.trans hEq.symm
      · simp [Assembly.Program.instrAtPcFrom, hEq] at hAt
        exact ih hAt

theorem instrAtPc_eq_query
    {program : Assembly.Program} {query pc : Nat}
    {instr : Assembly.Instr}
    (hAt : Assembly.Program.instrAtPc program query = some (pc, instr)) :
    pc = query :=
  instrAtPcFrom_eq_query hAt

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
      cases hEffect : AssemblyInstr.runningEffect? instr with
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

theorem uint256_ofNat_toNat (value : Word) :
    EvmYul.UInt256.ofNat value.toNat = value := by
  cases value with
  | mk val =>
      unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
      simp
      rfl

theorem state_pc_eq_of_instrAtPc
    {program : Assembly.Program} {state : EVMState}
    {pc : Nat} {instr : Assembly.Instr}
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr)) :
    state.pc = EvmYul.UInt256.ofNat pc := by
  have hQuery := instrAtPc_eq_query hAt
  rw [hQuery]
  exact (uint256_ofNat_toNat state.pc).symm

/--
Assembly-level stack-bound point used by whole-program checkers.

The first conjunct is the public headroom fact needed by gas-aware replay.  The
second conjunct records the stronger executable check-result fact when the
current PC decodes to an assembly instruction; terminal/fallthrough states with
no instruction therefore only need the public headroom fact.
-/
def SourceStackBoundPoint (program : Assembly.Program) (table : BoundTable)
    (reserved maxStack : Nat) (state : EVMState) : Prop :=
  state.stack.length + reserved ≤ maxStack ∧
    ∀ {pc instr},
      Assembly.Program.instrAtPc program state.pc.toNat = some (pc, instr) →
        ∃ bound,
          lookupBound? table state.pc = some bound ∧
            state.stack.length ≤ bound ∧
              bound + reserved ≤ maxStack

namespace SourceStackBoundPoint

theorem headroom {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat} {state : EVMState}
    (hPoint : SourceStackBoundPoint program table reserved maxStack state) :
    state.stack.length + reserved ≤ maxStack :=
  hPoint.1

end SourceStackBoundPoint

theorem sourceStackBoundPoint_initial_of_programBoundOk?
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat} {state : EVMState}
    (hCheck : programBoundOk? program table reserved maxStack = true)
    (hReserved : reserved ≤ maxStack) :
    SourceStackBoundPoint program table reserved maxStack
      { state with pc := Assembly.Program.pcAfter [], stack := [] } := by
  constructor
  · simpa using hReserved
  · intro pc instr hAt
    have hInstrCheck :
        instructionBoundOk? program table reserved maxStack pc instr = true :=
      programBoundOk?_instructionBoundOk hCheck hAt
    rcases instructionBoundOk?_lookup hInstrCheck with
      ⟨bound, hLookup, hBound⟩
    refine ⟨bound, ?_, by simp, hBound⟩
    have hPc := instrAtPc_eq_query hAt
    simpa [Assembly.Program.pcAfter_nil, hPc] using hLookup

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
  induction successors with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      simp [successorsBoundOk?] at hCheck
      have hMem' : pc = head ∨ pc ∈ tail := by
        simpa using hMem
      rcases hMem' with hEq | hTailMem
      · subst pc
        unfold successorBoundOk? at hCheck
        cases hLookup : lookupBound? table head with
        | none =>
            simp [hLookup] at hCheck
        | some bound =>
            simp [hLookup] at hCheck
            exact ⟨bound, rfl, hCheck.1.1, hCheck.1.2⟩
      · exact ih hCheck.2 hTailMem

theorem stepAtResult_running_pc_mem_successors?
    {program : Assembly.Program} {pc : Nat} {instr : Assembly.Instr}
    {successors : List Word} {state mid : EVMState}
    (hSuccessors : runningSuccessors? program pc instr = some successors)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc)
    (hStep :
      Assembly.Source.stepAtResult program pc instr state =
        .ok (.running mid)) :
    mid.pc ∈ successors := by
  cases instr with
  | label label =>
      simp [runningSuccessors?] at hSuccessors
      cases hSuccessors
      simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
        Assembly.Target.stepInstr] at hStep
      cases hStep
      simp [fallthroughPc, hPc, EvmYul.EVM.State.incrPC]
  | push value =>
      simp [runningSuccessors?] at hSuccessors
      cases hSuccessors
      simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
        Assembly.Target.stepInstr] at hStep
      cases hStep
      simp [fallthroughPc, hPc, Assembly.Instr.push32Size,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  | jump target =>
      unfold runningSuccessors? at hSuccessors
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [hDest] at hSuccessors
      | some dest =>
          simp [hDest] at hSuccessors
          cases hSuccessors
          unfold Assembly.Source.stepAtResult at hStep
          simp [Assembly.Source.stepAt, hDest, Assembly.Source.jumpPc] at hStep
          cases hStep
          simp
  | jumpi target =>
      unfold runningSuccessors? at hSuccessors
      cases hDest : Assembly.Program.labelPc program target with
      | none =>
          simp [hDest] at hSuccessors
      | some dest =>
          simp [hDest] at hSuccessors
          cases hSuccessors
          unfold Assembly.Source.stepAtResult at hStep
          simp [Assembly.Source.stepAt, Assembly.Instr.haltKind?, hDest] at hStep
          cases hPop : state.stack.pop with
          | none =>
              simp [hPop] at hStep
              change
                (Except.error EvmYul.EVM.ExecutionException.StackUnderflow :
                  Except EVMException Assembly.StepResult) =
                  .ok (.running mid) at hStep
              cases hStep
          | some popped =>
              rcases popped with ⟨stack, cond⟩
              simp [hPop] at hStep
              cases hStep
              by_cases hCond : cond != EvmYul.UInt256.ofNat 0
              · simp [hCond]
              · simp [hCond, Assembly.Source.jumpiFallthroughPc,
                  jumpiFallthroughPc, hPc]
  | prim op =>
      unfold runningSuccessors? at hSuccessors
      cases hHalt : op.haltKind? with
      | some kind =>
          simp [hHalt] at hSuccessors
          cases hSuccessors
          unfold Assembly.Source.stepAtResult at hStep
          cases hRun : Assembly.Source.stepAt program pc (.prim op) state with
          | error err =>
              simp [hRun, Bind.bind, Except.bind] at hStep
          | ok post =>
              simp [hRun, Assembly.Instr.haltKind?, hHalt, Bind.bind,
                Except.bind] at hStep
      | none =>
          simp [hHalt] at hSuccessors
          cases hCont : op.continuingStep? with
          | none =>
              simp [hCont] at hSuccessors
          | some step =>
              simp [hCont] at hSuccessors
              cases hSuccessors
              unfold Assembly.Source.stepAtResult at hStep
              simp [Assembly.Source.stepAt, Assembly.Instr.haltKind?,
                hHalt] at hStep
              have hRun :
                  step.run state = .ok mid := by
                have hStep' := hStep
                simp [Assembly.Target.stepInstr,
                  Assembly.PrimOp.step_eq_continuingStep_run hCont,
                  Bind.bind, Except.bind] at hStep'
                cases hRunStep : step.run state with
                | error err =>
                    rw [hRunStep] at hStep'
                    simp at hStep'
                | ok mid' =>
                    rw [hRunStep] at hStep'
                    simp at hStep'
                    cases hStep'
                    rfl
              have hMidPc := primStep_run_pc hRun
              simp [fallthroughPc, hPc, hMidPc]

theorem instructionBoundOk?_preserves_sourceStackBoundPoint
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack pc : Nat} {instr : Assembly.Instr}
    {state mid : EVMState}
    (hCheck :
      instructionBoundOk? program table reserved maxStack pc instr = true)
    (hPoint :
      SourceStackBoundPoint program table reserved maxStack state)
    (hAt :
      Assembly.Program.instrAtPc program state.pc.toNat =
        some (pc, instr))
    (hStep :
      Assembly.Source.stepAtResult program pc instr state =
        .ok (.running mid)) :
    SourceStackBoundPoint program table reserved maxStack mid := by
  have hPc := state_pc_eq_of_instrAtPc hAt
  rcases hPoint.2 hAt with
    ⟨bound, hLookupState, hStack, _hCurrentHeadroom⟩
  have hLookupPc :
      lookupBound? table (EvmYul.UInt256.ofNat pc) = some bound := by
    simpa [hPc] using hLookupState
  unfold instructionBoundOk? at hCheck
  rw [hLookupPc] at hCheck
  cases hEffect : AssemblyInstr.runningEffect? instr with
  | none =>
      cases hSuccs : runningSuccessors? program pc instr with
      | none =>
          simp [hEffect, hSuccs] at hCheck
      | some successors =>
          cases successors with
          | nil =>
              have hMem :=
                stepAtResult_running_pc_mem_successors?
                  hSuccs hPc hStep
              simp at hMem
          | cons head tail =>
              simp [hEffect, hSuccs] at hCheck
  | some effect =>
      cases hSuccs : runningSuccessors? program pc instr with
      | none =>
          simp [hEffect, hSuccs] at hCheck
      | some successors =>
          simp [hEffect, hSuccs] at hCheck
          have hMem :=
            stepAtResult_running_pc_mem_successors? hSuccs hPc hStep
          rcases
              successorsBoundOk?_sound hCheck.2 hMem with
            ⟨nextBound, hLookupNext, hNextHeight, hNextHeadroom⟩
          have hMidStack :
              mid.stack.length ≤ nextBound :=
            AssemblyInstr.stepAtResult_running_stack_le_of_effect?
              hEffect hStack hNextHeight hStep
          constructor
          · omega
          · intro _pc' _instr' _hAt
            exact
              ⟨nextBound, hLookupNext, hMidStack, hNextHeadroom⟩

theorem programBoundOk?_preserves_sourceStackBoundPoint
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat} {state mid : EVMState}
    (hCheck : programBoundOk? program table reserved maxStack = true)
    (hPoint :
      SourceStackBoundPoint program table reserved maxStack state)
    (hStep :
      Assembly.Source.stepResult program state = .ok (.running mid)) :
    SourceStackBoundPoint program table reserved maxStack mid := by
  unfold Assembly.Source.stepResult at hStep
  cases hAt : Assembly.Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some located =>
      rcases located with ⟨pc, instr⟩
      have hInstrCheck :
          instructionBoundOk? program table reserved maxStack pc instr = true :=
        programBoundOk?_instructionBoundOk hCheck hAt
      exact
        instructionBoundOk?_preserves_sourceStackBoundPoint
          hInstrCheck hPoint hAt (by simpa [hAt] using hStep)

theorem instructionBoundOk?_preserves_targetBlock_sourceStackBoundPoint
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack pc : Nat} {instr : Assembly.Instr}
    {emitted before after : List Assembly.LocatedTarget}
    {target : Assembly.TargetProgram}
    {state mid : EVMState}
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
      Assembly.Target.runListResult
          (emitted.map Assembly.LocatedTarget.instr) state =
        .ok (.running mid)) :
    SourceStackBoundPoint program table reserved maxStack mid := by
  exact
    instructionBoundOk?_preserves_sourceStackBoundPoint
      hCheck hPoint hAt
      (AssemblyInstr.stepAtResult_running_of_emit_runListResult hEmit hRun)

theorem sourceRunResultPoints_headroom_of_boundPoint_invariant
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack fuel : Nat} {initial : EVMState}
    {result : Assembly.StepResult}
    (hRun :
      Assembly.Source.runNResult program fuel initial = .ok result)
    (hInitial :
      SourceStackBoundPoint program table reserved maxStack initial)
    (hStep :
      ∀ {state mid : EVMState},
        SourceStackBoundPoint program table reserved maxStack state →
          Assembly.Source.stepResult program state = .ok (.running mid) →
            SourceStackBoundPoint program table reserved maxStack mid) :
    Preservation.SourceRunResultPoints program
      (fun state => state.stack.length + reserved ≤ maxStack)
      fuel initial result :=
  (Preservation.SourceRunResultPoints.of_runNResult_invariant
      hRun hInitial hStep).mono
    (fun _state hPoint => SourceStackBoundPoint.headroom hPoint)

theorem sourceRunResultPoints_headroom_of_programBoundOk?
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack fuel : Nat} {initial : EVMState}
    {result : Assembly.StepResult}
    (hRun :
      Assembly.Source.runNResult program fuel initial = .ok result)
    (hInitial :
      SourceStackBoundPoint program table reserved maxStack initial)
    (hCheck : programBoundOk? program table reserved maxStack = true) :
    Preservation.SourceRunResultPoints program
      (fun state => state.stack.length + reserved ≤ maxStack)
      fuel initial result :=
  sourceRunResultPoints_headroom_of_boundPoint_invariant
    hRun hInitial
    (fun hPoint hStep =>
      programBoundOk?_preserves_sourceStackBoundPoint
        hCheck hPoint hStep)

theorem sourceRunResultPoints_headroom_of_check
    {program : Assembly.Program} {reserved maxStack fuel : Nat}
    {initial : EVMState} {result : Assembly.StepResult}
    (check : ProgramBoundCheckResult program reserved maxStack)
    (hRun :
      Assembly.Source.runNResult program fuel initial = .ok result)
    (hInitial :
      SourceStackBoundPoint program check.table reserved maxStack initial) :
    Preservation.SourceRunResultPoints program
      (fun state => state.stack.length + reserved ≤ maxStack)
      fuel initial result :=
  sourceRunResultPoints_headroom_of_programBoundOk?
    hRun hInitial check.checked

theorem blockTraceResultPoints_headroom_of_programBoundOk?
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial : EVMState} {result : Assembly.StepResult}
    {hTrace :
      Assembly.Preservation.BlockTraceResult program target fuel initial
        result}
    (hInitial :
      SourceStackBoundPoint program table reserved maxStack initial)
    (hCheck : programBoundOk? program table reserved maxStack = true) :
    Preservation.BlockTraceResultPoints
      (fun state => state.stack.length + reserved ≤ maxStack) hTrace :=
  (Preservation.BlockTraceResultPoints.of_blockTraceResult_invariant
      hInitial
      (fun hPoint hAt hEmit hTargetBlock hRun =>
        instructionBoundOk?_preserves_targetBlock_sourceStackBoundPoint
          (programBoundOk?_instructionBoundOk hCheck hAt)
          hPoint hAt hEmit hTargetBlock hRun)
      hTrace).point_mono
    (fun _state hPoint => SourceStackBoundPoint.headroom hPoint)

theorem blockTraceResultPoints_headroom_of_check
    {program : Assembly.Program} {reserved maxStack : Nat}
    {target : Assembly.TargetProgram} {fuel : Nat}
    {initial : EVMState} {result : Assembly.StepResult}
    {hTrace :
      Assembly.Preservation.BlockTraceResult program target fuel initial
        result}
    (check : ProgramBoundCheckResult program reserved maxStack)
    (hInitial :
      SourceStackBoundPoint program check.table reserved maxStack initial) :
    Preservation.BlockTraceResultPoints
      (fun state => state.stack.length + reserved ≤ maxStack) hTrace :=
  blockTraceResultPoints_headroom_of_programBoundOk?
    hInitial check.checked

theorem aRunResultPoints_headroom_of_boundPoint_invariant
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat} {initial : EVMState}
    {post : Assembly.StepResult → Prop}
    (hRun : Preservation.ARunResult program initial post)
    (hInitial :
      SourceStackBoundPoint program table reserved maxStack initial)
    (hStep :
      ∀ {state mid : EVMState},
        SourceStackBoundPoint program table reserved maxStack state →
          Assembly.Source.stepResult program state = .ok (.running mid) →
            SourceStackBoundPoint program table reserved maxStack mid) :
    Preservation.ARunResultPoints program
      (fun state => state.stack.length + reserved ≤ maxStack)
      initial post :=
  (Preservation.ARunResultPoints.of_ARunResult_invariant
      hRun hInitial hStep).point_mono
    (fun _state hPoint => SourceStackBoundPoint.headroom hPoint)

theorem aRunResultPoints_headroom_of_programBoundOk?
    {program : Assembly.Program} {table : BoundTable}
    {reserved maxStack : Nat} {initial : EVMState}
    {post : Assembly.StepResult → Prop}
    (hRun : Preservation.ARunResult program initial post)
    (hInitial :
      SourceStackBoundPoint program table reserved maxStack initial)
    (hCheck : programBoundOk? program table reserved maxStack = true) :
    Preservation.ARunResultPoints program
      (fun state => state.stack.length + reserved ≤ maxStack)
      initial post :=
  aRunResultPoints_headroom_of_boundPoint_invariant
    hRun hInitial
    (fun hPoint hStep =>
      programBoundOk?_preserves_sourceStackBoundPoint
        hCheck hPoint hStep)

theorem aRunResultPoints_headroom_of_check
    {program : Assembly.Program} {reserved maxStack : Nat}
    {initial : EVMState} {post : Assembly.StepResult → Prop}
    (check : ProgramBoundCheckResult program reserved maxStack)
    (hRun : Preservation.ARunResult program initial post)
    (hInitial :
      SourceStackBoundPoint program check.table reserved maxStack initial) :
    Preservation.ARunResultPoints program
      (fun state => state.stack.length + reserved ≤ maxStack)
      initial post :=
  aRunResultPoints_headroom_of_programBoundOk?
    hRun hInitial check.checked

end AssemblyBounds

namespace Preservation
namespace Frame
namespace StateRel

theorem source_run_code_ctx_result_stackHeadroomPoints_of_analyzeFrom?
    {source final : RunState}
    {target : EVMState} {tokens : List Word} {code : Code}
    {pre post : Assembly.Program} {summary : Summary}
    (hSafe : Preservation.Code.RunnerSafe code)
    (hFrame : Code.FrameSafe code)
    (hFits : Preservation.Code.PCFitsFrom pre code)
    (hPc : target.pc = Assembly.Program.pcAfter pre)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hRun : Code.runState code source = .ok final)
    (hAnalyze :
      Code.analyzeFrom? target.stack.length code = some summary)
    (hPeakHeadroom : summary.peakHeight + 17 ≤ 1024) :
    Preservation.ARunResultPoints
      (pre ++ code.toAssembly ++ post)
      (fun state => state.stack.length + 17 ≤ 1024)
      target
      (fun result =>
        match result with
        | .running target' =>
            Preservation.Frame.StateRel final target' tokens ∧
              target'.pc =
                Assembly.Program.pcAfter (pre ++ code.toAssembly)
        | .halted _ => False) := by
  rcases
      Preservation.Frame.StateRel.runState_frameSafe_hidden_exists
        hRel hFrame hRun with
    ⟨hiddenFinal, hHiddenRun, hHiddenRel⟩
  have hRelAt :
      Preservation.RelAt (Assembly.Program.pcAfter pre) target
        { source.evm with stack := target.stack } := by
    exact ⟨hPc, hRel.dataRel⟩
  have hRunAssembly :
      Preservation.ARunResultPoints
        (pre ++ code.toAssembly ++ post)
        (fun state => state.stack.length + 17 ≤ 1024)
        target
        (fun result =>
          match result with
          | .running target' =>
              Preservation.RelAt
                (Assembly.Program.pcAfter (pre ++ code.toAssembly))
                target' hiddenFinal
          | .halted _ => False) :=
    Code.source_runResult_stackHeadroomPoints_of_analyzeFrom?
      hSafe hFits hRelAt hHiddenRun hAnalyze rfl hPeakHeadroom
  exact hRunAssembly.mono (by
    intro result hEnd
    cases result with
    | halted halt =>
        cases hEnd
    | running target' =>
        have hStack : target'.stack = hiddenFinal.stack :=
          Preservation.stack_eq_of_eraseControl_eq hEnd.sameData
        refine ⟨?_, hEnd.pc_eq⟩
        refine ⟨?_, ?_⟩
        · rw [hStack]
          exact hHiddenRel.stackRel
        · calc
            Preservation.eraseControl target'
                = Preservation.eraseControl hiddenFinal :=
                    hEnd.sameData
            _ =
                Preservation.eraseControl
                  { final.evm with stack := hiddenFinal.stack } :=
                    hHiddenRel.dataRel
            _ =
                Preservation.eraseControl
                  { final.evm with stack := target'.stack } := by
                    rw [hStack])

theorem source_run_code_segment_result_stackHeadroomPoints_of_analyzeFrom?
    {source final : RunState}
    {target : EVMState} {tokens : List Word} {code : Code}
    {asm : Assembly.Program} {summary : Summary}
    (hSafe : Preservation.Code.RunnerSafe code)
    (hFrame : Code.FrameSafe code)
    (segment : Preservation.CodeSegment asm code.toAssembly)
    (hPc : target.pc = segment.startPc)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hRun : Code.runState code source = .ok final)
    (hAnalyze :
      Code.analyzeFrom? target.stack.length code = some summary)
    (hPeakHeadroom : summary.peakHeight + 17 ≤ 1024) :
    Preservation.ARunResultPoints
      asm
      (fun state => state.stack.length + 17 ≤ 1024)
      target
      (fun result =>
        match result with
        | .running target' =>
            Preservation.Frame.StateRel final target' tokens ∧
              target'.pc = segment.fallthroughPc
        | .halted _ => False) := by
  have hPoints :
      Preservation.ARunResultPoints
        (segment.pre ++ code.toAssembly ++ segment.post)
        (fun state => state.stack.length + 17 ≤ 1024)
        target
        (fun result =>
          match result with
          | .running target' =>
              Preservation.Frame.StateRel final target' tokens ∧
                target'.pc =
                  Assembly.Program.pcAfter
                    (segment.pre ++ code.toAssembly)
          | .halted _ => False) :=
    source_run_code_ctx_result_stackHeadroomPoints_of_analyzeFrom?
      hSafe hFrame
      (Preservation.Code.PCFitsFrom.of_assembly segment.hFits)
      hPc hRel hRun hAnalyze hPeakHeadroom
  exact
    Preservation.ARunResultPoints.cast_program_mono
      segment.hAsm.symm hPoints
      (by
        intro result hResult
        cases result with
        | halted halt =>
            exact hResult
        | running target' =>
            simpa [Preservation.CodeSegment.fallthroughPc] using hResult)

end StateRel
end Frame

namespace ProcedurePreservation

theorem preserves_code_in_programLayout_stackHeadroomPoints_of_analyzeFrom?
    {program : Program}
    {layout : Preservation.ProcedurePreservation.ProgramLayout program}
    {ctx : CompileContext} {supply : LabelSupply} {code : Code}
    {fuel : Nat} {source : RunState} {outcome : Outcome}
    {target : EVMState} {tokens : List Word} {summary : Summary}
    (hSafe : Preservation.Code.RunnerSafe code)
    (hFrame : Code.FrameSafe code)
    (segment :
      Preservation.CodeSegment layout.asm
        (Stmt.compileFromCtxCore (.code code) ctx supply).code)
    (hPc : target.pc = segment.startPc)
    (hRel : Preservation.Frame.StateRel source target tokens)
    (hEval : Stmt.Eval program fuel (.code code) source outcome)
    (hAnalyze :
      Code.analyzeFrom? target.stack.length code = some summary)
    (hPeakHeadroom : summary.peakHeight + 17 ≤ 1024) :
    Preservation.ARunResultPoints
      layout.asm
      (fun state => state.stack.length + 17 ≤ 1024)
      target
      (fun result =>
        Preservation.CompiledOutcomeRel layout.asm ctx segment.fallthroughPc
          outcome result tokens) := by
  cases hEval with
  | code hCode =>
      let codeSegment :
          Preservation.CodeSegment layout.asm code.toAssembly :=
        Preservation.CodeSegment.cast_code
          (by simp [Stmt.compileFromCtxCore])
          segment
      have hPoints :=
        Preservation.Frame.StateRel.source_run_code_segment_result_stackHeadroomPoints_of_analyzeFrom?
          hSafe hFrame codeSegment hPc hRel hCode hAnalyze hPeakHeadroom
      exact hPoints.mono (by
        intro result hResult
        cases result with
        | halted halt =>
            cases hResult
        | running target' =>
            simpa [Preservation.CompiledOutcomeRel,
              Preservation.CodeSegment.fallthroughPc, codeSegment,
              Preservation.CodeSegment.cast_code, Stmt.compileFromCtxCore]
              using hResult)

end ProcedurePreservation
end Preservation

mutual
  def blockInternalCalls : Block → List Name
    | ⟨stmts⟩ => stmtListInternalCalls stmts

  def stmtInternalCalls : Stmt → List Name
    | .code _ => []
    | .if_ _ body => blockInternalCalls body
    | .switch _ cases defaultBody =>
        caseListInternalCalls cases ++ defaultInternalCalls defaultBody
    | .for_ init _ post body =>
        blockInternalCalls init ++ blockInternalCalls post ++
          blockInternalCalls body
    | .brk | .cont | .leave | .terminal _ => []
    | .call name => [name]

  def stmtListInternalCalls : List Stmt → List Name
    | [] => []
    | stmt :: rest => stmtInternalCalls stmt ++ stmtListInternalCalls rest

  def caseListInternalCalls : List (Word × Block) → List Name
    | [] => []
    | (_value, body) :: rest =>
        blockInternalCalls body ++ caseListInternalCalls rest

  def defaultInternalCalls : Option Block → List Name
    | none => []
    | some body => blockInternalCalls body
end

namespace Proc

def internalCalls (proc : Proc) : List Name :=
  blockInternalCalls proc.body

end Proc

namespace Program

def mainInternalCalls (program : Program) : List Name :=
  blockInternalCalls program.body

def hasCycleFrom (procs : List Proc) :
    Nat → List Name → Name → Bool
  | 0, _stack, _name => true
  | fuel + 1, stack, name =>
      if name ∈ stack then
        true
      else
        match ProcList.lookup? name procs with
        | none => false
        | some proc =>
            (Proc.internalCalls proc).any
              (hasCycleFrom procs fuel (name :: stack))

def hasInternalCallCycle? (program : Program) : Bool :=
  let fuel := program.procs.length + 1
  let mainHasCycle :=
    (mainInternalCalls program).any (hasCycleFrom program.procs fuel [])
  let procHasCycle :=
    program.procs.any
      (fun proc => hasCycleFrom program.procs fuel [] proc.name)
  mainHasCycle || procHasCycle

def internalCallGraphAcyclic? (program : Program) : Bool :=
  !(hasInternalCallCycle? program)

structure AcyclicCallGraphCheckResult (program : Program) : Type where
  checked : internalCallGraphAcyclic? program = true

def acyclicCallGraphCheckResult? (program : Program) :
    Option (AcyclicCallGraphCheckResult program) :=
  if h : internalCallGraphAcyclic? program = true then
    some ⟨h⟩
  else
    none

theorem acyclicCallGraphCheckResult?_eq_some
    {program : Program} {check : AcyclicCallGraphCheckResult program}
    (hCheck : acyclicCallGraphCheckResult? program = some check) :
    internalCallGraphAcyclic? program = true := by
  unfold acyclicCallGraphCheckResult? at hCheck
  by_cases h : internalCallGraphAcyclic? program = true
  · exact h
  · simp [h] at hCheck

end Program

namespace Examples

def zeroWord : Word :=
  EvmYul.UInt256.ofNat 0

def pushMany (count : Nat) : Code :=
  List.replicate count (BasicInstr.push zeroWord)

example :
    Code.stackSafeFrom? 0 17 1024 (pushMany 1007) = true := by
  native_decide

example :
    Code.stackSafeFrom? 0 17 1024 (pushMany 1008) = false := by
  native_decide

def pushPopAsm : Assembly.Program :=
  [.push zeroWord, .prim .pop]

def pushPopTable : AssemblyBounds.BoundTable :=
  [ (EvmYul.UInt256.ofNat 0, 0)
  , (EvmYul.UInt256.ofNat Assembly.Instr.push32Size, 1)
  , (EvmYul.UInt256.ofNat (Assembly.Instr.push32Size + 1), 0)
  ]

example :
    AssemblyBounds.programBoundOk? pushPopAsm pushPopTable 17 1024 = true := by
  native_decide

def loopLabel : Assembly.Label :=
  .named "loop"

def zeroStackLoopAsm : Assembly.Program :=
  [.label loopLabel, .push zeroWord, .prim .pop, .jump loopLabel]

def zeroStackLoopTable : AssemblyBounds.BoundTable :=
  [ (EvmYul.UInt256.ofNat 0, 0)
  , (EvmYul.UInt256.ofNat 1, 0)
  , (EvmYul.UInt256.ofNat (1 + Assembly.Instr.push32Size), 1)
  , (EvmYul.UInt256.ofNat (1 + Assembly.Instr.push32Size + 1), 0)
  ]

example :
    AssemblyBounds.programBoundOk? zeroStackLoopAsm zeroStackLoopTable
      17 1024 = true := by
  native_decide

example :
    (AssemblyBounds.checkProgramBoundCheckResult? zeroStackLoopAsm
        zeroStackLoopTable 17 1024).isSome = true := by
  native_decide

example :
    (AssemblyBounds.inferProgramBoundCheckResult? zeroStackLoopAsm
        17 1024).isSome = true := by
  native_decide

def growingStackLoopAsm : Assembly.Program :=
  [.label loopLabel, .push zeroWord, .jump loopLabel]

def growingStackLoopTable : AssemblyBounds.BoundTable :=
  [ (EvmYul.UInt256.ofNat 0, 0)
  , (EvmYul.UInt256.ofNat 1, 0)
  , (EvmYul.UInt256.ofNat (1 + Assembly.Instr.push32Size), 1)
  ]

example :
    AssemblyBounds.programBoundOk? growingStackLoopAsm growingStackLoopTable
      17 1024 = false := by
  native_decide

example :
    (AssemblyBounds.checkProgramBoundCheckResult? growingStackLoopAsm
        growingStackLoopTable 17 1024).isNone = true := by
  native_decide

example :
    (AssemblyBounds.inferProgramBoundCheckResult? growingStackLoopAsm
        17 1024).isNone = true := by
  native_decide

end Examples

end StackResource
end Structured
end EvmCompiler
