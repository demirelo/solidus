import EvmCompiler.Yul.Syntax
import EvmCompiler.YulToStackFreeCfg.Contract
import EvmCompiler.StackFreeCfg.PrimitiveAdapter
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace YulToStackFreeCfg
namespace Preservation

/-!
Top-down preservation interface for the imported-Yul -> StackFreeCfg pass.

This is the source-facing proof boundary above StackFreeCfg. It deliberately
mentions imported Yul states and StackFreeCfg observations, but not typed CFG
shapes, stack slots, assembly labels, return tokens, bytecode PCs, or gas.
-/

namespace Reference

abbrev State :=
  EvmYul.Yul.State

abbrev Exception :=
  EvmYul.Yul.Exception

inductive Result where
  | regular (state : State)
  | yulHalt (state : State) (value : Word)
  | revert (stateBeforeRevert : State)

def installContract (program : Yul.Program) : State → State
  | .Ok shared store =>
      .Ok
        { shared with
          executionEnv :=
            { shared.executionEnv with code := program.contract } }
        store
  | .OutOfFuel => .OutOfFuel
  | .Checkpoint jump => .Checkpoint jump

/--
Imported Yul source run used by this proof boundary.

This is stated directly against EVMYulLean's Yul interpreter to avoid pulling
in older proof-heavy compiler modules while this new adjacent tower is being
rebuilt.
-/
def run (fuel : Nat) (program : Yul.Program) (state : State) :
    Except Exception Result :=
  match
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) with
  | .ok (state', _rets) => .ok (.regular state')
  | .error (.YulHalt state' value) => .ok (.yulHalt state' value)
  | .error (.Revert stateBeforeRevert) => .ok (.revert stateBeforeRevert)
  | .error exception => .error exception

theorem run_of_callDispatcher_ok {fuel : Nat} {program : Yul.Program}
    {state state' : State} {rets : List Word}
    (h :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) = .ok (state', rets)) :
    run fuel program state = .ok (.regular state') := by
  simp [run, h]

theorem run_of_callDispatcher_yulHalt {fuel : Nat}
    {program : Yul.Program} {state state' : State} {value : Word}
    (h :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) =
          .error (.YulHalt state' value)) :
    run fuel program state = .ok (.yulHalt state' value) := by
  simp [run, h]

theorem run_of_callDispatcher_revert {fuel : Nat}
    {program : Yul.Program} {state stateBeforeRevert : State}
    (h :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) =
          .error (.Revert stateBeforeRevert)) :
    run fuel program state = .ok (.revert stateBeforeRevert) := by
  simp [run, h]

theorem run_of_callDispatcher_outOfFuel {fuel : Nat}
    {program : Yul.Program} {state : State}
    (h :
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) = .error .OutOfFuel) :
    run fuel program state = .error .OutOfFuel := by
  simp [run, h]

end Reference

abbrev SourceResult :=
  Except Reference.Exception Reference.Result

abbrev TargetResult :=
  Except StackFreeCfg.Exception StackFreeCfg.Observation

/--
Relation between the imported Yul shared state and the stack-free shared state.

The two states live at different `OperationType`s in EVMYulLean, so the final
bridge theorem should instantiate this relation with the exact field agreement
needed by the shared primitive semantics and object-layout contract.
-/
abbrev SharedRel :=
  EvmYul.SharedState .Yul → StackFreeCfg.SharedState → Prop

/--
Relation between imported Yul exceptions and StackFreeCfg source exceptions.

This is semantic glue between two source interpreters, not compiler evidence.
The eventual bridge should instantiate it from the shared primitive semantics
and the accepted source surface.
-/
abbrev ExceptionRel :=
  Reference.Exception → StackFreeCfg.Exception → Prop

namespace ReferenceState

def SharedStateRel (sharedRel : SharedRel) :
    Reference.State → StackFreeCfg.SharedState → Prop
  | .Ok shared _store, targetShared => sharedRel shared targetShared
  | .Checkpoint (.Continue shared _store), targetShared =>
      sharedRel shared targetShared
  | .Checkpoint (.Break shared _store), targetShared =>
      sharedRel shared targetShared
  | .Checkpoint (.Leave shared _store), targetShared =>
      sharedRel shared targetShared
  | .OutOfFuel, _targetShared => False

end ReferenceState

/--
Initial-state relation for the Yul -> StackFreeCfg theorem.

This is intentionally an input-state relation, not compiler evidence. The
eventual top theorem may keep an initial-state premise; it should not keep
layout, replay, or callee-preservation premises.
-/
structure InitialRel (sharedRel : SharedRel) (source : Reference.State)
    (targetShared : StackFreeCfg.SharedState) : Prop where
  ok_state :
    ∃ sourceShared sourceStore,
      source = (.Ok sourceShared sourceStore : Reference.State) ∧
        sharedRel sourceShared targetShared

def NonRevertingHalt (kind : Assembly.HaltKind) : Prop :=
  kind ≠ .revert

/--
Result relation at the Yul source boundary.

Imported Yul's public `ReferenceResult` distinguishes regular execution,
revert, and a generic `YulHalt`; it does not retain the concrete halt opcode
kind for non-reverting halts. The relation therefore preserves exactly that
observable distinction here: `revert` must map to StackFreeCfg `revert`, while
other Yul halts may map to any non-reverting terminal halt.
-/
inductive ResultRel (sharedRel : SharedRel) (exceptionRel : ExceptionRel) :
    SourceResult → TargetResult → Prop where
  | regular {sourceState : Reference.State}
      {targetObs : StackFreeCfg.Observation}
      (hMode : targetObs.mode = .regular)
      (hScope : targetObs.scope = [])
      (hShared :
        ReferenceState.SharedStateRel sharedRel sourceState
          targetObs.shared) :
      ResultRel sharedRel exceptionRel (.ok (.regular sourceState))
        (.ok targetObs)
  | yulHalt {sourceState : Reference.State} {value : Word}
      {targetObs : StackFreeCfg.Observation} {kind : Assembly.HaltKind}
      (hMode : targetObs.mode = .halt kind)
      (hKind : NonRevertingHalt kind)
      (hShared :
        ReferenceState.SharedStateRel sharedRel sourceState
          targetObs.shared) :
      ResultRel sharedRel exceptionRel (.ok (.yulHalt sourceState value))
        (.ok targetObs)
  | revert {sourceState : Reference.State}
      {targetObs : StackFreeCfg.Observation}
      (hMode : targetObs.mode = .halt .revert)
      (hShared :
        ReferenceState.SharedStateRel sharedRel sourceState
          targetObs.shared) :
      ResultRel sharedRel exceptionRel (.ok (.revert sourceState))
        (.ok targetObs)
  | outOfFuel {targetObs : StackFreeCfg.Observation}
      (hMode : targetObs.mode = .outOfFuel) :
      ResultRel sharedRel exceptionRel (.error .OutOfFuel) (.ok targetObs)
  | invalid {sourceError : Reference.Exception}
      {targetObs : StackFreeCfg.Observation}
      (hNotFuel : sourceError ≠ .OutOfFuel)
      (hMode : targetObs.mode = .invalid) :
      ResultRel sharedRel exceptionRel (.error sourceError) (.ok targetObs)
  | targetInvalidError {sourceError : Reference.Exception}
      (hNotFuel : sourceError ≠ .OutOfFuel) :
      ResultRel sharedRel exceptionRel (.error sourceError) (.error .invalid)
  | exception {sourceError : Reference.Exception}
      {targetError : StackFreeCfg.Exception}
      (hRel : exceptionRel sourceError targetError) :
      ResultRel sharedRel exceptionRel (.error sourceError)
        (.error targetError)

/--
Source-to-target fuel budget for this pass.

The Yul lowerer may introduce StackFreeCfg temporaries and generated control
statements, so the eventual preservation theorem should state an explicit fuel
translation/bound rather than silently using the same fuel on both sides.
-/
abbrev FuelBudget :=
  Nat → Nat → Prop

namespace Program

def CompilesTo (layout : ObjectLayout) (program : Yul.Program)
    (target : StackFreeCfg.Program) : Prop :=
  YulToStackFreeCfg.Program.lowerGate layout program =
    .accepted target

theorem coverage?_of_compilesTo {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h : CompilesTo layout program target) :
    Coverage.contract? layout program.contract = true := by
  unfold CompilesTo at h
  unfold YulToStackFreeCfg.Program.lowerGate at h
  unfold Contract.lowerGate at h
  by_cases hCoverage : Coverage.contract? layout program.contract
  · exact hCoverage
  · simp [hCoverage] at h

theorem sourceWF?_of_compilesTo {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h : CompilesTo layout program target) :
    SourceWF.contract? layout program.contract = true := by
  have hCoverage := coverage?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  unfold CompilesTo at h
  unfold YulToStackFreeCfg.Program.lowerGate at h
  unfold Contract.lowerGate at h
  by_cases hWF : SourceWF.contract? layout program.contract
  · exact hWF
  · simp [hCoverage, hWF] at h

theorem lower?_of_compilesTo {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h : CompilesTo layout program target) :
    YulToStackFreeCfg.Program.lower? layout program = some target := by
  have hCoverage := coverage?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  have hWF := sourceWF?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  unfold CompilesTo at h
  unfold YulToStackFreeCfg.Program.lowerGate at h
  unfold Contract.lowerGate at h
  cases hLower : Contract.lower? layout program.contract with
  | none =>
      simp [hCoverage, hWF, hLower] at h
  | some lowered =>
      by_cases hAccepted : StackFreeCfg.Program.accepted? lowered
      · simp [hCoverage, hWF, hLower, hAccepted] at h
        cases h
        simp [YulToStackFreeCfg.Program.lower?, hLower]
      · simp [hCoverage, hWF, hLower, hAccepted] at h

theorem accepted?_of_compilesTo {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h : CompilesTo layout program target) :
    StackFreeCfg.Program.accepted? target = true := by
  have hCoverage := coverage?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  have hWF := sourceWF?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  unfold CompilesTo at h
  unfold YulToStackFreeCfg.Program.lowerGate at h
  unfold Contract.lowerGate at h
  cases hLower : Contract.lower? layout program.contract with
  | none =>
      simp [hCoverage, hWF, hLower] at h
  | some lowered =>
      by_cases hAccepted : StackFreeCfg.Program.accepted? lowered
      · simp [hCoverage, hWF, hLower, hAccepted] at h
        cases h
        exact hAccepted
      · simp [hCoverage, hWF, hLower, hAccepted] at h

theorem lowerObserved?_of_compilesTo {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h : CompilesTo layout program target)
    (prim : StackFreeCfg.PrimitiveSemantics) (fuel : Nat)
    (shared : StackFreeCfg.SharedState) :
    YulToStackFreeCfg.Program.lowerObserved? layout prim fuel program shared =
      some (StackFreeCfg.Program.runObserved prim fuel target shared) := by
  unfold CompilesTo at h
  unfold YulToStackFreeCfg.Program.lowerObserved?
  simp [h]

theorem lowerAccepted?_of_compilesTo {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h : CompilesTo layout program target) :
    YulToStackFreeCfg.Program.lowerAccepted? layout program = some target := by
  have hCoverage := coverage?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  have hWF := sourceWF?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  have hLower := lower?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  have hLowerContract :
      Contract.lower? layout program.contract = some target := by
    simpa [YulToStackFreeCfg.Program.lower?] using hLower
  have hAccepted := accepted?_of_compilesTo (layout := layout)
    (program := program) (target := target) h
  unfold YulToStackFreeCfg.Program.lowerAccepted?
  unfold Contract.lowerAccepted?
  simp [hCoverage, hWF, hLowerContract, hAccepted]

theorem compilesTo_of_lowerAccepted? {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h :
      YulToStackFreeCfg.Program.lowerAccepted? layout program =
        some target) :
    CompilesTo layout program target := by
  unfold YulToStackFreeCfg.Program.lowerAccepted? at h
  unfold Contract.lowerAccepted? at h
  unfold CompilesTo
  unfold YulToStackFreeCfg.Program.lowerGate
  unfold Contract.lowerGate
  by_cases hCoverage : Coverage.contract? layout program.contract
  · by_cases hWF : SourceWF.contract? layout program.contract
    · cases hLower : Contract.lower? layout program.contract with
      | none =>
          simp [hCoverage, hWF, hLower] at h
      | some lowered =>
          by_cases hAccepted : StackFreeCfg.Program.accepted? lowered
          · simp [hCoverage, hWF, hLower, hAccepted] at h
            cases h
            simp [hCoverage, hWF, hAccepted]
          · simp [hCoverage, hWF, hLower, hAccepted] at h
    · simp [hCoverage, hWF] at h
  · simp [hCoverage] at h

theorem compilesTo_iff_lowerAccepted? {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program} :
    CompilesTo layout program target ↔
      YulToStackFreeCfg.Program.lowerAccepted? layout program =
        some target := by
  constructor
  · exact lowerAccepted?_of_compilesTo
  · exact compilesTo_of_lowerAccepted?

theorem lowerGate_toProgram?_of_compilesTo {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h : CompilesTo layout program target) :
    (YulToStackFreeCfg.Program.lowerGate layout program).toProgram? =
      some target := by
  unfold CompilesTo at h
  rw [h]
  rfl

theorem compilesTo_of_lowerGate_toProgram? {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program}
    (h :
      (YulToStackFreeCfg.Program.lowerGate layout program).toProgram? =
        some target) :
    CompilesTo layout program target := by
  unfold CompilesTo
  generalize hGate :
      YulToStackFreeCfg.Program.lowerGate layout program = gate
  rw [hGate] at h
  cases gate with
  | accepted lowered =>
      simp [LoweringGate.toProgram?] at h
      cases h
      rfl
  | rejected reason =>
      simp [LoweringGate.toProgram?] at h

theorem compilesTo_iff_lowerGate_toProgram? {layout : ObjectLayout}
    {program : Yul.Program} {target : StackFreeCfg.Program} :
    CompilesTo layout program target ↔
      (YulToStackFreeCfg.Program.lowerGate layout program).toProgram? =
        some target := by
  constructor
  · exact lowerGate_toProgram?_of_compilesTo
  · exact compilesTo_of_lowerGate_toProgram?

theorem lowerObserved?_eq_some_iff {layout : ObjectLayout}
    {program : Yul.Program} {prim : StackFreeCfg.PrimitiveSemantics}
    {fuel : Nat} {shared : StackFreeCfg.SharedState}
    {result : Except StackFreeCfg.Exception StackFreeCfg.Observation} :
    YulToStackFreeCfg.Program.lowerObserved? layout prim fuel program shared =
      some result ↔
      ∃ target,
        CompilesTo layout program target ∧
          result =
            StackFreeCfg.Program.runObserved prim fuel target shared := by
  unfold YulToStackFreeCfg.Program.lowerObserved?
  cases hGate : YulToStackFreeCfg.Program.lowerGate layout program with
  | accepted target =>
      constructor
      · intro h
        simp at h
        exact ⟨target, hGate, h.symm⟩
      · rintro ⟨target', hCompiles, hResult⟩
        unfold CompilesTo at hCompiles
        simp [hGate] at hCompiles
        cases hCompiles
        simp [hResult]
  | rejected reason =>
      constructor
      · intro h
        simp at h
      · rintro ⟨target, hCompiles, _hResult⟩
        unfold CompilesTo at hCompiles
        simp [hGate] at hCompiles

/--
Adjacent preservation property for one successfully lowered Yul program.
-/
def PreservesLowered (sharedRel : SharedRel) (exceptionRel : ExceptionRel)
    (fuelBudget : FuelBudget) (_layout : ObjectLayout) (program : Yul.Program)
    (target : StackFreeCfg.Program) : Prop :=
  ∀ sourceFuel targetFuel sourceInitial targetShared,
    fuelBudget sourceFuel targetFuel →
      InitialRel sharedRel sourceInitial targetShared →
        ResultRel sharedRel exceptionRel
          (Reference.run sourceFuel program sourceInitial)
          (StackFreeCfg.Program.runObserved
            StackFreeCfg.PrimitiveSemantics.canonical targetFuel target
            targetShared)

/--
Public theorem target for the imported-Yul -> StackFreeCfg pass.

The proof should discharge the compiler-generated obligations internally from
`lowerGate`; the public boundary keeps only source acceptedness/lowering
success, initial-state relation, and an explicit source-to-target fuel budget.
-/
def CompilePreserves (sharedRel : SharedRel) (exceptionRel : ExceptionRel)
    (fuelBudget : FuelBudget) (layout : ObjectLayout) : Prop :=
  ∀ program target,
    CompilesTo layout program target →
      PreservesLowered sharedRel exceptionRel fuelBudget layout program target

/--
Observation-boundary form of `CompilePreserves`.

This is the top-down proof shape the imported-Yul bridge should usually use:
prove preservation for any observable result returned by the public
`lowerObserved?` gate, and recover the generated StackFreeCfg program only
inside this lemma.  The statement mentions imported Yul, StackFreeCfg
observations, the source/target initial-state relation, and fuel; it does not
mention any lower compiler artifacts.
-/
theorem compilePreserves_iff_lowerObserved
    (sharedRel : SharedRel) (exceptionRel : ExceptionRel)
    (fuelBudget : FuelBudget) (layout : ObjectLayout) :
    CompilePreserves sharedRel exceptionRel fuelBudget layout ↔
      ∀ program sourceFuel targetFuel sourceInitial targetShared targetResult,
        fuelBudget sourceFuel targetFuel →
          InitialRel sharedRel sourceInitial targetShared →
            YulToStackFreeCfg.Program.lowerObserved? layout
              StackFreeCfg.PrimitiveSemantics.canonical targetFuel program
              targetShared = some targetResult →
              ResultRel sharedRel exceptionRel
                (Reference.run sourceFuel program sourceInitial)
                targetResult := by
  constructor
  · intro hCompile program sourceFuel targetFuel sourceInitial targetShared
      targetResult hFuel hInitial hObserved
    rcases
        (lowerObserved?_eq_some_iff
          (layout := layout)
          (program := program)
          (prim := StackFreeCfg.PrimitiveSemantics.canonical)
          (fuel := targetFuel)
          (shared := targetShared)
          (result := targetResult)).mp hObserved with
      ⟨target, hCompiles, hResult⟩
    rw [hResult]
    exact hCompile program target hCompiles sourceFuel targetFuel
      sourceInitial targetShared hFuel hInitial
  · intro hObserved program target hCompiles sourceFuel targetFuel
      sourceInitial targetShared hFuel hInitial
    exact hObserved program sourceFuel targetFuel sourceInitial targetShared
      (StackFreeCfg.Program.runObserved StackFreeCfg.PrimitiveSemantics.canonical
        targetFuel target targetShared)
      hFuel hInitial
      (lowerObserved?_of_compilesTo (layout := layout)
        (program := program) (target := target) hCompiles
        StackFreeCfg.PrimitiveSemantics.canonical targetFuel targetShared)

end Program

end Preservation
end YulToStackFreeCfg
end EvmCompiler
