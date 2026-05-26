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

end Program

end Preservation
end YulToStackFreeCfg
end EvmCompiler
