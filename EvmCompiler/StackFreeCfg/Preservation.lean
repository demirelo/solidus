import EvmCompiler.StackFreeCfg.Compiler
import EvmCompiler.StackFreeCfg.Contract
import EvmCompiler.StackFreeCfg.PrimitiveAdapter
import EvmCompiler.TypedCfg.Contract

namespace EvmCompiler
namespace StackFreeCfg
namespace Preservation

/-!
Top-down preservation interface for the StackFreeCfg -> TypedCfg pass.

This file intentionally contains no proof bodies. It fixes the public theorem
shape before the local proof work starts, so the implementation proofs can use
stack layouts and typed labels internally without leaking them above this
adjacent boundary.
-/

abbrev SourceResult :=
  Except Exception Observation

abbrev TargetResult :=
  Except TypedCfg.EVMException TypedCfg.Outcome

/--
Initial-state relation for running a compiled whole StackFreeCfg program.

The compiled CFG entry block has empty input shape. The only source-visible
part of the target state at entry is the shared EVM/Yul state; the target stack
starts empty.
-/
structure InitialRel (shared : SharedState) (target : TypedCfg.EVMState) :
    Prop where
  shared_eq : target.toSharedState = shared
  stack_empty : target.stack = []

/--
Result relation for the adjacent compiler proof.

This relation is allowed to mention `TypedCfg` outcomes because it is exactly
the StackFreeCfg -> TypedCfg boundary. It is not exported as the observation
model for higher source layers.
-/
inductive ResultRel : SourceResult → TargetResult → Prop where
  | regular {source : Observation} {target : TypedCfg.RunState}
      (hMode : source.mode = .regular)
      (hScope : source.scope = [])
      (hShared : target.evm.toSharedState = source.shared)
      (hStack : target.evm.stack = [])
      (hReturns : target.returns = []) :
      ResultRel (.ok source) (.ok (.fallthrough target))
  | halt {source : Observation} {target : TypedCfg.RunState}
      {kind : Assembly.HaltKind}
      (hMode : source.mode = .halt kind)
      (hShared : target.evm.toSharedState = source.shared) :
      ResultRel (.ok source) (.ok (.halt kind target))
  | invalidMode {source : Observation} {target : TypedCfg.RunState}
      (hMode : source.mode = .invalid) :
      ResultRel (.ok source) (.ok (.invalid target))
  | invalidError {target : TypedCfg.RunState} :
      ResultRel (.error .invalid) (.ok (.invalid target))
  | outOfFuel {source : Observation} {label : TypedCfg.Label}
      {target : TypedCfg.RunState}
      (hMode : source.mode = .outOfFuel)
      (hShared : target.evm.toSharedState = source.shared) :
      ResultRel (.ok source) (.ok (.outOfFuel label target))
  | primitiveError {error : TypedCfg.EVMException} :
      ResultRel (.error (.primitive error)) (.error error)

namespace Program

def CompilesTo (program : Program) (target : TypedCfg.CheckedProgram) : Prop :=
  Compiler.Program.toCheckedCfg? program = some target

theorem accepted?_of_compilesTo {program : Program}
    {target : TypedCfg.CheckedProgram}
    (h : CompilesTo program target) :
    Program.accepted? program = true := by
  unfold CompilesTo at h
  unfold Compiler.Program.toCheckedCfg? at h
  unfold Compiler.Program.toCfg? at h
  by_cases hAccepted : Program.accepted? program
  · exact hAccepted
  · simp [hAccepted] at h

theorem checked_of_compilesTo {program : Program}
    {target : TypedCfg.CheckedProgram}
    (_h : CompilesTo program target) :
    target.program.typeCheck? = some () :=
  target.checked

theorem toCfg?_of_compilesTo {program : Program}
    {target : TypedCfg.CheckedProgram}
    (h : CompilesTo program target) :
    Compiler.Program.toCfg? program = some target.program := by
  unfold CompilesTo at h
  unfold Compiler.Program.toCheckedCfg? at h
  cases hCfg : Compiler.Program.toCfg? program with
  | none =>
      simp [hCfg] at h
  | some cfg =>
      unfold TypedCfg.Program.check? at h
      by_cases hCheck : cfg.typeCheck? = some ()
      · simp [hCfg, hCheck] at h
        cases h
        rfl
      · simp [hCfg, hCheck] at h

/--
The adjacent whole-program preservation property we want to prove next.

This is partial in the standard verified-compiler sense: if the checked
compiler succeeds, running the generated typed CFG is related to running the
StackFreeCfg source interpreter with the canonical shared primitive semantics.
-/
def PreservesCompiled (program : Program) (target : TypedCfg.CheckedProgram) :
    Prop :=
  ∀ fuel sourceShared targetInitial,
    InitialRel sourceShared targetInitial →
      ResultRel
        (Program.runObserved PrimitiveSemantics.canonical fuel program
          sourceShared)
        (TypedCfg.Program.run fuel target.program targetInitial)

/--
Public theorem target for this pass.

The future theorem should prove this `Prop`, rather than taking generated
layout witnesses, replay certificates, or per-callee obligations as inputs.
-/
def CompilePreserves : Prop :=
  ∀ program target,
    CompilesTo program target →
      PreservesCompiled program target

end Program

end Preservation
end StackFreeCfg
end EvmCompiler
