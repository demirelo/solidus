import EvmCompiler.Yul.Semantics
import EvmCompiler.Objects.Preservation

namespace EvmCompiler
namespace Yul

namespace SourceLowered

abbrev WholeProgramOutcomeRel :=
  Objects.Source.WholeProgramOutcomeRel

end SourceLowered

namespace Program

noncomputable def compileChecked? (program : Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Structured.Preservation.ProcedurePreservation.compileChecked?
    lower.toStructured

theorem compileChecked?_eq_some {program : Program} {asm : Assembly.Program}
    (hCompile : compileChecked? program = some asm) :
    ∃ lower : Expressions.Program,
      program.toExpressions? = some lower ∧
        Structured.Preservation.ProcedurePreservation.compileChecked?
          lower.toStructured = some asm := by
  unfold compileChecked? at hCompile
  cases hLower : program.toExpressions? with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact ⟨lower, rfl, hCompile⟩

theorem compileChecked?_noCallCreate_of_loweredFunctions
    {program : Program} {asm : Assembly.Program}
    (hLoweredFunctionsNoCall :
      ∀ obj : Objects.Program,
        program.toObjects? = some obj →
          obj.toFunctions.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  unfold Program.toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hLower
  | some obj =>
      simp [hObj] at hLower
      exact
        Objects.Source.Program.compileChecked?_noCallCreate
          (program := obj) (asm := asm)
          (hLoweredFunctionsNoCall obj hObj)
          (by
            unfold Objects.Source.Program.compileChecked?
            simp [hLower, hLowerCompile])

theorem compile_preserves {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : Lowered.run fuel program initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  unfold Lowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun : obj.run fuel initial = .ok outcome := by
        simpa [hObj] using hRun
      exact
        Objects.Program.compile_preserves hLower hCompile hInitialPc hObjRun

theorem compile_preserves_checked {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : Lowered.run fuel program initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  unfold Lowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun : obj.run fuel initial = .ok outcome := by
        simpa [hObj] using hRun
      have hObjCompile :
          Objects.Program.compileChecked? obj = some asm := by
        unfold Objects.Program.compileChecked?
        unfold Expressions.Program.compileChecked?
        simp [hLower, hStructuredCompile]
      exact
        Objects.Program.compile_preserves_checked
          hObjCompile hInitialPc hObjRun

/--
Source-facing compiler theorem for the compiler-facing Yul adapter.

Unlike `Lowered.run`, this starts from `SourceLowered.run`, whose object and
function path uses the repaired stack-free source tower.  The remaining
frame-bound premise is a lower compiler obligation for the generated object,
not part of the Yul source semantics.
-/
theorem compile_source_preserves {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hSourceAccepted : program.SourceAccepted)
    (hFrameBound :
      ∀ lowerObj : Objects.Program, program.toObjects? = some lowerObj →
        Functions.SourceDirect.FrameBound.Program lowerObj.toFunctions)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  unfold SourceLowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun :
          Objects.Source.Program.run prim fuel obj initial =
            .ok sourceOutcome := by
        simpa [hObj] using hRun
      have hObjSourceAccepted : obj.SourceAccepted := by
        rcases hSourceAccepted with
          ⟨_hWF, _hSupported, witness, hWitness, hWitnessAccepted⟩
        have hEq : witness = obj := by
          have hSome : some witness = some obj := by
            rw [← hWitness, hObj]
          injection hSome
        simpa [hEq] using hWitnessAccepted
      exact
        Objects.Source.Program.compile_preserves
          (prim := prim) hPrim (program := obj) (lower := lower)
          (asm := asm) (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) hObjSourceAccepted
          (hFrameBound obj hObj) hLower hCompile hInitialPc hInitialStack
          hObjRun

theorem compile_source_preserves_checked
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hFrameBound :
      ∀ lowerObj : Objects.Program, program.toObjects? = some lowerObj →
        Functions.SourceDirect.FrameBound.Program lowerObj.toFunctions)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  exact
    compile_source_preserves hPrim hSourceAccepted hFrameBound hLower
      hStructuredCompile hInitialPc hInitialStack hRun

/--
Source-facing compiler acceptance for the Yul adapter.

This is not the imported Nethermind source semantics itself. It is the
compiler-side acceptance package for the lowering into the repaired source
tower: Yul source acceptedness plus object/function compiler resource bounds
for the object actually produced by `toObjects?`.
-/
structure SourceCompileAccepted (program : Program) : Prop where
  source : program.SourceAccepted
  objects :
    ∀ lowerObj : Objects.Program, program.toObjects? = some lowerObj →
      Objects.Source.Program.CompileAccepted lowerObj

theorem compile_source_preserves_of_compileAccepted
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hAccepted : SourceCompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  unfold SourceLowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun :
          Objects.Source.Program.run prim fuel obj initial =
            .ok sourceOutcome := by
        simpa [hObj] using hRun
      exact
        Objects.Source.Program.compile_preserves_of_compileAccepted
          (prim := prim) hPrim (program := obj) (lower := lower)
          (asm := asm) (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) (hAccepted.objects obj hObj)
          hLower hCompile hInitialPc hInitialStack hObjRun

theorem compile_source_preserves_checked_of_compileAccepted
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : SourceCompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  unfold SourceLowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun :
          Objects.Source.Program.run prim fuel obj initial =
            .ok sourceOutcome := by
        simpa [hObj] using hRun
      have hObjCompile :
          Objects.Source.Program.compileChecked? obj = some asm := by
        unfold Objects.Source.Program.compileChecked?
        simp [hLower, hStructuredCompile]
      exact
        Objects.Source.Program.compile_preserves_checked_of_compileAccepted
          (prim := prim) hPrim (program := obj) (asm := asm)
          (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) hObjCompile
          (hAccepted.objects obj hObj) hInitialPc hInitialStack hObjRun

end Program

end Yul
end EvmCompiler
