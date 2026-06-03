import EvmCompiler.Yul.Semantics
import EvmCompiler.Yul.SolcValidation
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

noncomputable def compileLiveNoInternalCallChecked?
    (program : Program) : Option Assembly.Program := do
  let obj ← program.toObjects?
  Objects.Source.Program.compileLiveNoInternalCallChecked? obj

noncomputable def compileSolcChecked? (program : Program) :
    Option Assembly.Program :=
  if SolcValidation.ProgramOk? program then
    compileChecked? program
  else
    none

theorem compileSolcChecked?_eq_some {program : Program}
    {asm : Assembly.Program}
    (hCompile : compileSolcChecked? program = some asm) :
    SolcValidation.ProgramOk program ∧
      compileChecked? program = some asm := by
  unfold compileSolcChecked? at hCompile
  cases hValid : SolcValidation.ProgramOk? program <;> simp [hValid] at hCompile
  exact ⟨hValid, hCompile⟩

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

theorem compileLiveNoInternalCallChecked?_eq_some
    {program : Program} {asm : Assembly.Program}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm) :
    ∃ obj : Objects.Program,
      program.toObjects? = some obj ∧
        Objects.Source.Program.compileLiveNoInternalCallChecked? obj =
          some asm := by
  unfold compileLiveNoInternalCallChecked? at hCompile
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hCompile
  | some obj =>
      simp [hObj] at hCompile
      exact ⟨obj, rfl, hCompile⟩

theorem accepted_of_sourceAccepted_compileChecked? {program : Program}
    {asm : Assembly.Program}
    (hSourceAccepted : program.SourceAccepted)
    (hCompile : compileChecked? program = some asm) :
    program.Accepted := by
  rcases hSourceAccepted with
    ⟨hWF, hSupported, lowerObj, hLowerObj, hObjSourceAccepted⟩
  rcases compileChecked?_eq_some hCompile with
    ⟨lowerExpr, hLowerExpr, hLowerCompile⟩
  have hObjExpr : lowerObj.toExpressions? = some lowerExpr := by
    unfold Program.toExpressions? at hLowerExpr
    simp [hLowerObj] at hLowerExpr
    exact hLowerExpr
  have hExprAccepted : lowerExpr.Accepted :=
    Structured.Preservation.ProcedurePreservation.accepted_of_compileChecked?
      hLowerCompile
  have hLocalsExpr :
      lowerObj.toFunctions.toLocals.toExpressions? = some lowerExpr := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?, Functions.Program.toExpressions?]
      using hObjExpr
  have hLocalsAccepted : lowerObj.toFunctions.toLocals.Accepted :=
    ⟨lowerExpr, hLocalsExpr, hExprAccepted⟩
  have hFunctionsAccepted :
      Functions.Inline.Program.Accepted lowerObj.toFunctions := by
    change Functions.Program.Accepted lowerObj.toFunctions
    exact
      ⟨hObjSourceAccepted.2.1, hObjSourceAccepted.2.2,
        hLocalsAccepted⟩
  exact
    ⟨hWF, hSupported, lowerObj, hLowerObj,
      ⟨hObjSourceAccepted.1, hFunctionsAccepted⟩⟩

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

theorem compileLiveNoInternalCallChecked?_noCallCreate_of_loweredFunctions
    {program : Program} {asm : Assembly.Program}
    (hLoweredFunctionsNoCall :
      ∀ obj : Objects.Program,
        program.toObjects? = some obj →
          obj.toFunctions.usesCallCreate = false)
    (hCompile : compileLiveNoInternalCallChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, hObjCompile⟩
  exact
    Objects.Source.Program.compileLiveNoInternalCallChecked?_noCallCreate
      (program := obj) (asm := asm)
      (hLoweredFunctionsNoCall obj hObj) hObjCompile

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

theorem compileSolcChecked?_preserves {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileSolcChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : Lowered.run fuel program initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileSolcChecked?_eq_some hCompile with ⟨_hSolc, hCompileCore⟩
  exact compile_preserves_checked hCompileCore hInitialPc hRun

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

theorem compileSolcChecked?_source_preserves
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileSolcChecked? program = some asm)
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
  rcases compileSolcChecked?_eq_some hCompile with ⟨_hSolc, hCompileCore⟩
  exact
    compile_source_preserves_checked hPrim hCompileCore hSourceAccepted
      hFrameBound hInitialPc hInitialStack hRun

theorem compile_live_noInternalCall_source_preserves_checked
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim (fuel + 1) program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, hObjCompile⟩
  unfold SourceLowered.run at hRun
  simp [hObj] at hRun
  have hObjSourceAccepted : obj.SourceAccepted := by
    rcases hSourceAccepted with
      ⟨_hWF, _hSupported, witness, hWitness, hWitnessAccepted⟩
    have hEq : witness = obj := by
      have hSome : some witness = some obj := by
        rw [← hWitness, hObj]
      injection hSome
    simpa [hEq] using hWitnessAccepted
  exact
    Objects.Source.Program.compile_live_noInternalCall_preserves_checked
      (prim := prim) hPrim (program := obj) (asm := asm)
      (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hObjCompile hObjSourceAccepted
      hInitialPc hInitialStack hRun

theorem compile_live_noInternalCall_source_preserves_checked_endPc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim (fuel + 1) program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, hObjCompile⟩
  unfold SourceLowered.run at hRun
  simp [hObj] at hRun
  have hObjSourceAccepted : obj.SourceAccepted := by
    rcases hSourceAccepted with
      ⟨_hWF, _hSupported, witness, hWitness, hWitnessAccepted⟩
    have hEq : witness = obj := by
      have hSome : some witness = some obj := by
        rw [← hWitness, hObj]
      injection hSome
    simpa [hEq] using hWitnessAccepted
  exact
    Objects.Source.Program.compile_live_noInternalCall_preserves_checked_endPc
      (prim := prim) hPrim (program := obj) (asm := asm)
      (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hObjCompile hObjSourceAccepted
      hInitialPc hInitialStack hRun

theorem compile_live_noInternalCall_source_preserves_checked_anyFuel
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, _hObjCompile⟩
  have hObjRun :
      Objects.Source.Program.run prim fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  have hObjRunSucc :
      Objects.Source.Program.run prim (fuel + 1) obj initial =
        .ok sourceOutcome := by
    have hFunctionRun :
        Functions.Source.Program.run prim fuel obj.toFunctions initial =
          .ok sourceOutcome := by
      cases obj with
      | mk root =>
          cases root with
          | mk name code data objects =>
              simpa [Objects.Source.Program.run, Objects.Source.Object.run,
                Objects.Program.toFunctions, Objects.Object.toFunctions]
                using hObjRun
    have hFunctionRunSucc :
        Functions.Source.Program.run prim (fuel + 1) obj.toFunctions initial =
          .ok sourceOutcome := by
      simpa [Functions.Source.Program.run,
        Functions.Source.Program.runState] using
        Functions.Source.Block.runScoped_mono prim obj.toFunctions
          (Nat.le_succ fuel) hFunctionRun
    cases obj with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Objects.Source.Program.run, Objects.Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions]
              using hFunctionRunSucc
  have hRunSucc :
      SourceLowered.run prim (fuel + 1) program initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hObjRunSucc
  exact
    compile_live_noInternalCall_source_preserves_checked
      (prim := prim) hPrim (program := program) (asm := asm)
      (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hCompile hSourceAccepted hInitialPc
      hInitialStack hRunSucc

theorem compile_live_noInternalCall_source_preserves_checked_endPc_anyFuel
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, _hObjCompile⟩
  have hObjRun :
      Objects.Source.Program.run prim fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  have hObjRunSucc :
      Objects.Source.Program.run prim (fuel + 1) obj initial =
        .ok sourceOutcome := by
    have hFunctionRun :
        Functions.Source.Program.run prim fuel obj.toFunctions initial =
          .ok sourceOutcome := by
      cases obj with
      | mk root =>
          cases root with
          | mk name code data objects =>
              simpa [Objects.Source.Program.run, Objects.Source.Object.run,
                Objects.Program.toFunctions, Objects.Object.toFunctions]
                using hObjRun
    have hFunctionRunSucc :
        Functions.Source.Program.run prim (fuel + 1) obj.toFunctions initial =
          .ok sourceOutcome := by
      simpa [Functions.Source.Program.run,
        Functions.Source.Program.runState] using
        Functions.Source.Block.runScoped_mono prim obj.toFunctions
          (Nat.le_succ fuel) hFunctionRun
    cases obj with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Objects.Source.Program.run, Objects.Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions]
              using hFunctionRunSucc
  have hRunSucc :
      SourceLowered.run prim (fuel + 1) program initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hObjRunSucc
  exact
    compile_live_noInternalCall_source_preserves_checked_endPc
      (prim := prim) hPrim (program := program) (asm := asm)
      (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hCompile hSourceAccepted hInitialPc
      hInitialStack hRunSucc

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

theorem compile_source_preserves_of_compileAccepted_endPc
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
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
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
        Objects.Source.Program.compile_preserves_of_compileAccepted_endPc
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

theorem compile_source_preserves_checked_of_compileAccepted_endPc
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
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
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
        Objects.Source.Program.compile_preserves_checked_of_compileAccepted_endPc
          (prim := prim) hPrim (program := obj) (asm := asm)
          (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) hObjCompile
          (hAccepted.objects obj hObj) hInitialPc hInitialStack hObjRun

theorem compileSolcChecked?_source_preserves_of_compileAccepted
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileSolcChecked? program = some asm)
    (hAccepted : SourceCompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileSolcChecked?_eq_some hCompile with ⟨_hSolc, hCompileCore⟩
  exact
    compile_source_preserves_checked_of_compileAccepted hPrim hCompileCore
      hAccepted hInitialPc hInitialStack hRun

end Program

end Yul
end EvmCompiler
