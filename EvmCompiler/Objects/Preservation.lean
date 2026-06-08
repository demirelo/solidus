import EvmCompiler.Objects.Semantics
import EvmCompiler.Objects.SourceSemantics
import EvmCompiler.Functions.Preservation
import EvmCompiler.Functions.LiveLayoutPreservation
import EvmCompiler.Functions.ScratchFrameSpill

namespace EvmCompiler
namespace Objects

namespace Program

theorem run_toFunctions {fuel : Nat} {program : Program}
    {initial : EVMState} :
    program.run fuel initial =
      Functions.Program.run fuel program.toFunctions initial := by
  cases program with
  | mk root =>
      cases root with
      | mk name code data objects =>
          rfl

theorem eval_toFunctions {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hEval : Program.Eval fuel program initial outcome) :
    Functions.Program.Eval fuel program.toFunctions initial outcome := by
  cases hEval with
  | ofRun hRun =>
      exact Functions.Program.eval_of_run
        (by simpa [run_toFunctions] using hRun)

noncomputable def compileChecked? (program : Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Expressions.Program.compileChecked? lower

theorem compileChecked?_eq_some {program : Program}
    {asm : Assembly.Program}
    (hCompile : compileChecked? program = some asm) :
    ∃ lower : Expressions.Program,
      program.toExpressions? = some lower ∧
        Expressions.Program.compileChecked? lower = some asm := by
  unfold compileChecked? at hCompile
  cases hLower : program.toExpressions? with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact ⟨lower, rfl, hCompile⟩

theorem compileChecked?_noCallCreate {program : Program}
    {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hFunctionCompile :
      Functions.Program.compileChecked? program.toFunctions = some asm := by
    unfold Functions.Program.compileChecked?
    have hFunctionLower :
        program.toFunctions.toExpressions? = some lower := by
      simpa [Program.toExpressions?, Functions.Inline.Program.toExpressions?]
        using hLower
    simp [hFunctionLower, hLowerCompile]
  exact
    Functions.Program.compileChecked?_noCallCreate hProgram hFunctionCompile

theorem compile_preserves {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  exact
    Functions.Inline.Program.compile_preserves hLower hCompile hInitialPc
      (by simpa [run_toFunctions] using hRun)

theorem compile_preserves_endPc {program : Program}
    {lower : Expressions.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  exact
    Functions.Inline.Program.compile_preserves_endPc hLower hCompile
      hInitialPc (by simpa [run_toFunctions] using hRun)

theorem compile_preserves_checked {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hFunctionCompile :
      Functions.Program.compileChecked? program.toFunctions = some asm := by
    unfold Functions.Program.compileChecked?
    have hFunctionLower :
        program.toFunctions.toExpressions? = some lower := by
      simpa [Program.toExpressions?, Functions.Inline.Program.toExpressions?]
        using hLower
    simp [hFunctionLower, hLowerCompile]
  exact
    Functions.Program.compile_preserves_checked
      hFunctionCompile hInitialPc (by simpa [run_toFunctions] using hRun)

theorem compile_preserves_checked_endPc {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hFunctionCompile :
      Functions.Program.compileChecked? program.toFunctions = some asm := by
    unfold Functions.Program.compileChecked?
    have hFunctionLower :
        program.toFunctions.toExpressions? = some lower := by
      simpa [Program.toExpressions?, Functions.Inline.Program.toExpressions?]
        using hLower
    simp [hFunctionLower, hLowerCompile]
  exact
    Functions.Program.compile_preserves_checked_endPc
      hFunctionCompile hInitialPc (by simpa [run_toFunctions] using hRun)

end Program

namespace Source

abbrev WholeProgramOutcomeRel :=
  Functions.Source.WholeProgramOutcomeRel

namespace Program

/--
Source-facing compiler acceptance for objects.

The object source semantics remains a root-object adapter over
`Functions.Source`.  Function-frame resource bounds are bundled as compiler
acceptance for the extracted function program rather than exposed as object
source semantics.
-/
structure CompileAccepted (program : Objects.Program) : Prop where
  source : Objects.Program.SourceAccepted program
  functions : Functions.Source.Program.CompileAccepted program.toFunctions

noncomputable def compileChecked? (program : Objects.Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Structured.Preservation.ProcedurePreservation.compileChecked?
    lower.toStructured

noncomputable def compileLiveNoInternalCallChecked?
    (program : Objects.Program) : Option Assembly.Program :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?
    program.toFunctions

noncomputable def compileCheckedWithConservativeSpillSourceOwned?
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Objects.Program) : Option Assembly.Program :=
  Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?
    range program.toFunctions

noncomputable def compileCheckedWithAdaptiveSpillSourceOwned?
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Objects.Program) : Option Assembly.Program :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?
    range program.toFunctions

noncomputable def compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
    (maxWords : Nat) (program : Objects.Program) :
    Option (Locals.SourceLowering.StateRel.SpillScratch.ScratchRange ×
      Assembly.Program) :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
    maxWords program.toFunctions

noncomputable def compileCheckedWithScratchFrameSpill?
    (maxFrameWords : Nat) (program : Objects.Program) :
    Option (Expressions.Program × Assembly.Program) :=
  Functions.ScratchFrameSpill.compileChecked? maxFrameWords
    program.toFunctions

noncomputable def compileCheckedAssemblyWithScratchFrameSpill?
    (maxFrameWords : Nat) (program : Objects.Program) :
    Option Assembly.Program := do
  let (_exprProgram, asm) ←
    compileCheckedWithScratchFrameSpill? maxFrameWords program
  some asm

theorem compileChecked?_eq_some {program : Objects.Program}
    {asm : Assembly.Program}
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

theorem compileChecked?_noCallCreate {program : Objects.Program}
    {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hLowerNo :
      lower.usesCallCreate = false := by
    have hLocalsNo :
        program.toFunctions.toLocals.usesCallCreate = false :=
      Functions.CompilerFacts.Program.toLocals_noCallCreate
        program.toFunctions hProgram
    exact
      Locals.CompilerFacts.Program.toExpressions?_noCallCreate
        program.toFunctions.toLocals hLocalsNo
        (by
          simpa [Program.toExpressions?,
            Functions.Inline.Program.toExpressions?,
            Functions.Program.toExpressions?] using hLower)
  exact
    Structured.Preservation.ProcedurePreservation.compileChecked?_noCallCreate
      (program := lower.toStructured) (asm := asm)
      (by
        simpa [Expressions.CompilerFacts.Program.toStructured_usesCallCreate]
          using hLowerNo)
      hLowerCompile

theorem compileLiveNoInternalCallChecked?_noCallCreate
    {program : Objects.Program} {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile : compileLiveNoInternalCallChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?_noCallCreate
    hProgram hCompile

theorem compileCheckedWithConservativeSpillSourceOwned?_eq_some
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm) :
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?
        range program.toFunctions =
      some asm := by
  simpa [compileCheckedWithConservativeSpillSourceOwned?] using hCompile

theorem compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    {asm : Assembly.Program}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hCompile :
      Expressions.Program.compileChecked?
          (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
            plan) =
        some asm) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some asm := by
  simpa [compileCheckedWithConservativeSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?
      hOwnedCheck hPlan hCompile

theorem compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  simpa [compileCheckedWithConservativeSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?_bounds
      hOwnedCheck hPlan hBounds

theorem compileCheckedWithConservativeSpillSourceOwned?_of_scopedFallback_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  simpa [compileCheckedWithConservativeSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_scopedFallback_bounds
      hOwnedCheck hPlan hBounds

theorem compileCheckedWithConservativeSpillSourceOwned?_noCallCreate
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_noCallCreate
    (compileCheckedWithConservativeSpillSourceOwned?_eq_some hCompile)

theorem compileCheckedWithAdaptiveSpillSourceOwned?_eq_some
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm) :
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?
        range program.toFunctions =
      some asm := by
  simpa [compileCheckedWithAdaptiveSpillSourceOwned?] using hCompile

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    {asm : Assembly.Program}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hCompile :
      Expressions.Program.compileChecked?
          (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
            plan) =
        some asm) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some asm := by
  simpa [compileCheckedWithAdaptiveSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?
      hOwnedCheck hPlan hCompile

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  simpa [compileCheckedWithAdaptiveSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?_bounds
      hOwnedCheck hPlan hBounds

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_adaptiveFallback_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  simpa [compileCheckedWithAdaptiveSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_adaptiveFallback_bounds
      hOwnedCheck hPlan hBounds

theorem compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate
    (compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile)

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
    {maxWords : Nat} {program : Objects.Program}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm)) :
    Functions.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
        maxWords program.toFunctions =
      some (range, asm) := by
  simpa [compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?]
    using hCompile

theorem compileCheckedWithScratchFrameSpill?_eq_some
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm)) :
    Functions.ScratchFrameSpill.compileExpressionsProgram? maxFrameWords
        program.toFunctions =
      some exprProgram ∧
      Expressions.Program.compileChecked? exprProgram = some asm := by
  exact
    Functions.ScratchFrameSpill.compileChecked?_eq_some
      (by
        simpa [compileCheckedWithScratchFrameSpill?] using hCompile)

theorem compileCheckedWithScratchFrameSpill?_noCallCreate
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hExprNo : exprProgram.usesCallCreate = false)
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false := by
  exact
    Functions.ScratchFrameSpill.compileChecked?_noCallCreate hExprNo
      (by
        simpa [compileCheckedWithScratchFrameSpill?] using hCompile)

theorem compileCheckedWithScratchFrameSpill?_noCallCreate_of_source
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.ScratchFrameSpill.compileChecked?_noCallCreate_of_source
    hProgram
    (by
      simpa [compileCheckedWithScratchFrameSpill?] using hCompile)

theorem compileCheckedAssemblyWithScratchFrameSpill?_eq_some
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm) :
    ∃ exprProgram : Expressions.Program,
      Functions.ScratchFrameSpill.compileExpressionsProgram? maxFrameWords
          program.toFunctions =
        some exprProgram ∧
        Expressions.Program.compileChecked? exprProgram = some asm := by
  unfold compileCheckedAssemblyWithScratchFrameSpill? at hCompile
  cases hScratch :
      compileCheckedWithScratchFrameSpill? maxFrameWords program with
  | none =>
      simp [hScratch] at hCompile
  | some result =>
      rcases result with ⟨exprProgram, asm'⟩
      simp [hScratch] at hCompile
      cases hCompile
      exact ⟨exprProgram,
        compileCheckedWithScratchFrameSpill?_eq_some hScratch⟩

theorem compileCheckedAssemblyWithScratchFrameSpill?_noCallCreate
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    (hExprNo :
      ∀ exprProgram : Expressions.Program,
        Functions.ScratchFrameSpill.compileExpressionsProgram? maxFrameWords
            program.toFunctions =
          some exprProgram →
          exprProgram.usesCallCreate = false)
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileCheckedAssemblyWithScratchFrameSpill?_eq_some hCompile with
    ⟨exprProgram, hExpr, hAsm⟩
  exact Expressions.Program.compileChecked?_noCallCreate
    (hExprNo exprProgram hExpr) hAsm

theorem compileCheckedAssemblyWithScratchFrameSpill?_noCallCreate_of_source
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.ScratchFrameSpill.compileCheckedAssembly?_noCallCreate_of_source
    hProgram
    (by
      simpa [compileCheckedAssemblyWithScratchFrameSpill?] using hCompile)

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_noCallCreate
    {maxWords : Nat} {program : Objects.Program}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_noCallCreate
    (compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
      hCompile)

theorem compile_preserves {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hFrameBound :
      Functions.SourceDirect.FrameBound.Program program.toFunctions)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionLower :
      program.toFunctions.toExpressions? = some lower := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?] using hLower
  exact
    Functions.Source.Program.compile_preserves
      (prim := prim) hPrim (program := program.toFunctions) (lower := lower)
      (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hSourceAccepted.2.2 hFrameBound
      hFunctionLower hCompile hInitialPc hInitialStack hFunctionRun

theorem compile_preserves_endPc {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hFrameBound :
      Functions.SourceDirect.FrameBound.Program program.toFunctions)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionLower :
      program.toFunctions.toExpressions? = some lower := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?] using hLower
  exact
    Functions.Source.Program.compile_preserves_endPc
      (prim := prim) hPrim (program := program.toFunctions) (lower := lower)
      (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hSourceAccepted.2.2 hFrameBound
      hFunctionLower hCompile hInitialPc hInitialStack hFunctionRun

theorem compile_preserves_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hAccepted : CompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionLower :
      program.toFunctions.toExpressions? = some lower := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?] using hLower
  exact
    Functions.Source.Program.compile_preserves_of_compileAccepted
      (prim := prim) hPrim (program := program.toFunctions)
      (lower := lower) (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hAccepted.functions hFunctionLower
      hCompile hInitialPc hInitialStack hFunctionRun

theorem compile_preserves_of_compileAccepted_endPc
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hAccepted : CompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionLower :
      program.toFunctions.toExpressions? = some lower := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?] using hLower
  exact
    Functions.Source.Program.compile_preserves_of_compileAccepted_endPc
      (prim := prim) hPrim (program := program.toFunctions)
      (lower := lower) (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hAccepted.functions hFunctionLower
      hCompile hInitialPc hInitialStack hFunctionRun

theorem compile_preserves_checked_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : CompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  exact
    compile_preserves_of_compileAccepted hPrim hAccepted hLower
      hStructuredCompile hInitialPc hInitialStack hRun

theorem compile_preserves_checked_of_compileAccepted_endPc
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : CompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  exact
    compile_preserves_of_compileAccepted_endPc hPrim hAccepted hLower
      hStructuredCompile hInitialPc hInitialStack hRun

theorem compile_live_noInternalCall_preserves_checked
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      Source.Program.run prim (fuel + 1) program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim (fuel + 1) program.toFunctions
          initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.LiveLayout.SourceTarget.Program.compileLiveNoInternalCallChecked_preserves
      (prim := prim) hPrim (sourceProgram := program.toFunctions)
      (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hCompile hSourceAccepted.2.2
      hInitialPc hInitialStack hFunctionRun

theorem compile_live_noInternalCall_preserves_checked_endPc
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      Source.Program.run prim (fuel + 1) program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim (fuel + 1) program.toFunctions
          initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.LiveLayout.SourceTarget.Program.compileLiveNoInternalCallChecked_preserves_endPc
      (prim := prim) hPrim (sourceProgram := program.toFunctions)
      (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hCompile hSourceAccepted.2.2
      hInitialPc hInitialStack hFunctionRun

theorem compileCheckedWithConservativeSpillSourceOwned?_preserves
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.ConservativeSpillProgramOutcomeRel range initial
        sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_preserves
      hSpec hWordBytes
      (compileCheckedWithConservativeSpillSourceOwned?_eq_some hCompile)
      hBoundary hInitialPc hFunctionRun

theorem compileCheckedWithConservativeSpillSourceOwned?_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.ConservativeSpillObservableOutcomeRel range
        sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_observations
      hSpec hWordBytes
      (compileCheckedWithConservativeSpillSourceOwned?_eq_some hCompile)
      hBoundary hInitialPc hFunctionRun

theorem compileCheckedWithAdaptiveSpillSourceOwned?_preserves
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillProgramOutcomeRel range initial
        sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_preserves
      hSpec hWordBytes
      (compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile)
      hBoundary hInitialPc hFunctionRun

theorem compileCheckedWithAdaptiveSpillSourceOwned?_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillObservableOutcomeRel range
        sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_observations
      hSpec hWordBytes
      (compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile)
      hBoundary hInitialPc hFunctionRun

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxWords : Nat}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm))
    (hInitialMemory :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchInitialMemoryEmpty
        initial.toMachineState)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillPrivateObservableProgramOutcomeRel
        range sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_observations
      hSpec hWordBytes
      (compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
        hCompile)
      hInitialMemory hInitialPc hFunctionRun

end Program
end Source

end Objects
end EvmCompiler
