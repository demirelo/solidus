import EvmCompiler.Objects.Semantics
import EvmCompiler.Objects.SourceSemantics
import EvmCompiler.Functions.Preservation
import EvmCompiler.Functions.LiveLayoutPreservation

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

end Program
end Source

end Objects
end EvmCompiler
