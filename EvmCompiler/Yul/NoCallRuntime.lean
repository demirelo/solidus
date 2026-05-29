import EvmCompiler.Yul.RecursiveBridgeSupport
import EvmCompiler.Yul.NoCallCreate
import EvmCompiler.Assembly.GasAware

/-!
Glue from the accepted Yul no-CALL/CREATE lowering theorem to the final
target-runtime assumption package.

This file intentionally sits after both `RecursiveBridgeSupport` and
`NoCallCreate`: the lowering proof should not depend on the recursive bridge
surface, and the bridge surface should not expose generated no-call evidence as
an unproved public assumption.
-/

namespace EvmCompiler
namespace Yul
namespace Program

theorem compileCheckedAssemblyTarget?_noCallCreate
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hAccepted : Reference.Accepted program)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target)) :
    asm.usesCallCreate = false := by
  rcases compileCheckedAssemblyTarget?_eq_some hCheckedCompileTarget with
    ⟨hCompile, _hAssemble⟩
  exact
    _root_.EvmCompiler.Yul.NoCallCreate.compileChecked?_noCallCreate
      hAccepted hCompile

def canonicalEntryState (initial : EVMState) : EVMState :=
  { initial with
    pc := Assembly.Program.pcAfter []
    stack := [] }

def RecursiveBridgeInitialWorldRel
    (cfg : Reference.StateRelConfig)
    (program : Program)
    (shared : EvmYul.SharedState .Yul)
    (initial : EVMState) : Prop :=
  Reference.SharedStateRel cfg
    { shared with
      executionEnv :=
        { shared.executionEnv with code := program.contract } }
    initial.toSharedState

/--
Initial source/target relation for programs that use Yul object/data code
image builtins. The ordinary world relation carries equality between the Yul
`ExecutionEnv.codeBytes` field and the target EVM execution code; this wrapper
also exposes that code as the assembled target byte image.
-/
structure RecursiveBridgeInitialCodeImageRel
    (cfg : Reference.StateRelConfig)
    (program : Program)
    (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (initial : EVMState) : Prop where
  world :
    RecursiveBridgeInitialWorldRel cfg program shared initial
  targetCode :
    initial.executionEnv.code = Assembly.Bytecode.encodeTarget target

theorem RecursiveBridgeInitialCodeImageRel.sourceCodeBytes
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {initial : EVMState}
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial) :
    shared.executionEnv.codeBytes =
      Assembly.Bytecode.encodeTarget target := by
  have hBytes := Reference.SharedStateRel.codeBytes
    hInitialCodeImageRel.world
  simpa [RecursiveBridgeInitialWorldRel,
    hInitialCodeImageRel.targetCode] using hBytes

@[simp] theorem canonicalEntryState_pc (initial : EVMState) :
    (canonicalEntryState initial).pc = Assembly.Program.pcAfter [] :=
  rfl

@[simp] theorem canonicalEntryState_stack (initial : EVMState) :
    (canonicalEntryState initial).stack = [] :=
  rfl

theorem RecursiveBridgeInitialWorldRel.to_canonicalEntryState
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {shared : EvmYul.SharedState .Yul}
    {initial : EVMState}
    (hInitialWorldRel :
      RecursiveBridgeInitialWorldRel cfg program shared initial) :
    Reference.SharedStateRel cfg
      { shared with
        executionEnv :=
          { shared.executionEnv with code := program.contract } }
      (canonicalEntryState initial).toSharedState := by
  simpa [RecursiveBridgeInitialWorldRel] using hInitialWorldRel

/--
Checked no-CALL runtime boundary used by the gas-aware `EVM.X` bridge.

The existing feature/source-static checker rules out external calls, external
code inspection, CREATE, and source-static failures. This wrapper additionally
rejects source and emitted-target `RETURNDATACOPY` until the source/gasless
target semantics carry the same return-data bounds enforced by gas-aware
`EVM.X`.
-/
noncomputable def
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
    (program : Program) :
    Option (Assembly.Program × Assembly.TargetProgram) :=
  match compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
      program with
  | none => none
  | some (asm, target) =>
      if Reference.Safe.FeatureCoverage.returnDataCopyBoundaryProgram? program
      then
        if Assembly.GasAware.targetProgramNoReturnDataCopy? target
        then some (asm, target)
        else none
      else none

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target)) :
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
        program =
      some (asm, target) ∧
        Reference.Safe.FeatureCoverage.returnDataCopyBoundaryProgram
          program ∧
          Assembly.GasAware.targetProgramNoReturnDataCopy target := by
  unfold
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
      at hCompileTarget
  cases hBase :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
        program with
  | none =>
      simp [hBase] at hCompileTarget
  | some pair =>
      rcases pair with ⟨asm', target'⟩
      simp [hBase] at hCompileTarget
      cases hReturnDataCopy :
          Reference.Safe.FeatureCoverage.returnDataCopyBoundaryProgram?
            program <;>
        simp [hReturnDataCopy] at hCompileTarget
      cases hTargetReturnDataCopy :
          Assembly.GasAware.targetProgramNoReturnDataCopy? target' <;>
        simp [hTargetReturnDataCopy] at hCompileTarget
      rcases hCompileTarget with ⟨rfl, rfl⟩
      exact
        ⟨by simp,
          Reference.Safe.FeatureCoverage.returnDataCopyBoundaryProgram_of_check
            (by simpa using hReturnDataCopy),
          Assembly.GasAware.targetProgramNoReturnDataCopy_of_check
            (by simpa using hTargetReturnDataCopy)⟩

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_compileChecked
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target)) :
    compileChecked? program = some asm :=
  compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_compileChecked
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
      hCompileTarget).1

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_targetNoReturnDataCopy
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target)) :
    Assembly.GasAware.targetProgramNoReturnDataCopy target :=
  (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
    hCompileTarget).2.2

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoReturnDataCopy
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target)) :
    Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy asm target :=
  Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy.of_target_noReturnDataCopy
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_targetNoReturnDataCopy
      hCompileTarget)

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target)) :
    Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate asm target := by
  let hBase :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
      hCompileTarget
  let hStatic :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hBase.1
  let hFeatures :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some hStatic.1
  let hResources :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hFeatures.1
  let hBytecode :=
    compileCheckedAssemblyTargetBytecode?_eq_some hResources.1
  let hProgramSourceAccepted : Program.SourceAccepted program :=
    Program.sourceAccepted_of_sourceAcceptedCore_supported
      hStatic.2.sourceAcceptedCore hStatic.2.supported
  let hProgramAccepted : Program.Accepted program :=
    accepted_of_sourceAccepted_compileChecked? hProgramSourceAccepted
      (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_compileChecked
        hBase.1)
  let hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program :=
    hStatic.2.toFullSourceAccepted hProgramAccepted
  let hCompile := (compileCheckedAssemblyTarget?_eq_some hBytecode.1).1
  let hSourceAccepted : RecursiveBridgeSourceAccepted program :=
    RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked
      hFullSourceAccepted hFeatures.2 hCompile
  let hNoCallAsm : asm.usesCallCreate = false :=
    Program.compileCheckedAssemblyTarget?_noCallCreate
      hSourceAccepted.reference hBytecode.1
  intro pc instr emitted before after blockState blockResult hAt hEmit
    hTargetBlock hRun targetInstr hMem
  rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
  subst targetInstr
  exact
    Assembly.GasAware.targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
      hNoCallAsm hAt hEmit hLocatedMem

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockPathChecks_of_core
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hCore :
      Assembly.GasAware.XStepTrace.XBlockReplayCoreNonGasReady asm target
        (Assembly.GasAware.validJumps target)) :
    Assembly.GasAware.XStepTrace.XBlockPathChecksReady asm target
      (Assembly.GasAware.validJumps target) :=
  Assembly.GasAware.XStepTrace.XBlockPathChecksReady.of_core_noReturnDataCopy_noCallCreate
    hCore
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoReturnDataCopy
      hCompileTarget)
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
      hCompileTarget)

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_assemble
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target)) :
    Assembly.assemble? asm = some target := by
  let hBase :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
      hCompileTarget
  let hStatic :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hBase.1
  let hFeatures :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some hStatic.1
  let hResources :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hFeatures.1
  let hBytecode :=
    compileCheckedAssemblyTargetBytecode?_eq_some hResources.1
  exact
    Assembly.Preservation.compile?_some_assemble
      (compileCheckedAssemblyTarget?_eq_some hBytecode.1).2

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_jumpdestCorrect
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target)) :
    Assembly.Bytecode.JumpdestCorrect target := by
  let hBase :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
      hCompileTarget
  let hStatic :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hBase.1
  let hFeatures :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some hStatic.1
  let hResources :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hFeatures.1
  exact
    (compileCheckedAssemblyTargetBytecode?_eq_some hResources.1).2.2

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_decodeSafety
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target)) :
    Assembly.Bytecode.DecodeSafety target := by
  let hBase :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
      hCompileTarget
  let hStatic :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hBase.1
  let hFeatures :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some hStatic.1
  let hResources :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hFeatures.1
  let hBytecode :=
    compileCheckedAssemblyTargetBytecode?_eq_some hResources.1
  exact
    Assembly.Bytecode.compile_decodeSafety
      (compileCheckedAssemblyTarget?_eq_some hBytecode.1).2
      hBytecode.2.1

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_instrCoreReady
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {targetOutcome : Assembly.StepResult}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hInstrCoreReady :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreReady asm target)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel state
        targetOutcome) :
    Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
      (Assembly.GasAware.validJumps target) hTrace :=
  Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.of_block_instr_core_ready
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_assemble
      hCompileTarget)
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_jumpdestCorrect
      hCompileTarget)
    hTrace hInstrCoreReady

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_traceInstrCoreReady
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {targetOutcome : Assembly.StepResult}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    {hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel state
        targetOutcome}
    (hTraceInstrCoreReady :
      Assembly.GasAware.XStepTrace.InstrCoreBlockTraceReadyFor target
        hTrace) :
    Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
      (Assembly.GasAware.validJumps target) hTrace :=
  Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.of_trace_instr_core_ready
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_assemble
      hCompileTarget)
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_jumpdestCorrect
      hCompileTarget)
    hTraceInstrCoreReady

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_traceInputsReady
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {targetOutcome : Assembly.StepResult}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    {hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel state
        targetOutcome}
    (hTraceInputsReady :
      Assembly.GasAware.XStepTrace.InstrCoreBlockTraceInputsReadyFor target
        hTrace) :
    Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
      (Assembly.GasAware.validJumps target) hTrace :=
  compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_traceInstrCoreReady
    hCompileTarget
    (Assembly.GasAware.XStepTrace.InstrCoreBlockTraceReadyFor.of_inputs_ready
      hTraceInputsReady)

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_instrCoreInputsReady
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {targetOutcome : Assembly.StepResult}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hInstrCoreInputsReady :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreInputsReady asm target)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel state
        targetOutcome) :
    Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
      (Assembly.GasAware.validJumps target) hTrace :=
  compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_traceInputsReady
    hCompileTarget
    (Assembly.GasAware.XStepTrace.InstrCoreBlockTraceInputsReadyFor.of_block_instr_inputs_ready
      hTrace hInstrCoreInputsReady)

theorem
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_instrCoreResources
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    {targetFuel : Nat} {state : EVMState}
    {targetOutcome : Assembly.StepResult}
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hResources :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreInputResources asm target)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target targetFuel state
        targetOutcome) :
    Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
      (Assembly.GasAware.validJumps target) hTrace :=
  compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_instrCoreInputsReady
    hCompileTarget
    (Assembly.GasAware.XStepTrace.XBlockInstrCoreInputsReady.of_resources
      hResources)
    hTrace

namespace RecursiveBridgeTargetRuntime

def withAcceptedNoCallCreate {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {initial : EVMState}
    (hAccepted : Reference.Accepted program)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (outOfGasPolicy : Assembly.OutOfGasPolicyAssumption asm initial)
    (currentContractProjection :
      Assembly.CurrentContractProjectionAssumption asm initial)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    RecursiveBridgeTargetRuntime asm target initial :=
  withNoCallCreate decodeWindow jumpdestCorrect outOfGasPolicy
    currentContractProjection
    (compileCheckedAssemblyTarget?_noCallCreate hAccepted hCheckedCompileTarget)
    hInitialPc hInitialStack

end RecursiveBridgeTargetRuntime

namespace RecursiveBridgeTopAssumptions

def withAcceptedNoCallCreate
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hSourceAccepted : RecursiveBridgeSourceAccepted program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hSemantics :
      RecursiveBridgeSemanticContracts cfg terminalRel revertRel prim
        outcomeRel program shared store)
    (hInitialWorldRel :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceFuelRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (outOfGasPolicy : Assembly.OutOfGasPolicyAssumption asm initial)
    (currentContractProjection :
      Assembly.CurrentContractProjectionAssumption asm initial)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    RecursiveBridgeTopAssumptions cfg terminalRel revertRel prim outcomeRel
      program asm target shared store sourceFuel initial referenceResult where
  sourceAccepted := hSourceAccepted
  compileResources := hCompileResources
  semantics := hSemantics
  initialShared := by
    simpa [RecursiveBridgeInitialWorldRel] using hInitialWorldRel
  sourceRun := hSourceFuelRun
  compileTarget := hCheckedCompileTarget
  targetRuntime :=
    RecursiveBridgeTargetRuntime.withAcceptedNoCallCreate
      hSourceAccepted.reference hCheckedCompileTarget decodeWindow jumpdestCorrect
      outOfGasPolicy currentContractProjection hInitialPc hInitialStack

end RecursiveBridgeTopAssumptions

/--
Final no-CALL/CREATE public assumption package.

This is the preferred surface for the current verified imported-Yul route when
the source bridge rejects call/create primitives. It keeps the gas-aware target
assumptions explicit but does not let callers provide an arbitrary
`RecursiveBridgeTargetRuntime`; the no-call/create part of the target runtime is
derived from source acceptedness and checked compile-target success.
-/
structure RecursiveBridgeTopNoCallAssumptions
    (cfg : Reference.StateRelConfig)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (outcomeRel : Reference.OutcomeRel)
    (program : Program)
    (asm : Assembly.Program) (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (sourceFuel : Nat)
    (initial : EVMState)
    (referenceResult : Reference.Result) : Prop where
  sourceAccepted : RecursiveBridgeSourceAccepted program
  compileResources : RecursiveBridgeCompileResources program
  semantics :
    RecursiveBridgeSemanticContracts cfg terminalRel revertRel prim
      outcomeRel program shared store
  initialShared :
    Reference.SharedStateRel cfg
      { shared with
        executionEnv :=
          { shared.executionEnv with code := program.contract } }
      initial.toSharedState
  sourceRun :
    RecursiveBridgeSourceRun program shared store sourceFuel referenceResult
  compileTarget :
    compileCheckedAssemblyTarget? program = some (asm, target)
  decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target
  jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target
  outOfGasPolicy : Assembly.OutOfGasPolicyAssumption asm initial
  currentContractProjection :
    Assembly.CurrentContractProjectionAssumption asm initial
  initialPc : initial.pc = Assembly.Program.pcAfter []
  initialStack : initial.stack = []

structure RecursiveBridgeTopNoCallSourceCompileAssumptions
    (cfg : Reference.StateRelConfig)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (outcomeRel : Reference.OutcomeRel)
    (program : Program)
    (asm : Assembly.Program) (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (sourceFuel : Nat)
    (initial : EVMState)
    (referenceResult : Reference.Result) : Prop where
  sourceAccepted : RecursiveBridgeSourceAccepted program
  sourceCompileAccepted : SourceCompileAccepted program
  semantics :
    RecursiveBridgeSemanticContracts cfg terminalRel revertRel prim
      outcomeRel program shared store
  initialShared :
    Reference.SharedStateRel cfg
      { shared with
        executionEnv :=
          { shared.executionEnv with code := program.contract } }
      initial.toSharedState
  sourceRun :
    RecursiveBridgeSourceRun program shared store sourceFuel referenceResult
  compileTarget :
    compileCheckedAssemblyTarget? program = some (asm, target)
  decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target
  jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target
  outOfGasPolicy : Assembly.OutOfGasPolicyAssumption asm initial
  currentContractProjection :
    Assembly.CurrentContractProjectionAssumption asm initial
  initialPc : initial.pc = Assembly.Program.pcAfter []
  initialStack : initial.stack = []

namespace RecursiveBridgeTopNoCallSourceCompileAssumptions

def withCanonicalObservation
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hSourceAccepted : RecursiveBridgeSourceAccepted program)
    (hSourceCompileAccepted : SourceCompileAccepted program)
    (hSemantics :
      RecursiveBridgeSemanticCoreContracts cfg terminalRel revertRel prim
        program)
    (hInitialWorldRel :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceFuelRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (outOfGasPolicy : Assembly.OutOfGasPolicyAssumption asm initial)
    (currentContractProjection :
      Assembly.CurrentContractProjectionAssumption asm initial)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    RecursiveBridgeTopNoCallSourceCompileAssumptions cfg terminalRel
      revertRel prim
      (RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store))
      program asm target shared store sourceFuel initial referenceResult where
  sourceAccepted := hSourceAccepted
  sourceCompileAccepted := hSourceCompileAccepted
  semantics := hSemantics.toSemanticContracts
  initialShared := by
    simpa [RecursiveBridgeInitialWorldRel] using hInitialWorldRel
  sourceRun := hSourceFuelRun
  compileTarget := hCheckedCompileTarget
  decodeWindow := decodeWindow
  jumpdestCorrect := jumpdestCorrect
  outOfGasPolicy := outOfGasPolicy
  currentContractProjection := currentContractProjection
  initialPc := hInitialPc
  initialStack := hInitialStack

def toNoCallAssumptions
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallSourceCompileAssumptions cfg terminalRel
        revertRel prim outcomeRel program asm target shared store sourceFuel
        initial referenceResult) :
    RecursiveBridgeTopNoCallAssumptions cfg terminalRel revertRel prim
      outcomeRel program asm target shared store sourceFuel initial
      referenceResult where
  sourceAccepted := hTop.sourceAccepted
  compileResources :=
    RecursiveBridgeCompileResources.of_sourceCompileAccepted
      hTop.sourceCompileAccepted
  semantics := hTop.semantics
  initialShared := hTop.initialShared
  sourceRun := hTop.sourceRun
  compileTarget := hTop.compileTarget
  decodeWindow := hTop.decodeWindow
  jumpdestCorrect := hTop.jumpdestCorrect
  outOfGasPolicy := hTop.outOfGasPolicy
  currentContractProjection := hTop.currentContractProjection
  initialPc := hTop.initialPc
  initialStack := hTop.initialStack

end RecursiveBridgeTopNoCallSourceCompileAssumptions

namespace RecursiveBridgeTopNoCallAssumptions

def toTopAssumptions
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallAssumptions cfg terminalRel revertRel prim
        outcomeRel program asm target shared store sourceFuel initial
        referenceResult) :
    RecursiveBridgeTopAssumptions cfg terminalRel revertRel prim outcomeRel
      program asm target shared store sourceFuel initial referenceResult :=
  RecursiveBridgeTopAssumptions.withAcceptedNoCallCreate
    hTop.sourceAccepted hTop.compileResources hTop.semantics
    hTop.initialShared hTop.sourceRun hTop.compileTarget hTop.decodeWindow
    hTop.jumpdestCorrect hTop.outOfGasPolicy hTop.currentContractProjection
    hTop.initialPc hTop.initialStack

end RecursiveBridgeTopNoCallAssumptions

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallAssumptions cfg terminalRel revertRel prim
        outcomeRel program asm target shared store sourceFuel initial
        referenceResult) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
    (hTop := hTop.toTopAssumptions)

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_budgetedConcreteGas_X
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallAssumptions cfg terminalRel revertRel prim
        outcomeRel program asm target shared store sourceFuel initial
        referenceResult)
    (hCode : initial.executionEnv.code = Assembly.Bytecode.encodeTarget target)
    (hTargetGasBudgetFits :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceGasBudgetFits asm targetFuel
          initial targetOutcome)
    (hTargetNonGasChecks :
      Assembly.GasAware.XStepTrace.XBlockPathChecksReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gas result,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      gas =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel initial targetOutcome ∧
                      gas < EvmYul.UInt256.size ∧
                        EvmYul.EVM.X evmFuel
                            (Assembly.GasAware.validJumps target)
                            (Assembly.GasAware.installCodeAndGas target gas
                              initial) =
                          .ok result ∧
                        Assembly.GasAware.XResultAgrees targetOutcome
                          result := by
  obtain
    ⟨sourceOutcome, targetFuel, targetOutcome, hRun, hOutcome,
      hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace⟩ :=
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall
      hTop
  have hGasFits := hTargetGasBudgetFits hTrace
  have hDoneContinue := hTargetDoneContinuation hTrace
  have hSafety : Assembly.Bytecode.DecodeSafety target :=
    Assembly.Bytecode.compile_decodeSafety
      (compileCheckedAssemblyTarget?_eq_some hTop.compileTarget).2
      hTop.decodeWindow
  have hNoCallCreate :
      Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate asm target :=
    Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate.of_program_no_call_create
      (Program.compileCheckedAssemblyTarget?_noCallCreate
        hTop.sourceAccepted.reference hTop.compileTarget)
  obtain ⟨evmFuel, result, hGasValueFits, hXRun, hAgrees⟩ :=
    Assembly.GasAware.XStepTrace.blockTraceResult_computed_gas_of_path_checks_no_call_create_and_budget
      (program := asm)
      (target := target)
      (initial := initial)
      (targetFuel := targetFuel)
      (targetResult := targetOutcome)
      hEncoding hSafety hCode hTrace hGasFits hTargetNonGasChecks hNoCallCreate
      (Assembly.GasAware.XStepTrace.XTraceDoneContinuation.to_path
        hDoneContinue)
  let gasValue :=
    Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel initial
      targetOutcome
  exact
    ⟨sourceOutcome, targetFuel, targetOutcome, evmFuel, gasValue, result,
      hRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding, hOutOfGas,
      hProjection, hTrace, rfl, hGasValueFits, hXRun, hAgrees⟩

/--
Trace-local sufficient-gas bridge at the no-CALL top-assumption boundary.

The non-gas `EVM.X` safety obligation is indexed by the actual gasless target
trace produced by preservation. This is the thin bridge we want higher layers
to construct, rather than a global path-check predicate over every target
state.
-/
theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sufficientGas_traceChecks_X
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallAssumptions cfg terminalRel revertRel prim
        outcomeRel program asm target shared store sourceFuel initial
        referenceResult)
    (hCode : initial.executionEnv.code = Assembly.Bytecode.encodeTarget target)
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel initial
            targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel initial targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  initial) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  obtain
    ⟨sourceOutcome, targetFuel, targetOutcome, hRun, hOutcome,
      hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace⟩ :=
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall
      hTop
  have hDoneContinue := hTargetDoneContinuation hTrace
  have hSafety : Assembly.Bytecode.DecodeSafety target :=
    Assembly.Bytecode.compile_decodeSafety
      (compileCheckedAssemblyTarget?_eq_some hTop.compileTarget).2
      hTop.decodeWindow
  have hNoCallCreate :
      Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate asm target :=
    Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate.of_program_no_call_create
      (Program.compileCheckedAssemblyTarget?_noCallCreate
        hTop.sourceAccepted.reference hTop.compileTarget)
  let gasBound :=
    Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel initial
      targetOutcome
  refine
    ⟨sourceOutcome, targetFuel, targetOutcome, gasBound, hRun, hOutcome,
      hWholeRel, hAccepted, hBytes, hEncoding, hOutOfGas, hProjection,
      hTrace, rfl, ?_⟩
  intro gas hGasAtLeast hGasFits
  obtain ⟨evmFuel, result, hXRun, hAgrees⟩ :=
    Assembly.GasAware.XStepTrace.blockTraceResult_runs_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget
      (program := asm)
      (target := target)
      (initial := initial)
      (targetFuel := targetFuel)
      (targetResult := targetOutcome)
      hEncoding hSafety hCode hTrace (hTargetTraceChecks hTrace)
      hNoCallCreate
      (Assembly.GasAware.XStepTrace.XTraceDoneContinuation.to_path
        hDoneContinue)
      (gas := gas)
      (by simpa [gasBound] using hGasAtLeast)
      hGasFits
  exact ⟨evmFuel, result, hXRun, hAgrees⟩

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sufficientGas_coreNoReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallAssumptions cfg terminalRel revertRel prim
        outcomeRel program asm target shared store sourceFuel initial
        referenceResult)
    (hCode : initial.executionEnv.code = Assembly.Bytecode.encodeTarget target)
    (hTargetCoreChecks :
      Assembly.GasAware.XStepTrace.XBlockReplayCoreNonGasReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetNoReturnDataCopy :
      Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy asm target)
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel initial targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  initial) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  have hNoCallCreate :
      Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate asm target :=
    Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate.of_program_no_call_create
      (Program.compileCheckedAssemblyTarget?_noCallCreate
        hTop.sourceAccepted.reference hTop.compileTarget)
  have hPathChecks :
      Assembly.GasAware.XStepTrace.XBlockPathChecksReady asm target
        (Assembly.GasAware.validJumps target) :=
    Assembly.GasAware.XStepTrace.XBlockPathChecksReady.of_core_noReturnDataCopy_noCallCreate
      hTargetCoreChecks hTargetNoReturnDataCopy hNoCallCreate
  exact
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sufficientGas_traceChecks_X
      hTop hCode
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor.of_block_path_checks
          hTrace hPathChecks)
      hTargetDoneContinuation

/--
Sufficient-gas public bridge at the no-CALL top-assumption boundary.

This version exposes the computed gasless trace budget as a lower bound rather
than asking callers to prove that the exact budget itself fits in a `UInt256`.
For every installed UInt256 gas value at or above that bound, the gas-aware EVM
run follows the checked path and agrees with the gasless target result.
-/
theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sufficientGas_X
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallAssumptions cfg terminalRel revertRel prim
        outcomeRel program asm target shared store sourceFuel initial
        referenceResult)
    (hCode : initial.executionEnv.code = Assembly.Bytecode.encodeTarget target)
    (hTargetNonGasChecks :
      Assembly.GasAware.XStepTrace.XBlockPathChecksReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel initial targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  initial) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sufficientGas_traceChecks_X
    hTop hCode
    (fun hTrace =>
      Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor.of_block_path_checks
        hTrace hTargetNonGasChecks)
    hTargetDoneContinuation

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_budgetedConcreteGas_X
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallSourceCompileAssumptions cfg terminalRel
        revertRel prim outcomeRel program asm target shared store sourceFuel
        initial referenceResult)
    (hCode : initial.executionEnv.code = Assembly.Bytecode.encodeTarget target)
    (hTargetGasBudgetFits :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceGasBudgetFits asm targetFuel
          initial targetOutcome)
    (hTargetNonGasChecks :
      Assembly.GasAware.XStepTrace.XBlockPathChecksReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gas result,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      gas =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel initial targetOutcome ∧
                      gas < EvmYul.UInt256.size ∧
                        EvmYul.EVM.X evmFuel
                            (Assembly.GasAware.validJumps target)
                            (Assembly.GasAware.installCodeAndGas target gas
                              initial) =
                          .ok result ∧
                        Assembly.GasAware.XResultAgrees targetOutcome
                          result :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_budgetedConcreteGas_X
    hTop.toNoCallAssumptions hCode hTargetGasBudgetFits
    hTargetNonGasChecks hTargetDoneContinuation

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_sufficientGas_traceChecks_X
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallSourceCompileAssumptions cfg terminalRel
        revertRel prim outcomeRel program asm target shared store sourceFuel
        initial referenceResult)
    (hCode : initial.executionEnv.code = Assembly.Bytecode.encodeTarget target)
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel initial
            targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel initial targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  initial) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sufficientGas_traceChecks_X
    hTop.toNoCallAssumptions hCode hTargetTraceChecks
    hTargetDoneContinuation

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_sufficientGas_coreNoReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallSourceCompileAssumptions cfg terminalRel
        revertRel prim outcomeRel program asm target shared store sourceFuel
        initial referenceResult)
    (hCode : initial.executionEnv.code = Assembly.Bytecode.encodeTarget target)
    (hTargetCoreChecks :
      Assembly.GasAware.XStepTrace.XBlockReplayCoreNonGasReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetNoReturnDataCopy :
      Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy asm target)
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel initial targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  initial) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sufficientGas_coreNoReturnDataCopy_X
    hTop.toNoCallAssumptions hCode hTargetCoreChecks hTargetNoReturnDataCopy
    hTargetDoneContinuation

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_sufficientGas_X
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallSourceCompileAssumptions cfg terminalRel
        revertRel prim outcomeRel program asm target shared store sourceFuel
        initial referenceResult)
    (hCode : initial.executionEnv.code = Assembly.Bytecode.encodeTarget target)
    (hTargetNonGasChecks :
      Assembly.GasAware.XStepTrace.XBlockPathChecksReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel initial targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  initial) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_sufficientGas_traceChecks_X
    hTop hCode
    (fun hTrace =>
      Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor.of_block_path_checks
        hTrace hTargetNonGasChecks)
    hTargetDoneContinuation

/--
Concrete-gas public wrapper using the checked explicit block-trace gas budget.

Unlike the older `concreteGas_X` theorem, this does not ask callers to provide
the former broad gas-precondition bridge. The target-side boundary is split
into its actual pieces: the computed finite gas budget fits in `UInt256`, the
path-local non-gas `EVM.X` checks are safe, and fuel-exhausted target traces
have a continuation. Bytecode decode readiness is derived from the checked
compiler encoding and decode-safety facts.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_budgetedConcreteGas_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hTargetGasBudgetFits :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (canonicalEntryState initial) targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceGasBudgetFits asm targetFuel
          (canonicalEntryState initial) targetOutcome)
    (hTargetNonGasChecks :
      Assembly.GasAware.XStepTrace.XBlockPathChecksReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (canonicalEntryState initial) targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gas result,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gas =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      gas < EvmYul.UInt256.size ∧
                        EvmYul.EVM.X evmFuel
                            (Assembly.GasAware.validJumps target)
                            (Assembly.GasAware.installCodeAndGas target gas
                              (canonicalEntryState initial)) =
                          .ok result ∧
                        Assembly.GasAware.XResultAgrees targetOutcome
                          result := by
  obtain ⟨sourceFuel, hRun⟩ := hSourceFuelRun
  let hStatic :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hCheckedCompileTarget
  let hFeatures :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some hStatic.1
  let hResources :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hFeatures.1
  let hBytecode :=
    compileCheckedAssemblyTargetBytecode?_eq_some hResources.1
  let hProgramSourceAccepted : Program.SourceAccepted program :=
    Program.sourceAccepted_of_sourceAcceptedCore_supported
      hStatic.2.sourceAcceptedCore hStatic.2.supported
  let hProgramAccepted : Program.Accepted program :=
    accepted_of_sourceAccepted_compileChecked? hProgramSourceAccepted
      (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_compileChecked
        hCheckedCompileTarget)
  let hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program :=
    hStatic.2.toFullSourceAccepted hProgramAccepted
  let hCompile := (compileCheckedAssemblyTarget?_eq_some hBytecode.1).1
  let hSourceAccepted : RecursiveBridgeSourceAccepted program :=
    RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked
      hFullSourceAccepted hFeatures.2 hCompile
  let hSourceCompileAccepted : SourceCompileAccepted program :=
    RecursiveBridgeCompileResources.to_sourceCompileAccepted hSourceAccepted
      hResources.2
  have hCode :
      (canonicalEntryState initial).executionEnv.code =
        Assembly.Bytecode.encodeTarget target := by
    simpa [canonicalEntryState] using hInitialCodeImageRel.targetCode
  obtain
    ⟨sourceOutcome, targetFuel, targetOutcome, evmFuel, gas, result,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, hGasFits, hXRun, hAgrees⟩ :=
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_budgetedConcreteGas_X
      (RecursiveBridgeTopNoCallSourceCompileAssumptions.withCanonicalObservation
        hSourceAccepted hSourceCompileAccepted
        (RecursiveBridgeSemanticCoreContracts.ofBoundaries
          RecursiveBridgePrimitiveArityContracts.structured
          (RecursiveBridgeTerminalContracts.structured_of_observation
            (RecursiveBridgeTerminalObservationContracts.canonical cfg program))
          hExprNoSuccessfulOutOfFuel.to_resultContracts)
        (RecursiveBridgeInitialWorldRel.to_canonicalEntryState
          hInitialCodeImageRel.world)
        hRun hBytecode.1 hBytecode.2.1 hBytecode.2.2
        (Assembly.OutOfGasPolicyAssumption.trivial (program := asm)
          (initial := canonicalEntryState initial))
        (Assembly.CurrentContractProjectionAssumption.trivial (program := asm)
          (initial := canonicalEntryState initial))
        (canonicalEntryState_pc initial) (canonicalEntryState_stack initial))
      hCode hTargetGasBudgetFits hTargetNonGasChecks
      hTargetDoneContinuation
  exact
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, evmFuel, gas,
      result, hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, hGasFits, hXRun, hAgrees⟩

/--
Preferred trace-local sufficient-gas theorem for the canonical imported-Yul
boundary.

This is the same public observation theorem as `..._sufficientGas_X`, but its
target-side non-gas safety premise is indexed by the actual gasless trace
produced by the compiler-preservation proof.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (canonicalEntryState initial) targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  obtain ⟨sourceFuel, hRun⟩ := hSourceFuelRun
  let hStatic :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hCheckedCompileTarget
  let hFeatures :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some hStatic.1
  let hResources :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hFeatures.1
  let hBytecode :=
    compileCheckedAssemblyTargetBytecode?_eq_some hResources.1
  let hProgramSourceAccepted : Program.SourceAccepted program :=
    Program.sourceAccepted_of_sourceAcceptedCore_supported
      hStatic.2.sourceAcceptedCore hStatic.2.supported
  let hProgramAccepted : Program.Accepted program :=
    accepted_of_sourceAccepted_compileChecked? hProgramSourceAccepted
      (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_compileChecked
        hCheckedCompileTarget)
  let hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program :=
    hStatic.2.toFullSourceAccepted hProgramAccepted
  let hCompile := (compileCheckedAssemblyTarget?_eq_some hBytecode.1).1
  let hSourceAccepted : RecursiveBridgeSourceAccepted program :=
    RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked
      hFullSourceAccepted hFeatures.2 hCompile
  let hSourceCompileAccepted : SourceCompileAccepted program :=
    RecursiveBridgeCompileResources.to_sourceCompileAccepted hSourceAccepted
      hResources.2
  have hCode :
      (canonicalEntryState initial).executionEnv.code =
        Assembly.Bytecode.encodeTarget target := by
    simpa [canonicalEntryState] using hInitialCodeImageRel.targetCode
  obtain
    ⟨sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, hRunsAbove⟩ :=
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_sufficientGas_traceChecks_X
      (RecursiveBridgeTopNoCallSourceCompileAssumptions.withCanonicalObservation
        hSourceAccepted hSourceCompileAccepted
        (RecursiveBridgeSemanticCoreContracts.ofBoundaries
          RecursiveBridgePrimitiveArityContracts.structured
          (RecursiveBridgeTerminalContracts.structured_of_observation
            (RecursiveBridgeTerminalObservationContracts.canonical cfg program))
          hExprNoSuccessfulOutOfFuel.to_resultContracts)
        (RecursiveBridgeInitialWorldRel.to_canonicalEntryState
          hInitialCodeImageRel.world)
        hRun hBytecode.1 hBytecode.2.1 hBytecode.2.2
        (Assembly.OutOfGasPolicyAssumption.trivial (program := asm)
          (initial := canonicalEntryState initial))
        (Assembly.CurrentContractProjectionAssumption.trivial (program := asm)
          (initial := canonicalEntryState initial))
        (canonicalEntryState_pc initial) (canonicalEntryState_stack initial))
      hCode hTargetTraceChecks hTargetDoneContinuation
  exact
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, hRunsAbove⟩

/--
Trace-local sufficient-gas theorem whose public source boundary is the
expression-result contract directly, rather than the older successful
`.OutOfFuel` exclusion used to manufacture it.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_traceChecks_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprResultContracts : RecursiveBridgeExprResultContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (canonicalEntryState initial) targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  obtain ⟨sourceFuel, hRun⟩ := hSourceFuelRun
  let hStatic :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hCheckedCompileTarget
  let hFeatures :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some hStatic.1
  let hResources :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hFeatures.1
  let hBytecode :=
    compileCheckedAssemblyTargetBytecode?_eq_some hResources.1
  let hProgramSourceAccepted : Program.SourceAccepted program :=
    Program.sourceAccepted_of_sourceAcceptedCore_supported
      hStatic.2.sourceAcceptedCore hStatic.2.supported
  let hProgramAccepted : Program.Accepted program :=
    accepted_of_sourceAccepted_compileChecked? hProgramSourceAccepted
      (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_compileChecked
        hCheckedCompileTarget)
  let hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program :=
    hStatic.2.toFullSourceAccepted hProgramAccepted
  let hCompile := (compileCheckedAssemblyTarget?_eq_some hBytecode.1).1
  let hSourceAccepted : RecursiveBridgeSourceAccepted program :=
    RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked
      hFullSourceAccepted hFeatures.2 hCompile
  let hSourceCompileAccepted : SourceCompileAccepted program :=
    RecursiveBridgeCompileResources.to_sourceCompileAccepted hSourceAccepted
      hResources.2
  have hCode :
      (canonicalEntryState initial).executionEnv.code =
        Assembly.Bytecode.encodeTarget target := by
    simpa [canonicalEntryState] using hInitialCodeImageRel.targetCode
  obtain
    ⟨sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, hRunsAbove⟩ :=
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_sufficientGas_traceChecks_X
      (RecursiveBridgeTopNoCallSourceCompileAssumptions.withCanonicalObservation
        hSourceAccepted hSourceCompileAccepted
        (RecursiveBridgeSemanticCoreContracts.ofBoundaries
          RecursiveBridgePrimitiveArityContracts.structured
          (RecursiveBridgeTerminalContracts.structured_of_observation
            (RecursiveBridgeTerminalObservationContracts.canonical cfg program))
          hExprResultContracts)
        (RecursiveBridgeInitialWorldRel.to_canonicalEntryState
          hInitialCodeImageRel.world)
        hRun hBytecode.1 hBytecode.2.1 hBytecode.2.2
        (Assembly.OutOfGasPolicyAssumption.trivial (program := asm)
          (initial := canonicalEntryState initial))
        (Assembly.CurrentContractProjectionAssumption.trivial (program := asm)
          (initial := canonicalEntryState initial))
        (canonicalEntryState_pc initial) (canonicalEntryState_stack initial))
      hCode hTargetTraceChecks hTargetDoneContinuation
  exact
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, hRunsAbove⟩

/--
Trace-local sufficient-gas theorem with the running-result finalization
condition made concrete.

Halted gasless target traces need no continuation.  If preservation stops with
a `.running` state, callers only need to prove the precise fallthrough-STOP
observation condition for that final state; the generic
`XTraceDoneContinuation` package is built internally here.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_fallthrough_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  refine
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hTargetTraceChecks ?_
  intro targetFuel targetOutcome hTrace
  cases targetOutcome with
  | running targetState =>
      exact
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation.running_of_fallthrough_stop
          (hTargetFallthrough hTrace)
  | halted halt =>
      exact Assembly.GasAware.XStepTrace.XTraceDoneContinuation.halted

/--
Stricter fallthrough theorem for the public no-CALL gas-aware boundary.

This is the fallthrough theorem above, but its checked compile premise also
structurally rejects `RETURNDATACOPY`, avoiding the known mismatch where
gas-aware `EVM.X` checks return-data bounds that the current source/gasless
target bridge does not yet model.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_fallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  exact
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_fallthrough_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
        hCheckedCompileTarget).1
      hTargetTraceChecks hTargetFallthrough

/--
Preferred no-CALL gas-aware public root with trace-local core non-gas checks.

The checked compiler boundary supplies the no-CALL/CREATE and
no-`RETURNDATACOPY` side conditions. The remaining target-side safety premise
is local to the concrete gasless block trace rather than a global replay
certificate over arbitrary emitted-code suffix states.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_fallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceCoreChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceCoreChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  exact
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_fallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor.of_trace_core_noReturnDataCopy_noCallCreate
          (hTargetTraceCoreChecks hTrace)
          (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoReturnDataCopy
            hCheckedCompileTarget)
            (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
              hCheckedCompileTarget))
      hTargetFallthrough

/--
Preferred no-CALL gas-aware public root with concrete clean fallthrough facts.

Running gasless target traces are finalized in gas-aware `EVM.X` by one
fallthrough `STOP` step. This wrapper keeps that finalization premise concrete:
the final state must decode off the end of bytecode, have a bounded stack, and
already have the empty return buffers that `STOP` writes.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceCoreChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceCoreChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  exact
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_fallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hTargetTraceCoreChecks
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady.of_clean
          (hTargetFallthrough hTrace))

/--
Preferred no-CALL gas-aware public root through the core-safe target trace
layer.

The remaining target-side execution premise is now phrased as a gasless
intermediate trace (`CoreBlockTraceResultFor`) rather than directly as the
gas-aware replay predicate. The checked compiler facts still discharge
no-CALL/CREATE and no-`RETURNDATACOPY`.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_coreTrace_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetCoreTrace :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  exact
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.to_trace_core_checks
          (hTargetCoreTrace hTrace)
          (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
            hCheckedCompileTarget))
      hTargetFallthrough

/--
Preferred no-CALL gas-aware public root through local emitted-block core
readiness.

The checked compiler boundary constructs the assembly layout and jumpdest facts
needed to lift this local premise into the core-safe target trace layer.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_instrCoreReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetInstrCoreReady :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreReady asm target)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  exact
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_coreTrace_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_instrCoreReady
          hCheckedCompileTarget hTargetInstrCoreReady hTrace)
      hTargetFallthrough

/--
Preferred no-CALL gas-aware public root through trace-local emitted-block core
readiness.

Unlike `XBlockInstrCoreReady`, this premise only talks about blocks that occur
in the actual gasless target trace, so later stack/resource invariants can
discharge it without proving false facts about arbitrary starting stacks.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceInstrCoreReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceInstrCoreReady :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.InstrCoreBlockTraceReadyFor target
          hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  exact
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_coreTrace_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_traceInstrCoreReady
          hCheckedCompileTarget (hTargetTraceInstrCoreReady hTrace))
      hTargetFallthrough

/--
Preferred no-CALL gas-aware public root through trace-local core inputs.

This is the proof-facing boundary we want to discharge next: stack bounds and
primitive core readiness are attached to the exact gasless target trace
constructor before being lifted to emitted-block core readiness.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceInputsReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceInputsReady :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.InstrCoreBlockTraceInputsReadyFor target
          hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  exact
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceInstrCoreReady_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.InstrCoreBlockTraceReadyFor.of_inputs_ready
          (hTargetTraceInputsReady hTrace))
      hTargetFallthrough

/--
Audit-facing sufficient-gas theorem whose conclusion exposes the checked
`EVM.X` path witness.

The older `traceInputsReady` theorem only exposes the final `EVM.X = .ok`
equation.  This wrapper keeps the same public premises but strengthens the
sufficient-gas conclusion with the `XStepTrace` proof that the gas-aware run
follows the decoded bytecode path certified from the gasless trace.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_stepTrace_traceInputsReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceInputsReady :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.InstrCoreBlockTraceInputsReadyFor target
          hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            Assembly.GasAware.XStepTrace
                                (Assembly.GasAware.validJumps target) evmFuel
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) result ∧
                              EvmYul.EVM.X evmFuel
                                  (Assembly.GasAware.validJumps target)
                                  (Assembly.GasAware.installCodeAndGas target gas
                                    (canonicalEntryState initial)) =
                                .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result := by
  obtain
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, _hRunsAbove⟩ :=
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceInputsReady_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hTargetTraceInputsReady hTargetFallthrough
  have hCode :
      (canonicalEntryState initial).executionEnv.code =
        Assembly.Bytecode.encodeTarget target := by
    simpa [canonicalEntryState] using hInitialCodeImageRel.targetCode
  have hSafety : Assembly.Bytecode.DecodeSafety target :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_decodeSafety
      hCheckedCompileTarget
  have hNoCallCreate :
      Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate asm target :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
      hCheckedCompileTarget
  have hNoReturnDataCopy :
      Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy asm target :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoReturnDataCopy
      hCheckedCompileTarget
  have hCoreTrace :
      Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
        (Assembly.GasAware.validJumps target) hTrace :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_traceInputsReady
      hCheckedCompileTarget (hTargetTraceInputsReady hTrace)
  have hTraceCoreChecks :
      Assembly.GasAware.XStepTrace.XBlockTraceCoreChecksReadyFor
        (Assembly.GasAware.validJumps target) hTrace :=
    Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.to_trace_core_checks
      hCoreTrace hNoCallCreate
  have hTraceChecks :
      Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
        (Assembly.GasAware.validJumps target) hTrace :=
    Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor.of_trace_core_noReturnDataCopy_noCallCreate
      hTraceCoreChecks hNoReturnDataCopy hNoCallCreate
  have hDoneContinue :
      Assembly.GasAware.XStepTrace.XTraceDoneContinuation
        (Assembly.GasAware.validJumps target) targetOutcome := by
    cases targetOutcome with
    | running targetState =>
        exact
          Assembly.GasAware.XStepTrace.XTraceDoneContinuation.running_of_fallthrough_stop
            (Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady.of_clean
              (hTargetFallthrough hTrace))
    | halted halt =>
        exact Assembly.GasAware.XStepTrace.XTraceDoneContinuation.halted
  refine
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, ?_⟩
  intro gas hGasAtLeast hGasFits
  obtain ⟨evmFuel, result, hTraceX, hXRun, hAgrees⟩ :=
    Assembly.GasAware.XStepTrace.blockTraceResult_stepTrace_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget
      (program := asm)
      (target := target)
      (initial := canonicalEntryState initial)
      (targetFuel := targetFuel)
      (targetResult := targetOutcome)
      hEncoding hSafety hCode hTrace hTraceChecks hNoCallCreate
      (Assembly.GasAware.XStepTrace.XTraceDoneContinuation.to_path
        hDoneContinue)
      (gas := gas)
      (by simpa [hGasEq] using hGasAtLeast)
      hGasFits
  exact ⟨evmFuel, result, hTraceX, hXRun, hAgrees⟩

/--
Audit-facing sufficient-gas theorem through a named block-input resource
predicate.

This removes the public per-trace callback shape: callers supply one checked
`XBlockInstrCoreInputsReady` fact for emitted target blocks, and the trace-local
`InstrCoreBlockTraceInputsReadyFor` evidence is constructed by induction over
the actual gasless target trace.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_stepTrace_instrCoreInputsReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetInstrCoreInputsReady :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreInputsReady asm target)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            Assembly.GasAware.XStepTrace
                                (Assembly.GasAware.validJumps target) evmFuel
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) result ∧
                              EvmYul.EVM.X evmFuel
                                  (Assembly.GasAware.validJumps target)
                                  (Assembly.GasAware.installCodeAndGas target gas
                                    (canonicalEntryState initial)) =
                                .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result :=
  compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_stepTrace_traceInputsReady_cleanFallthrough_noReturnDataCopy_X
    hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
    hCheckedCompileTarget
    (fun hTrace =>
      Assembly.GasAware.XStepTrace.InstrCoreBlockTraceInputsReadyFor.of_block_instr_inputs_ready
        hTrace hTargetInstrCoreInputsReady)
    hTargetFallthrough

/--
Preferred no-CALL gas-aware public root with the remaining non-CALL boundaries
named directly.

The source side asks for the expression-result contract itself, not the older
program-wide successful-`.OutOfFuel` exclusion.  The target side splits the
trace-local non-gas `EVM.X` checks into a resource package and a finalization
package, both tied to the compiled target trace.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_stepTrace_instrCoreResources_finalization_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprResultContracts : RecursiveBridgeExprResultContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetInstrCoreResources :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreInputResources asm target)
    (hTargetFinalization :
      Assembly.GasAware.XStepTrace.XBlockTraceFinalizationReady
        (Assembly.GasAware.validJumps target) asm target
        (canonicalEntryState initial)) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            Assembly.GasAware.XStepTrace
                                (Assembly.GasAware.validJumps target) evmFuel
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) result ∧
                              EvmYul.EVM.X evmFuel
                                  (Assembly.GasAware.validJumps target)
                                  (Assembly.GasAware.installCodeAndGas target gas
                                    (canonicalEntryState initial)) =
                                .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result := by
  have hCheckedBase :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target) :=
    (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
      hCheckedCompileTarget).1
  have hNoCallCreate :
      Assembly.GasAware.XStepTrace.XBlockReplayNoCallCreate asm target :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
      hCheckedCompileTarget
  have hNoReturnDataCopy :
      Assembly.GasAware.XStepTrace.XBlockReplayNoReturnDataCopy asm target :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoReturnDataCopy
      hCheckedCompileTarget
  have hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace := by
    intro targetFuel targetOutcome hTrace
    have hCoreTrace :
        Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
          (Assembly.GasAware.validJumps target) hTrace :=
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_instrCoreResources
        hCheckedCompileTarget hTargetInstrCoreResources hTrace
    have hTraceCoreChecks :
        Assembly.GasAware.XStepTrace.XBlockTraceCoreChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace :=
      Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.to_trace_core_checks
        hCoreTrace hNoCallCreate
    exact
      Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor.of_trace_core_noReturnDataCopy_noCallCreate
        hTraceCoreChecks hNoReturnDataCopy hNoCallCreate
  obtain
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, _hRunsAbove⟩ :=
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_traceChecks_X
      hExprResultContracts hInitialCodeImageRel hSourceFuelRun
      hCheckedBase hTargetTraceChecks
      (Assembly.GasAware.XStepTrace.XBlockTraceFinalizationReady.to_done_continuation
        hTargetFinalization)
  have hCode :
      (canonicalEntryState initial).executionEnv.code =
        Assembly.Bytecode.encodeTarget target := by
    simpa [canonicalEntryState] using hInitialCodeImageRel.targetCode
  have hSafety : Assembly.Bytecode.DecodeSafety target :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_decodeSafety
      hCheckedCompileTarget
  have hTraceChecks :
      Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
        (Assembly.GasAware.validJumps target) hTrace :=
    hTargetTraceChecks hTrace
  have hDoneContinue :
      Assembly.GasAware.XStepTrace.XTraceDoneContinuation
        (Assembly.GasAware.validJumps target) targetOutcome :=
    Assembly.GasAware.XStepTrace.XBlockTraceFinalizationReady.to_done_continuation
      hTargetFinalization hTrace
  refine
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, ?_⟩
  intro gas hGasAtLeast hGasFits
  obtain ⟨evmFuel, result, hTraceX, hXRun, hAgrees⟩ :=
    Assembly.GasAware.XStepTrace.blockTraceResult_stepTrace_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget
      (program := asm)
      (target := target)
      (initial := canonicalEntryState initial)
      (targetFuel := targetFuel)
      (targetResult := targetOutcome)
      hEncoding hSafety hCode hTrace hTraceChecks hNoCallCreate
      (Assembly.GasAware.XStepTrace.XTraceDoneContinuation.to_path
        hDoneContinue)
      (gas := gas)
      (by simpa [hGasEq] using hGasAtLeast)
      hGasFits
  exact ⟨evmFuel, result, hTraceX, hXRun, hAgrees⟩

/--
Sharper no-CALL gas-aware public root using the remaining core non-gas
obligation directly.

The checked compiler boundary supplies the no-CALL/CREATE and
no-`RETURNDATACOPY` target-side side conditions; callers only provide the
remaining core checks that are neither gas nor decoded-bytecode facts.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_core_fallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetCoreChecks :
      Assembly.GasAware.XStepTrace.XBlockReplayCoreNonGasReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  exact
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_fallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.to_trace_core_checks
          (Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.of_block_replay_core
            hTrace hTargetCoreChecks)
          (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
            hCheckedCompileTarget))
      hTargetFallthrough

/--
Preferred sufficient-gas theorem for the canonical imported-Yul boundary.

The theorem hides the source fuel existential and exposes the gas-aware EVM
bridge as a lower-bound statement: once the caller installs any UInt256 gas
value at or above the checked gasless trace budget, `EVM.X` produces an
agreeing result. The remaining target-side premise is the non-gas path-check
safety package; gas is no longer supplied through an oracle-style assumption.
-/
theorem compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hTargetNonGasChecks :
      Assembly.GasAware.XStepTrace.XBlockPathChecksReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (canonicalEntryState initial) targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (canonicalEntryState initial)
                          targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ evmFuel result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                            Assembly.GasAware.XResultAgrees targetOutcome
                              result := by
  obtain ⟨sourceFuel, hRun⟩ := hSourceFuelRun
  let hStatic :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hCheckedCompileTarget
  let hFeatures :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some hStatic.1
  let hResources :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hFeatures.1
  let hBytecode :=
    compileCheckedAssemblyTargetBytecode?_eq_some hResources.1
  let hProgramSourceAccepted : Program.SourceAccepted program :=
    Program.sourceAccepted_of_sourceAcceptedCore_supported
      hStatic.2.sourceAcceptedCore hStatic.2.supported
  let hProgramAccepted : Program.Accepted program :=
    accepted_of_sourceAccepted_compileChecked? hProgramSourceAccepted
      (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_compileChecked
        hCheckedCompileTarget)
  let hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program :=
    hStatic.2.toFullSourceAccepted hProgramAccepted
  let hCompile := (compileCheckedAssemblyTarget?_eq_some hBytecode.1).1
  let hSourceAccepted : RecursiveBridgeSourceAccepted program :=
    RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked
      hFullSourceAccepted hFeatures.2 hCompile
  let hSourceCompileAccepted : SourceCompileAccepted program :=
    RecursiveBridgeCompileResources.to_sourceCompileAccepted hSourceAccepted
      hResources.2
  have hCode :
      (canonicalEntryState initial).executionEnv.code =
        Assembly.Bytecode.encodeTarget target := by
    simpa [canonicalEntryState] using hInitialCodeImageRel.targetCode
  obtain
    ⟨sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, hRunsAbove⟩ :=
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_sufficientGas_X
      (RecursiveBridgeTopNoCallSourceCompileAssumptions.withCanonicalObservation
        hSourceAccepted hSourceCompileAccepted
        (RecursiveBridgeSemanticCoreContracts.ofBoundaries
          RecursiveBridgePrimitiveArityContracts.structured
          (RecursiveBridgeTerminalContracts.structured_of_observation
            (RecursiveBridgeTerminalObservationContracts.canonical cfg program))
          hExprNoSuccessfulOutOfFuel.to_resultContracts)
        (RecursiveBridgeInitialWorldRel.to_canonicalEntryState
          hInitialCodeImageRel.world)
        hRun hBytecode.1 hBytecode.2.1 hBytecode.2.2
        (Assembly.OutOfGasPolicyAssumption.trivial (program := asm)
          (initial := canonicalEntryState initial))
        (Assembly.CurrentContractProjectionAssumption.trivial (program := asm)
          (initial := canonicalEntryState initial))
        (canonicalEntryState_pc initial) (canonicalEntryState_stack initial))
      hCode hTargetNonGasChecks hTargetDoneContinuation
  exact
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hAccepted, hBytes, hEncoding,
      hOutOfGas, hProjection, hTrace, hGasEq, hRunsAbove⟩

/--
No-out-of-gas projection of the preferred trace-local sufficient-gas theorem.

This companion keeps the audit-facing no-out-of-gas root on the same
non-oracle gas boundary as the result theorem: for every UInt256 gas value at
or above the checked gasless trace budget, there is an `EVM.X` fuel value whose
run is not an out-of-gas error.
-/
theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetDoneContinuation :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel
          (canonicalEntryState initial) targetOutcome →
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation
          (Assembly.GasAware.validJumps target) targetOutcome) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, _hAccepted, _hBytes, _hEncoding,
      _hOutOfGas, _hProjection, hTrace, hGasEq, hRunsAbove⟩ :=
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hTargetTraceChecks hTargetDoneContinuation
  refine
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hTrace, hGasEq, ?_⟩
  intro gas hGasAtLeast hGasFits
  obtain ⟨evmFuel, result, hXRun, _hAgrees⟩ :=
    hRunsAbove gas hGasAtLeast hGasFits
  refine ⟨evmFuel, ?_⟩
  rw [hXRun]
  intro hImpossible
  cases hImpossible

/--
No-out-of-gas projection with the running-result continuation exposed as the
fallthrough-STOP observation condition.
-/
theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_fallthrough_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  refine
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hTargetTraceChecks ?_
  intro targetFuel targetOutcome hTrace
  cases targetOutcome with
  | running targetState =>
      exact
        Assembly.GasAware.XStepTrace.XTraceDoneContinuation.running_of_fallthrough_stop
          (hTargetFallthrough hTrace)
  | halted halt =>
      exact Assembly.GasAware.XStepTrace.XTraceDoneContinuation.halted

/--
No-out-of-gas projection for the stricter no-`RETURNDATACOPY` checked
boundary.
-/
theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_fallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  exact
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_fallthrough_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_eq_some
        hCheckedCompileTarget).1
      hTargetTraceChecks hTargetFallthrough

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_fallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceCoreChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceCoreChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  exact
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceChecks_fallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.XBlockTraceChecksReadyFor.of_trace_core_noReturnDataCopy_noCallCreate
          (hTargetTraceCoreChecks hTrace)
          (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoReturnDataCopy
            hCheckedCompileTarget)
          (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
            hCheckedCompileTarget))
      hTargetFallthrough

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceCoreChecks :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.XBlockTraceCoreChecksReadyFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  exact
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_fallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hTargetTraceCoreChecks
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady.of_clean
          (hTargetFallthrough hTrace))

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_coreTrace_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetCoreTrace :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor
          (Assembly.GasAware.validJumps target) hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  exact
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.to_trace_core_checks
          (hTargetCoreTrace hTrace)
          (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
            hCheckedCompileTarget))
      hTargetFallthrough

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_instrCoreReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetInstrCoreReady :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreReady asm target)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  exact
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_coreTrace_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_instrCoreReady
          hCheckedCompileTarget hTargetInstrCoreReady hTrace)
      hTargetFallthrough

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceInstrCoreReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceInstrCoreReady :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.InstrCoreBlockTraceReadyFor target
          hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  exact
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_coreTrace_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_coreTrace_of_traceInstrCoreReady
          hCheckedCompileTarget (hTargetTraceInstrCoreReady hTrace))
      hTargetFallthrough

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceInputsReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetTraceInputsReady :
      ∀ {targetFuel targetOutcome}
        (hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) targetOutcome),
        Assembly.GasAware.XStepTrace.InstrCoreBlockTraceInputsReadyFor target
          hTrace)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  exact
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceInstrCoreReady_cleanFallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.InstrCoreBlockTraceReadyFor.of_inputs_ready
          (hTargetTraceInputsReady hTrace))
      hTargetFallthrough

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_instrCoreInputsReady_cleanFallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetInstrCoreInputsReady :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreInputsReady asm target)
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopCleanReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceInputsReady_cleanFallthrough_noReturnDataCopy_X
    hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
    hCheckedCompileTarget
    (fun hTrace =>
      Assembly.GasAware.XStepTrace.InstrCoreBlockTraceInputsReadyFor.of_block_instr_inputs_ready
        hTrace hTargetInstrCoreInputsReady)
    hTargetFallthrough

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_instrCoreResources_finalization_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprResultContracts : RecursiveBridgeExprResultContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetInstrCoreResources :
      Assembly.GasAware.XStepTrace.XBlockInstrCoreInputResources asm target)
    (hTargetFinalization :
      Assembly.GasAware.XStepTrace.XBlockTraceFinalizationReady
        (Assembly.GasAware.validJumps target) asm target
        (canonicalEntryState initial)) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, _hAccepted, _hBytes, _hEncoding,
      _hOutOfGas, _hProjection, hTrace, hGasEq, hRunsAbove⟩ :=
    compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_stepTrace_instrCoreResources_finalization_noReturnDataCopy_X
      hExprResultContracts hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hTargetInstrCoreResources hTargetFinalization
  refine
    ⟨sourceFuel, sourceOutcome, targetFuel, targetOutcome, gasBound,
      hSourceRun, hOutcome, hWholeRel, hTrace, hGasEq, ?_⟩
  intro gas hGasAtLeast hGasFits
  obtain ⟨evmFuel, result, _hTraceX, hXRun, _hAgrees⟩ :=
    hRunsAbove gas hGasAtLeast hGasFits
  exact
    ⟨evmFuel, by
      rw [hXRun]
      intro hImpossible
      cases hImpossible⟩

theorem compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_core_fallthrough_noReturnDataCopy_X
    {cfg : Reference.StateRelConfig}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hExprNoSuccessfulOutOfFuel : RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      RecursiveBridgeInitialCodeImageRel cfg program target shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCheckedCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?
          program =
        some (asm, target))
    (hTargetCoreChecks :
      Assembly.GasAware.XStepTrace.XBlockReplayCoreNonGasReady asm target
        (Assembly.GasAware.validJumps target))
    (hTargetFallthrough :
      ∀ {targetFuel targetState}
        (_hTrace :
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (canonicalEntryState initial) (.running targetState)),
        Assembly.GasAware.XStepTrace.XFallthroughStopContinuationReady
          targetState) :
    ∃ sourceFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
      gasBound =
        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
          (canonicalEntryState initial) targetOutcome ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          ∃ evmFuel,
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  exact
    compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_traceCoreChecks_fallthrough_noReturnDataCopy_X
      hExprNoSuccessfulOutOfFuel hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget
      (fun hTrace =>
        Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.to_trace_core_checks
          (Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor.of_block_replay_core
            hTrace hTargetCoreChecks)
          (compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?_blockReplayNoCallCreate
            hCheckedCompileTarget))
      hTargetFallthrough

end Program
end Yul
end EvmCompiler
