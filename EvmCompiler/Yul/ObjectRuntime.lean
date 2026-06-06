import EvmCompiler.Yul.ObjectPreservation
import EvmCompiler.Yul.RecursiveBridgeSupport

namespace EvmCompiler
namespace Yul
namespace ObjectModel
namespace Program

theorem exists_recursiveBridgeSourceRun_of_sourceRun_succ_ok
    {program : Program} {sourceFuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {referenceResult : Reference.Result}
    (hInitialCodeBytes :
      bytecodeImage? program = some shared.executionEnv.codeBytes)
    (hRun :
      Source.Program.sourceRun? sourceFuel.succ program (.Ok shared store) =
        some (.ok referenceResult))
    (hNoOutOfFuel : referenceResult ≠ .regular .OutOfFuel) :
    ∃ core : Yul.Program,
      toRootCoreProgram? program = some core ∧
        Yul.Program.RecursiveBridgeSourceRun core shared store sourceFuel
          referenceResult := by
  rcases
      exists_coreRun_of_sourceRun?_ok_initial_codeBytes
        hInitialCodeBytes hRun with
    ⟨core, hCore, hCoreRun⟩
  refine ⟨core, hCore, ?_⟩
  exact
    { run := by
        simpa [Reference.runResult_eq_program_run] using hCoreRun
      noOutOfFuel := hNoOutOfFuel }

theorem exists_recursiveBridgeSourceRun_of_sourceRunWithCodeImage_succ_ok
    {program : Program} {sourceFuel : Nat} {codeImage : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {referenceResult : Reference.Result}
    (hInitialCodeBytes : shared.executionEnv.codeBytes = codeImage)
    (hRun :
      Source.Program.sourceRunWithCodeImage? sourceFuel.succ program codeImage
          (.Ok shared store) =
        some (.ok referenceResult))
    (hNoOutOfFuel : referenceResult ≠ .regular .OutOfFuel) :
    ∃ core : Yul.Program,
      toRootCoreProgram? program = some core ∧
        Yul.Program.RecursiveBridgeSourceRun core shared store sourceFuel
          referenceResult := by
  rcases
      exists_coreRun_of_sourceRunWithCodeImage?_ok_initial_codeBytes
        hInitialCodeBytes hRun with
    ⟨core, hCore, hCoreRun⟩
  refine ⟨core, hCore, ?_⟩
  exact
    { run := by
        simpa [Reference.runResult_eq_program_run] using hCoreRun
      noOutOfFuel := hNoOutOfFuel }

theorem exists_recursiveBridgeSourceRun_of_sourceRunWithCodeSuffix_succ_ok
    {program : Program} {sourceFuel : Nat} {suffix : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {referenceResult : Reference.Result}
    (hInitialCodeBytes :
      ∃ image : ByteArray,
        bytecodeImage? program = some image ∧
          shared.executionEnv.codeBytes = image ++ suffix)
    (hRun :
      Source.Program.sourceRunWithCodeSuffix? sourceFuel.succ program suffix
          (.Ok shared store) =
        some (.ok referenceResult))
    (hNoOutOfFuel : referenceResult ≠ .regular .OutOfFuel) :
    ∃ core : Yul.Program,
      toRootCoreProgram? program = some core ∧
        Yul.Program.RecursiveBridgeSourceRun core shared store sourceFuel
          referenceResult := by
  rcases
      exists_coreRun_of_sourceRunWithCodeSuffix?_ok_initial_codeBytes
        hInitialCodeBytes hRun with
    ⟨core, hCore, hCoreRun⟩
  refine ⟨core, hCore, ?_⟩
  exact
    { run := by
        simpa [Reference.runResult_eq_program_run] using hCoreRun
      noOutOfFuel := hNoOutOfFuel }

structure RecursiveBridgeObjectTopAssumptions
    (cfg : Reference.StateRelConfig)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (outcomeRel : Reference.OutcomeRel)
    (objectProgram : Program)
    (core : Yul.Program)
    (asm : Assembly.Program) (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (sourceFuel : Nat)
    (initial : EVMState)
    (referenceResult : Reference.Result) : Prop where
  coreProgram : toRootCoreProgram? objectProgram = some core
  initialCodeBytes :
    bytecodeImage? objectProgram = some shared.executionEnv.codeBytes
  sourceAccepted : Yul.Program.RecursiveBridgeSourceAccepted core
  compileResources : Yul.Program.RecursiveBridgeCompileResources core
  semantics :
    Yul.Program.RecursiveBridgeSemanticContracts cfg terminalRel revertRel
      prim outcomeRel core shared store
  initialShared :
    Reference.SharedStateRel cfg
      { shared with
        executionEnv :=
          { shared.executionEnv with code := core.contract } }
      initial.toSharedState
  objectSourceRun :
    Source.Program.sourceRun? sourceFuel.succ objectProgram
        (.Ok shared store) =
      some (.ok referenceResult)
  noOutOfFuel : referenceResult ≠ .regular .OutOfFuel
  compileTarget :
    Yul.Program.compileCheckedAssemblyTarget? core = some (asm, target)
  targetRuntime :
    Yul.Program.RecursiveBridgeTargetRuntime asm target initial

namespace RecursiveBridgeObjectTopAssumptions

theorem to_coreTopAssumptions
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectTopAssumptions cfg terminalRel revertRel prim
        outcomeRel objectProgram core asm target shared store sourceFuel
        initial referenceResult) :
    Yul.Program.RecursiveBridgeTopAssumptions cfg terminalRel revertRel prim
      outcomeRel core asm target shared store sourceFuel initial
      referenceResult := by
  rcases
      exists_coreRun_of_sourceRun?_ok_initial_codeBytes
        hTop.initialCodeBytes hTop.objectSourceRun with
    ⟨core', hCore', hCoreRun⟩
  have hEq : core' = core := by
    rw [hTop.coreProgram] at hCore'
    injection hCore' with hEq
    exact hEq.symm
  subst core'
  exact
    { sourceAccepted := hTop.sourceAccepted
      compileResources := hTop.compileResources
      semantics := hTop.semantics
      initialShared := hTop.initialShared
      sourceRun :=
        { run := by
            simpa [Reference.runResult_eq_program_run] using hCoreRun
          noOutOfFuel := hTop.noOutOfFuel }
      compileTarget := hTop.compileTarget
      targetRuntime := hTop.targetRuntime }

end RecursiveBridgeObjectTopAssumptions

theorem compile_whole_program_result_sound_of_recursiveBridgeObjectTopAssumptions
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectTopAssumptions cfg terminalRel revertRel prim
        outcomeRel objectProgram core asm target shared store sourceFuel
        initial referenceResult) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome,
      Source.Program.sourceRun? sourceFuel.succ objectProgram
          (.Ok shared store) =
        some (.ok referenceResult) ∧
      Reference.runResult sourceFuel.succ core (.Ok shared store) =
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
                    asm target targetFuel initial targetOutcome := by
  rcases
      Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
        (RecursiveBridgeObjectTopAssumptions.to_coreTopAssumptions hTop) with
    ⟨sourceOutcome, targetFuel, targetOutcome, hRun, hOutcome, hWhole,
      hAsm, hBytes, hEncoding, hGas, hProjection, hTarget⟩
  exact
    ⟨sourceOutcome, targetFuel, targetOutcome, hTop.objectSourceRun, hRun,
      hOutcome, hWhole, hAsm, hBytes, hEncoding, hGas, hProjection, hTarget⟩

structure RecursiveBridgeObjectCodeImageTopAssumptions
    (cfg : Reference.StateRelConfig)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (outcomeRel : Reference.OutcomeRel)
    (objectProgram : Program)
    (core : Yul.Program)
    (asm : Assembly.Program) (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (sourceFuel : Nat)
    (initial : EVMState)
    (codeImage : ByteArray)
    (referenceResult : Reference.Result) : Prop where
  coreProgram : toRootCoreProgram? objectProgram = some core
  initialCodeBytes : shared.executionEnv.codeBytes = codeImage
  sourceAccepted : Yul.Program.RecursiveBridgeSourceAccepted core
  compileResources : Yul.Program.RecursiveBridgeCompileResources core
  semantics :
    Yul.Program.RecursiveBridgeSemanticContracts cfg terminalRel revertRel
      prim outcomeRel core shared store
  initialShared :
    Reference.SharedStateRel cfg
      { shared with
        executionEnv :=
          { shared.executionEnv with code := core.contract } }
      initial.toSharedState
  objectSourceRun :
    Source.Program.sourceRunWithCodeImage? sourceFuel.succ objectProgram
        codeImage (.Ok shared store) =
      some (.ok referenceResult)
  noOutOfFuel : referenceResult ≠ .regular .OutOfFuel
  compileTarget :
    Yul.Program.compileCheckedAssemblyTarget? core = some (asm, target)
  targetRuntime :
    Yul.Program.RecursiveBridgeTargetRuntime asm target initial

namespace RecursiveBridgeObjectCodeImageTopAssumptions

theorem to_coreTopAssumptions
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {codeImage : ByteArray}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectCodeImageTopAssumptions cfg terminalRel revertRel
        prim outcomeRel objectProgram core asm target shared store
        sourceFuel initial codeImage referenceResult) :
    Yul.Program.RecursiveBridgeTopAssumptions cfg terminalRel revertRel prim
      outcomeRel core asm target shared store sourceFuel initial
      referenceResult := by
  rcases
      exists_coreRun_of_sourceRunWithCodeImage?_ok_initial_codeBytes
        hTop.initialCodeBytes hTop.objectSourceRun with
    ⟨core', hCore', hCoreRun⟩
  have hEq : core' = core := by
    rw [hTop.coreProgram] at hCore'
    injection hCore' with hEq
    exact hEq.symm
  subst core'
  exact
    { sourceAccepted := hTop.sourceAccepted
      compileResources := hTop.compileResources
      semantics := hTop.semantics
      initialShared := hTop.initialShared
      sourceRun :=
        { run := by
            simpa [Reference.runResult_eq_program_run] using hCoreRun
          noOutOfFuel := hTop.noOutOfFuel }
      compileTarget := hTop.compileTarget
      targetRuntime := hTop.targetRuntime }

end RecursiveBridgeObjectCodeImageTopAssumptions

theorem compile_whole_program_result_sound_of_recursiveBridgeObjectCodeImageTopAssumptions
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {codeImage : ByteArray}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectCodeImageTopAssumptions cfg terminalRel revertRel
        prim outcomeRel objectProgram core asm target shared store sourceFuel
        initial codeImage referenceResult) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome,
      Source.Program.sourceRunWithCodeImage? sourceFuel.succ objectProgram
          codeImage (.Ok shared store) =
        some (.ok referenceResult) ∧
      Reference.runResult sourceFuel.succ core (.Ok shared store) =
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
                    asm target targetFuel initial targetOutcome := by
  rcases
      Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
        (RecursiveBridgeObjectCodeImageTopAssumptions.to_coreTopAssumptions
          hTop) with
    ⟨sourceOutcome, targetFuel, targetOutcome, hRun, hOutcome, hWhole,
      hAsm, hBytes, hEncoding, hGas, hProjection, hTarget⟩
  exact
    ⟨sourceOutcome, targetFuel, targetOutcome, hTop.objectSourceRun, hRun,
      hOutcome, hWhole, hAsm, hBytes, hEncoding, hGas, hProjection, hTarget⟩

structure RecursiveBridgeObjectSuffixTopAssumptions
    (cfg : Reference.StateRelConfig)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop)
    (revertRel : Reference.State → Objects.Source.State → Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (outcomeRel : Reference.OutcomeRel)
    (objectProgram : Program)
    (core : Yul.Program)
    (asm : Assembly.Program) (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (sourceFuel : Nat)
    (initial : EVMState)
    (suffix : ByteArray)
    (referenceResult : Reference.Result) : Prop where
  coreProgram : toRootCoreProgram? objectProgram = some core
  initialCodeBytes :
    ∃ image : ByteArray,
      bytecodeImage? objectProgram = some image ∧
        shared.executionEnv.codeBytes = image ++ suffix
  sourceAccepted : Yul.Program.RecursiveBridgeSourceAccepted core
  compileResources : Yul.Program.RecursiveBridgeCompileResources core
  semantics :
    Yul.Program.RecursiveBridgeSemanticContracts cfg terminalRel revertRel
      prim outcomeRel core shared store
  initialShared :
    Reference.SharedStateRel cfg
      { shared with
        executionEnv :=
          { shared.executionEnv with code := core.contract } }
      initial.toSharedState
  objectSourceRun :
    Source.Program.sourceRunWithCodeSuffix? sourceFuel.succ objectProgram
        suffix (.Ok shared store) =
      some (.ok referenceResult)
  noOutOfFuel : referenceResult ≠ .regular .OutOfFuel
  compileTarget :
    Yul.Program.compileCheckedAssemblyTarget? core = some (asm, target)
  targetRuntime :
    Yul.Program.RecursiveBridgeTargetRuntime asm target initial

namespace RecursiveBridgeObjectSuffixTopAssumptions

theorem to_coreTopAssumptions
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {suffix : ByteArray}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectSuffixTopAssumptions cfg terminalRel revertRel
        prim outcomeRel objectProgram core asm target shared store
        sourceFuel initial suffix referenceResult) :
    Yul.Program.RecursiveBridgeTopAssumptions cfg terminalRel revertRel prim
      outcomeRel core asm target shared store sourceFuel initial
      referenceResult := by
  rcases
      exists_coreRun_of_sourceRunWithCodeSuffix?_ok_initial_codeBytes
        hTop.initialCodeBytes hTop.objectSourceRun with
    ⟨core', hCore', hCoreRun⟩
  have hEq : core' = core := by
    rw [hTop.coreProgram] at hCore'
    injection hCore' with hEq
    exact hEq.symm
  subst core'
  exact
    { sourceAccepted := hTop.sourceAccepted
      compileResources := hTop.compileResources
      semantics := hTop.semantics
      initialShared := hTop.initialShared
      sourceRun :=
        { run := by
            simpa [Reference.runResult_eq_program_run] using hCoreRun
          noOutOfFuel := hTop.noOutOfFuel }
      compileTarget := hTop.compileTarget
      targetRuntime := hTop.targetRuntime }

end RecursiveBridgeObjectSuffixTopAssumptions

theorem compile_whole_program_result_sound_of_recursiveBridgeObjectSuffixTopAssumptions
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {suffix : ByteArray}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectSuffixTopAssumptions cfg terminalRel revertRel prim
        outcomeRel objectProgram core asm target shared store sourceFuel
        initial suffix referenceResult) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome,
      Source.Program.sourceRunWithCodeSuffix? sourceFuel.succ objectProgram
          suffix (.Ok shared store) =
        some (.ok referenceResult) ∧
      Reference.runResult sourceFuel.succ core (.Ok shared store) =
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
                    asm target targetFuel initial targetOutcome := by
  rcases
      Yul.Program.compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
        (RecursiveBridgeObjectSuffixTopAssumptions.to_coreTopAssumptions
          hTop) with
    ⟨sourceOutcome, targetFuel, targetOutcome, hRun, hOutcome, hWhole,
      hAsm, hBytes, hEncoding, hGas, hProjection, hTarget⟩
  exact
    ⟨sourceOutcome, targetFuel, targetOutcome, hTop.objectSourceRun, hRun,
      hOutcome, hWhole, hAsm, hBytes, hEncoding, hGas, hProjection, hTarget⟩

abbrev CanonicalOutcomeRel
    (cfg : Reference.StateRelConfig)
    (core : Yul.Program)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) : Reference.OutcomeRel :=
  Yul.Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
    (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
      cfg)
    (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
      cfg)
    core (.Ok shared store)

theorem compile_whole_program_result_sound_of_recursiveBridgeObjectTopAssumptions_canonical
    {cfg : Reference.StateRelConfig}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectTopAssumptions cfg
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          cfg)
        Locals.Source.PrimitiveSemantics.structured
        (CanonicalOutcomeRel cfg core shared store)
        objectProgram core asm target shared store sourceFuel initial
        referenceResult) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome,
      Source.Program.sourceRun? sourceFuel.succ objectProgram
          (.Ok shared store) =
        some (.ok referenceResult) ∧
      Reference.runResult sourceFuel.succ core (.Ok shared store) =
        .ok referenceResult ∧
      CanonicalOutcomeRel cfg core shared store referenceResult
        sourceOutcome ∧
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
  compile_whole_program_result_sound_of_recursiveBridgeObjectTopAssumptions hTop

theorem compile_whole_program_result_sound_of_recursiveBridgeObjectCodeImageTopAssumptions_canonical
    {cfg : Reference.StateRelConfig}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {codeImage : ByteArray}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectCodeImageTopAssumptions cfg
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          cfg)
        Locals.Source.PrimitiveSemantics.structured
        (CanonicalOutcomeRel cfg core shared store)
        objectProgram core asm target shared store sourceFuel initial codeImage
        referenceResult) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome,
      Source.Program.sourceRunWithCodeImage? sourceFuel.succ objectProgram
          codeImage (.Ok shared store) =
        some (.ok referenceResult) ∧
      Reference.runResult sourceFuel.succ core (.Ok shared store) =
        .ok referenceResult ∧
      CanonicalOutcomeRel cfg core shared store referenceResult
        sourceOutcome ∧
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
  compile_whole_program_result_sound_of_recursiveBridgeObjectCodeImageTopAssumptions
    hTop

theorem compile_whole_program_result_sound_of_recursiveBridgeObjectSuffixTopAssumptions_canonical
    {cfg : Reference.StateRelConfig}
    {objectProgram : Program}
    {core : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat}
    {initial : EVMState}
    {suffix : ByteArray}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeObjectSuffixTopAssumptions cfg
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          cfg)
        Locals.Source.PrimitiveSemantics.structured
        (CanonicalOutcomeRel cfg core shared store)
        objectProgram core asm target shared store sourceFuel initial suffix
        referenceResult) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome,
      Source.Program.sourceRunWithCodeSuffix? sourceFuel.succ objectProgram
          suffix (.Ok shared store) =
        some (.ok referenceResult) ∧
      Reference.runResult sourceFuel.succ core (.Ok shared store) =
        .ok referenceResult ∧
      CanonicalOutcomeRel cfg core shared store referenceResult
        sourceOutcome ∧
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
  compile_whole_program_result_sound_of_recursiveBridgeObjectSuffixTopAssumptions
    hTop

end Program
end ObjectModel
end Yul
end EvmCompiler
