import EvmCompiler.Yul.NoCallRuntime
import EvmCompiler.Functions.LiveLayout
import EvmCompiler.Functions.LiveLayoutBridge
import EvmCompiler.Functions.LiveLayoutPreservation

/-!
Current public theorem spine.

This module intentionally exposes only the preferred public imported-Yul to
gas-aware EVM theorem roots. Solidity and object/Yul-object interfaces live in
their own modules; this audit file should not keep stale theorem routes alive.
-/

namespace EvmCompiler
namespace LayerAudit
namespace ImportedYulBoundary

abbrev recursiveBridgeTopToGasAwareEVM :=
  @Yul.Program.compile_whole_program_result_sound_of_liveNoInternalCallChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_stepTrace_executableAssemblyInferredBoundStackSafeCompile_initialPerm_noReturnDataCopy_X

abbrev recursiveBridgeTopToGasAwareEVMNoOutOfGas :=
  @Yul.Program.compile_whole_program_result_no_out_of_gas_of_liveNoInternalCallChecked_canonicalObservation_codeImage_existsSourceFuel_sufficientGas_executableAssemblyInferredBoundStackSafeCompile_initialPerm_noReturnDataCopy_X

namespace PublicSpineRegression

noncomputable section

/-!
These examples are public-spine tripwires. They type-check only if the exported
roots consume the live no-internal-CALL checked compile gate plus inferred
assembly stack-bound check. Repointing `LayerAudit` at an older root that uses
the stale checked-compile path, or accepts only a caller-supplied
stack/headroom witness, makes these applications fail.
-/

abbrev SoundConclusion
    (cfg : Yul.Reference.StateRelConfig)
    (program : Yul.Program)
    (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (initial : Yul.EVMState)
    (referenceResult : Yul.Reference.Result) : Prop :=
  ∃ sourceFuel : Nat,
  ∃ sourceOutcome : Objects.Source.Outcome,
  ∃ targetFuel targetOutcome gasBound,
    Yul.Reference.runResult sourceFuel.succ program
        (EvmYul.Yul.State.Ok shared store) =
      Except.ok referenceResult ∧
      Yul.Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
          (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            cfg)
          (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
            cfg)
          program (EvmYul.Yul.State.Ok shared store) referenceResult
          sourceOutcome ∧
        Yul.SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
          Assembly.Accepted asm ∧
            Assembly.Bytecode.compileBytes? asm =
              some (Assembly.Bytecode.encodeTarget target) ∧
              Assembly.Bytecode.EncodingCorrect target
                (Assembly.Bytecode.encodeTarget target) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (Yul.Program.canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (Yul.Program.canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult asm target
                      targetFuel (Yul.Program.canonicalEntryState initial)
                      targetOutcome ∧
                      gasBound =
                        Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm
                          targetFuel (Yul.Program.canonicalEntryState initial)
                          targetOutcome ∧
                        ∀ gas,
                          gasBound ≤ gas →
                            gas < EvmYul.UInt256.size →
                              ∃ evmFuel result,
                                Assembly.GasAware.XStepTrace
                                    (Assembly.GasAware.validJumps target)
                                    evmFuel
                                    (Assembly.GasAware.installCodeAndGas target
                                      gas
                                      (Yul.Program.canonicalEntryState initial))
                                    result ∧
                                  EvmYul.EVM.X evmFuel
                                      (Assembly.GasAware.validJumps target)
                                      (Assembly.GasAware.installCodeAndGas
                                        target gas
                                        (Yul.Program.canonicalEntryState
                                          initial)) =
                                    Except.ok result ∧
                                    Assembly.GasAware.XResultAgrees
                                      targetOutcome result

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCheckedCompileTarget :
      Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target))
    (hInitialPerm : initial.executionEnv.perm = true) :
    SoundConclusion cfg program asm target shared store initial
      referenceResult :=
  recursiveBridgeTopToGasAwareEVM hExprNoSuccessfulOutOfFuel
    hInitialCodeImageRel hSourceFuelRun hCheckedCompileTarget hInitialPerm

abbrev NoOutOfGasConclusion
    (cfg : Yul.Reference.StateRelConfig)
    (program : Yul.Program)
    (asm : Assembly.Program)
    (target : Assembly.TargetProgram)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (initial : Yul.EVMState)
    (referenceResult : Yul.Reference.Result) : Prop :=
  ∃ sourceFuel : Nat,
  ∃ sourceOutcome : Objects.Source.Outcome,
  ∃ targetFuel targetOutcome gasBound,
    Yul.Reference.runResult sourceFuel.succ program
        (EvmYul.Yul.State.Ok shared store) =
      Except.ok referenceResult ∧
      Yul.Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
          (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            cfg)
          (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
            cfg)
          program (EvmYul.Yul.State.Ok shared store) referenceResult
          sourceOutcome ∧
        Yul.SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
          Assembly.Preservation.BlockTraceResult asm target targetFuel
            (Yul.Program.canonicalEntryState initial) targetOutcome ∧
            gasBound =
              Assembly.GasAware.XStepTrace.XBlockTraceGasBudget asm targetFuel
                (Yul.Program.canonicalEntryState initial) targetOutcome ∧
              ∀ gas,
                gasBound ≤ gas →
                  gas < EvmYul.UInt256.size →
                    ∃ evmFuel,
                      EvmYul.EVM.X evmFuel
                          (Assembly.GasAware.validJumps target)
                          (Assembly.GasAware.installCodeAndGas target gas
                            (Yul.Program.canonicalEntryState initial)) ≠
                        Except.error
                          EvmYul.EVM.ExecutionException.OutOfGass

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCheckedCompileTarget :
      Yul.Program.compileLiveNoInternalCallCheckedAssemblyTargetBytecodeFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target))
    (hInitialPerm : initial.executionEnv.perm = true) :
    NoOutOfGasConclusion cfg program asm target shared store initial
      referenceResult :=
  recursiveBridgeTopToGasAwareEVMNoOutOfGas hExprNoSuccessfulOutOfFuel
    hInitialCodeImageRel hSourceFuelRun hCheckedCompileTarget hInitialPerm

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    Yul.Program.RecursiveBridgeSourceFrameWordSumResourceBound program :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_sourceFrameWordSumResourceBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    _root_.EvmCompiler.Structured.StackResource.AssemblyBounds.inferProgramBoundCheckResult?
        asm 17 1024 =
      some
        (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_assemblyBoundCheck
          hCheckedCompileTarget) :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordSumStackSafeNoReturnDataCopy?_assemblyBoundCheck_checked
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    Functions.CallDepth.Ranked.SourceRecurrenceBound
      (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceRecurrenceCheck
        hCheckedCompileTarget).lowerObj.toFunctions
      (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceRecurrenceCheck
        hCheckedCompileTarget).maxFrames :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceRecurrenceBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    ∃ depth,
      Yul.Program.recursiveBridgeSourceResourceDepth? program = some depth ∧
        Yul.Program.RecursiveBridgeSourceResourceBound program depth :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceResourceBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    ∃ checked :
      Yul.Program.ExecutableStackSafeNoReturnDataCopyCheckedCompile program,
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableStackSafeNoReturnDataCopyFull?
          program =
        some checked ∧
        checked.asm = asm ∧ checked.target = target :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableStackSafeNoReturnDataCopy?_eq_some_full
    (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_executableBase
      hCheckedCompileTarget)

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    ∃ checked :
      Yul.Program.ExecutableAssemblyInferredBoundStackSafeNoReturnDataCopyCheckedCompile
        program,
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopyFull?
          program =
        some checked ∧
        checked.asm = asm ∧ checked.target = target :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_eq_some_full
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    _root_.EvmCompiler.Structured.StackResource.AssemblyBounds.inferProgramBoundCheckResult?
        (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked
          hCheckedCompileTarget).asm 17 1024 =
      some
        (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked
          hCheckedCompileTarget).assemblyBound :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked_assemblyBound_checked
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    Yul.Program.recursiveBridgeSourceResourceDepth? program =
        some
          (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked
            hCheckedCompileTarget).sourceDepth ∧
      Yul.Program.RecursiveBridgeSourceResourceBound program
        (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked
          hCheckedCompileTarget).sourceDepth :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked_sourceResourceBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {initial : Yul.EVMState}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint
      (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked_sourceResourceBound
        hCheckedCompileTarget).2
      (Yul.Program.canonicalEntryState initial) :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.initial
    (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked_sourceResourceBound
      hCheckedCompileTarget).2
    initial

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {active layout : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Functions.Source.State}
    {baseState baseState' : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    (hBase :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions active layout hiddenReturns source
        baseState)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames active)
    (hRel :
      Functions.SourceDirect.StateRel layout hiddenReturns source'
        baseState')
    (hFrameRel :
      Structured.Preservation.Frame.StateRel baseState' state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.of_base_withStateRel
    hBase hActive hRel hFrameRel

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {active layout layout' returns : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Functions.Source.State}
    {baseState target' : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    (hBase :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions active layout hiddenReturns source
        baseState)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames active)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      Functions.SourceDirect.BlockScopedOutcomeRel returns layout'
        hiddenReturns
        (Functions.Source.Outcome.regular source')
        (Structured.Outcome.regular target'))
    (hFrameRel :
      Structured.Preservation.Frame.StateRel target' state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.of_regularBlockScopedOutcomeRel
    hBase hActive hLayout' hRel hFrameRel

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {active layout returns : List Yul.Name} {retc : Nat}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Functions.Source.State}
    {baseState target' : Structured.RunState}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    (hBase :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions active layout hiddenReturns source
        baseState)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames active)
    (hLayout' : targetCtx.layout.length ≤ 16)
    (hRel :
      Functions.SourceDirect.BlockOpenResultRel retc returns hiddenReturns
        (Functions.Source.Outcome.regular source', sourceCtx)
        (Structured.Outcome.regular target', targetCtx))
    (hFrameRel :
      Structured.Preservation.Frame.StateRel target' state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.of_regularBlockOpenResultRel
    hBase hActive hLayout' hRel hFrameRel

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {callerLayout : List Yul.Name}
    {callerSource calleeSource : Functions.Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    {callee : Yul.Name} {calleeFn : Functions.FunDef} {retc : Nat}
    (hCaller :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions [] callerLayout [] callerSource
        callerTarget)
    (hRoot :
      callee ∈
        Functions.CallDepth.Program.mainInternalCalls
          hResource.lowerObj.toFunctions)
    (hCalleeFind :
      Functions.FunList.find? callee
          hResource.lowerObj.toFunctions.functions =
        some calleeFn)
    (hCalleeBound :
      Functions.SourceDirect.FrameBound.FunDef calleeFn)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames [callee])
    (hRel :
      Functions.SourceDirect.StateRel
        (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel calleeTarget state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.rootCallBodyTargetCtx
    hCaller hRoot hCalleeFind hCalleeBound hActive hRel hFrameRel

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {active callerLayout : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Functions.Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    {caller callee : Yul.Name} {callerFn calleeFn : Functions.FunDef}
    {retc : Nat}
    (hCallerContext :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions active callerLayout hiddenReturns
        callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      Functions.FunList.find? caller
          hResource.lowerObj.toFunctions.functions =
        some callerFn)
    (hCall :
      callee ∈ Functions.CallDepth.FunDef.internalCalls callerFn)
    (hCalleeFind :
      Functions.FunList.find? callee
          hResource.lowerObj.toFunctions.functions =
        some calleeFn)
    (hCalleeBound :
      Functions.SourceDirect.FrameBound.FunDef calleeFn)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames (active ++ [callee]))
    (hRel :
      Functions.SourceDirect.StateRel
        (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel calleeTarget state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.callBodyTargetCtx
    hCallerContext hCaller hCallerFind hCall hCalleeFind hCalleeBound hActive
    hRel hFrameRel

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hCompile : Assembly.compile? asm = some target)
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target))
    (hPoints :
      Yul.Program.RecursiveBridgeActualSourceRunActiveResourcePoints cfg
        program asm target
        (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked_sourceResourceBound
          hCheckedCompileTarget).2
        shared store initial referenceResult) :
    Yul.Program.RecursiveBridgeActualSourceRunFrameStackHeadroom cfg program
      asm target shared store initial referenceResult :=
  Yul.Program.RecursiveBridgeActualSourceRunActiveResourcePoints.toFrameStackHeadroom
    hCompile hPoints

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    Yul.Program.recursiveBridgeSourceResourceDepth? program =
        some
          (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked
            hCheckedCompileTarget).sourceDepth ∧
      Yul.Program.RecursiveBridgeSourceActiveDepthBound program
        (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked
          hCheckedCompileTarget).sourceDepth :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked_sourceActiveDepthBound
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {check : Yul.Program.RecursiveBridgeExecutableSCCRecurrenceCheckResult
      program}
    (hCheck :
      Yul.Program.recursiveBridgeExecutableSCCRecurrenceCheckResult?
          program =
        some check) :
    Functions.CallDepth.Ranked.SourceRecurrenceBound
      check.lowerObj.toFunctions check.maxFrames :=
  let _hChecked :=
      Yul.Program.recursiveBridgeExecutableSCCRecurrenceCheckResult?_eq_some
        hCheck
  check.sourceRecurrenceBound

example
    {program : Yul.Program}
    {check : Yul.Program.RecursiveBridgeExecutableSCCRecurrenceCheckResult
      program}
    (hCheck :
      Yul.Program.recursiveBridgeExecutableSCCRecurrenceCheckResult?
          program =
        some check)
    {frame : Functions.CallDepth.Ranked.GuardedZeroCalls.SourceCallFrame}
    {depth : Nat}
    (hRoot :
      Functions.CallDepth.Ranked.GuardedZeroCalls.GuardedSemanticRootFrame
        check.lowerObj.toFunctions frame)
    (hChain :
      Functions.CallDepth.Ranked.ConcreteCallChain
        (Functions.CallDepth.Ranked.GuardedZeroCalls.GuardedSemanticDirectCall
          check.lowerObj.toFunctions)
        frame depth) :
    depth + 1 ≤ check.maxFrames := by
  let _hChecked :=
    Yul.Program.recursiveBridgeExecutableSCCRecurrenceCheckResult?_eq_some
      hCheck
  exact check.guardedSemanticRootChain_frame_count_bound hRoot hChain

example
    {program : Yul.Program} {lowerObj : Objects.Program}
    (hLower : program.toObjects? = some lowerObj)
    (hAcyclic :
      Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
          lowerObj.toFunctions =
        none)
    (hSCC :
      Functions.CallDepth.Ranked.checkSCCRecurrence?
          lowerObj.toFunctions =
        none) :
    Yul.Program.recursiveBridgeExecutableSourceRecurrenceDepth? program =
      none :=
  Yul.Program.recursiveBridgeExecutableSourceRecurrenceDepth?_none_of_default_branches_none
    hLower hAcyclic hSCC

example
    {program : Yul.Program} {lowerObj : Objects.Program}
    (hLower : program.toObjects? = some lowerObj)
    (hAcyclic :
      Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
          lowerObj.toFunctions =
        none)
    (hSCC :
      Functions.CallDepth.Ranked.checkSCCRecurrence?
          lowerObj.toFunctions =
        none) :
    Yul.Program.recursiveBridgeSourceResourceDepth? program = none :=
  Yul.Program.recursiveBridgeSourceResourceDepth?_none_of_default_branches_none
    hLower hAcyclic hSCC

example
    {program : Yul.Program} {depth : Nat}
    (hDepth :
      Yul.Program.recursiveBridgeExecutableSourceRecurrenceDepth? program =
        some depth) :
    ∃ lowerObj,
      program.toObjects? = some lowerObj ∧
        ((∃ check :
            Functions.CallDepth.Ranked.CheckedProgramRecurrenceCheckResult
              lowerObj.toFunctions,
            check.depth = depth) ∨
          (Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
              lowerObj.toFunctions =
            none ∧
              ∃ check :
                Functions.CallDepth.Ranked.SCCRecurrenceCheckResult
                  lowerObj.toFunctions,
                Functions.CallDepth.Ranked.checkSCCRecurrence?
                    lowerObj.toFunctions =
                  some check ∧
                  check.maxFrames = depth)) :=
  Yul.Program.recursiveBridgeExecutableSourceRecurrenceDepth?_eq_some_cases
    hDepth

example
    {program : Yul.Program} {depth : Nat}
    (hDepth :
      Yul.Program.recursiveBridgeSourceResourceDepth? program = some depth) :
    ∃ lowerObj,
      program.toObjects? = some lowerObj ∧
        ((Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
              lowerObj.toFunctions =
            some depth ∧
            Functions.CallDepth.Ranked.sourceStackFitsEVM? depth = true ∧
            ∃ check :
              Functions.CallDepth.Ranked.CheckedProgramRecurrenceCheckResult
                lowerObj.toFunctions,
              check.depth = depth) ∨
          (((Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
                lowerObj.toFunctions =
              none) ∨
              ∃ acyclicDepth,
                Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
                    lowerObj.toFunctions =
                  some acyclicDepth ∧
                  Functions.CallDepth.Ranked.sourceStackFitsEVM?
                      acyclicDepth =
                    false) ∧
            ∃ check :
              Functions.CallDepth.Ranked.SCCRecurrenceCheckResult
                lowerObj.toFunctions,
              Functions.CallDepth.Ranked.checkSCCRecurrence?
                  lowerObj.toFunctions =
                some check ∧
                check.maxFrames = depth ∧
                  Functions.CallDepth.Ranked.sourceStackFitsEVM? depth =
                    true)) :=
  Yul.Program.recursiveBridgeSourceResourceDepth?_eq_some_cases hDepth

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    (hCheck :
      Functions.CallDepth.Program.stackFrameWordSumCheck? program =
        some check) :
    Functions.CallDepth.Program.maxActiveFrameWords? program =
        some check.frameWords ∧
      16 + check.frameWords + 17 ≤ 1024 :=
  Functions.CallDepth.Program.stackFrameWordSumCheck?_eq_some hCheck

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {name : Functions.Name} {pathWords : Nat}
    (hRoot :
      name ∈ Functions.CallDepth.Program.mainInternalCalls program)
    (hPath :
      Functions.CallDepth.FunctionPathFrameWords program.functions name
        pathWords) :
    pathWords ≤ check.frameWords :=
  check.path_words_bound hRoot hPath

example
    {program : Functions.Program} {bound : Nat}
    (hBound :
      Functions.CallDepth.Program.maxActiveFrameWords? program = some bound)
    {name : Functions.Name} {pathWords : Nat}
    (hRoot :
      name ∈ Functions.CallDepth.Program.mainInternalCalls program)
    (hPath :
      Functions.CallDepth.FunctionPathFrameWords program.functions name
        pathWords) :
    pathWords ≤ bound :=
  Functions.CallDepth.Program.maxActiveFrameWords?_sound hBound hRoot hPath

example
    {functions : List Functions.FunDef}
    {root current : Functions.Name} {pathWords : Nat}
    (hPath :
      Functions.CallDepth.FunctionPathFrameWordsTo functions root current
        pathWords) :
    Functions.CallDepth.FunctionPathFrameWords functions root pathWords :=
  hPath.toFunctionPathFrameWords

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active : List Functions.Name} {pathWords : Nat}
    (hPath :
      Functions.CallDepth.Program.ActiveCallFrameWords program active
        pathWords) :
    pathWords ≤ check.frameWords :=
  Functions.CallDepth.Program.ActiveCallFrameWords.words_le_check check hPath

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active : List Functions.Name}
    {source : Structured.RunState}
    (hContext :
      Functions.CallDepth.ActiveHiddenFrameWordsContext program active
        source.returns)
    (hVisible : source.evm.stack.length ≤ 16) :
    Structured.Preservation.Frame.SourceStackHeadroom source :=
  Functions.CallDepth.ActiveHiddenFrameWordsContext.sourceStackHeadroom
    (check := check) hContext hVisible

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.ActiveHiddenFrameWordsContext program active
        hiddenReturns)
    (hLayout : layout.length ≤ 16)
    (hRel :
      Functions.SourceDirect.StateRel layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  Functions.CallDepth.ActiveHiddenFrameWordsContext.sourceStackHeadroom_of_sourceDirectStateRel
    (check := check) hContext hLayout hRel

example
    {program : Functions.Program}
    {active : List Functions.Name} {callee : Functions.Name}
    {frame : Structured.ReturnDest}
    {hiddenReturns : List Structured.ReturnDest}
    (hContext :
      Functions.CallDepth.ActiveHiddenFrameWordsContext program
        (active ++ [callee]) (frame :: hiddenReturns)) :
    Functions.CallDepth.ActiveHiddenFrameWordsContext program active
      hiddenReturns :=
  Functions.CallDepth.ActiveHiddenFrameWordsContext.afterReturn hContext

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  Functions.CallDepth.SourceDirectWeightedFrameContext.sourceStackHeadroom
    (check := check) hContext

example
    {program : Functions.Program}
    {active callerLayout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Functions.Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Functions.Name}
    {callerFn calleeFn : Functions.FunDef} {retc : Nat}
    (hCallerContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        callerLayout hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      Functions.FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ Functions.CallDepth.FunDef.internalCalls callerFn)
    (hCalleeFind :
      Functions.FunList.find? callee program.functions = some calleeFn)
    (hCalleeBound : Functions.SourceDirect.FrameBound.FunDef calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hRel :
      Functions.SourceDirect.StateRel
        (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    Functions.CallDepth.SourceDirectWeightedFrameContext program
      (active ++ [callee])
      (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget :=
  Functions.CallDepth.SourceDirectWeightedFrameContext.callBodyTargetCtxOfArgCallerBound
    hCallerContext hCaller hCallerFind hCall hCalleeFind hCalleeBound
    hArgCallerBound hRel

example
    {program : Functions.Program}
    {active : List Functions.Name} {callee : Functions.Name}
    {calleeLayout callerLayout : List Functions.Name}
    {calleeHidden callerHidden : List Structured.ReturnDest}
    {calleeSource callerSource : Functions.Source.State}
    {state returned callerTarget : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Functions.Word}
    (hCalleeContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program
        (active ++ [callee]) calleeLayout calleeHidden calleeSource state)
    (hActive :
      Functions.CallDepth.Program.ActiveCallStack program active)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16)
    (hCallerTarget :
      callerTarget = returned.withEVM { state.evm with stack := stack })
    (hRel :
      Functions.SourceDirect.StateRel callerLayout callerHidden callerSource
        callerTarget) :
    Functions.CallDepth.SourceDirectWeightedFrameContext program active
      callerLayout callerHidden callerSource callerTarget :=
  Functions.CallDepth.SourceDirectWeightedFrameContext.afterAttachReturns?
    hCalleeContext hActive hPop hAttach hReturnFrameVisible hCallerTarget hRel

example
    {program : Functions.Program}
    {bound :
      Functions.CallDepth.SourceFrameWordSumResourceBound program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  bound.sourceStackHeadroom_of_weightedContext hContext

example
    {program : Functions.Program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        layout hiddenReturns source target) :
    ∃ activeWords,
      Functions.CallDepth.Program.ActiveCallFrameWords program active
        activeWords ∧
        Structured.Preservation.Frame.sourceStackWeight target ≤
          layout.length + activeWords :=
  hContext.sourceStackWeight_le_layout_plus_activeWords

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        layout hiddenReturns source target) :
    Structured.Preservation.Frame.sourceStackWeight target ≤
      16 + check.frameWords :=
  hContext.sourceStackWeight_le_checked_frameWords

example
    {program : Functions.Program}
    {bound :
      Functions.CallDepth.SourceFrameWordSumResourceBound program}
    (hBound :
      Functions.CallDepth.Program.sourceFrameWordSumResourceBound? program =
        some bound) :
    Functions.CallDepth.Program.stackFrameWordSumCheck? program =
      some bound.check :=
  Functions.CallDepth.Program.sourceFrameWordSumResourceBound?_eq_some
    hBound

example
    {program : Functions.Program}
    {bound :
      Functions.CallDepth.SourceFrameWordSumResourceBound program}
    (hBound :
      Functions.CallDepth.Program.sourceFrameWordSumResourceBound? program =
        some bound) :
    Functions.CallDepth.Program.maxActiveFrameWords? program =
        some bound.check.frameWords ∧
      16 + bound.check.frameWords + 17 ≤ 1024 :=
  Functions.CallDepth.Program.sourceFrameWordSumResourceBound?_sound hBound

example
    {program : Yul.Program} {depth : Nat}
    (hDepth :
      Yul.Program.recursiveBridgeSourceFrameWordsResourceDepth? program =
        some depth) :
    Yul.Program.RecursiveBridgeSourceFrameWordsResourceBound program depth :=
  Yul.Program.recursiveBridgeSourceFrameWordsResourceDepth?_sound hDepth

example
    {program : Yul.Program} {depth : Nat}
    (hDepth :
      Yul.Program.recursiveBridgeSourceFrameWordsResourceDepth? program =
        some depth) :
    Yul.Program.RecursiveBridgeSourceActiveDepthBound program depth :=
  Yul.Program.recursiveBridgeSourceFrameWordsResourceDepth?_sourceActiveDepthBound
    hDepth

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource :
      Yul.Program.RecursiveBridgeSourceFrameWordsResourceBound program
        maxFrames}
    {active layout : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (context :
      Functions.CallDepth.SourceDirectFrameWordsContext
        hResource.lowerObj.toFunctions
        (Functions.CallDepth.Program.maxSourceReturnFrameWords
          hResource.lowerObj.toFunctions)
        active layout hiddenReturns source target)
    (hActiveLength : active.length ≤ maxFrames) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  Yul.Program.RecursiveBridgeSourceFrameWordsResourceBound.sourceStackHeadroom_of_frameWordsContext
    hResource context hActiveLength

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource :
      Yul.Program.RecursiveBridgeSourceFrameWordsResourceBound program
        maxFrames}
    {state : Yul.EVMState}
    (hPoint :
      Yul.Program.RecursiveBridgeSourceDirectFrameWordsPoint hResource
        state) :
    ∃ baseState tokens,
      Structured.Preservation.Frame.StateRel baseState state tokens ∧
        Structured.Preservation.Frame.SourceStackHeadroom baseState :=
  Yul.Program.RecursiveBridgeSourceDirectFrameWordsPoint.point_sourceStackHeadroom
    hPoint

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource :
      Yul.Program.RecursiveBridgeSourceFrameWordsResourceBound program
        maxFrames}
    {active callerLayout : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Functions.Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    {caller callee : Yul.Name} {callerFn calleeFn : Functions.FunDef}
    {retc : Nat}
    (hCallerContext :
      Functions.CallDepth.SourceDirectFrameWordsContext
        hResource.lowerObj.toFunctions
        (Functions.CallDepth.Program.maxSourceReturnFrameWords
          hResource.lowerObj.toFunctions)
        active callerLayout hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      Functions.FunList.find? caller
          hResource.lowerObj.toFunctions.functions =
        some callerFn)
    (hCall :
      callee ∈ Functions.CallDepth.FunDef.internalCalls callerFn)
    (hCalleeFind :
      Functions.FunList.find? callee
          hResource.lowerObj.toFunctions.functions =
        some calleeFn)
    (hCalleeBound :
      Functions.SourceDirect.FrameBound.FunDef calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames (active ++ [callee]))
    (hRel :
      Functions.SourceDirect.StateRel
        (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel calleeTarget state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectFrameWordsPoint hResource state :=
  Yul.Program.RecursiveBridgeSourceDirectFrameWordsPoint.callBodyTargetCtxOfArgCallerBound
    hCallerContext hCaller hCallerFind hCall hCalleeFind hCalleeBound
    hArgCallerBound hActive hRel hFrameRel

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    ∃ lowerObj,
      ∃ depth,
        ∃ resource :
          Functions.CallDepth.Ranked.SourceResourceBound
            lowerObj.toFunctions depth,
          Yul.Program.recursiveBridgeSourceResourceDepth? program =
              some depth ∧
            program.toObjects? = some lowerObj ∧
              _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceSafeFromBase
                lowerObj.toFunctions resource.toStackBudget := by
  rcases
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceResourceBound
        hCheckedCompileTarget with
    ⟨depth, hDepth, _hResource⟩
  rcases
      Yul.Program.recursiveBridgeSourceResourceDepth?_stackResourceSafeFromBase
        hDepth with
    ⟨lowerObj, resource, hLower, hSafe⟩
  exact ⟨lowerObj, depth, resource, hDepth, hLower, hSafe⟩

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    _root_.EvmCompiler.Functions.CallDepth.Program.StackResourceSafeFromBase
      (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_stackResourceCheck
        hCheckedCompileTarget).lowerObj.toFunctions
      (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_stackResourceCheck
        hCheckedCompileTarget).toStackBudget :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_stackResourceSafeFromBase
    hCheckedCompileTarget

example
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target)) :
    (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_stackResourceCheck
        hCheckedCompileTarget).toStackBudget.depth =
      (Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked
        hCheckedCompileTarget).sourceDepth := by
  unfold
    Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_stackResourceCheck
    Yul.Program.RecursiveBridgeSourceResourceBound.toStackResourceCheckResult
    Yul.Program.RecursiveBridgeExecutableStackResourceCheckResult.toStackBudget
    Functions.CallDepth.Ranked.SourceResourceBound.toStackResourceCheckResult
    Functions.CallDepth.Ranked.SourceResourceBound.toStackBudget
  simp

/--
The preferred executable stack-safe public result theorem must not expose a
source/direct resource-point one-step invariant.  This tripwire applies the
public root from only source-facing inputs, checked compilation, and the entry
permission bit.
-/
example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprResultContracts :
      Yul.Program.RecursiveBridgeExprResultContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target
        shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target))
    (hInitialPerm : initial.executionEnv.perm = true) :
    True := by
  have _hResult :=
    Yul.Program.compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_stepTrace_executableAssemblyInferredBoundStackSafeCompile_initialPerm_noReturnDataCopy_X
      hExprResultContracts hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hInitialPerm
  trivial

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprResultContracts :
      Yul.Program.RecursiveBridgeExprResultContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target
        shared initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCheckedCompileTarget :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
          program =
        some (asm, target))
    (hInitialPerm : initial.executionEnv.perm = true) :
    True := by
  have _hNoOut :=
  Yul.Program.compile_whole_program_result_no_out_of_gas_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_executableAssemblyInferredBoundStackSafeCompile_initialPerm_noReturnDataCopy_X
      hExprResultContracts hInitialCodeImageRel hSourceFuelRun
      hCheckedCompileTarget hInitialPerm
  trivial

end

end PublicSpineRegression

namespace LiveLayoutRegression

example {layout live : List Functions.Name}
    (hCheck : Functions.LiveLayout.Layout.entryWindowOk? layout live = true)
    {name : Functions.Name} (hName : name ∈ live) :
    ∃ idx,
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live)[idx]? =
          some name ∧
        idx + 1 ≤ 16 :=
  Functions.LiveLayout.Layout.entryWindowOk?_sound hCheck hName

example {layout live : List Functions.Name} :
    Functions.LiveLayout.Layout.entryWindowOk? layout live = true ↔
      ∀ {name : Functions.Name}, name ∈ live →
        ∃ idx,
          Functions.LiveLayout.Layout.index? name
              (Functions.LiveLayout.Layout.trimDeadPrefix layout live) =
            some idx ∧
          idx + 1 ≤ 16 :=
  Functions.LiveLayout.Layout.entryWindowOk?_iff_index

example :
    Functions.LiveLayout.Layout.promoteName?
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] "x" =
      some
        (["x", "d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
          "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"],
          16) := by
  native_decide

example :
    Functions.LiveLayout.Layout.promoteName?
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "d16", "x"] "x" = none := by
  native_decide

example {protectedDepth : Nat} {layout : List Functions.Name}
    {reqs : List Functions.LiveLayout.Prepare.NameReq}
    {promoteStmt : Locals.Stmt} {promoted : List Functions.Name}
    (hPromote :
      Functions.LiveLayout.Prepare.promoteBlockedAboveSuffix?
          protectedDepth layout reqs =
        some (promoteStmt, promoted)) :
    ∃ name idx,
      promoteStmt = .promoteName name ∧
        Functions.LiveLayout.Layout.promoteName? layout name =
          some (promoted, idx) ∧
        idx < layout.length - protectedDepth :=
  Functions.LiveLayout.Prepare.promoteBlockedAboveSuffix?_eq_some hPromote

example :
    Functions.LiveLayout.Prepare.promoteBlockedAboveSuffix? 0
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] [(1, "x")] =
      some
        (.promoteName "x",
          ["x", "d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
            "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"]) := by
  rfl

example :
    Functions.LiveLayout.Prepare.promoteBlockedAboveSuffix? 1
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] [(1, "x")] = none := by
  rfl

example :
    Functions.LiveLayout.Prepare.forStmtAboveSuffix? 0 []
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] ["x"]
      (.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil))) =
      some
        ([Locals.Stmt.promoteName "x"],
          ["x", "d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
            "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"]) := by
  rfl

example :
    Functions.LiveLayout.Prepare.forStmtAboveSuffix? 1 []
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] ["x"]
      (.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil))) = none := by
  rfl

set_option maxRecDepth 20000 in
example :
    Functions.LiveLayout.Checked.StmtList.check? [] {}
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "dead",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14"]
      [(.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil)))] =
      some
        ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
          "d8", "d9", "d10", "d11", "d12", "d13", "d14", "dead"] := by
  rfl

set_option maxRecDepth 20000 in
example :
    ∃ lower,
      Functions.LiveLayout.Lower.StmtList.toLocals? [] {}
        ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
          "d8", "d9", "d10", "d11", "d12", "d13", "d14", "dead",
          "x"]
        ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
          "d8", "d9", "d10", "d11", "d12", "d13", "d14"]
        [(.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil)))] =
        some
          (lower,
            ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
              "d8", "d9", "d10", "d11", "d12", "d13", "d14", "dead"]) := by
  refine ⟨_, rfl⟩

set_option maxRecDepth 50000 in
example :
    (Functions.LiveLayout.Prepare.forStmtAboveSuffix? 0 []
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "dead", "y",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "x", "y"]
      (.expr (.prim .pop (Locals.ExprSeq.cons
        (.prim .add (Locals.ExprSeq.cons (.var "x")
          (Locals.ExprSeq.cons (.var "y") .nil))) .nil)))).map
        (fun pair => pair.1.length) = some 2 := by
  native_decide

set_option maxRecDepth 50000 in
example :
    Functions.LiveLayout.Checked.StmtList.check? [] {}
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "dead", "y",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13"]
      [(.expr (.prim .pop (Locals.ExprSeq.cons
        (.prim .add (Locals.ExprSeq.cons (.var "x")
          (Locals.ExprSeq.cons (.var "y") .nil))) .nil)))] =
      some ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "dead"] := by
  native_decide

set_option maxRecDepth 50000 in
example :
    (Functions.LiveLayout.Lower.StmtList.toLocals? [] {}
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "dead", "y",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13"]
      [(.expr (.prim .pop (Locals.ExprSeq.cons
        (.prim .add (Locals.ExprSeq.cons (.var "x")
          (Locals.ExprSeq.cons (.var "y") .nil))) .nil)))]).isSome =
      true := by
  native_decide

set_option maxRecDepth 20000 in
example :
    Functions.LiveLayout.Checked.StmtList.check? [] {}
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"]
      [(.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil)))] =
      none := by
  rfl

example {protectedDepth fuel : Nat} {returns live layout : List Functions.Name}
    {stmt : Functions.Stmt} {reqs : List Functions.LiveLayout.Prepare.NameReq}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hLoop :
      Functions.LiveLayout.Prepare.loopAboveSuffix protectedDepth returns live
          stmt reqs fuel layout =
        some (prep, finalLayout)) :
    Functions.LiveLayout.Prepare.checked? returns live finalLayout stmt =
      true :=
  Functions.LiveLayout.Prepare.loopAboveSuffix_checked hLoop

example {protectedDepth fuel : Nat} {returns live layout : List Functions.Name}
    {stmt : Functions.Stmt} {reqs : List Functions.LiveLayout.Prepare.NameReq}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hLoop :
      Functions.LiveLayout.Prepare.loopAboveSuffix protectedDepth returns live
          stmt reqs fuel layout =
        some (prep, finalLayout)) :
    Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout layout prep =
      finalLayout :=
  Functions.LiveLayout.TargetLayout.Prepare.loopAboveSuffix_regularOutLayout
    hLoop

example {protectedDepth : Nat} {returns live layout : List Functions.Name}
    {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          layout live stmt =
        some (prep, finalLayout)) :
    Functions.LiveLayout.Layout.entryWindowOk? finalLayout live = true ∧
      Functions.LiveLayout.StmtAccess.accessible? returns finalLayout stmt =
        true :=
  Functions.LiveLayout.Prepare.forStmtAboveSuffix?_checked hPrepare

example {protectedDepth : Nat} {returns live layout : List Functions.Name}
    {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          layout live stmt =
        some (prep, finalLayout)) :
    Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout layout prep =
      finalLayout :=
  Functions.LiveLayout.TargetLayout.Prepare.forStmtAboveSuffix?_regularOutLayout
    hPrepare

example {retc protectedDepth idx : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {promoted : List Functions.Name} {name : Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hPromote :
      Functions.LiveLayout.Layout.promoteName? target.layout name =
        some (promoted, idx))
    (hIdx : idx < target.layout.length - protectedDepth)
    (hBreakDepth :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth)
    (hContinueDepth :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout promoted) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.promoteName_of_idx_lt_protectedDepth
    hRel hPromote hIdx hBreakDepth hContinueDepth

example {retc protectedDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {returns live : List Functions.Name} {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          target.layout live stmt =
        some (prep, finalLayout))
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hBreakDepth :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth)
    (hContinueDepth :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout finalLayout) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.forStmtAboveSuffix_of_depth_bounds
    hPrepare hRel hBreakDepth hContinueDepth

example {retc targetDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {live : Functions.LiveLayout.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.breakDepth_le_protectedDepth
    hRel hControl hNoDup hTargetDepth

example {retc targetDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {live : Functions.LiveLayout.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.continueDepth_le_protectedDepth
    hRel hControl hNoDup hTargetDepth

example {retc : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {liveCtx : Functions.LiveLayout.Ctx}
    {returns live : List Functions.Name} {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix?
          liveCtx.protectedDepth returns target.layout live stmt =
        some (prep, finalLayout))
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel liveCtx source)
    (hNoDup : target.layout.Nodup) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout finalLayout) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.forStmtAboveSuffix_of_liveControl
    hPrepare hRel hControl hNoDup

example {layout₁ layout₂ : List Locals.Name}
    {source : Locals.Source.State}
    {target₁ target₂ : Structured.RunState}
    (hRel₁ :
      Locals.SourceLowering.StateRel layout₁ source target₁)
    (hRel₂ :
      Locals.SourceLowering.StateRel layout₂ source target₂) :
    target₁.evm.toSharedState = target₂.evm.toSharedState :=
  Locals.SourceLowering.StateRel.target_shared_eq_of_same_source hRel₁ hRel₂

example :
    ¬ Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
      ({ (default : EvmYul.MachineState) with activeWords := ⟨0⟩ })
      (⟨0⟩ : Locals.Word) := by
  change ¬ EvmYul.UInt256.ofNat (EvmYul.MachineState.M 0 0 32) =
    (⟨0⟩ : EvmYul.UInt256)
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
      ({ (default : EvmYul.MachineState) with activeWords := ⟨1⟩ })
      (⟨0⟩ : Locals.Word) := by
  change EvmYul.UInt256.ofNat (EvmYul.MachineState.M 1 0 32) =
    (⟨1⟩ : EvmYul.UInt256)
  native_decide

example :
    ¬ Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
      ({ (default : EvmYul.MachineState) with activeWords := ⟨1⟩ })
      (⟨0⟩ : Locals.Word) := by
  change ¬ 0 + 32 ≤ (default : EvmYul.MachineState).memory.size
  native_decide

example {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordWithinActiveNat
        machine offset) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchWordReserved_of_withinActiveNat
    hWithin

example {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordWithinActiveNat
        machine offset)
    (hNoOverflow :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchActiveBytesNoOverflow
        machine) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReadable
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchWordReadable_of_allocated_withinActiveNat
    hAllocated hWithin hNoOverflow

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec) :
    ffi.ByteArray.zeroes 0 = ByteArray.empty :=
  Locals.SourceLowering.StateRel.SpillScratch.zeroPadding_zero_eq_empty hSpec

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (n : USize) :
    (ffi.ByteArray.zeroes n).size = n.toNat :=
  Locals.SourceLowering.StateRel.SpillScratch.zeroPadding_size hSpec n

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (n : USize) :
    (ffi.ByteArray.zeroes n).data.toList = List.replicate n.toNat 0 :=
  Locals.SourceLowering.StateRel.SpillScratch.zeroPadding_data_toList
    hSpec n

example (xs : List UInt8) :
    (List.toByteArray xs).data.toList = xs :=
  Locals.SourceLowering.StateRel.SpillScratch.list_toByteArray_data_toList
    xs

example (bytes : ByteArray) :
    bytes.toList = bytes.data.toList :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_toList_eq_data_toList
    bytes

example {n : Nat} (hLen : n ≤ 32) :
    ({ toBitVec := 32 - (n : BitVec System.Platform.numBits) } : USize).toNat +
        n = 32 :=
  Locals.SourceLowering.StateRel.SpillScratch.usize_wordPadding_toNat_add hLen

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec) :
    Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.wordByteEncoding_of_zeroPadding
    hSpec

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec) :
    Locals.SourceLowering.StateRel.SpillScratch.WordByteRoundTripSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.wordByteRoundTrip_of_zeroPadding
    hSpec

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec) :
    Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.wordByteEncodingModel_of_zeroPadding
    hSpec

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {memory : ByteArray} {offset : Nat}
    (hAllocated : offset + 32 ≤ memory.size) :
    memory.readWithPadding offset 32 =
      { data := memory.data.extract offset (offset + 32) } :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_readWithPadding32_allocated
    hSpec hAllocated

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source restore : ByteArray} {offset : Nat}
    (hSource : source.size = 32)
    (hRestore : restore.size = 32)
    (hDest : offset + 32 ≤ dest.size)
    (hRestoreBytes :
      restore.data = dest.data.extract offset (offset + 32)) :
    restore.write 0 (source.write 0 dest offset 32) offset 32 = dest :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_restore_exact
    hSpec hSource hRestore hDest hRestoreBytes

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hReadable :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReadable
        machine offset) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordBytesCanonical
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchWordBytesCanonical_of_readable
    hSpec hEncoding hAllocated hReadable

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hCanonical :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordBytesCanonical
        machine offset) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordMemoryRestoreObligation
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.memoryRestore_of_wordBytesCanonical
    hSpec hWordBytes hAllocated hCanonical

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hReadable :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReadable
        machine offset) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordMemoryRestoreObligation
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.memoryRestore_of_readable
    hSpec hEncoding hAllocated hReadable

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordWithinActiveNat
        machine offset)
    (hNoOverflow :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchActiveBytesNoOverflow
        machine) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordMemoryRestoreObligation
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.memoryRestore_of_allocated_withinActiveNat
    hSpec hEncoding hAllocated hWithin hNoOverflow

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordWithinActiveNat
        machine offset)
    (hNoOverflow :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchActiveBytesNoOverflow
        machine) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordOverwriteRestoreObligation
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.overwriteRestore_of_allocated_withinActiveNat
    hSpec hEncoding hAllocated hWithin hNoOverflow

example {machine : EvmYul.MachineState} {base count slot : Nat}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionAllocatedNat
        machine base count)
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionWithinActiveNat
        machine base count)
    (hNoOverflow :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchActiveBytesNoOverflow
        machine)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated machine
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base slot) :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchWordAllocated_of_regionNat
    hAllocated hWithin hNoOverflow hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {base count slot : Nat}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionAllocatedNat
        machine base count)
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionWithinActiveNat
        machine base count)
    (hNoOverflow :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchActiveBytesNoOverflow
        machine)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordOverwriteRestoreObligation
      machine
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base slot) :=
  Locals.SourceLowering.StateRel.SpillScratch.overwriteRestore_of_regionNat
    hSpec hEncoding hAllocated hWithin hNoOverflow hSlot

example {machine : EvmYul.MachineState} {base count : Nat}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
        machine base count = true) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      machine base count :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_sound
    hCheck

example :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      ({ (default : EvmYul.MachineState) with activeWords := ⟨0⟩ }) 0 1 =
        false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      ({ (default : EvmYul.MachineState) with activeWords := ⟨1⟩ }) 0 1 =
        false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      ({ (default : EvmYul.MachineState) with
          activeWords := ⟨1⟩
          memory := List.toByteArray (List.replicate 32 (0 : UInt8)) })
      0 1 = true := by
  native_decide

example {machine : EvmYul.MachineState} {base count slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base slot) :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.scratchWordReserved
    hReady hSlot

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len : Nat}
    (hEnd : offset + len ≤ range.base) :
    range.disjointBytes offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.disjointBytes_of_before
    hEnd

example {a lenA b lenB : Nat}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint.check
        a lenA b lenB = true) :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
      a lenA b lenB :=
  Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint.check_sound
    hCheck

example :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint.check
      0 32 64 32 = true := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint.check
      16 32 0 32 = false := by
  native_decide

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len : Nat}
    (hCheck : range.disjointBytes? offset len = true) :
    range.disjointBytes offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.disjointBytes?_sound
    hCheck

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len : Nat}
    (hDisjoint : range.disjointBytes offset len) :
    range.disjointBytes? offset len = true :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.disjointBytes?_complete
    hDisjoint

example {op : Structured.BasicOp}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.basicOp?
        op = true) :
    ¬
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.BasicOpMemoryTouching
        op :=
  Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.basicOp?_sound
    hCheck

example :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.basicOp?
      Structured.BasicOp.add = true := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.basicOp?
      Structured.BasicOp.mload = false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.haltKind?
      Assembly.HaltKind.return = false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.program?
      { procs := []
        body :=
          { stmts :=
              [Locals.Stmt.expr
                (Locals.Expr.prim Structured.BasicOp.mload
                  (Locals.ExprSeq.cons
                    (Locals.Expr.lit (EvmYul.UInt256.ofNat 0))
                    Locals.ExprSeq.nil))] } } =
      false := by
  native_decide

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
        range sourceScope stackLayout layout = true) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
      range sourceScope stackLayout layout :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?_sound
    hCheck

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    {name : Locals.Name} {slot : Nat}
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    slot < range.words :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed.scratch_binding
    hLayout hBinding

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
      { base := 0, words := 1 }
      ["x", "y"]
      ["x"]
      [("x",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
            0),
        ("y",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            0)] =
      true := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
      { base := 0, words := 2 }
      ["x", "y"]
      []
      [("x",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            0),
        ("y",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            0)] =
      false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
      { base := 0, words := 1 }
      ["x"]
      []
      [("x",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            1)] =
      false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
      { base := 0, words := 1 }
      ["x"]
      ["y"]
      [("x",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
            0)] =
      false := by
  native_decide

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    {name : Locals.Name} {depth : Nat}
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
          depth) ∈ layout) :
    stack[depth]? = store name :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.stack_binding
    hValues hBinding

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    {name : Locals.Name} {slot : Nat}
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ value, store name = some value ∧
      (machine.mload (range.word slot)).1 = value :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.scratch_binding
    hValues hBinding

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    {name : Locals.Name} {slot : Nat}
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    slot < range.words ∧
      ∃ value, store name = some value ∧
        (machine.mload (range.word slot)).1 = value :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.scratch_binding_of_wellFormed
    hLayout hValues hBinding

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {writeSlot : Nat} {value : Locals.Word}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hWriteSlot : writeSlot < range.words)
    (hStoreMatches :
      ∀ {name : Locals.Name},
        (name,
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            writeSlot) ∈ layout →
          store name = some value) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
      range store
      ((machine.mstore (range.word writeSlot) value).mload
        (range.word writeSlot)).2 stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.mload_after_mstore_target_scratch_slot_preserve
    hSpec hWordBytes hLayout hValues hReady hWriteSlot hStoreMatches

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len : Nat}
    (hStart : range.endExclusive ≤ offset) :
    range.disjointBytes offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.disjointBytes_of_after
    hStart

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len slot : Nat}
    (hDisjoint : range.disjointBytes offset len)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint offset len
      (range.slot slot) 32 :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.byteDisjoint_slot_of_disjointBytes
    hDisjoint hSlot

example {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        machine range = true) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      machine range.base range.words :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?_sound
    hReady

example {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hDisjoint : range.disjointBytes offset len)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint offset len
      (range.word slot).toNat 32 :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.byteDisjoint_word_slot_of_disjointBytes
    hReady hDisjoint hSlot

example {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {left right : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hLeft : left < range.words)
    (hRight : right < range.words)
    (hNe : left ≠ right) :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
      (range.word left).toNat 32 (range.word right).toNat 32 :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.byteDisjoint_word_slots_of_ne
    hReady hLeft hRight hNe

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {machine : EvmYul.MachineState} :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range machine machine :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.refl
    range machine

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range target source :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.symm
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target) :
    target.msize = source.msize :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.msize_eq
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset.toNat 32) :
    target.lookupMemory offset = source.lookupMemory offset :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.lookupMemory_eq_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset.toNat 32) :
    (target.mload offset).1 = (source.mload offset).1 ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range (source.mload offset).2 (target.mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.mload_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {machine : EvmYul.MachineState} :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range machine machine :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.refl
    range machine

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range target source :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.symm
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range source target :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.toMemoryEqOutsideScratch
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset.toNat 32) :
    (target.mload offset).1 = (source.mload offset).1 ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range (source.mload offset).2 (target.mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mload_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset len : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset len) :
    target.memory.readWithoutPadding offset len =
      source.memory.readWithoutPadding offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.readWithoutPadding_eq_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset len : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset len) :
    target.memory.readWithPadding offset len =
      source.memory.readWithPadding offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.readWithPadding_eq_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : ByteArray} {offset len : Nat}
    (hSize : target.size = source.size)
    (hByteEq :
      ∀ idx (_hDisjoint : range.disjointBytes idx 1)
        (hTarget : idx < target.size)
        (hSource : idx < source.size),
          target[idx]'hTarget = source[idx]'hSource)
    (hDisjoint : range.disjointBytes offset len) :
    target.readWithPadding offset len =
      source.readWithPadding offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.byteArray_readWithPadding_eq_of_disjoint_byte_eq
    hSize hByteEq hDisjoint

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {target source bytes : ByteArray} {writeOffset idx : Nat}
    (hBytes : bytes.size = 32)
    (hTargetAlloc : writeOffset + 32 ≤ target.size)
    (hSourceAlloc : writeOffset + 32 ≤ source.size)
    (hByteEq :
      ∀ (hTarget : idx < target.size)
        (hSource : idx < source.size),
          target[idx]'hTarget = source[idx]'hSource)
    (hTargetIdx : idx < (bytes.write 0 target writeOffset 32).size)
    (hSourceIdx : idx < (bytes.write 0 source writeOffset 32).size) :
    (bytes.write 0 target writeOffset 32)[idx]'hTargetIdx =
      (bytes.write 0 source writeOffset 32)[idx]'hSourceIdx :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_byte_eq_noExpansion
    hSpec hBytes hTargetAlloc hSourceAlloc hByteEq hTargetIdx hSourceIdx

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {offset value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hTargetAllocated : offset.toNat + 32 ≤ target.memory.size) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range (source.mstore offset value) (target.mstore offset value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mstore_pair_noExpansion
    hSpec hWordBytes hRel hTargetAllocated

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray} {offset : Nat}
    (hSource : source.size = 32)
    (hPadNoOverflow : offset - dest.size < USize.size) :
    (source.write 0 dest offset 32).size =
      max dest.size (offset + 32) :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_size_general
    hSpec hSource hPadNoOverflow

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray} {offset : Nat}
    (hSource : source.size = 32)
    (hPadNoOverflow : offset - dest.size < USize.size)
    (hExpanding : ¬ offset + 32 ≤ dest.size) :
    source.write 0 dest offset 32 =
      { data :=
          (dest.data ++
            (ffi.ByteArray.zeroes
              (OfNat.ofNat (offset - dest.size))).data).extract 0 offset ++
            source.data } :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_expanding_exact
    hSpec hSource hPadNoOverflow hExpanding

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {target source bytes : ByteArray} {writeOffset idx : Nat}
    (hBytes : bytes.size = 32)
    (hSize : target.size = source.size)
    (hPadNoOverflow : writeOffset - target.size < USize.size)
    (hByteEq :
      ∀ (hTarget : idx < target.size)
        (hSource : idx < source.size),
          target[idx]'hTarget = source[idx]'hSource)
    (hTargetIdx : idx < (bytes.write 0 target writeOffset 32).size)
    (hSourceIdx : idx < (bytes.write 0 source writeOffset 32).size) :
    (bytes.write 0 target writeOffset 32)[idx]'hTargetIdx =
      (bytes.write 0 source writeOffset 32)[idx]'hSourceIdx :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_byte_eq_boundedExpansion
    hSpec hBytes hSize hPadNoOverflow hByteEq hTargetIdx hSourceIdx

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {offset value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hTargetPadNoOverflow :
      offset.toNat - target.memory.size < USize.size) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range (source.mstore offset value) (target.mstore offset value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mstore_pair_boundedExpansion
    hSpec hWordBytes hRel hTargetPadNoOverflow

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray}
    {writeOffset readOffset len : Nat}
    (hSource : source.size = 32)
    (hDest : writeOffset + 32 ≤ dest.size)
    (hDisjoint :
      Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
        readOffset len writeOffset 32) :
    (source.write 0 dest writeOffset 32).readWithoutPadding
        readOffset len =
      dest.readWithoutPadding readOffset len :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_readWithoutPadding_write32_eq_of_byteDisjoint
    hSpec hSource hDest hDisjoint

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray}
    {writeOffset readOffset len : Nat}
    (hSource : source.size = 32)
    (hDest : writeOffset + 32 ≤ dest.size)
    (hDisjoint :
      Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
        readOffset len writeOffset 32) :
    (source.write 0 dest writeOffset 32).readWithPadding
        readOffset len =
      dest.readWithPadding readOffset len :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_readWithPadding_write32_eq_of_byteDisjoint
    hSpec hSource hDest hDisjoint

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray}
    {writeOffset idx : Nat}
    (hSource : source.size = 32)
    (hDest : writeOffset + 32 ≤ dest.size)
    (hDisjoint :
      Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
        idx 1 writeOffset 32)
    (hWrittenIdx : idx < (source.write 0 dest writeOffset 32).size)
    (hDestIdx : idx < dest.size) :
    (source.write 0 dest writeOffset 32)[idx]'hWrittenIdx =
      dest[idx]'hDestIdx :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_getElem_eq_of_byteDisjoint
    hSpec hSource hDest hDisjoint hWrittenIdx hDestIdx

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (value : Locals.Word) :
    EvmYul.fromByteArrayBigEndian value.toByteArray = value.toNat :=
  Locals.SourceLowering.StateRel.SpillScratch.word_fromByteArrayBigEndian_toByteArray
    hSpec value

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray} {offset : Nat}
    (hSource : source.size = 32)
    (hDest : offset + 32 ≤ dest.size) :
    (source.write 0 dest offset 32).readWithPadding offset 32 =
      source :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_readWithPadding32_write32_same
    hSpec hSource hDest

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target range.base range.words)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range source (target.mstore (range.word slot) value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.mstore_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target range = true)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range source (target.mstore (range.word slot) value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.mstore_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target range.base range.words)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range source (target.mstore (range.word slot) value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mstore_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target range = true)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range source (target.mstore (range.word slot) value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mstore_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target range.base range.words)
    (hSlot : slot < range.words) :
    ((target.mstore (range.word slot) value).mload
        (range.word slot)).1 =
      value ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source
          ((target.mstore (range.word slot) value).mload
            (range.word slot)).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mload_after_mstore_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target range = true)
    (hSlot : slot < range.words) :
    ((target.mstore (range.word slot) value).mload
        (range.word slot)).1 =
      value ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source
          ((target.mstore (range.word slot) value).mload
            (range.word slot)).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mload_after_mstore_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example {state : Locals.EVMState} {offset value : Locals.Word} :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillReloadCode
            offset value) state =
        .ok final ∧
      final.stack =
        ((state.toMachineState.mstore offset value).mload offset).1 ::
          state.stack ∧
      final.toMachineState =
        ((state.toMachineState.mstore offset value).mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.run_spillReloadCode
    state offset value

example {state : Locals.EVMState} {baseStack : EvmYul.Stack Locals.Word}
    {offset value : Locals.Word} :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            offset) { state with stack := value :: baseStack } =
        .ok final ∧
      final.stack =
        ((state.toMachineState.mstore offset value).mload offset).1 ::
          baseStack ∧
      final.toMachineState =
        ((state.toMachineState.mstore offset value).mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.run_spillTopReloadCode
    state baseStack offset value

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillReloadCode
            (range.word slot) value) target =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillReloadCode_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target.toMachineState range = true)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillReloadCode
            (range.word slot) value) target =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillReloadCode_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillTopReloadCode_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target.toMachineState range = true)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillTopReloadCode_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store target.toMachineState target.stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hSlot : slot < range.words)
    (hStoreMatches :
      ∀ {name : Locals.Name},
        (name,
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            slot) ∈ layout →
          store name = some value) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store final.toMachineState target.stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillTopReloadCode_target_scratch_slot_valueRel
    hSpec hWordBytes hRel hLayout hValues hReady hSlot hStoreMatches

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store target.toMachineState target.stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target.toMachineState range = true)
    (hSlot : slot < range.words)
    (hStoreMatches :
      ∀ {name : Locals.Name},
        (name,
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            slot) ∈ layout →
          store name = some value) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store final.toMachineState target.stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillTopReloadCode_target_scratch_slot_valueRel_of_ready?
    hSpec hWordBytes hRel hLayout hValues hReady hSlot hStoreMatches

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {offset value : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hReadableAfter :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReadable
        (machine.mstore offset value) offset) :
    (machine.mstore offset value).lookupMemory offset = value :=
  Locals.SourceLowering.StateRel.SpillScratch.lookupMemory_mstore_same_of_allocated_readable
    hSpec hWordBytes hAllocated hReadableAfter

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {slot : Nat} {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hSlot : slot < range.words) :
    (machine.mstore (range.word slot) value).lookupMemory
        (range.word slot) =
      value :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.lookupMemory_mstore_range_slot_same
    hSpec hWordBytes hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {slot : Nat} {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hSlot : slot < range.words) :
    ((machine.mstore (range.word slot) value).mload
        (range.word slot)).1 =
      value :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_mstore_range_slot_value
    hSpec hWordBytes hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {writeSlot readSlot : Nat} {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hWriteSlot : writeSlot < range.words)
    (hReadSlot : readSlot < range.words)
    (hNe : readSlot ≠ writeSlot) :
    ((machine.mstore (range.word writeSlot) value).mload
        (range.word readSlot)).1 =
      (machine.mload (range.word readSlot)).1 :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_mstore_range_other_slot_value
    hSpec hWordBytes hReady hWriteSlot hReadSlot hNe

example {machine : EvmYul.MachineState} {base count left right : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hLeft : left < count)
    (hRight : right < count)
    (hLt : left < right) :
    (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base left).toNat + 32 ≤
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base right).toNat :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.scratchWordSlotEndLeSlotStart
    hReady hLeft hRight hLt

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {base count slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordOverwriteRestoreObligation
      machine
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base slot) :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.scratchWordOverwriteRestore
    hSpec hEncoding hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {state : Locals.EVMState} {base count slot : Nat}
    {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        state.toMachineState base count)
    (hSlot : slot < count) :
    ({ state with
        toMachineState :=
          (state.toMachineState.mstore
              (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
                base slot) value).mstore
            (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
              base slot)
            (state.toMachineState.mload
              (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
                base slot)).1 } :
      Locals.EVMState).toSharedState = state.toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.slot_mstore_restore_loaded_evm_shared_eq
    hSpec hEncoding hReady hSlot

example
    {machine : EvmYul.MachineState} {base count slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      (machine.mload
        (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
          base slot)).2
      base count :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_slot
    hReady hSlot

example
    {machine : EvmYul.MachineState} {base count slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
        machine base count = true)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      (machine.mload
        (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
          base slot)).2
      base count = true :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_mload_slot
    hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {base count slot : Nat}
    {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      (machine.mstore
        (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
          base slot) value)
      base count :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mstore_slot
    hSpec hEncoding.size hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {base count slot : Nat}
    {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
        machine base count = true)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      (machine.mstore
        (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
          base slot) value)
      base count = true :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_mstore_slot
    hSpec hEncoding.size hReady hSlot

example {machine : EvmYul.MachineState} {offset value : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset) :
    (machine.mstore offset value).activeWords = machine.activeWords :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_activeWords hScratch

example {machine : EvmYul.MachineState} {offset : Locals.Word} :
    (machine.mload offset).2.activeWords = machine.activeWords ↔
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset :=
  Locals.SourceLowering.StateRel.SpillScratch.mload_activeWords_eq_iff_reserved

example {machine : EvmYul.MachineState} {offset value : Locals.Word} :
    (machine.mstore offset value).activeWords = machine.activeWords ↔
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_activeWords_eq_iff_reserved

example {machine : EvmYul.MachineState} {offset value : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
      (machine.mstore offset value) offset :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_scratch_reserved hScratch

example {machine : EvmYul.MachineState} {offset value : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset)
    (hMemory :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordMemoryRestoreObligation
        machine offset) :
    (machine.mstore offset value).mstore offset (machine.mload offset).1 =
      machine :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_restore_loaded_machine_eq_of_memoryRestore
    hScratch hMemory

example {machine : EvmYul.MachineState} {offset value : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset)
    (hRestore :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordOverwriteRestoreObligation
        machine offset) :
    (machine.mstore offset value).mstore offset (machine.mload offset).1 =
      machine :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_restore_loaded_machine_eq
    hScratch hRestore

example {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset) :
    (machine.mload offset).2 = machine :=
  Locals.SourceLowering.StateRel.SpillScratch.mload_machine_eq hScratch

example {state : Locals.EVMState} {offset : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
        state.toMachineState offset) :
    ({ state with
        toMachineState := (state.toMachineState.mload offset).2 } :
      Locals.EVMState).toSharedState = state.toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.mload_evm_shared_eq hScratch

example {state : Locals.EVMState} {offset : Locals.Word}
    {stack : EvmYul.Stack Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
        state.toMachineState offset) :
    (({ state with
        toMachineState := (state.toMachineState.mload offset).2 } :
      Locals.EVMState).replaceStackAndIncrPC stack).toSharedState =
      state.toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.mload_replaceStackAndIncrPC_shared_eq
    hScratch

example {state : Locals.EVMState} {offset value : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
        state.toMachineState offset)
    (hMemory :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordMemoryRestoreObligation
        state.toMachineState offset) :
    ({ state with
        toMachineState :=
          (state.toMachineState.mstore offset value).mstore offset
            (state.toMachineState.mload offset).1 } :
      Locals.EVMState).toSharedState = state.toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_restore_loaded_evm_shared_eq_of_memoryRestore
    hScratch hMemory

example {state : Locals.EVMState} {offset value : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
        state.toMachineState offset)
    (hRestore :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordOverwriteRestoreObligation
        state.toMachineState offset) :
    ({ state with
        toMachineState :=
          (state.toMachineState.mstore offset value).mstore offset
            (state.toMachineState.mload offset).1 } :
      Locals.EVMState).toSharedState = state.toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_restore_loaded_evm_shared_eq
    hScratch hRestore

example :
    Functions.LiveLayout.Layout.allAccessible? 0
      (List.replicate 17 "dead" ++ ["x"]) ["x"] = false := by
  native_decide

example :
    Functions.LiveLayout.Layout.entryWindowOk?
      (List.replicate 17 "dead" ++ ["x"]) ["x"] = true := by
  native_decide

example {layout live : List Functions.Name}
    (hCheck : Functions.LiveLayout.Layout.entryWindowOk? layout live = true) :
    Functions.LiveLayout.NameSet.allIn?
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live) live = true :=
  Functions.LiveLayout.Layout.entryWindowOk?_allIn_trimDeadPrefix hCheck

example {ctx : Functions.LiveLayout.Ctx} {after : List Functions.Name}
    {body : Functions.Block} {name : Functions.Name}
    (hMem :
      name ∈ Functions.LiveLayout.Block.liveBefore ctx after body) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.block body) :=
  Functions.LiveLayout.LiveBefore.block_body_subset_stmt hMem

example {ctx : Functions.LiveLayout.Ctx} {after : List Functions.Name}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {name : Functions.Name}
    (hMem :
      name ∈ Functions.LiveLayout.Block.liveBefore ctx after body) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.if_ cond body) :=
  Functions.LiveLayout.LiveBefore.if_body_subset_stmt hMem

example {ctx : Functions.LiveLayout.Ctx} {after : List Functions.Name}
    {switchExpr : Functions.Expr 1} {scrutinee : EvmYul.UInt256}
    {cases : List (EvmYul.UInt256 × Functions.Block)}
    {defaultBody : Option Functions.Block} {body : Functions.Block}
    {name : Functions.Name}
    (hSelect :
      Functions.Switch.select scrutinee cases defaultBody = some body)
    (hMem :
      name ∈ Functions.LiveLayout.Block.liveBefore ctx after body) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.switch switchExpr cases defaultBody) :=
  Functions.LiveLayout.LiveBefore.switch_selected_body_subset_stmt
    hSelect hMem

example {ctx : Functions.LiveLayout.Ctx} {after : List Functions.Name}
    {declared name : Functions.Name} {value : Functions.Expr 1}
    (hAfter : name ∈ after)
    (hNe : name ≠ declared) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.let_ declared value) :=
  Functions.LiveLayout.LiveBefore.let_after_of_ne hAfter hNe

example {ctx : Functions.LiveLayout.Ctx} {after env : List Functions.Name}
    {declared name : Functions.Name} {value : Functions.Expr 1}
    (hScoped :
      Functions.Scope.Stmt.Scoped env (Functions.Stmt.let_ declared value))
    (hScope : name ∈ env)
    (hAfter : name ∈ after) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.let_ declared value) :=
  Functions.LiveLayout.LiveBefore.let_after_of_scoped_scope hScoped hScope
    hAfter

example {results : Nat} {layout : List Functions.Name}
    {expr : Functions.Expr results}
    (hCheck : Functions.LiveLayout.ExprAccess.expr? 0 layout expr = true) :
    Locals.SourceLowering.Expr.Accessible layout 0 expr :=
  Functions.LiveLayout.ExprAccess.expr?_sound hCheck

example {layout names : List Functions.Name}
    (hCheck : Functions.LiveLayout.NamesAccess.names? 0 layout names = true)
    {idx : Nat} {name : Functions.Name}
    (hGet : names[idx]? = some name) :
    ∃ layoutIdx,
      layout[layoutIdx]? = some name ∧ idx + layoutIdx + 1 ≤ 16 :=
  by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Functions.LiveLayout.NamesAccess.names?_get?_sound hCheck hGet

example {layout names : List Functions.Name}
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible layout 0 names) :
    Functions.SourceDirect.ReturnValuesRel.Accessible layout 0 names :=
  Functions.LiveLayout.NamesAccess.to_returnValuesAccessible hAccess

example {layout names : List Functions.Name}
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible layout 0 names) :
    names.length ≤ 16 :=
  Functions.LiveLayout.NamesAccess.length_le_16_of_accessible_zero hAccess

example {returns layout : List Functions.Name} {stmt : Functions.Stmt}
    (hCheck :
      Functions.LiveLayout.StmtAccess.accessible? returns layout stmt =
        true) :
    Functions.LiveLayout.StmtAccess.Accessible returns layout stmt :=
  Functions.LiveLayout.StmtAccess.accessible?_sound hCheck

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name} {block : Functions.Block}
    {outLayout : List Functions.Name}
    (hCheck :
      Functions.LiveLayout.Checked.Block.check? returns ctx layout after block =
        some outLayout) :
    Functions.LiveLayout.Checked.Block.Sound returns ctx layout after block
      outLayout :=
  Functions.LiveLayout.Checked.Block.check?_sound hCheck

example {fn : Functions.FunDef}
    (hCheck : Functions.LiveLayout.Checked.FunDef.check? fn = true) :
    ∃ layout,
      Functions.LiveLayout.Checked.Block.Sound fn.returns
        { returns := fn.returns }
        (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body layout ∧
        Functions.LiveLayout.NamesAccess.Accessible layout 0 fn.returns :=
  Functions.LiveLayout.Checked.FunDef.check?_sound hCheck

example {fn : Functions.FunDef} {proc : Locals.Proc}
    (hLower :
      Functions.LiveLayout.Lower.FunDef.toLocalsProc? fn = some proc) :
    ∃ lowerBody layout,
      Functions.LiveLayout.Lower.Block.toLocals? fn.returns
          { returns := fn.returns }
          (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body =
        some (lowerBody, layout) ∧
      Functions.LiveLayout.NamesAccess.Accessible layout 0 fn.returns ∧
      proc =
        { name := fn.name
          argc := fn.params.length
          retc := fn.returns.length
          entryLayout := fn.params.reverse
          body :=
            { stmts :=
                Functions.Lower.initReturns fn.returns ++
                  (lowerBody.stmts ++
                    Functions.Lower.pushReturns fn.returns) } } :=
  Functions.LiveLayout.Lower.FunDef.toLocalsProc?_components hLower

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name} {block : Functions.Block}
    {lowerBlock : Locals.Block} {outLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout)) :
    Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout layout
        lowerBlock.stmts =
      outLayout :=
  Functions.LiveLayout.TargetLayout.Lower.block_toLocals?_layout hLower

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {fuel : Nat} {stmt : Locals.Stmt}
    {state final : Locals.RunState}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel stmt state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx.layout =
      Functions.LiveLayout.TargetLayout.Stmt.regularOutLayout ctx.layout
        stmt :=
  Functions.LiveLayout.TargetLayout.Stmt.run_regular_layout hRun

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {fuel : Nat} {stmt : Locals.Stmt}
    {state final : Locals.RunState}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel stmt state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx =
      ctx.withLayout
        (Functions.LiveLayout.TargetLayout.Stmt.regularOutLayout ctx.layout
          stmt) :=
  Functions.LiveLayout.TargetLayout.Stmt.run_regular_ctx hRun

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {fuel : Nat} {block : Locals.Block}
    {state final : Locals.RunState}
    (hRun :
      Locals.Direct.Block.runOpen program ctx fuel block state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx.layout =
      Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout
        ctx.layout block.stmts :=
  Functions.LiveLayout.TargetLayout.StmtList.block_runOpen_regular_layout
    hRun

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {fuel : Nat} {block : Locals.Block}
    {state final : Locals.RunState}
    (hRun :
      Locals.Direct.Block.runOpen program ctx fuel block state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx =
      ctx.withLayout
        (Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout
          ctx.layout block.stmts) :=
  Functions.LiveLayout.TargetLayout.StmtList.block_runOpen_regular_ctx
    hRun

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name} {block : Functions.Block}
    {lowerBlock : Locals.Block} {outLayout : List Functions.Name}
    {program : Locals.Program} {targetCtx runCtx : Locals.Ctx}
    {fuel : Nat} {state final : Locals.RunState}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout))
    (hCtxLayout : targetCtx.layout = layout)
    (hRun :
      Locals.Direct.Block.runOpen program targetCtx fuel lowerBlock state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx.layout = outLayout :=
  Functions.LiveLayout.TargetLayout.Lower.block_runOpen_regular_layout_of_lower
    hLower hCtxLayout hRun

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name} {block : Functions.Block}
    {lowerBlock : Locals.Block} {outLayout : List Functions.Name}
    {program : Locals.Program} {targetCtx runCtx : Locals.Ctx}
    {fuel : Nat} {state final : Locals.RunState}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout))
    (hCtxLayout : targetCtx.layout = layout)
    (hRun :
      Locals.Direct.Block.runOpen program targetCtx fuel lowerBlock state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx = targetCtx.withLayout outLayout :=
  Functions.LiveLayout.TargetLayout.Lower.block_runOpen_regular_ctx_of_lower
    hLower hCtxLayout hRun

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after outLayout : List Functions.Name} {block : Functions.Block}
    {lowerBlock : Locals.Block}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {program : Locals.Program} {targetCtx : Locals.Ctx}
    {fuel : Nat} {state : Locals.RunState}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout))
    (hCtxLayout : targetCtx.layout = layout)
    (hRun :
      Locals.Direct.Block.runOpen program targetCtx fuel lowerBlock state =
        .ok targetResult) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
      outLayout sourceResult targetResult :=
  Functions.LiveLayout.SourceTarget.block_target_regular_output_layout_of_lower_run
    hLower hCtxLayout hRun

example {outLayout returns : List Functions.Name}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetState : Locals.RunState} {targetCtx : Locals.Ctx}
    (hLayout :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
        outLayout sourceResult
        (Structured.Outcome.regular targetState, targetCtx))
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible outLayout 0 returns) :
    Functions.LiveLayout.NamesAccess.Accessible targetCtx.layout 0 returns :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel.namesAccessible_of_regular
    hLayout hAccess

example {outLayout returns : List Functions.Name}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetState : Locals.RunState} {targetCtx : Locals.Ctx}
    (hLayout :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
        outLayout sourceResult
        (Structured.Outcome.regular targetState, targetCtx))
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible outLayout 0 returns) :
    Functions.SourceDirect.ReturnValuesRel.Accessible targetCtx.layout 0
      returns :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel.returnValuesAccessible_of_regular
    hLayout hAccess

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after outLayout baseLayout : List Functions.Name}
    {block : Functions.Block} {lowerBlock : Locals.Block}
    {retc : Nat} {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {program : Locals.Program} {targetCtx : Locals.Ctx}
    {target : Locals.RunState}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout))
    (hCtxLayout : targetCtx.layout = layout)
    (hResult :
      ∃ targetFuel targetResult,
        Locals.Direct.Block.runOpen program targetCtx targetFuel lowerBlock
            target =
          .ok targetResult ∧
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
          returns hiddenReturns sourceResult targetResult ∧
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRegularLayoutRelTo
          baseLayout sourceResult targetResult) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen program targetCtx targetFuel lowerBlock
          target =
        .ok targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns sourceResult targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRegularLayoutRelTo
        baseLayout sourceResult targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
        outLayout sourceResult targetResult :=
  Functions.LiveLayout.SourceTarget.block_target_result_with_output_layout_of_lower
    hLower hCtxLayout hResult

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {after outLayout baseLayout : List Functions.Name}
    {retc fuel : Nat} {sourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Functions.Block} {lowerBlock : Locals.Block}
    {source : Functions.Source.State} {target : Locals.RunState}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx targetCtx.layout
        after block =
        some (lowerBlock, outLayout))
    (hSourceRun :
      Functions.Source.Block.runOpen prim sourceProgram sourceCtx (fuel + 1)
          block source =
        .ok sourceResult)
    (hNilLayout :
      block.stmts = [] →
        Functions.SourceDirect.CleanupLayoutRel
          (Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout after)
          baseLayout)
    (hStateRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hCtxRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hHead :
      ∀ {stmt rest restLive stmtLive liveLayout prep preparedLayout lowerStmt
          nextLayout lowerRest},
        restLive = Functions.LiveLayout.StmtList.liveBefore ctx after rest →
        stmtLive = Functions.LiveLayout.Stmt.liveBefore ctx restLive stmt →
        liveLayout =
          Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout
            stmtLive →
        Functions.LiveLayout.Prepare.forStmtAboveSuffix? ctx.protectedDepth
          returns liveLayout stmtLive stmt =
          some (prep, preparedLayout) →
        Functions.LiveLayout.Layout.entryWindowOk? preparedLayout stmtLive =
          true →
        Functions.LiveLayout.StmtAccess.accessible? returns preparedLayout
          stmt = true →
        Functions.LiveLayout.Lower.Stmt.toLocals? returns ctx preparedLayout
          restLive stmt =
          some (lowerStmt, nextLayout) →
        Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx nextLayout
          after rest =
          some (lowerRest, outLayout) →
        ∀ {cleaned},
          Functions.SourceDirect.StateRel preparedLayout hiddenReturns source
            cleaned →
          Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
            sourceProgram targetProgram returns retc fuel sourceCtx
            (targetCtx.withLayout preparedLayout)
            hiddenReturns stmt { stmts := lowerStmt } source cleaned)
    (hTail :
      ∀ {stmt rest restLive stmtLive liveLayout prep preparedLayout lowerStmt
          nextLayout lowerRest},
        restLive = Functions.LiveLayout.StmtList.liveBefore ctx after rest →
        stmtLive = Functions.LiveLayout.Stmt.liveBefore ctx restLive stmt →
        liveLayout =
          Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout
            stmtLive →
        Functions.LiveLayout.Prepare.forStmtAboveSuffix? ctx.protectedDepth
          returns liveLayout stmtLive stmt =
          some (prep, preparedLayout) →
        Functions.LiveLayout.Layout.entryWindowOk? preparedLayout stmtLive =
          true →
        Functions.LiveLayout.StmtAccess.accessible? returns preparedLayout
          stmt = true →
        Functions.LiveLayout.Lower.Stmt.toLocals? returns ctx preparedLayout
          restLive stmt =
          some (lowerStmt, nextLayout) →
        Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx nextLayout
          after rest =
          some (lowerRest, outLayout) →
        ∀ {sourceAfter : Functions.Source.State}
          {targetAfter : Locals.RunState}
          {sourceCtxAfter : Functions.Source.Ctx}
          {targetCtxAfter : Locals.Ctx},
          Functions.SourceDirect.StateRel targetCtxAfter.layout hiddenReturns
            sourceAfter targetAfter →
          Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc
            sourceCtxAfter targetCtxAfter →
          Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
            prim sourceProgram targetProgram returns retc fuel sourceCtxAfter
            targetCtxAfter baseLayout hiddenReturns { stmts := rest }
            { stmts := lowerRest } sourceAfter targetAfter) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel lowerBlock
          target =
        .ok targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns sourceResult targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRegularLayoutRelTo
        baseLayout sourceResult targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
        outLayout sourceResult targetResult :=
  Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_output_layout
    hLower hSourceRun hNilLayout hStateRel hCtxRel hHead hTail

example {ctx : Locals.Ctx} {targetDepth : Nat}
    {source : Locals.Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx targetDepth target = .ok cleaned)
    (hRel : Locals.SourceLowering.StateRel ctx.layout source target) :
    Locals.SourceLowering.StateRel
        (ctx.layout.drop (ctx.layout.length - targetDepth)) source cleaned ∧
      cleaned.returns = target.returns :=
  Functions.LiveLayout.Drop.cleanupTo_stateRel_drop hRun hRel

example {ctx : Locals.Ctx} {live : List Functions.Name}
    {source : Locals.Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx
          (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live).length
          target =
        .ok cleaned)
    (hRel : Locals.SourceLowering.StateRel ctx.layout source target) :
    Locals.SourceLowering.StateRel
        (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live) source
        cleaned ∧
      cleaned.returns = target.returns :=
  Functions.LiveLayout.Drop.cleanupTo_trimDeadPrefix_stateRel hRun hRel

example :
    let deadNames : List Functions.Name :=
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7", "d8",
        "d9", "d10", "d11", "d12", "d13", "d14", "d15", "d16"]
    Functions.LiveLayout.Checked.Program.check?
      { functions := []
        body :=
          { stmts :=
              [.let_ "x" Functions.LiveLayout.Examples.lit0] ++
                (deadNames.map fun name =>
                  Functions.Stmt.let_ name
                    Functions.LiveLayout.Examples.lit0) ++
                [Functions.LiveLayout.Examples.popVar "x"] } } = true := by
  native_decide

example :
    (Functions.LiveLayout.Lower.Program.toExpressions?
      Functions.LiveLayout.Examples.manyDeadProgram).isSome = true := by
  native_decide

example :
    (Functions.LiveLayout.Lower.Program.toExpressionsNoInternalCall?
      Functions.LiveLayout.Examples.manyDeadProgram).isSome = true := by
  native_decide

example {program : Functions.Program} {lower : Locals.Program}
    (hLower :
      Functions.LiveLayout.Lower.Program.toLocals? program = some lower) :
    Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.LiveLayout.Lower.Program.toLocals?_checked hLower

example {program : Functions.Program} {lower : Locals.Program}
    (hLower :
      Functions.LiveLayout.Lower.Program.toLocals? program = some lower) :
    ∃ lowerProcs lowerBody bodyLayout,
      Functions.LiveLayout.Lower.FunList.toLocalsProcs? program.functions =
          some lowerProcs ∧
        Functions.LiveLayout.Lower.Block.toLocals? [] {} [] [] program.body =
          some (lowerBody, bodyLayout) ∧
        lower = { procs := lowerProcs, body := lowerBody } :=
  Functions.LiveLayout.Lower.Program.toLocals?_components hLower

example {program : Functions.Program} {lower : Locals.Program}
    (hLower :
      Functions.LiveLayout.Lower.Program.toLocalsNoInternalCall? program =
        some lower) :
    Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.LiveLayout.Lower.Program.toLocalsNoInternalCall?_checked hLower

example {program : Functions.Program} {lower : Locals.Program}
    (hLower :
      Functions.LiveLayout.Lower.Program.toLocalsNoInternalCall? program =
        some lower) :
    Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      ∃ lowerProcs lowerBody bodyLayout,
        Functions.LiveLayout.Lower.FunList.toLocalsProcs?
            program.functions =
          some lowerProcs ∧
          Functions.LiveLayout.Lower.Block.toLocals? [] {} [] []
              program.body =
            some (lowerBody, bodyLayout) ∧
          lower = { procs := lowerProcs, body := lowerBody } :=
  Functions.LiveLayout.Lower.Program.toLocalsNoInternalCall?_components hLower

example {program : Functions.Program} {asm : Assembly.TargetProgram}
    (hCompile :
      Functions.LiveLayout.Lower.Program.compile? program = some asm) :
    Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.LiveLayout.Lower.Program.compile?_checked hCompile

example {program : Functions.Program} {asm : Assembly.TargetProgram}
    (hCompile :
      Functions.LiveLayout.Lower.Program.compileNoInternalCall? program =
        some asm) :
    Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.LiveLayout.Lower.Program.compileNoInternalCall?_checked hCompile

example {program : Functions.Program} {asm : Assembly.Program}
    (hCompile :
      Functions.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    ∃ lower : Expressions.Program,
      Functions.LiveLayout.Lower.Program.toExpressionsNoInternalCall?
          program =
        some lower ∧
        Structured.Preservation.ProcedurePreservation.compileChecked?
          lower.toStructured = some asm :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?_eq_some hCompile

example {program : Functions.Program} {asm : Assembly.Program}
    (hCompile :
      Functions.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?_liveGate hCompile

example {program : Functions.Program} {asm : Assembly.Program}
    (hNoCallCreate : program.usesCallCreate = false)
    (hCompile :
      Functions.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?_noCallCreate
    hNoCallCreate hCompile

example {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      Objects.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    Functions.Source.Program.compileLiveNoInternalCallChecked?
        program.toFunctions =
      some asm := by
  simpa [Objects.Source.Program.compileLiveNoInternalCallChecked?]
    using hCompile

example {program : Objects.Program} {asm : Assembly.Program}
    (hNoCallCreate : program.toFunctions.usesCallCreate = false)
    (hCompile :
      Objects.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Objects.Source.Program.compileLiveNoInternalCallChecked?_noCallCreate
    hNoCallCreate hCompile

example {layout live : List Functions.Name} {name : Functions.Name}
    (hMem :
      name ∈ Functions.LiveLayout.Layout.trimDeadPrefix layout live) :
    name ∈ layout :=
  Functions.LiveLayout.Layout.mem_trimDeadPrefix hMem

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel : Functions.SourceDirect.CtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.of_ctxRel hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel : Functions.SourceDirect.CtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      target :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.of_ctxRel hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc
      source.withoutLoopControl target.withoutLoopControl :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.withoutLoopControl
    hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} (names : List Functions.Name)
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc
      { source with scope := names ++ source.scope }
      (target.withLayout (names ++ target.layout)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.withScopePrepend
    names hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {layout : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hSubset :
      ∀ {name : Functions.Name}, name ∈ layout → name ∈ source.scope)
    (hCleanupLayout :
      Functions.SourceDirect.CleanupLayoutRel layout target.layout) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout layout) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.withLayout_of_source_subset_cleanupLayoutRel
    hRel hSubset hCleanupLayout

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.withLoopControl_self
    hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {live : Functions.LiveLayout.Ctx}
    {keepLive : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreakLiveSubset :
      ∀ {name : Functions.Name}, name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      ∀ {name : Functions.Name},
        name ∈ live.continueLive → name ∈ keepLive) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout
        (Functions.LiveLayout.Layout.trimDeadPrefix target.layout keepLive)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.trimDeadPrefix_of_handler_live_subset
    hRel hControl hBreakLiveSubset hContinueLiveSubset

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      source target sourceOutcome :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.of_cleanupRel
    hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.ctxRel hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Functions.Source.Outcome}
    {breakScope : List Functions.Name} {targetDepth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hMode : sourceOutcome.mode = .brk)
    (hBreak : source.breakScope? = some breakScope)
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel target.layout
      targetDepth breakScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.breakCleanup
    hRel hMode hBreak hTargetDepth

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Functions.Source.Outcome}
    {continueScope : List Functions.Name} {targetDepth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hMode : sourceOutcome.mode = .cont)
    (hContinue : source.continueScope? = some continueScope)
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel target.layout
      targetDepth continueScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.continueCleanup
    hRel hMode hContinue hTargetDepth

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {live : Functions.LiveLayout.Ctx}
    {keepLive : List Functions.Name}
    {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreakLiveSubset :
      sourceOutcome.mode = .brk →
        ∀ {name : Functions.Name},
          name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      sourceOutcome.mode = .cont →
        ∀ {name : Functions.Name},
          name ∈ live.continueLive → name ∈ keepLive) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      source
      (target.withLayout
        (Functions.LiveLayout.Layout.trimDeadPrefix target.layout keepLive))
      sourceOutcome :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.trimDeadPrefix_of_mode_live_subset
    hRel hControl hBreakLiveSubset hContinueLiveSubset

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {live : Functions.LiveLayout.Ctx}
    {keepLive : List Functions.Name}
    {outerOutcome sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target outerOutcome)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreakMode :
      sourceOutcome.mode = .brk → outerOutcome.mode = .brk)
    (hContinueMode :
      sourceOutcome.mode = .cont → outerOutcome.mode = .cont)
    (hBreakLiveSubset :
      sourceOutcome.mode = .brk →
        ∀ {name : Functions.Name},
          name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      sourceOutcome.mode = .cont →
        ∀ {name : Functions.Name},
          name ∈ live.continueLive → name ∈ keepLive) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      source
      (target.withLayout
        (Functions.LiveLayout.Layout.trimDeadPrefix target.layout keepLive))
      sourceOutcome :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.trimDeadPrefix_of_outer_mode_live_subset
    hRel hControl hBreakMode hContinueMode hBreakLiveSubset
    hContinueLiveSubset

example {retc protectedDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {returns live : List Functions.Name} {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    {sourceOutcome : Functions.Source.Outcome}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          target.layout live stmt =
        some (prep, finalLayout))
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hBreakDepth :
      sourceOutcome.mode = .brk →
        ∀ {depth : Nat}, target.breakDepth? = some depth →
          depth ≤ protectedDepth)
    (hContinueDepth :
      sourceOutcome.mode = .cont →
        ∀ {depth : Nat}, target.continueDepth? = some depth →
          depth ≤ protectedDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      source (target.withLayout finalLayout) sourceOutcome :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.forStmtAboveSuffix_of_mode_depth_bounds
    hPrepare hRel hBreakDepth hContinueDepth

example {retc targetDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {live : Functions.LiveLayout.Ctx}
    {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hMode : sourceOutcome.mode = .brk)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.breakDepth_le_protectedDepth
    hRel hMode hControl hNoDup hTargetDepth

example {retc targetDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {live : Functions.LiveLayout.Ctx}
    {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hMode : sourceOutcome.mode = .cont)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.continueDepth_le_protectedDepth
    hRel hMode hControl hNoDup hTargetDepth

example {live : Functions.LiveLayout.Ctx} :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      Functions.Source.Ctx.initial :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.initial

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {breakLive continueLive breakScope continueScope :
      List Functions.Name}
    (hBreak :
      Functions.SourceDirect.SameScope breakLive breakScope)
    (hContinue :
      Functions.SourceDirect.SameScope continueLive continueScope)
    (hBreakScope :
      ∀ name, name ∈ breakScope → name ∈ source.scope)
    (hContinueScope :
      ∀ name, name ∈ continueScope → name ∈ source.scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel
      (live.withLoop breakLive continueLive)
      (source.withLoopControl breakScope continueScope) :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.withLoop_sameScope
    hBreak hContinue hBreakScope hContinueScope

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {breakLive continueLive : List Functions.Name}
    (hBreak :
      Functions.SourceDirect.SameScope breakLive source.scope)
    (hContinue :
      Functions.SourceDirect.SameScope continueLive source.scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel
      (live.withLoop breakLive continueLive)
      (source.withLoopControl source.scope source.scope) :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.withLoop_self
    hBreak hContinue

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx} :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      source.withoutLoopControl :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.withoutLoopControl

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    (names : List Functions.Name)
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      { source with scope := names ++ source.scope } :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.withScopePrepend
    names hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {program : Functions.Program} {live : Functions.LiveLayout.Ctx}
    {source sourceOut : Functions.Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {state sourceAfter : Functions.Source.State}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source)
    (hRun :
      Functions.Source.Stmt.run prim program source fuel stmt state =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceOut)) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      sourceOut :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.stmt_regular
    hRel hRun

example {prim : Functions.Source.PrimitiveSemantics}
    {program : Functions.Program} {live : Functions.LiveLayout.Ctx}
    {source sourceOut : Functions.Source.Ctx} {fuel : Nat}
    {block : Functions.Block} {state sourceAfter : Functions.Source.State}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source)
    (hRun :
      Functions.Source.Block.runOpen prim program source fuel block state =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceOut)) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      sourceOut :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.block_regular
    hRel hRun

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {after : List Functions.Name} {declared : Functions.Name}
    {value : Functions.Expr 1} {breakScope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source)
    (hBreak : source.breakScope? = some breakScope)
    (hScoped :
      Functions.Scope.Stmt.Scoped source.scope
        (Functions.Stmt.let_ declared value))
    (hAfter :
      ∀ {name : Functions.Name}, name ∈ live.breakLive → name ∈ after) :
    ∀ {name : Functions.Name}, name ∈ live.breakLive →
      name ∈
        Functions.LiveLayout.Stmt.liveBefore live after
          (Functions.Stmt.let_ declared value) :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.breakLive_subset_let_liveBefore_of_scoped
    hRel hBreak hScoped hAfter

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {after : List Functions.Name} {declared : Functions.Name}
    {value : Functions.Expr 1} {continueScope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source)
    (hContinue : source.continueScope? = some continueScope)
    (hScoped :
      Functions.Scope.Stmt.Scoped source.scope
        (Functions.Stmt.let_ declared value))
    (hAfter :
      ∀ {name : Functions.Name}, name ∈ live.continueLive → name ∈ after) :
    ∀ {name : Functions.Name}, name ∈ live.continueLive →
      name ∈
        Functions.LiveLayout.Stmt.liveBefore live after
          (Functions.Stmt.let_ declared value) :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.continueLive_subset_let_liveBefore_of_scoped
    hRel hContinue hScoped hAfter

example {env : List Functions.Name} {value : EvmYul.UInt256}
    {cases : List (EvmYul.UInt256 × Functions.Block)}
    {defaultBody : Option Functions.Block} {body : Functions.Block}
    (hCases : Functions.Scope.CaseList.Scoped env cases)
    (hDefault : Functions.Scope.Default.Scoped env defaultBody)
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = some body) :
    Functions.Scope.Block.Scoped env body :=
  Functions.LiveLayout.SourceScoped.blockScoped_of_source_select_some
    hCases hDefault hSelect

example {env : List Functions.Name} {value : EvmYul.UInt256}
    {scrutinee : Functions.Expr 1}
    {cases : List (EvmYul.UInt256 × Functions.Block)}
    {defaultBody : Option Functions.Block} {body : Functions.Block}
    (hScoped :
      Functions.Scope.Stmt.Scoped env
        (Functions.Stmt.switch scrutinee cases defaultBody))
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = some body) :
    Functions.Scope.Block.Scoped env body :=
  Functions.LiveLayout.SourceScoped.blockScoped_of_switch_select_some
    hScoped hSelect

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {live : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source
      (target.withLayout
        (Functions.LiveLayout.Layout.trimDeadPrefix target.layout live)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.cleanupTo_trimDeadPrefix
    hRel

example {layout scope : List Functions.Name}
    (hRel : Functions.SourceDirect.CleanupScopeRel layout scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout
      scope.length scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.of_cleanupScope
    hRel

example {layout scope : List Functions.Name} {depth : Nat}
    {name : Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (name :: layout) depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.cons hRel

example {layout scope added : List Functions.Name} {depth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (added ++ layout) depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.prepend added
    hRel

example {layout base scope : List Functions.Name} {depth : Nat}
    (hLayout :
      Functions.SourceDirect.CleanupLayoutRel layout base)
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel base depth
        scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
      scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.of_cleanupLayoutRel
    hLayout hRel

example {layout promoted scope : List Functions.Name} {depth idx : Nat}
    {name : Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        scope)
    (hPromote :
      Functions.LiveLayout.Layout.promoteName? layout name =
        some (promoted, idx))
    (hIdx : idx < layout.length - depth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel promoted depth
      scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.promoteName_of_idx_lt_suffix
    hRel hPromote hIdx

example {layout live scope : List Functions.Name} {depth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        scope)
    (hKeep :
      ∀ {name : Functions.Name},
        name ∈ layout.drop (layout.length - depth) → name ∈ live) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live) depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.trimDeadPrefix_of_keep
    hRel hKeep

example {layout scope : List Functions.Name}
    (hSubset : ∀ {name : Functions.Name}, name ∈ layout → name ∈ scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout
      layout.length scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.full_layout
    hSubset

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {scope : List Functions.Name} {depth : Nat}
    (hRel : Functions.SourceDirect.CtxRel retc source target)
    (hBreak : source.breakScope? = some scope)
    (hTargetDepth : target.breakDepth? = some depth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel target.layout
      depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.break_of_ctxRel
    hRel hBreak hTargetDepth

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {scope : List Functions.Name} {depth : Nat}
    (hRel : Functions.SourceDirect.CtxRel retc source target)
    (hContinue : source.continueScope? = some scope)
    (hTargetDepth : target.continueDepth? = some depth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel target.layout
      depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.continue_of_ctxRel
    hRel hContinue hTargetDepth

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {scope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target)
    (hBreak : source.breakScope? = some scope) :
    ∃ depth, target.breakDepth? = some depth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.breakDepth_some
    hRel hBreak

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {scope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target)
    (hContinue : source.continueScope? = some scope) :
    ∃ depth, target.continueDepth? = some depth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.continueDepth_some
    hRel hContinue

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.withLoopControl_self
    hRel

example {layout live scope : List Functions.Name}
    (hNoDup : layout.Nodup)
    (hCleanup :
      Functions.SourceDirect.CleanupScopeRel layout scope)
    (hSame :
      Functions.SourceDirect.SameScope live scope) :
    Functions.SourceDirect.CleanupScopeRel
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live) scope :=
  Functions.LiveLayout.Layout.cleanupScope_trimDeadPrefix_of_sameScope
    hNoDup hCleanup hSame

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {breakLive continueLive breakScope continueScope :
      List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreak :
      Functions.SourceDirect.SameScope breakLive breakScope)
    (hContinue :
      Functions.SourceDirect.SameScope continueLive continueScope) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel
      (live.withLoop breakLive continueLive)
      (source.withLoopControl breakScope continueScope) :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.withLoop
    hRel hBreak hContinue

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {layout breakScope : List Functions.Name} {depth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreak : source.breakScope? = some breakScope)
    (hCleanup :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        breakScope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live.breakLive) depth
      breakScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.breakCleanup_trimDeadPrefix
    hRel hBreak hCleanup

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {layout continueScope : List Functions.Name} {depth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hContinue : source.continueScope? = some continueScope)
    (hCleanup :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        continueScope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live.continueLive)
      depth continueScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.continueCleanup_trimDeadPrefix
    hRel hContinue hCleanup

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {returns leaveScope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hReturns : live.returns = returns)
    (hLeave : source.leaveScope? = some leaveScope) :
    ∀ name, name ∈ returns → name ∈ leaveScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.returnScope_of_returns_eq
    hRel hReturns hLeave

example (fn : Functions.FunDef) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel
      { returns := fn.returns }
      (Functions.SourceDirect.FunDef.sourceBodyCtx fn) :=
  Functions.LiveLayout.SourceDirectBridge.FunDef.liveControlRel_bodyCtx fn

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel live
      source.withoutLoopControl :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.withoutLoopControl
    hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {program : Functions.Program} {live : Functions.LiveLayout.Ctx}
    {source sourceOut : Functions.Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {state sourceAfter : Functions.Source.State}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hRun :
      Functions.Source.Stmt.run prim program source fuel stmt state =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceOut)) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel live sourceOut :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.stmt_regular
    hRel hRun

example {prim : Functions.Source.PrimitiveSemantics}
    {program : Functions.Program} {live : Functions.LiveLayout.Ctx}
    {source sourceOut : Functions.Source.Ctx} {fuel : Nat}
    {block : Functions.Block} {state sourceAfter : Functions.Source.State}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hRun :
      Functions.Source.Block.runOpen prim program source fuel block state =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceOut)) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel live sourceOut :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.block_regular
    hRel hRun

example (fn : Functions.FunDef) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel fn.returns.length
      (Functions.SourceDirect.FunDef.sourceBodyCtx fn)
      (Functions.SourceDirect.FunDef.targetBodyCtx fn) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.bodyCtx fn

example (fn : Functions.FunDef) :
    ∀ {breakScope targetDepth},
      (Functions.SourceDirect.FunDef.sourceBodyCtx fn).breakScope? =
        some breakScope →
      (Functions.SourceDirect.FunDef.targetBodyCtx fn).breakDepth? =
        some targetDepth →
        Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
          (Functions.SourceDirect.FunDef.targetBodyCtx fn).layout targetDepth
          breakScope :=
  Functions.LiveLayout.SourceDirectBridge.FunDef.bodyCtx_breakCleanupScope fn

example (fn : Functions.FunDef) :
    ∀ {continueScope targetDepth},
      (Functions.SourceDirect.FunDef.sourceBodyCtx fn).continueScope? =
        some continueScope →
      (Functions.SourceDirect.FunDef.targetBodyCtx fn).continueDepth? =
        some targetDepth →
        Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
          (Functions.SourceDirect.FunDef.targetBodyCtx fn).layout targetDepth
          continueScope :=
  Functions.LiveLayout.SourceDirectBridge.FunDef.bodyCtx_continueCleanupScope fn

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      Functions.SourceDirect.StmtRunResultRel retc returns hiddenReturns
        sourceResult targetResult) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel retc returns
      hiddenReturns sourceResult targetResult :=
  Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel.of_sourceDirect
    hRel

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Functions.Source.Outcome}
    {targetOutcome : Locals.Outcome}
    {sourceCtx stmtSourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel retc returns
        hiddenReturns (sourceOutcome, stmtSourceCtx)
        (targetOutcome, targetCtx))
    (hSourceCtx : stmtSourceCtx = sourceCtx)
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc returns
      hiddenReturns (sourceOutcome, sourceCtx) (targetOutcome, targetCtx) :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel.of_stmt_nonregular
    hRel hSourceCtx hNonregular

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns sourceResult targetResult) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceResult.2
      targetResult.2 :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel.ctxRel hRel

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns sourceResult targetResult)
    (hNotBreak : sourceResult.1.mode ≠ .brk)
    (hNotContinue : sourceResult.1.mode ≠ .cont) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      sourceResult.2 targetResult.2 sourceResult.1 :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel.outcomeCleanup_of_not_break_continue
    hRel hNotBreak hNotContinue

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunResultRel.to_liveStmtRunResultRel
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunResultRel.to_stmtOutcomeRel_of_target_layout
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenResultRel.to_liveBlockOpenResultRel
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenResultRel.of_liveLoopStmtRunResultRel
  trivial

example {ctx : Locals.Ctx} {live : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx
          (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live).length
          target =
        .ok cleaned)
    (hRel :
      Functions.SourceDirect.StateRel ctx.layout hiddenReturns source target) :
    Functions.SourceDirect.StateRel
      (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live)
      hiddenReturns source cleaned :=
  Functions.LiveLayout.SourceDirectBridge.stateRel_cleanupTo_trimDeadPrefix
    hRun hRel

example {program : Locals.Program}
    {ctx midCtx : Locals.Ctx} {fuel : Nat} {stmt : Locals.Stmt}
    {state mid : Locals.RunState}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel stmt state =
        .ok (Structured.Outcome.regular mid, midCtx)) :
    ∃ blockFuel,
      Locals.Direct.Block.runOpen program ctx blockFuel { stmts := [stmt] }
        state =
        .ok (Structured.Outcome.regular mid, midCtx) :=
  Functions.LiveLayout.Target.runOpen_singleton_regular_exists hRun

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {live : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {tail : List Locals.Stmt} {outcome : Locals.Outcome}
    (hRel :
      Functions.SourceDirect.StateRel ctx.layout hiddenReturns source target)
    (hTail :
      ∀ {cleaned},
        Functions.SourceDirect.StateRel
          (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live)
          hiddenReturns source cleaned →
        ∃ tailFuel,
          Locals.Direct.Block.runOpen program
            (ctx.withLayout
              (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live))
            tailFuel { stmts := tail } cleaned =
            .ok (outcome, runCtx)) :
    ∃ blockFuel,
      Locals.Direct.Block.runOpen program ctx blockFuel
        { stmts :=
            Functions.LiveLayout.Lower.cleanupToLive ctx.layout live :: tail }
        target =
        .ok (outcome, runCtx) :=
  Functions.LiveLayout.Target.cleanupToLive_prefix_runOpen_exists hRel hTail

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx sourceCtxAfter : Functions.Source.Ctx}
    {targetCtx targetCtxAfter : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {targetStmtBlock targetRestBlock : Locals.Block}
    {source sourceAfter : Functions.Source.State}
    {target targetAfter : Locals.RunState}
    {stmtTargetFuel : Nat}
    (hSourceStmt :
      Functions.Source.Stmt.run prim sourceProgram sourceCtx fuel stmt source =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceCtxAfter))
    (hTargetStmt :
      Locals.Direct.Block.runOpen targetProgram targetCtx stmtTargetFuel
        targetStmtBlock target =
        .ok (Structured.Outcome.regular targetAfter, targetCtxAfter))
    (hRest :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
        sourceProgram targetProgram returns retc fuel sourceCtxAfter
        targetCtxAfter hiddenReturns { stmts := rest } targetRestBlock
        sourceAfter targetAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns { stmts := stmt :: rest }
      { stmts := targetStmtBlock.stmts ++ targetRestBlock.stmts } source
      target :=
  Functions.LiveLayout.SourceTarget.blockOpen_cons_regular_runBridge_of_parts
    hSourceStmt hTargetStmt hRest

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx stmtSourceCtx : Functions.Source.Ctx}
    {targetCtx targetRunCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {targetStmtBlock : Locals.Block} {targetTail : List Locals.Stmt}
    {source : Functions.Source.State} {target : Locals.RunState}
    {sourceOutcome : Functions.Source.Outcome}
    {targetOutcome : Locals.Outcome}
    {stmtTargetFuel : Nat}
    (hSourceStmt :
      Functions.Source.Stmt.run prim sourceProgram sourceCtx fuel stmt source =
        .ok (sourceOutcome, stmtSourceCtx))
    (hSourceCtx : stmtSourceCtx = sourceCtx)
    (hNonregular : sourceOutcome.mode ≠ .regular)
    (hTargetStmt :
      Locals.Direct.Block.runOpen targetProgram targetCtx stmtTargetFuel
        targetStmtBlock target =
        .ok (targetOutcome, targetRunCtx))
    (hStmtRel :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel retc returns
        hiddenReturns (sourceOutcome, stmtSourceCtx)
        (targetOutcome, targetRunCtx)) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns { stmts := stmt :: rest }
      { stmts := targetStmtBlock.stmts ++ targetTail } source target :=
  Functions.LiveLayout.SourceTarget.blockOpen_cons_nonregular_runBridge_of_parts
    hSourceStmt hSourceCtx hNonregular hTargetStmt hStmtRel

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {lowerStmts : List Locals.Stmt} {outLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx layout after
        (stmt :: rest) = some (lowerStmts, outLayout)) :
    ∃ restLive stmtLive liveLayout,
      ∃ (prep : List Locals.Stmt),
      ∃ preparedLayout lowerStmt nextLayout lowerRest,
      restLive =
          Functions.LiveLayout.StmtList.liveBefore ctx after rest ∧
        stmtLive =
          Functions.LiveLayout.Stmt.liveBefore ctx restLive stmt ∧
        liveLayout =
          Functions.LiveLayout.Layout.trimDeadPrefix layout stmtLive ∧
        Functions.LiveLayout.Prepare.forStmtAboveSuffix? ctx.protectedDepth
          returns liveLayout stmtLive stmt =
          some (prep, preparedLayout) ∧
        Functions.LiveLayout.Layout.entryWindowOk? preparedLayout stmtLive =
          true ∧
        Functions.LiveLayout.StmtAccess.accessible? returns
          preparedLayout stmt = true ∧
        Functions.LiveLayout.Lower.Stmt.toLocals? returns ctx
          preparedLayout restLive stmt =
            some (lowerStmt, nextLayout) ∧
        Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx nextLayout
          after rest =
            some (lowerRest, outLayout) ∧
        lowerStmts =
          Functions.LiveLayout.Lower.cleanupToLive layout stmtLive ::
            (prep ++ (lowerStmt ++ lowerRest)) :=
  Functions.LiveLayout.Lower.StmtList.toLocals?_cons_components hLower

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {lowerStmts : List Locals.Stmt} {outLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx layout after
        (stmt :: rest) = some (lowerStmts, outLayout)) :
    ∃ restLive stmtLive liveLayout,
      ∃ (prep : List Locals.Stmt),
      ∃ (preparedLayout : List Functions.Name),
      restLive =
          Functions.LiveLayout.StmtList.liveBefore ctx after rest ∧
        stmtLive =
          Functions.LiveLayout.Stmt.liveBefore ctx restLive stmt ∧
        liveLayout =
          Functions.LiveLayout.Layout.trimDeadPrefix layout stmtLive ∧
        Functions.LiveLayout.Prepare.forStmtAboveSuffix? ctx.protectedDepth
          returns liveLayout stmtLive stmt =
            some (prep, preparedLayout) ∧
        Functions.LiveLayout.Layout.entryWindowOk? preparedLayout stmtLive =
          true :=
  by
    rcases Functions.LiveLayout.Lower.StmtList.toLocals?_cons_components
        hLower with
      ⟨restLive, stmtLive, liveLayout, prep, preparedLayout, lowerStmt,
        nextLayout, lowerRest, hRestLive, hStmtLive, hLiveLayout, hPrepare,
        hEntry, _hAccess, _hLowerStmt, _hLowerRest, _hLowerStmts⟩
    exact ⟨restLive, stmtLive, liveLayout, prep, preparedLayout, hRestLive,
      hStmtLive, hLiveLayout, hPrepare, hEntry⟩

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name}
    {init post body : Functions.Block} {cond : Functions.Expr 1}
    {lowerStmt : List Locals.Stmt} {outLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns ctx layout after
        (.for_ init cond post body) = some (lowerStmt, outLayout)) :
    let loopMentioned :=
      Functions.LiveLayout.NameSet.unions
        [Functions.LiveLayout.Reads.expr cond,
          Functions.LiveLayout.Reads.block post,
          Functions.LiveLayout.Reads.block body, after]
    let postLive := Functions.LiveLayout.Block.liveBefore ctx loopMentioned post
    let bodyCtx := ctx.withLoop after postLive
    let bodyLive :=
      Functions.LiveLayout.Block.liveBefore bodyCtx postLive body
    let loopLive :=
      Functions.LiveLayout.NameSet.unions
        [Functions.LiveLayout.Reads.expr cond, after, postLive, bodyLive]
    let initAfter := Functions.LiveLayout.NameSet.union loopLive layout
    ∃ lowerInit loopLayout lowerPost postLayout lowerBody bodyLayout,
      Functions.LiveLayout.Lower.Block.toLocals? returns
          (ctx.withProtectedLayout layout) layout initAfter init =
        some (lowerInit, loopLayout) ∧
      Functions.LiveLayout.ExprAccess.expr? 0 loopLayout cond = true ∧
      let postAfter :=
        Functions.LiveLayout.Checked.scopedAfter loopLayout loopMentioned
      let bodyAfter :=
        Functions.LiveLayout.Checked.scopedAfter loopLayout postLive
      let postCtx := ctx.withProtectedLayout loopLayout
      let bodyCheckCtx :=
        (ctx.withLoop
          (Functions.LiveLayout.Checked.scopedAfter loopLayout after)
          bodyAfter).withProtectedLayout loopLayout
      Functions.LiveLayout.Lower.Block.toLocals? returns postCtx loopLayout
          postAfter post =
        some (lowerPost, postLayout) ∧
      Functions.LiveLayout.Lower.Block.toLocals? returns bodyCheckCtx
          loopLayout bodyAfter body =
        some (lowerBody, bodyLayout) ∧
      lowerStmt =
        [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] ∧
      outLayout = layout :=
  Functions.LiveLayout.Lower.ForLowering.components_of_toLocals? hLower

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {targetOutcome : Locals.Outcome}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel retc returns
        hiddenReturns
        (Functions.Source.Outcome.regular source, sourceCtx)
        (targetOutcome, targetCtx)) :
    ∃ target,
      targetOutcome = Structured.Outcome.regular target ∧
        Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
          target ∧
        Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
          targetCtx :=
  Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel.source_regular_target_regular
    hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {name : Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc
      { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.withScopeCons hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} (names : List Functions.Name)
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc
      { source with scope := names ++ source.scope }
      (target.withLayout (names ++ target.layout)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.withScopePrepend names
    hRel

example {program : Locals.Program} {ctx : Locals.Ctx}
    {fuel : Nat} {name : Functions.Name} {expr : Locals.Expr 1}
    {state targetAfter : Locals.RunState}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel (.assign name expr) state =
        .ok (Structured.Outcome.regular targetAfter, ctx)) :
    targetAfter.returns = state.returns :=
  Functions.LiveLayout.SourceTarget.Target.assign_returns hRun

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterExpr : Functions.Source.State}
    {target : Locals.RunState}
    {expr : Locals.Expr 0} {values : List EvmYul.UInt256}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEval :
      Functions.Source.Expr.eval prim expr source =
        .ok (sourceAfterExpr, values)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.expr expr) { stmts := [Locals.Stmt.expr expr] }
      source target :=
  Functions.LiveLayout.SourceTarget.expr_liveStmtRunBridge hPrim hCtx hNoDup
    hOwned hAccess hRel hEval

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterValue : Functions.Source.State}
    {target : Locals.RunState}
    {name : Functions.Name} {value : EvmYul.UInt256}
    {expr : Locals.Expr 1}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim expr source =
        .ok (sourceAfterValue, value)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.let_ name expr)
      { stmts := [Locals.Stmt.let_ name expr] } source target :=
  Functions.LiveLayout.SourceTarget.let_liveStmtRunBridge hPrim hCtx hNoDup
    hOwned hAccess hFresh hRel hEvalOne

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterValue : Functions.Source.State}
    {target : Locals.RunState}
    {name : Functions.Name} {idx : Nat} {value : EvmYul.UInt256}
    {expr : Locals.Expr 1}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hName : targetCtx.layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim expr source =
        .ok (sourceAfterValue, value)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.assign name expr)
      { stmts := [Locals.Stmt.assign name expr] } source target :=
  Functions.LiveLayout.SourceTarget.assign_liveStmtRunBridge hPrim hCtx
    hNoDup hName hBound hOwned hAccess hRel hEvalOne

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterExpr : Functions.Source.State}
    {target : Locals.RunState}
    {expr : Locals.Expr 0} {values : List EvmYul.UInt256}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.expr expr) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEval :
      Functions.Source.Expr.eval prim expr source =
        .ok (sourceAfterExpr, values)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.expr expr) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.expr_liveStmtRunBridge_of_lower hPrim
    hLower hCtx hNoDup hOwned hAccess hRel hEval

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterValue : Functions.Source.State}
    {target : Locals.RunState}
    {name : Functions.Name} {value : EvmYul.UInt256}
    {expr : Locals.Expr 1}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.let_ name expr) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim expr source =
        .ok (sourceAfterValue, value)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.let_ name expr) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.let_liveStmtRunBridge_of_lower hPrim
    hLower hCtx hNoDup hOwned hAccess hFresh hRel hEvalOne

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterValue : Functions.Source.State}
    {target : Locals.RunState}
    {name : Functions.Name} {value : EvmYul.UInt256}
    {expr : Locals.Expr 1}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.assign name expr) =
        some (lowerStmt, nextLayout))
    (hAccessCheck :
      Functions.LiveLayout.StmtAccess.accessible? returns targetCtx.layout
          (.assign name expr) =
        true)
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim expr source =
        .ok (sourceAfterValue, value)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.assign name expr) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.assign_liveStmtRunBridge_of_lower hPrim
    hLower hAccessCheck hCtx hNoDup hOwned hRel hEvalOne

example {program : Locals.Program} {ctx : Locals.Ctx}
    {fuel : Nat} {stmt : Locals.Stmt}
    {state : Locals.RunState} {outcome : Locals.Outcome}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel stmt state = .ok (outcome, ctx))
    (hNonregular : outcome.mode ≠ .regular) :
    ∃ blockFuel,
      Locals.Direct.Block.runOpen program ctx blockFuel { stmts := [stmt] }
        state =
        .ok (outcome, ctx) :=
  Functions.LiveLayout.Target.runOpen_singleton_nonregular_exists hRun
    hNonregular

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {kind : Assembly.HaltKind}
    {sharedAfter : EvmYul.SharedState .EVM}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hTerminal : prim.terminal kind source.shared [] = .ok sharedAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.terminal kind)
      { stmts := [Locals.Stmt.terminal kind] } source target :=
  Functions.LiveLayout.SourceTarget.terminal_liveStmtRunBridge hPrim hCtx hRel
    hTerminal

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {kind : Assembly.HaltKind}
    {sharedAfter : EvmYul.SharedState .EVM}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.terminal kind) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hTerminal : prim.terminal kind source.shared [] = .ok sharedAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.terminal kind) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.terminal_liveStmtRunBridge_of_lower hPrim
    hLower hCtx hRel hTerminal

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterArgs : Functions.Source.State}
    {target : Locals.RunState}
    {kind : Assembly.HaltKind} {args : Locals.ExprSeq kind.argCount}
    {values : List EvmYul.UInt256}
    {sharedAfter : EvmYul.SharedState .EVM}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.terminalArgs kind args) =
        some (lowerStmt, nextLayout))
    (hAccessCheck :
      Functions.LiveLayout.StmtAccess.accessible? returns targetCtx.layout
          (.terminalArgs kind args) =
        true)
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.ExprSeq.SourceOwned args)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalArgs :
      Locals.Source.Expr.ExprSeq.eval prim args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      prim.terminal kind sourceAfterArgs.shared values = .ok sharedAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.terminalArgs kind args) { stmts := lowerStmt } source
      target :=
  Functions.LiveLayout.SourceTarget.terminalArgs_liveStmtRunBridge_of_lower
    hPrim hLower hAccessCheck hCtx hNoDup hOwned hRel hEvalArgs hTerminal

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {breakScope : List Functions.Name}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBreak : sourceCtx.breakScope? = some breakScope)
    (hCleanupScope :
      ∀ {targetDepth},
        targetCtx.breakDepth? = some targetDepth →
          Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
            targetCtx.layout targetDepth breakScope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .brk { stmts := [Locals.Stmt.brk] } source target :=
  Functions.LiveLayout.SourceTarget.brk_liveStmtRunBridge
    hCtx hBreak hCleanupScope hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {breakScope : List Functions.Name}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after .brk =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBreak : sourceCtx.breakScope? = some breakScope)
    (hCleanupScope :
      ∀ {targetDepth},
        targetCtx.breakDepth? = some targetDepth →
          Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
            targetCtx.layout targetDepth breakScope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .brk { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.brk_liveStmtRunBridge_of_lower
    hLower hCtx hBreak hCleanupScope hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {continueScope : List Functions.Name}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hContinue : sourceCtx.continueScope? = some continueScope)
    (hCleanupScope :
      ∀ {targetDepth},
        targetCtx.continueDepth? = some targetDepth →
          Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
            targetCtx.layout targetDepth continueScope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .cont { stmts := [Locals.Stmt.cont] } source target :=
  Functions.LiveLayout.SourceTarget.cont_liveStmtRunBridge
    hCtx hContinue hCleanupScope hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {continueScope : List Functions.Name}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after .cont =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hContinue : sourceCtx.continueScope? = some continueScope)
    (hCleanupScope :
      ∀ {targetDepth},
        targetCtx.continueDepth? = some targetDepth →
          Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
            targetCtx.layout targetDepth continueScope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .cont { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.cont_liveStmtRunBridge_of_lower
    hLower hCtx hContinue hCleanupScope hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {leaveScope : List Functions.Name}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hLeave : sourceCtx.leaveScope? = some leaveScope)
    (hReturnScope :
      ∀ name, name ∈ returns → name ∈ leaveScope)
    (hNoDup : targetCtx.layout.Nodup)
    (hReturnsLen : returns.length = retc)
    (hHiddenReturns : hiddenReturns ≠ [])
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible targetCtx.layout 0 returns)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .leave
      { stmts :=
          Functions.Lower.pushReturns returns ++ [Locals.Stmt.leave] }
      source target :=
  Functions.LiveLayout.SourceTarget.leave_liveStmtRunBridge
    hCtx hLeave hReturnScope hNoDup hReturnsLen hHiddenReturns hAccess hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {leaveScope : List Functions.Name}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hLeave : sourceCtx.leaveScope? = some leaveScope)
    (hReturnScope :
      ∀ name, name ∈ returns → name ∈ leaveScope)
    (hNoDup : targetCtx.layout.Nodup)
    (hReturnsLen : returns.length = retc)
    (hLeaveFrame :
      Functions.SourceDirect.LeaveFrameAvailable sourceCtx hiddenReturns)
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible targetCtx.layout 0 returns)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .leave
      { stmts :=
          Functions.Lower.pushReturns returns ++ [Locals.Stmt.leave] }
      source target :=
  Functions.LiveLayout.SourceTarget.leave_liveStmtRunBridge_of_leaveFrame
    hCtx hLeave hReturnScope hNoDup hReturnsLen hLeaveFrame hAccess hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {leaveScope : List Functions.Name}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after .leave =
        some (lowerStmt, nextLayout))
    (hAccessCheck :
      Functions.LiveLayout.StmtAccess.accessible? returns targetCtx.layout
          .leave =
        true)
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hLeave : sourceCtx.leaveScope? = some leaveScope)
    (hReturnScope :
      ∀ name, name ∈ returns → name ∈ leaveScope)
    (hNoDup : targetCtx.layout.Nodup)
    (hReturnsLen : returns.length = retc)
    (hHiddenReturns : hiddenReturns ≠ [])
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .leave { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.leave_liveStmtRunBridge_of_lower
    hLower hAccessCheck hCtx hLeave hReturnScope hNoDup hReturnsLen
    hHiddenReturns hRel

example {ctx : Locals.Ctx}
    {outer scope : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State}
    {target cleaned : Locals.RunState}
    (hRel :
      Functions.SourceDirect.StateRel ctx.layout hiddenReturns source target)
    (hLayout :
      Functions.SourceDirect.CleanupLayoutRel ctx.layout outer)
    (hSubset : ∀ {name : Functions.Name}, name ∈ outer → name ∈ scope)
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx outer.length target =
        .ok cleaned) :
    Functions.SourceDirect.StateRel outer hiddenReturns
      (Locals.Source.State.restrictTo scope source) cleaned :=
  Functions.LiveLayout.SourceDirectBridge.stateRel_cleanupTo_layout_subset
    hRel hLayout hSubset hRun

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
        sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        hiddenReturns body lowerBody source target)
    (hRegularLayout :
      ∀ {sourceInner : Functions.Source.State}
        {sourceCtxOut : Functions.Source.Ctx}
        {targetInner : Locals.RunState} {targetCtxOut : Locals.Ctx}
        {bodyTargetFuel : Nat},
        Functions.Source.Block.runOpen prim sourceProgram sourceCtx fuel body
            source =
          .ok (Functions.Source.Outcome.regular sourceInner, sourceCtxOut) →
        Locals.Direct.Block.runOpen targetProgram targetCtx bodyTargetFuel
            lowerBody target =
          .ok (Structured.Outcome.regular targetInner, targetCtxOut) →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
          returns hiddenReturns
          (Functions.Source.Outcome.regular sourceInner, sourceCtxOut)
          (Structured.Outcome.regular targetInner, targetCtxOut) →
        Functions.SourceDirect.CleanupLayoutRel targetCtxOut.layout
          targetCtx.layout) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.block body) { stmts := [Locals.Stmt.block lowerBody] }
      source target :=
  Functions.LiveLayout.block_liveStmtRunBridge_of_open_bridge
    hCtx hBody hRegularLayout

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
        prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.block body) { stmts := [Locals.Stmt.block lowerBody] }
      source target :=
  Functions.LiveLayout.block_liveStmtRunBridge_of_open_bridge_with_layout
    hCtx hBody

example : True := by
  have _ :=
    @Functions.LiveLayout.blockScoped_from_open_bridge_with_layout
  have _ :=
    @Functions.LiveLayout.blockScoped_from_open_target_result_with_layout
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.blockScoped_from_loop_open_bridge_with_layout
  trivial

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after nextLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerStmt : List Locals.Stmt}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
        targetCtx.layout after (.block body) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBody :
      ∀ {lowerBody bodyLayout},
        Functions.LiveLayout.Lower.Block.toLocals? returns
          (liveCtx.withProtectedLayout targetCtx.layout) targetCtx.layout
          (Functions.LiveLayout.Checked.scopedAfter targetCtx.layout after)
          body =
          some (lowerBody, bodyLayout) →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
          prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
          hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.block body) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.block_liveStmtRunBridge_of_lower hLower hCtx hBody

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after nextLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterCond : Functions.Source.State}
    {target : Locals.RunState}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {lowerStmt : List Locals.Stmt} {value : EvmYul.UInt256}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
        targetCtx.layout after (.if_ cond body) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned cond)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 cond)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim cond source =
        .ok (sourceAfterCond, value))
    (hBody :
      ∀ {lowerBody bodyLayout targetAfterCond},
        Functions.LiveLayout.Lower.Block.toLocals? returns
          (liveCtx.withProtectedLayout targetCtx.layout) targetCtx.layout
          (Functions.LiveLayout.Checked.scopedAfter targetCtx.layout after)
          body =
          some (lowerBody, bodyLayout) →
        Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns
          sourceAfterCond targetAfterCond →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
          prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
          hiddenReturns body lowerBody sourceAfterCond targetAfterCond) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns (.if_ cond body) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.if_liveStmtRunBridge_of_lower hPrim hLower hCtx hNoDup
    hOwned hAccess hRel hEvalOne hBody

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after nextLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterScrutinee : Functions.Source.State}
    {target : Locals.RunState}
    {scrutinee : Functions.Expr 1}
    {cases : List (EvmYul.UInt256 × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {lowerStmt : List Locals.Stmt} {value : EvmYul.UInt256}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
        targetCtx.layout after (.switch scrutinee cases defaultBody) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned scrutinee)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 scrutinee)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim scrutinee source =
        .ok (sourceAfterScrutinee, value))
    (hBody :
      ∀ {value body lowerBody bodyLayout targetAfterPop},
        Functions.Source.Switch.select value cases defaultBody = some body →
        Functions.LiveLayout.Lower.Block.toLocals? returns
          (liveCtx.withProtectedLayout targetCtx.layout) targetCtx.layout
          (Functions.LiveLayout.Checked.scopedAfter targetCtx.layout after)
          body =
          some (lowerBody, bodyLayout) →
        Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns
          sourceAfterScrutinee targetAfterPop →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
          prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
          hiddenReturns body lowerBody sourceAfterScrutinee targetAfterPop) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns (.switch scrutinee cases defaultBody) { stmts := lowerStmt }
      source target :=
  Functions.LiveLayout.switch_liveStmtRunBridge_of_lower hPrim hLower hCtx
    hNoDup hOwned hAccess hRel hEvalOne hBody

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.stateRel_restrictTo_layout_subset
  trivial

example : True := by
  have _ := @Functions.LiveLayout.runForLoop_condition_bridge_live
  trivial

example : True := by
  have _ := @Functions.LiveLayout.runForLoop_false_from_eval_live
  trivial

example : True := by
  have _ := @Functions.LiveLayout.runForLoop_from_exact_source_run_live
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.runForLoop_from_exact_source_run_live_with_block_bridges
  trivial

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name}
    {retc sourceFuel initTargetFuel loopTargetFuel : Nat}
    {sourceCtx sourceInitCtx : Functions.Source.Ctx}
    {targetCtx targetInitCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterInit sourceLoop : Functions.Source.State}
    {target targetAfterInit targetLoop : Locals.RunState}
    {init post body : Functions.Block} {cond : Functions.Expr 1}
    {lowerInit lowerPost lowerBody : Locals.Block}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hSourceInit :
      Functions.Source.Block.runOpen prim sourceProgram
          sourceCtx.withoutLoopControl sourceFuel init source =
        .ok (Functions.Source.Outcome.regular sourceAfterInit, sourceInitCtx))
    (hTargetInit :
      Locals.Direct.Block.runOpen targetProgram targetCtx.withoutLoopControl
          initTargetFuel lowerInit target =
        .ok (Structured.Outcome.regular targetAfterInit, targetInitCtx))
    (hLoop :
      Functions.Source.Stmt.runForLoop prim sourceProgram sourceInitCtx cond
          sourceInitCtx.withoutLoopControl post
          (sourceInitCtx.withLoopControl sourceInitCtx.scope
            sourceInitCtx.scope)
          body sourceFuel sourceAfterInit =
        .ok (Functions.Source.Outcome.regular sourceLoop))
    (hTargetLoop :
      Locals.Direct.Stmt.runForLoop targetProgram targetInitCtx cond
          targetInitCtx.withoutLoopControl lowerPost
          (targetInitCtx.withLoopControl targetInitCtx.layout.length)
          lowerBody loopTargetFuel targetAfterInit =
        .ok (Structured.Outcome.regular targetLoop))
    (hLoopRel :
      Functions.SourceDirect.StateRel targetInitCtx.layout hiddenReturns
        sourceLoop targetLoop)
    (hLayout :
      Functions.SourceDirect.CleanupLayoutRel targetInitCtx.layout
        targetCtx.layout) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (sourceFuel + 1) sourceCtx
      targetCtx hiddenReturns (.for_ init cond post body)
      { stmts := [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] }
      source target :=
  Functions.LiveLayout.for_regular_liveStmtRunBridge_from_init_loop_regular
    hCtx hSourceInit hTargetInit hLoop hTargetLoop hLoopRel hLayout

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name}
    {retc sourceFuel initTargetFuel : Nat}
    {sourceCtx sourceInitCtx : Functions.Source.Ctx}
    {targetCtx targetInitCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {init post body : Functions.Block} {cond : Functions.Expr 1}
    {lowerInit lowerPost lowerBody : Locals.Block}
    {sourceInit : Functions.Source.Outcome} {targetInit : Locals.Outcome}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hSourceInit :
      Functions.Source.Block.runOpen prim sourceProgram
          sourceCtx.withoutLoopControl sourceFuel init source =
        .ok (sourceInit, sourceInitCtx))
    (hTargetInit :
      Locals.Direct.Block.runOpen targetProgram targetCtx.withoutLoopControl
          initTargetFuel lowerInit target =
        .ok (targetInit, targetInitCtx))
    (hInitRel :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns (sourceInit, sourceInitCtx)
        (targetInit, targetInitCtx))
    (hPass :
      sourceInit.mode = .leave ∨
        ∃ kind, sourceInit.mode = .halt kind) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (sourceFuel + 1) sourceCtx
      targetCtx hiddenReturns (.for_ init cond post body)
      { stmts := [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] }
      source target :=
  Functions.LiveLayout.for_leave_or_halt_liveStmtRunBridge_from_init_open
    hCtx hSourceInit hTargetInit hInitRel hPass

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name}
    {retc sourceFuel initTargetFuel loopTargetFuel : Nat}
    {sourceCtx sourceInitCtx : Functions.Source.Ctx}
    {targetCtx targetInitCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterInit : Functions.Source.State}
    {target targetAfterInit : Locals.RunState}
    {init post body : Functions.Block} {cond : Functions.Expr 1}
    {lowerInit lowerPost lowerBody : Locals.Block}
    {sourceLoop : Functions.Source.Outcome} {targetLoop : Locals.Outcome}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hSourceInit :
      Functions.Source.Block.runOpen prim sourceProgram
          sourceCtx.withoutLoopControl sourceFuel init source =
        .ok (Functions.Source.Outcome.regular sourceAfterInit, sourceInitCtx))
    (hTargetInit :
      Locals.Direct.Block.runOpen targetProgram targetCtx.withoutLoopControl
          initTargetFuel lowerInit target =
        .ok (Structured.Outcome.regular targetAfterInit, targetInitCtx))
    (hLoop :
      Functions.Source.Stmt.runForLoop prim sourceProgram sourceInitCtx cond
          sourceInitCtx.withoutLoopControl post
          (sourceInitCtx.withLoopControl sourceInitCtx.scope
            sourceInitCtx.scope)
          body sourceFuel sourceAfterInit =
        .ok sourceLoop)
    (hTargetLoop :
      Locals.Direct.Stmt.runForLoop targetProgram targetInitCtx cond
          targetInitCtx.withoutLoopControl lowerPost
          (targetInitCtx.withLoopControl targetInitCtx.layout.length)
          lowerBody loopTargetFuel targetAfterInit =
        .ok targetLoop)
    (hOutcomeRel :
      ∃ outcomeLayout,
        Functions.SourceDirect.StmtOutcomeRel returns outcomeLayout
          hiddenReturns sourceLoop targetLoop)
    (hPass :
      sourceLoop.mode = .leave ∨
        ∃ kind, sourceLoop.mode = .halt kind) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (sourceFuel + 1) sourceCtx
      targetCtx hiddenReturns (.for_ init cond post body)
      { stmts := [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] }
      source target :=
  Functions.LiveLayout.for_leave_or_halt_liveStmtRunBridge_from_init_loop
    hCtx hSourceInit hTargetInit hLoop hTargetLoop hOutcomeRel hPass

example : True := by
  have _ :=
    @Functions.LiveLayout.for_liveStmtRunBridge_from_exact_source_run_of_lower
  trivial

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
        prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns body lowerBody source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout.to_open
    hBody

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {stmt : Functions.Stmt} {targetBlock : Locals.Block}
    (hStmt :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayout prim
        sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        hiddenReturns stmt targetBlock source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns stmt targetBlock source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayout.to_stmt
    hStmt

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns baseLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
        prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        baseLayout hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns body lowerBody source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo.to_open
    hBody

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns baseLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {stmt : Functions.Stmt} {targetBlock : Locals.Block}
    (hStmt :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayoutTo prim
        sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        baseLayout hiddenReturns stmt targetBlock source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns stmt targetBlock source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayoutTo.to_stmt
    hStmt

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayout
        prim sourceProgram targetProgram returns loopLayout retc fuel sourceCtx
        targetCtx hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns body lowerBody source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayout.to_open_with_layout
    hBody

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {stmt : Functions.Stmt} {targetBlock : Locals.Block}
    (hStmt :
      Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayout prim
        sourceProgram targetProgram returns loopLayout retc fuel sourceCtx
        targetCtx hiddenReturns stmt targetBlock source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayout prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns stmt targetBlock source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayout.to_stmt_with_layout
    hStmt

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns loopLayout baseLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayoutTo
        prim sourceProgram targetProgram returns loopLayout retc fuel sourceCtx
        targetCtx baseLayout hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
      prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      baseLayout hiddenReturns body lowerBody source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayoutTo.to_open_with_layout
    hBody

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns loopLayout baseLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {stmt : Functions.Stmt} {targetBlock : Locals.Block}
    (hStmt :
      Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayoutTo
        prim sourceProgram targetProgram returns loopLayout retc fuel sourceCtx
        targetCtx baseLayout hiddenReturns stmt targetBlock source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayoutTo prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      baseLayout hiddenReturns stmt targetBlock source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayoutTo.to_stmt_with_layout
    hStmt

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayoutTo.target_result_of_source
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayoutTo.target_result_of_source
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo.source_mono
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayoutTo.target_result_of_source
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo.target_result_of_source
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo.target_result_with_noncontrol_outcome_cleanup_of_source
  have _ :=
    @Functions.LiveLayout.Layout.trimDeadPrefix_nodup
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_runBridge_of_lower_with_layout_to
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_runBridge_of_lower_with_layout_to_prepared_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_prepared_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to
  have _ :=
    @Functions.LiveLayout.SourceTarget.expr_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.let_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.assign_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.terminal_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.terminalArgs_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.brk_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.cont_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.leave_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.if_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.switch_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.LiveAtomicStmt
  have _ :=
    @Functions.LiveLayout.SourceTarget.atomic_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.atomic_liveStmtRunBridge_from_source_run_of_lower_case_handlers
  have _ :=
    @Functions.LiveLayout.SourceTarget.LiveNonLoopNonCallStmt
  have _ :=
    @Functions.LiveLayout.SourceTarget.nonloop_noncall_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.nonloop_noncall_liveStmtRunBridge_from_source_run_of_lower_case_handlers
  have _ :=
    @Functions.LiveLayout.SourceTarget.nonloop_noncall_liveStmtRunBridge_from_source_run_of_lower_noInternalCall
  have _ :=
    @Functions.LiveLayout.SourceTarget.nonloop_noncall_liveStmtRunBridge_from_source_run_of_lower_noInternalCall_case_handlers
  have _ :=
    @Functions.LiveLayout.SourceTarget.noncall_liveStmtRunBridge_from_source_run_of_lower_noInternalCall
  have _ :=
    @Functions.LiveLayout.SourceTarget.noncall_liveStmtRunBridge_from_source_run_of_lower_noInternalCall_case_handlers
  have _ :=
    @Functions.LiveLayout.SourceTarget.LiveNonCallStmt
  have _ :=
    @Functions.LiveLayout.NoInternalCall.Program.check?_sound
  have _ :=
    @Functions.LiveLayout.NoInternalCall.Block.holds_cons
  have _ :=
    @Functions.LiveLayout.SourceTarget.SourceScopeFacts.block_scoped_cons
  have _ :=
    @Functions.LiveLayout.SourceTarget.SourceScopeFacts.stmt_scoped_block
  have _ :=
    @Functions.LiveLayout.SourceTarget.SourceScopeFacts.stmt_scoped_if_body
  have _ :=
    @Functions.LiveLayout.SourceTarget.SourceScopeFacts.stmt_scoped_switch_select_body
  have _ :=
    @Functions.LiveLayout.SourceTarget.SourceScopeFacts.stmt_scoped_for_init
  have _ :=
    @Functions.LiveLayout.SourceTarget.SourceScopeFacts.stmt_scoped_for_post
  have _ :=
    @Functions.LiveLayout.SourceTarget.SourceScopeFacts.stmt_scoped_for_body
  have _ :=
    @Functions.LiveLayout.SourceTarget.liveNonCallStmt_of_noInternalCall
  have _ :=
    @Functions.LiveLayout.SourceTarget.liveNonCallStmt_of_noInternalCall_block_cons
  have _ :=
    @Functions.LiveLayout.SourceTarget.scopedStmt_of_scoped_block_cons
  have _ :=
    @Functions.LiveLayout.cleanupLayoutRel_promoteName_of_idx_lt_protected
  have _ :=
    @Functions.LiveLayout.Prepare.loopAboveSuffix_cleanupLayoutRel_of_baseDepth
  have _ :=
    @Functions.LiveLayout.Prepare.forStmtAboveSuffix?_cleanupLayoutRel_of_baseDepth
  have _ :=
    @Functions.LiveLayout.SourceTarget.preparedLayout_cleanupLayoutRel_of_block_scopedAfter_regular_tail
  have _ :=
    @Functions.LiveLayout.TargetLayout.Stmt.run_regular_ctx
  have _ :=
    @Functions.LiveLayout.TargetLayout.StmtList.runOpen_regular_ctx
  have _ :=
    @Functions.LiveLayout.TargetLayout.StmtList.block_runOpen_regular_ctx
  have _ :=
    @Functions.LiveLayout.TargetLayout.Lower.block_runOpen_regular_ctx_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.noInternalCall_switch_select_block_holds
  have _ :=
    @Functions.LiveLayout.SourceTarget.noInternalCall_stmt_block_body
  have _ :=
    @Functions.LiveLayout.SourceTarget.noInternalCall_stmt_if_body
  have _ :=
    @Functions.LiveLayout.SourceTarget.noInternalCall_stmt_switch_select_body
  have _ :=
    @Functions.LiveLayout.SourceTarget.noInternalCall_stmt_for_init
  have _ :=
    @Functions.LiveLayout.SourceTarget.noInternalCall_stmt_for_post
  have _ :=
    @Functions.LiveLayout.SourceTarget.noInternalCall_stmt_for_body
  have _ :=
    @Functions.LiveLayout.SourceTarget.noncall_liveStmtRunBridge_from_source_run_of_lower
  have _ :=
    @Functions.LiveLayout.Checked.Stmt.regularOutLayout_cleanupLayoutRel
  have _ :=
    @Functions.LiveLayout.Checked.Stmt.regularOutLayout_suffix_drop
  have _ :=
    @Functions.LiveLayout.Checked.Stmt.check?_suffix_drop
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.prepareLoopAboveSuffix_suffix_drop
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.forStmtAboveSuffix_suffix_drop
  have _ :=
    @Functions.LiveLayout.Lower.stmt_toLocals?_regularOutLayout
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRegularLayoutRelTo.trans_cleanup
  have _ :=
    @Functions.LiveLayout.TargetLayout.Lower.stmt_toLocals?_cleanupLayoutRel
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_components_with_layout_to
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_components_with_layout_to_tail_nextLayout
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_components_with_layout_to_tail_entryLayout
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to_tail_nextLayout
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to_tail_entryLayout
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to_noInternalCall_head
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to_noInternalCall_head_structural_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to_noInternalCall_head_structural_callbacks_case_handlers
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to_noInternalCall_head_structural_callbacks_case_handlers_tail_entryLayout_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveStmtTargetRegularOutputLayoutRel
  have _ :=
    @Functions.LiveLayout.TargetLayout.Lower.stmt_runOpen_regular_layout_of_lower
  have _ :=
    @Functions.LiveLayout.TargetLayout.Lower.stmt_runOpen_regular_ctx_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmt_target_regular_output_layout_of_lower_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmt_target_result_with_output_layout_of_lower
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_source_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noncall_heads
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_heads
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks_case_handlers
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks_case_handlers_tail_entryLayout_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks_live_control_handlers
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks_live_control_handlers_tail_entryLayout_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks_live_control_handlers_tail_entryLayout_protected_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks_live_control_handlers_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks_live_control_handlers
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallCallbackBundle
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallCallbackBundle.ctxCleanup
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallCallbackBundle.tailEntry
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeBodyCallbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeCallbackBundle
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeCallbackBundle.ctxCleanup
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeCallbackBundle.tailEntry
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeOutcomeCallbackBundle
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeOutcomeCallbackBundle.outcomeCleanup
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeOutcomeCallbackBundle.tailEntry
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveCallbackBundle
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveCallbackBundle.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runOpen_cons_brk_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runOpen_cons_cont_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runScoped_of_open_brk_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runScoped_of_open_cont_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runOpen_cons_block_body_brk_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runOpen_cons_block_body_cont_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runOpen_cons_if_body_brk_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runOpen_cons_if_body_cont_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runOpen_cons_switch_body_brk_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runOpen_cons_switch_body_cont_mode
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runScoped_brk_open_exists
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_runScoped_cont_open_exists
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_breakLive_mem_of_brk_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.stmt_breakLive_mem_of_brk_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.stmtList_breakLive_mem_of_brk_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.block_continueLive_mem_of_cont_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.stmt_continueLive_mem_of_cont_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.HandlerRunLiveBefore.stmtList_continueLive_mem_of_cont_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.block_trimDeadPrefix_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.blockBody_of_open_block_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.blockBody_of_open_block_of_outer_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.blockBody_of_open_block_of_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.blockBody_of_open_block_of_body_mode_live_subset_of_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.blockBody_of_open_block_of_outer_outcome_cleanup
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.blockBody_of_open_block_of_outer_outcome_cleanup_of_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.ifBody_of_open_block_of_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.ifBody_of_open_block_of_body_mode_live_subset_of_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.ifBody_of_open_block_of_outer_outcome_cleanup_of_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.switchBody_of_open_block_of_selected_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.switchBody_of_open_block_of_selected_body_mode_live_subset_of_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.switchBody_of_open_block_of_outer_outcome_cleanup_of_run
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveCallbacksUpTo.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveCallbacksUpTo.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveCallbacksUpTo.block_succ_of_cleanup_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.noncall_liveStmtRunBridge_from_source_run_of_lower_noInternalCall_shape_handlers_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to_noInternalCall_head_shape_callbacks_tail_entryLayout_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.stmtList_cons_target_result_of_source_run_lower_with_layout_to_noInternalCall_head_shape_outcome_callbacks_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_outcome_callbacks_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_outcome_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_succ_of_shape_outcome_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_recursive_callback_bundle_tail_entryLayout_protected_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_recursive_callback_bundle_tail_entryLayout_protected_scopedAfter_of_cleanup_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter_of_cleanup_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveCallbackBundle
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveCallbackBundle.to_callbackBundle
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveCallbackBundle.to_callbackBundle_of_ctxRel
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveCallbackBundle.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveCallbacksUpTo.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveCallbacksUpTo.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_tail_entryLayout_protected_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_tail_entryLayout_protected_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_tail_entryLayout_protected_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_scopedAfter_of_ctxRel
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_scopedAfter_of_ctxRel
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpTo.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpTo.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpTo.block_succ_of_recursive_callbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpTo.succ_of_recursive_callbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpToOfLeaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpToOfLeaveFrame.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpToOfLeaveFrame.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpToOfLeaveFrame.block_succ_of_recursive_callbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockCallbacksUpToOfLeaveFrame.succ_of_recursive_callbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.to_cleanup_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.block_trimDeadPrefix_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.blockBody_of_open_block_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.ifBody_of_open_block_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.switchBody_of_open_block_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.blockBody_of_open_block_of_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.ifBody_of_open_block_of_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.switchBody_of_open_block_of_selected_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockLayoutToCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockLayoutToCallbacksUpTo.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockLayoutToCallbacksUpTo.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockLayoutToOutcomeCallbacksUpToOfLeaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockLayoutToOutcomeCallbacksUpToOfLeaveFrame.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockLayoutToOutcomeCallbacksUpToOfLeaveFrame.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockLayoutToOutcomeCallbacksUpToOfLeaveFrame.to_scopedAfter_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockLayoutToOutcomeAnyEntryCallbacksUpToOfLeaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockLayoutToOutcomeAnyEntryCallbacksUpToOfLeaveFrame.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockLayoutToOutcomeAnyEntryCallbacksUpToOfLeaveFrame.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockLayoutToOutcomeAnyEntryCallbacksUpToOfLeaveFrame.to_scopedAfter_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.preparedLayout_cleanupLayoutRel_of_regular_tail_to_base
  have _ :=
    @Functions.LiveLayout.SourceTarget.tail_outcomeCleanup_of_regular_head
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.outcomeBodyCallbacks_of_anyEntry_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.anyEntry_succ_of_callback_families
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.allFuel_callback_families
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.anyEntry_allFuel
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.loopOpenBlock_allFuel
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.openBlock_allFuel
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveLoopOpenBlockLayoutToOutcomeCallbacksUpToOfLeaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveLoopOpenBlockLayoutToOutcomeCallbacksUpToOfLeaveFrame.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveLoopOpenBlockLayoutToOutcomeCallbacksUpToOfLeaveFrame.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveLoopOpenBlockLayoutToOutcomeCallbacksUpToOfLeaveFrame.blockScoped_loopOpenBridge
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveAllCallbacksUpToOfLeaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveAllCallbacksUpToOfLeaveFrame.zero
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveAllCallbacksUpToOfLeaveFrame.mono
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.runForLoop_with_block_callback_families
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.runForLoop_with_block_callback_families_induction
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.forLoop_callback_of_open_block_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.to_cleanup_callbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.block_trimDeadPrefix_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.blockBody_of_open_block_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.ifBody_of_open_block_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.switchBody_of_open_block_of_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.blockBody_of_open_block_of_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.ifBody_of_open_block_of_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo.switchBody_of_open_block_of_selected_body_mode_live_subset
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_nil_safe
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_nil_safe_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_tail_entryLayout_protected_scopedAfter
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_callback_bundle_scopedAfter_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_tail_entryLayout_protected_scopedAfter_of_ctxRel
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_tail_entryLayout_protected_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter_of_ctxRel
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_scopedAfter_of_ctxRel
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callback_bundle_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_scopedAfter_of_ctxRel
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_recursive_callbacksUpTo_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.block_scoped_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter_of_ctxRel_of_leaveFrame
  have _ :=
    @Functions.LiveLayout.SourceTarget.Program.runState_toLocalsNoInternalCall_exists_of_shapeRecursiveCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.Program.runState_toLocalsNoInternalCall_exists_of_openBlockOutcomeCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.Program.runState_toLocalsNoInternalCall_exists_of_all_shapeRecursiveCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.Program.runState_toLocalsNoInternalCall_exists_of_derivedOpenBlockCallbacks
  have _ :=
    @Functions.LiveLayout.SourceTarget.Program.compileLiveNoInternalCallChecked_preserves
  have _ :=
    @Objects.Source.Program.compile_live_noInternalCall_preserves_checked
  have _ :=
    @Functions.LiveLayout.SourceTarget.Program.runState_toLocalsNoInternalCall_exists_of_recursiveCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.Program.runState_toLocalsNoInternalCall_exists_of_all_recursiveCallbacksUpTo
  have _ :=
    @Functions.LiveLayout.SourceTarget.nil_cleanupLayoutRel_of_nonempty_or_after_contains_layout
  have _ :=
    @Functions.LiveLayout.SourceTarget.nil_cleanupLayoutRel_scopedAfter
  trivial

example {targets : List Functions.Name} {functionName : Functions.Name}
    {args : List (Functions.Expr 1)} :
    Functions.LiveLayout.NoInternalCall.Stmt.check?
        (.call targets functionName args) = false := by
  rfl

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {fuel : Nat}
    {sourceCtx stmtSourceCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {source : Functions.Source.State}
    {sourceOutcome : Functions.Source.Outcome}
    (hSourceStmt :
      Functions.Source.Stmt.run prim sourceProgram sourceCtx fuel stmt
          source =
        .ok (sourceOutcome, stmtSourceCtx))
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    stmtSourceCtx = sourceCtx :=
  Functions.Source.Stmt.run_nonregular_ctx hSourceStmt hNonregular

example {program : Locals.Program} {protectedDepth : Nat}
    {returns live : List Functions.Name} {stmt : Functions.Stmt}
    {ctx : Locals.Ctx} {prep : List Locals.Stmt}
    {finalLayout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          ctx.layout live stmt =
        some (prep, finalLayout))
    (hRel :
      Functions.SourceDirect.StateRel ctx.layout hiddenReturns source target) :
    ∃ prepared prepareFuel,
      Locals.Direct.Block.runOpen program ctx prepareFuel { stmts := prep }
          target =
        .ok (Structured.Outcome.regular prepared,
          ctx.withLayout finalLayout) ∧
      Functions.SourceDirect.StateRel finalLayout hiddenReturns source
        prepared :=
  Functions.LiveLayout.Target.prepareForStmtAboveSuffix_runOpen_exists
    hPrepare hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {protectedDepth retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {stmtLive liveLayout preparedLayout : List Functions.Name}
    {prep lowerStmt lowerRest : List Locals.Stmt}
    {source : Functions.Source.State} {target : Locals.RunState}
    (hLiveLayout :
      liveLayout =
        Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout stmtLive)
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
        liveLayout stmtLive stmt =
        some (prep, preparedLayout))
    (hStateRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hHead :
      ∀ {cleaned},
        Functions.SourceDirect.StateRel preparedLayout hiddenReturns source
          cleaned →
        Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
          sourceProgram targetProgram returns retc fuel sourceCtx
          (targetCtx.withLayout preparedLayout)
          hiddenReturns stmt { stmts := lowerStmt } source cleaned)
    (hTail :
      ∀ {sourceAfter : Functions.Source.State} {targetAfter : Locals.RunState}
        {sourceCtxAfter : Functions.Source.Ctx} {targetCtxAfter : Locals.Ctx},
        Functions.SourceDirect.StateRel targetCtxAfter.layout hiddenReturns
          sourceAfter targetAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtxAfter
          targetCtxAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
          sourceProgram targetProgram returns retc fuel sourceCtxAfter
          targetCtxAfter hiddenReturns { stmts := rest }
          { stmts := lowerRest } sourceAfter targetAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns { stmts := stmt :: rest }
      { stmts :=
          Functions.LiveLayout.Lower.cleanupToLive targetCtx.layout stmtLive ::
            (prep ++ (lowerStmt ++ lowerRest)) } source target :=
  Functions.LiveLayout.SourceTarget.stmtList_cons_runBridge_of_lower_components
    hLiveLayout hPrepare hStateRel hHead hTail

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {stmtLive : List Functions.Name}
    {lowerStmt lowerRest : List Locals.Stmt}
    {source : Functions.Source.State} {target : Locals.RunState}
    (hStateRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEntryLayout :
      Functions.SourceDirect.CleanupLayoutRel
        (Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout stmtLive)
        targetCtx.layout)
    (hHead :
      ∀ {cleaned},
        Functions.SourceDirect.StateRel
          (Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout
            stmtLive)
          hiddenReturns source cleaned →
        Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayout prim
          sourceProgram targetProgram returns retc fuel sourceCtx
          (targetCtx.withLayout
            (Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout
              stmtLive))
          hiddenReturns stmt { stmts := lowerStmt } source cleaned)
    (hTail :
      ∀ {sourceAfter : Functions.Source.State} {targetAfter : Locals.RunState}
        {sourceCtxAfter : Functions.Source.Ctx} {targetCtxAfter : Locals.Ctx},
        Functions.SourceDirect.StateRel targetCtxAfter.layout hiddenReturns
          sourceAfter targetAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtxAfter
          targetCtxAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
          prim sourceProgram targetProgram returns retc fuel sourceCtxAfter
          targetCtxAfter hiddenReturns { stmts := rest }
          { stmts := lowerRest } sourceAfter targetAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
      prim sourceProgram targetProgram returns retc (fuel + 1) sourceCtx
      targetCtx hiddenReturns { stmts := stmt :: rest }
      { stmts :=
          Functions.LiveLayout.Lower.cleanupToLive targetCtx.layout stmtLive ::
            lowerStmt ++ lowerRest } source target :=
  Functions.LiveLayout.SourceTarget.stmtList_cons_runBridge_of_lower_components_with_layout
    hStateRel hEntryLayout hHead hTail

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns baseLayout : List Functions.Name} {protectedDepth retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {stmtLive liveLayout preparedLayout : List Functions.Name}
    {prep lowerStmt lowerRest : List Locals.Stmt}
    {source : Functions.Source.State} {target : Locals.RunState}
    (hLiveLayout :
      liveLayout =
        Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout stmtLive)
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
        liveLayout stmtLive stmt =
        some (prep, preparedLayout))
    (hStateRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hHead :
      ∀ {cleaned},
        Functions.SourceDirect.StateRel preparedLayout hiddenReturns source
          cleaned →
        Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
          sourceProgram targetProgram returns retc fuel sourceCtx
          (targetCtx.withLayout preparedLayout)
          hiddenReturns stmt { stmts := lowerStmt } source cleaned)
    (hTail :
      ∀ {sourceAfter : Functions.Source.State} {targetAfter : Locals.RunState}
        {sourceCtxAfter : Functions.Source.Ctx} {targetCtxAfter : Locals.Ctx},
        Functions.SourceDirect.StateRel targetCtxAfter.layout hiddenReturns
          sourceAfter targetAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtxAfter
          targetCtxAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
          prim sourceProgram targetProgram returns retc fuel sourceCtxAfter
          targetCtxAfter baseLayout hiddenReturns { stmts := rest }
          { stmts := lowerRest } sourceAfter targetAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
      prim sourceProgram targetProgram returns retc (fuel + 1) sourceCtx
      targetCtx baseLayout hiddenReturns { stmts := stmt :: rest }
      { stmts :=
          Functions.LiveLayout.Lower.cleanupToLive targetCtx.layout stmtLive ::
            (prep ++ (lowerStmt ++ lowerRest)) } source target :=
  Functions.LiveLayout.SourceTarget.stmtList_cons_runBridge_of_lower_components_with_layout_to
    hLiveLayout hPrepare hStateRel hHead hTail

example :
    Functions.LiveLayout.FunDef.entryLive
      { name := "f"
        params := ["x"]
        returns := []
        body :=
          { stmts :=
              [ .let_ "dead" (.lit (EvmYul.UInt256.ofNat 0))
              , .expr (.prim .pop
                  (Locals.ExprSeq.cons (.var "x") .nil)) ] } } =
      ["x"] := by
  native_decide

example :
    Functions.LiveLayout.Layout.promoteName?
      ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8",
        "v9", "v10", "v11", "v12", "v13", "v14", "v15", "v16",
        "deep"]
      "deep" = none := by
  native_decide

example :
    Functions.LiveLayout.Layout.promoteNameUnbounded?
      ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8",
        "v9", "v10", "v11", "v12", "v13", "v14", "v15", "v16",
        "deep"]
      "deep" =
        some
          (["deep", "v0", "v1", "v2", "v3", "v4", "v5", "v6",
              "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14",
              "v15", "v16"],
            17) := by
  native_decide

example :
    (Locals.Ctx.promoteNameStackOnly?
      { Locals.Ctx.initial with
        layout :=
          ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8",
            "v9", "v10", "v11", "v12", "v13", "v14", "v15", "v16",
            "deep"] }
      "deep").isNone = true := by
  native_decide

end LiveLayoutRegression

end ImportedYulBoundary
end LayerAudit
end EvmCompiler
