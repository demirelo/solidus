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
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target)) :
    asm.usesCallCreate = false := by
  rcases compileCheckedAssemblyTarget?_eq_some hCompileTarget with
    ⟨hCompile, _hAssemble⟩
  exact
    _root_.EvmCompiler.Yul.NoCallCreate.compileChecked?_noCallCreate
      hAccepted hCompile

namespace RecursiveBridgeTargetRuntime

def withAcceptedNoCallCreate {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {initial : EVMState}
    (hAccepted : Reference.Accepted program)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (gasOracle : Assembly.GasOracleAssumption asm initial)
    (outOfGasPolicy : Assembly.OutOfGasPolicyAssumption asm initial)
    (currentContractProjection :
      Assembly.CurrentContractProjectionAssumption asm initial)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
    RecursiveBridgeTargetRuntime asm target initial :=
  withNoCallCreate decodeWindow jumpdestCorrect gasOracle outOfGasPolicy
    currentContractProjection
    (compileCheckedAssemblyTarget?_noCallCreate hAccepted hCompileTarget)
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
    (hInitialSharedRel :
      Reference.SharedStateRel cfg
        { shared with
          executionEnv :=
            { shared.executionEnv with code := program.contract } }
        initial.toSharedState)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (gasOracle : Assembly.GasOracleAssumption asm initial)
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
  initialShared := hInitialSharedRel
  sourceRun := hSourceRun
  compileTarget := hCompileTarget
  targetRuntime :=
    RecursiveBridgeTargetRuntime.withAcceptedNoCallCreate
      hSourceAccepted.reference hCompileTarget decodeWindow jumpdestCorrect
      gasOracle outOfGasPolicy currentContractProjection hInitialPc
      hInitialStack

end RecursiveBridgeTopAssumptions

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top_withAcceptedNoCallCreate
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
    (hInitialSharedRel :
      Reference.SharedStateRel cfg
        { shared with
          executionEnv :=
            { shared.executionEnv with code := program.contract } }
        initial.toSharedState)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (gasOracle : Assembly.GasOracleAssumption asm initial)
    (outOfGasPolicy : Assembly.OutOfGasPolicyAssumption asm initial)
    (currentContractProjection :
      Assembly.CurrentContractProjectionAssumption asm initial)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = []) :
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
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm initial ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
    (hTop :=
      RecursiveBridgeTopAssumptions.withAcceptedNoCallCreate
        hSourceAccepted hCompileResources hSemantics hInitialSharedRel
        hSourceRun hCompileTarget decodeWindow jumpdestCorrect gasOracle
        outOfGasPolicy currentContractProjection hInitialPc hInitialStack)

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
  gasOracle : Assembly.GasOracleAssumption asm initial
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
  gasOracle : Assembly.GasOracleAssumption asm initial
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
    (hInitialSharedRel :
      Reference.SharedStateRel cfg
        { shared with
          executionEnv :=
            { shared.executionEnv with code := program.contract } }
        initial.toSharedState)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (gasOracle : Assembly.GasOracleAssumption asm initial)
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
  initialShared := hInitialSharedRel
  sourceRun := hSourceRun
  compileTarget := hCompileTarget
  decodeWindow := decodeWindow
  jumpdestCorrect := jumpdestCorrect
  gasOracle := gasOracle
  outOfGasPolicy := outOfGasPolicy
  currentContractProjection := currentContractProjection
  initialPc := hInitialPc
  initialStack := hInitialStack

theorem sourceReferenceAccepted
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
    Reference.Accepted program :=
  hTop.sourceAccepted.reference

theorem sourceCompile
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
    SourceCompileAccepted program :=
  hTop.sourceCompileAccepted

theorem emittedNoCallCreate
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
    asm.usesCallCreate = false :=
  compileCheckedAssemblyTarget?_noCallCreate hTop.sourceAccepted.reference
    hTop.compileTarget

theorem targetFitsDecodeWindow
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
    Assembly.Bytecode.TargetFitsDecodeWindow target :=
  hTop.decodeWindow

theorem targetJumpdestCorrect
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
    Assembly.Bytecode.JumpdestCorrect target :=
  hTop.jumpdestCorrect

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
  gasOracle := hTop.gasOracle
  outOfGasPolicy := hTop.outOfGasPolicy
  currentContractProjection := hTop.currentContractProjection
  initialPc := hTop.initialPc
  initialStack := hTop.initialStack

end RecursiveBridgeTopNoCallSourceCompileAssumptions

namespace RecursiveBridgeTopNoCallAssumptions

theorem lowerObjectCompileAccepted
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
    {lowerObj : Objects.Program}
    (hLower : program.toObjects? = some lowerObj) :
    Objects.Source.Program.CompileAccepted lowerObj :=
  hTop.compileResources.objectCompileAccepted lowerObj hLower

theorem sourceReferenceAccepted
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
    Reference.Accepted program :=
  hTop.sourceAccepted.reference

theorem sourceCompileAccepted
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
    SourceCompileAccepted program where
  source :=
    sourceAccepted_of_accepted
      (Reference.programAccepted_of_accepted hTop.sourceAccepted.reference)
  objects := hTop.compileResources.objectCompileAccepted

theorem emittedNoCallCreate
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
    asm.usesCallCreate = false :=
  compileCheckedAssemblyTarget?_noCallCreate hTop.sourceAccepted.reference
    hTop.compileTarget

theorem targetFitsDecodeWindow
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
    Assembly.Bytecode.TargetFitsDecodeWindow target :=
  hTop.decodeWindow

theorem targetJumpdestCorrect
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
    Assembly.Bytecode.JumpdestCorrect target :=
  hTop.jumpdestCorrect

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
    hTop.jumpdestCorrect hTop.gasOracle hTop.outOfGasPolicy
    hTop.currentContractProjection hTop.initialPc hTop.initialStack

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
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm initial ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top
    (hTop := hTop.toTopAssumptions)

/--
Gas-aware `X` theorem for the preferred no-CALL/CREATE imported-Yul route.

The compiler proof constructs the gasless result trace and all bytecode
evidence. The only additional premise is the explicit result-level gas analysis
contract: for any target result produced by the gasless trace, the gas-aware
runner has an EVM fuel and gas bound above which it returns an agreeing result.
-/
theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_X
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
    (hX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target initial
          targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm initial ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  initial) =
                              .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result := by
  obtain
    ⟨sourceOutcome, targetFuel, targetOutcome, hRun, hOutcome,
      hWholeRel, hAccepted, hBytes, hEncoding, hGasBoundary, hGasOracle,
      hOutOfGas, hProjection, hTrace⟩ :=
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall
      hTop
  let hPreconditions := hX hTrace
  exact
    ⟨sourceOutcome, targetFuel, targetOutcome, hPreconditions.evmFuel,
      hPreconditions.gasBound, hRun, hOutcome, hWholeRel, hAccepted,
      hBytes, hEncoding, hGasBoundary, hGasOracle, hOutOfGas, hProjection,
      hTrace, hPreconditions.runsAboveBound⟩

theorem compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_X
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
    (hX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target initial
          targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel initial targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain
    ⟨sourceOutcome, targetFuel, targetOutcome, evmFuel, gasBound, hRun,
      hOutcome, hWholeRel, _hAccepted, _hBytes, _hEncoding, _hGasBoundary,
      _hGasOracle, _hOutOfGas, _hProjection, hTrace, hRuns⟩ :=
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_X
      hTop hX
  exact
    ⟨sourceOutcome, targetFuel, targetOutcome, evmFuel, gasBound, hRun,
      hOutcome, hWholeRel, hTrace, fun gas hGas hUInt256 => by
        obtain ⟨result, hRunX, _hAgree⟩ := hRuns gas hGas hUInt256
        rw [hRunX]
        intro hImpossible
        cases hImpossible⟩

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile
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
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm initial ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall
    hTop.toNoCallAssumptions

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_X
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
    (hX :
      ∀ {targetFuel targetOutcome},
        Assembly.Preservation.BlockTraceResult asm target targetFuel initial
          targetOutcome →
        Assembly.GasAware.XResultPreconditionAssumptions target initial
          targetOutcome) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      outcomeRel referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm initial ∧
                Assembly.OutOfGasPolicyAssumption asm initial ∧
                  Assembly.CurrentContractProjectionAssumption asm initial ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel initial targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  initial) =
                              .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result :=
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_X
    hTop.toNoCallAssumptions hX

end Program
end Yul
end EvmCompiler
