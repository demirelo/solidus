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

@[simp] theorem canonicalEntryState_toSharedState (initial : EVMState) :
    (canonicalEntryState initial).toSharedState = initial.toSharedState :=
  rfl

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
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial) :
    Reference.SharedStateRel cfg
      { shared with
        executionEnv :=
          { shared.executionEnv with code := program.contract } }
      (canonicalEntryState initial).toSharedState := by
  simpa [RecursiveBridgeInitialWorldRel] using hInitialWorld

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
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
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
  initialShared := by
    simpa [RecursiveBridgeInitialWorldRel] using hInitialWorld
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
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
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
        hSourceAccepted hCompileResources hSemantics hInitialWorld
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
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
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
  initialShared := by
    simpa [RecursiveBridgeInitialWorldRel] using hInitialWorld
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
  RecursiveBridgeCompileResources.lowerObjectCompileAccepted
    hTop.sourceAccepted hTop.compileResources hLower

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
  objects := by
    intro lowerObj hLower
    exact
      RecursiveBridgeCompileResources.lowerObjectCompileAccepted
        hTop.sourceAccepted hTop.compileResources hLower

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

/--
Preferred result-level top theorem for the canonical imported-Yul observation
relation.

This wrapper exposes the irreducible semantic core directly and constructs the
ordinary top-assumption package internally, so callers do not provide an
arbitrary `outcomeRel`/observation pair.
-/
theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X
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
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_X
    (RecursiveBridgeTopNoCallSourceCompileAssumptions.withCanonicalObservation
      hSourceAccepted hSourceCompileAccepted hSemantics hInitialWorld
      hSourceRun hCompileTarget decodeWindow jumpdestCorrect
      (Assembly.GasOracleAssumption.trivial (program := asm)
        (initial := initial))
      (Assembly.OutOfGasPolicyAssumption.trivial (program := asm)
        (initial := initial))
      (Assembly.CurrentContractProjectionAssumption.trivial (program := asm)
        (initial := initial))
      hInitialPc hInitialStack)
    hX

theorem compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X
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
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
    compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X
      hSourceAccepted hSourceCompileAccepted hSemantics hInitialWorld
      hSourceRun hCompileTarget decodeWindow jumpdestCorrect
      hInitialPc hInitialStack hX
  exact
    ⟨sourceOutcome, targetFuel, targetOutcome, evmFuel, gasBound, hRun,
      hOutcome, hWholeRel, hTrace, fun gas hGas hUInt256 => by
        obtain ⟨result, hRunX, _hAgree⟩ := hRuns gas hGas hUInt256
        rw [hRunX]
        intro hImpossible
        cases hImpossible⟩

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalBoundaries_X
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
    (hPrimitive : RecursiveBridgePrimitiveContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X
    hSourceAccepted hSourceCompileAccepted
    (RecursiveBridgeSemanticCoreContracts.ofBoundaries hPrimitive hTerminal
      hExpr)
    hInitialWorld hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack hX

theorem compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalBoundaries_X
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
    (hPrimitive : RecursiveBridgePrimitiveContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel initial targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X
    hSourceAccepted hSourceCompileAccepted
    (RecursiveBridgeSemanticCoreContracts.ofBoundaries hPrimitive hTerminal
      hExpr)
    hInitialSharedRel hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack hX

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalResourceBoundaries_X
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
    (hPrimitive : RecursiveBridgePrimitiveContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalBoundaries_X
    hSourceAccepted hSourceCompileAccepted hPrimitive hTerminal hExpr
    hInitialSharedRel hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack hX

theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X
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
    (hPrimitiveSound : Locals.SourceLowering.PrimitiveSound prim)
    (hPrimitiveStack : RecursiveBridgePrimitiveStackContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalResourceBoundaries_X
    hSourceAccepted hSourceCompileAccepted
    (RecursiveBridgePrimitiveContracts.of_stack hPrimitiveSound
      hPrimitiveStack)
    hTerminal hExpr hInitialSharedRel hSourceRun hCompileTarget decodeWindow
    jumpdestCorrect hInitialPc hInitialStack hX

theorem compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalResourceBoundaries_X
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
    (hPrimitive : RecursiveBridgePrimitiveContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel initial targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalBoundaries_X
    hSourceAccepted hSourceCompileAccepted hPrimitive hTerminal hExpr
    hInitialSharedRel hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack hX

theorem compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X
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
    (hPrimitiveSound : Locals.SourceLowering.PrimitiveSound prim)
    (hPrimitiveStack : RecursiveBridgePrimitiveStackContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel initial targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalResourceBoundaries_X
    hSourceAccepted hSourceCompileAccepted
    (RecursiveBridgePrimitiveContracts.of_stack hPrimitiveSound
      hPrimitiveStack)
    hTerminal hExpr hInitialSharedRel hSourceRun hCompileTarget decodeWindow
    jumpdestCorrect hInitialPc hInitialStack hX

/--
Preferred full-source acceptedness wrapper for the current gas-aware route.

The theorem takes full Yul source validity, current bridge feature coverage, and
object-level compiler resources separately. The old `SourceCompileAccepted`
package is constructed internally from those two honest boundaries instead of
being exposed as a mixed source/compiler premise.
-/
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X
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
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hPrimitiveSound : Locals.SourceLowering.PrimitiveSound prim)
    (hPrimitiveStack : RecursiveBridgePrimitiveStackContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
  let hCompile := (compileCheckedAssemblyTarget?_eq_some hCompileTarget).1
  let hSourceAccepted :=
    RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked
      hFullSourceAccepted hFeatureCoverage hCompile
  compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X
    hSourceAccepted
    (RecursiveBridgeCompileResources.to_sourceCompileAccepted hSourceAccepted
      hCompileResources)
    hPrimitiveSound hPrimitiveStack hTerminal hExpr hInitialSharedRel
    hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack hX

theorem compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X
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
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hPrimitiveSound : Locals.SourceLowering.PrimitiveSound prim)
    (hPrimitiveStack : RecursiveBridgePrimitiveStackContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
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
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel initial targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  let hCompile := (compileCheckedAssemblyTarget?_eq_some hCompileTarget).1
  let hSourceAccepted :=
    RecursiveBridgeSourceAccepted.ofFullCoverageAndCompileChecked
      hFullSourceAccepted hFeatureCoverage hCompile
  compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X
    hSourceAccepted
    (RecursiveBridgeCompileResources.to_sourceCompileAccepted hSourceAccepted
      hCompileResources)
    hPrimitiveSound hPrimitiveStack hTerminal hExpr hInitialSharedRel
    hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack hX

/--
Preferred full-source gas-aware wrapper using the named runner-completeness
boundary instead of a raw trace-to-`X` certificate callback.

The compiler still derives the concrete `BlockTraceResult`; the remaining
premise is exactly the gas-aware runner theorem for the assembled
program/target/initial state. The marker-only gas bookkeeping packages are
constructed internally by their checked trivial constructors.
-/
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_XRunner
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
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hPrimitiveSound : Locals.SourceLowering.PrimitiveSound prim)
    (hPrimitiveStack : RecursiveBridgePrimitiveStackContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target initial) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
  compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X
    hFullSourceAccepted hFeatureCoverage hCompileResources
    hPrimitiveSound hPrimitiveStack hTerminal hExpr hInitialSharedRel
    hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack
    (fun hTrace =>
      Assembly.GasAware.XResultRunnerCompleteness.toPreconditions
        hRunner hTrace)

theorem compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_XRunner
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
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hPrimitiveSound : Locals.SourceLowering.PrimitiveSound prim)
    (hPrimitiveStack : RecursiveBridgePrimitiveStackContracts cfg prim)
    (hTerminal :
      RecursiveBridgeTerminalContracts cfg terminalRel revertRel prim
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target initial) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel initial targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_X
    hFullSourceAccepted hFeatureCoverage hCompileResources
    hPrimitiveSound hPrimitiveStack hTerminal hExpr hInitialSharedRel
    hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack
    (fun hTrace =>
      Assembly.GasAware.XResultRunnerCompleteness.toPreconditions
        hRunner hTrace)

theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target initial) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
  compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_XRunner
    hFullSourceAccepted hFeatureCoverage hCompileResources
    Locals.SourceLowering.PrimitiveSemantics.structured_primitiveSound
    RecursiveBridgePrimitiveStackArityContracts.structured
    (RecursiveBridgeTerminalContracts.structured_of_observation hTerminal)
    hExpr hInitialSharedRel hSourceRun
    hCompileTarget decodeWindow jumpdestCorrect hInitialPc hInitialStack
    hRunner

theorem compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr : RecursiveBridgeExprResultContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target initial) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel initial targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_XRunner
    hFullSourceAccepted hFeatureCoverage hCompileResources
    Locals.SourceLowering.PrimitiveSemantics.structured_primitiveSound
    RecursiveBridgePrimitiveStackArityContracts.structured
    (RecursiveBridgeTerminalContracts.structured_of_observation hTerminal)
    hExpr hInitialSharedRel hSourceRun
    hCompileTarget decodeWindow jumpdestCorrect hInitialPc hInitialStack
    hRunner

/--
Preferred structured-primitive wrapper with the expression side condition stated
as the actual resource boundary.

Safe expression evaluation can only produce the bad result shape by succeeding
with the imported `.OutOfFuel` marker; the checkpoint cases are ruled out by
checked safe-expression facts in
`RecursiveBridgeExprResultContracts.ofNoSuccessfulOutOfFuel`.
-/
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target initial) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
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
  compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_XRunner
    hFullSourceAccepted hFeatureCoverage hCompileResources hTerminal
    (RecursiveBridgeExprResultContracts.ofNoSuccessfulOutOfFuel hExpr)
    hInitialSharedRel hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack hRunner

theorem compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
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
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target initial) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel initial targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_XRunner
    hFullSourceAccepted hFeatureCoverage hCompileResources hTerminal
    (RecursiveBridgeExprResultContracts.ofNoSuccessfulOutOfFuel hExpr)
    hInitialSharedRel hSourceRun hCompileTarget decodeWindow jumpdestCorrect
    hInitialPc hInitialStack hRunner

/--
Preferred wrapper with the EVM entry state constructed internally.

The caller supplies the initial shared EVM world; the theorem runs the target
from the canonical compiler entry state with `pc = pcAfter []` and an empty
stack. These two entry facts are therefore no longer public assumptions.
-/
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm
                (canonicalEntryState initial) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result :=
  compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_XRunner
    (initial := canonicalEntryState initial)
    hFullSourceAccepted hFeatureCoverage hCompileResources
    hTerminal
    hExpr
    (RecursiveBridgeInitialWorldRel.to_canonicalEntryState hInitialWorld)
    hSourceRun hCompileTarget
    decodeWindow jumpdestCorrect
    (canonicalEntryState_pc initial) (canonicalEntryState_stack initial)
    hRunner

theorem compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTarget? program = some (asm, target))
    (decodeWindow : Assembly.Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Assembly.Bytecode.JumpdestCorrect target)
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass :=
  compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_XRunner
    (initial := canonicalEntryState initial)
    hFullSourceAccepted hFeatureCoverage hCompileResources
    hTerminal
    hExpr
    (RecursiveBridgeInitialWorldRel.to_canonicalEntryState hInitialWorld)
    hSourceRun hCompileTarget
    decodeWindow jumpdestCorrect
    (canonicalEntryState_pc initial) (canonicalEntryState_stack initial)
    hRunner

/--
Preferred canonical-entry wrapper with bytecode bridge checks constructed by
the compiler boundary.
-/
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_bytecodeChecked_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecode? program = some (asm, target))
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm
                (canonicalEntryState initial) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result := by
  let hChecked := compileCheckedAssemblyTargetBytecode?_eq_some hCompileTarget
  exact
    compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_XRunner
      hFullSourceAccepted hFeatureCoverage hCompileResources hTerminal hExpr
      hInitialWorld hSourceRun hChecked.1 hChecked.2.1 hChecked.2.2
      hRunner

theorem compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_bytecodeChecked_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hCompileResources : RecursiveBridgeCompileResources program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecode? program = some (asm, target))
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let hChecked := compileCheckedAssemblyTargetBytecode?_eq_some hCompileTarget
  exact
    compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_XRunner
      hFullSourceAccepted hFeatureCoverage hCompileResources hTerminal hExpr
      hInitialWorld hSourceRun hChecked.1 hChecked.2.1 hChecked.2.2
      hRunner

/--
Preferred canonical-entry wrapper with lower source/direct frame resources and
bytecode bridge checks constructed by the compiler boundary.
-/
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_resourceBytecodeChecked_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResources? program =
        some (asm, target))
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm
                (canonicalEntryState initial) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result := by
  let hChecked :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hCompileTarget
  exact
    compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_bytecodeChecked_XRunner
      hFullSourceAccepted hFeatureCoverage hChecked.2 hTerminal hExpr
      hInitialWorld hSourceRun hChecked.1 hRunner

theorem compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_resourceBytecodeChecked_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hFeatureCoverage : RecursiveBridgeFeatureCoverage program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResources? program =
        some (asm, target))
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let hChecked :=
    compileCheckedAssemblyTargetBytecodeResources?_eq_some hCompileTarget
  exact
    compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_bytecodeChecked_XRunner
      hFullSourceAccepted hFeatureCoverage hChecked.2 hTerminal hExpr
      hInitialWorld hSourceRun hChecked.1 hRunner

/--
Preferred canonical-entry wrapper with source feature-family exclusions, lower
source/direct frame resources, and bytecode bridge checks constructed by one
checked compiler/source boundary.
-/
theorem compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_featureResourceBytecodeChecked_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeatures? program =
        some (asm, target))
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm
                (canonicalEntryState initial) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result := by
  let hChecked :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some
      hCompileTarget
  exact
    compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_resourceBytecodeChecked_XRunner
      hFullSourceAccepted hChecked.2 hTerminal hExpr hInitialWorld hSourceRun
      hChecked.1 hRunner

theorem compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_featureResourceBytecodeChecked_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hFullSourceAccepted : RecursiveBridgeFullSourceAccepted program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeatures? program =
        some (asm, target))
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let hChecked :=
    compileCheckedAssemblyTargetBytecodeResourcesFeatures?_eq_some
      hCompileTarget
  exact
    compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_resourceBytecodeChecked_XRunner
      hFullSourceAccepted hChecked.2 hTerminal hExpr hInitialWorld hSourceRun
      hChecked.1 hRunner

/--
Preferred canonical-entry wrapper with source-static bridge facts, source
feature-family exclusions, lower source/direct frame resources, and bytecode
bridge checks constructed by one checked compiler/source boundary.  The only
source acceptedness input left in this wrapper is the fundamental
`Reference.FullAccepted` boundary.
-/
theorem compile_whole_program_result_sound_of_fullReferenceRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hReference : Reference.FullAccepted program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Accepted asm ∧
        Assembly.Bytecode.compileBytes? asm =
          some (Assembly.Bytecode.encodeTarget target) ∧
          Assembly.Bytecode.EncodingCorrect target
            (Assembly.Bytecode.encodeTarget target) ∧
            target.GasOpcodeBoundary ∧
              Assembly.GasOracleAssumption asm
                (canonicalEntryState initial) ∧
                Assembly.OutOfGasPolicyAssumption asm
                  (canonicalEntryState initial) ∧
                  Assembly.CurrentContractProjectionAssumption asm
                    (canonicalEntryState initial) ∧
                    Assembly.Preservation.BlockTraceResult
                      asm target targetFuel (canonicalEntryState initial)
                      targetOutcome ∧
                      ∀ gas,
                        gasBound ≤ gas →
                        gas < EvmYul.UInt256.size →
                          ∃ result,
                            EvmYul.EVM.X evmFuel
                                (Assembly.GasAware.validJumps target)
                                (Assembly.GasAware.installCodeAndGas target gas
                                  (canonicalEntryState initial)) =
                              .ok result ∧
                              Assembly.GasAware.XResultAgrees targetOutcome
                                result := by
  let hChecked :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hCompileTarget
  let hFullSourceAccepted :
      RecursiveBridgeFullSourceAccepted program :=
    hChecked.2.toFullSourceAccepted hReference
  exact
    compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_featureResourceBytecodeChecked_XRunner
      hFullSourceAccepted hTerminal hExpr hInitialWorld hSourceRun
      hChecked.1 hRunner

theorem compile_whole_program_result_no_out_of_gas_of_fullReferenceRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_XRunner
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → Reference.State →
        Objects.Source.State → Prop}
    {revertRel : Reference.State → Objects.Source.State → Prop}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hReference : Reference.FullAccepted program)
    (hTerminal :
      RecursiveBridgeTerminalObservationContracts cfg terminalRel revertRel
        program)
    (hExpr :
      RecursiveBridgeExprNoSuccessfulOutOfFuelContracts cfg program)
    (hInitialWorld :
      RecursiveBridgeInitialWorldRel cfg program shared initial)
    (hSourceRun :
      RecursiveBridgeSourceRun program shared store sourceFuel referenceResult)
    (hCompileTarget :
      compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?
          program =
        some (asm, target))
    (hRunner :
      Assembly.GasAware.XResultRunnerCompleteness asm target
        (canonicalEntryState initial)) :
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ targetFuel targetOutcome evmFuel gasBound,
      Reference.runResult sourceFuel.succ program (.Ok shared store) =
        .ok referenceResult ∧
      RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg terminalRel
        revertRel program (.Ok shared store) referenceResult sourceOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Assembly.Preservation.BlockTraceResult
        asm target targetFuel (canonicalEntryState initial) targetOutcome ∧
        ∀ gas,
          gasBound ≤ gas →
          gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (Assembly.GasAware.validJumps target)
                (Assembly.GasAware.installCodeAndGas target gas
                  (canonicalEntryState initial)) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let hChecked :=
    compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?_eq_some
      hCompileTarget
  let hFullSourceAccepted :
      RecursiveBridgeFullSourceAccepted program :=
    hChecked.2.toFullSourceAccepted hReference
  exact
    compile_whole_program_result_no_out_of_gas_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitiveNoSuccessfulOutOfFuel_canonicalEntry_featureResourceBytecodeChecked_XRunner
      hFullSourceAccepted hTerminal hExpr hInitialWorld hSourceRun
      hChecked.1 hRunner

end Program
end Yul
end EvmCompiler
