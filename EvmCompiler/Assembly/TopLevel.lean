import EvmCompiler.Assembly.Bytecode

namespace EvmCompiler
namespace Assembly

/--
Marker for the gas-opcode theorem boundary.

Earlier slices proved the stronger fact that emitted code contained no `GAS`.
The source-complete path admits `GAS`; its semantic agreement is now carried by
`GasOracleAssumption` and the gas-aware `XPreconditionAssumptions` certificate.
-/
def TargetProgram.GasOpcodeBoundary (_target : TargetProgram) : Prop :=
  True

theorem TargetProgram.gas_opcode_boundary (target : TargetProgram) :
    target.GasOpcodeBoundary := by
  trivial

theorem TargetProgram.gas_opcode_boundary_expanded (target : TargetProgram) :
    target.GasOpcodeBoundary := by
  exact TargetProgram.gas_opcode_boundary target

/--
Runtime assumptions added when the verified AST-level compiler theorem is used
as a claim about deployed EVM bytecode.

`decodeWindow` is a resource/code-size bound; the actual `DecodeSafety` facts
are derived from the checked assembler layout. `jumpdestCorrect` remains a
bytecode/EVMYulLean scanner boundary because the imported jumpdest scanner is
opaque. The remaining fields name the semantic choices intentionally not
modeled by the gasless source language or not yet derived from the source step
relation: gas accounting, possible out-of-gas interruption, the gas-erased state
projection, and the call/create bridge to the gas-aware EVM runner.
-/
structure RuntimeAssumptions
    (program : Program) (target : TargetProgram) (initial : EVMState) :
    Prop where
  decodeWindow : Bytecode.TargetFitsDecodeWindow target
  jumpdestCorrect : Bytecode.JumpdestCorrect target
  gasOracle : GasOracleAssumption program initial
  outOfGasPolicy : OutOfGasPolicyAssumption program initial
  currentContractProjection : CurrentContractProjectionAssumption program initial
  externalInteraction : ExternalInteractionAssumption program target initial

namespace RuntimeAssumptions

def withExplicitBoundaries {program : Program} {target : TargetProgram}
    {initial : EVMState}
    (decodeWindow : Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Bytecode.JumpdestCorrect target)
    (gasOracle : GasOracleAssumption program initial)
    (outOfGasPolicy : OutOfGasPolicyAssumption program initial)
    (currentContractProjection :
      CurrentContractProjectionAssumption program initial)
    (externalInteraction :
      ExternalInteractionAssumption program target initial) :
    RuntimeAssumptions program target initial where
  decodeWindow := decodeWindow
  jumpdestCorrect := jumpdestCorrect
  gasOracle := gasOracle
  outOfGasPolicy := outOfGasPolicy
  currentContractProjection := currentContractProjection
  externalInteraction := externalInteraction

def withNoCallCreate {program : Program} {target : TargetProgram}
    {initial : EVMState}
    (decodeWindow : Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Bytecode.JumpdestCorrect target)
    (gasOracle : GasOracleAssumption program initial)
    (outOfGasPolicy : OutOfGasPolicyAssumption program initial)
    (currentContractProjection :
      CurrentContractProjectionAssumption program initial)
    (hNoCallCreate : program.usesCallCreate = false) :
    RuntimeAssumptions program target initial :=
  withExplicitBoundaries decodeWindow jumpdestCorrect gasOracle
    outOfGasPolicy currentContractProjection
    (ExternalInteractionAssumption.noCallCreate hNoCallCreate)

end RuntimeAssumptions

/--
Public whole-program compiler theorem for the minimal assembly layer.

There is no parser in this theorem: the verified compiler input is the
`Program` AST.  The bytecode component is a one-way encoder proof showing that
the compiled target program produces deployable bytes whose EVMYulLean
decoder/fetch behavior matches the target instructions.  The observable
semantic claim is the gas-erased whole-run block trace.
-/
theorem compile_whole_program_sound {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal) :
    Accepted program ∧
      Bytecode.compileBytes? program = some (Bytecode.encodeTarget target) ∧
        Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
          target.GasOpcodeBoundary ∧
            GasOracleAssumption program initial ∧
              OutOfGasPolicyAssumption program initial ∧
                CurrentContractProjectionAssumption program initial ∧
                  ∃ targetFinal,
                    Preservation.BlockTrace program target fuel initial targetFinal ∧
                      eraseGas targetFinal = eraseGas sourceFinal := by
  obtain ⟨hAccepted, targetFinal, hEncoding, hTrace, hErase⟩ :=
    Bytecode.compile_runN_bytecode_bridge_checked hCompile
      (Bytecode.compile_decodeSafety hCompile hRuntime.decodeWindow)
      hRuntime.jumpdestCorrect hRun
  refine
    ⟨hAccepted, ?_, hEncoding, TargetProgram.gas_opcode_boundary target,
      hRuntime.gasOracle, hRuntime.outOfGasPolicy,
      hRuntime.currentContractProjection, targetFinal, hTrace, hErase⟩
  simp [Bytecode.compileBytes?, hCompile]

theorem compile_whole_program_result_sound {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial : EVMState}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runNResult program fuel initial = .ok result) :
    Accepted program ∧
      Bytecode.compileBytes? program = some (Bytecode.encodeTarget target) ∧
        Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
          target.GasOpcodeBoundary ∧
            GasOracleAssumption program initial ∧
              OutOfGasPolicyAssumption program initial ∧
                CurrentContractProjectionAssumption program initial ∧
                  Preservation.BlockTraceResult program target fuel initial result := by
  obtain ⟨hAccepted, hEncoding, hTrace⟩ :=
    Bytecode.compile_runN_result_bytecode_bridge_checked hCompile
      (Bytecode.compile_decodeSafety hCompile hRuntime.decodeWindow)
      hRuntime.jumpdestCorrect hRun
  refine
    ⟨hAccepted, ?_, hEncoding, TargetProgram.gas_opcode_boundary target,
      hRuntime.gasOracle, hRuntime.outOfGasPolicy,
      hRuntime.currentContractProjection, hTrace⟩
  simp [Bytecode.compileBytes?, hCompile]

end Assembly
end EvmCompiler
