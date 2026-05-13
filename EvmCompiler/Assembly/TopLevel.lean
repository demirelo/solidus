import EvmCompiler.Assembly.Bytecode

namespace EvmCompiler
namespace Assembly

theorem PrimOp.toEVM_ne_gas (op : PrimOp) :
    op.toEVM ≠ (EvmYul.Operation.GAS : EVMOp) := by
  cases op <;> simp [PrimOp.toEVM]

theorem TargetInstr.op_ne_gas (instr : TargetInstr) :
    instr.op ≠ (EvmYul.Operation.GAS : EVMOp) := by
  cases instr with
  | push32 value =>
      simp [TargetInstr.op]
  | jump =>
      simp [TargetInstr.op]
  | jumpi =>
      simp [TargetInstr.op]
  | jumpdest =>
      simp [TargetInstr.op]
  | prim op =>
      simp [TargetInstr.op]
      exact PrimOp.toEVM_ne_gas op

def TargetProgram.GasOpcodeAbsent (target : TargetProgram) : Prop :=
  ∀ located,
    located ∈ target.code →
      located.instr.op ≠ (EvmYul.Operation.GAS : EVMOp)

theorem TargetProgram.no_gas_opcode (target : TargetProgram) :
    target.GasOpcodeAbsent := by
  intro located _hMem
  exact TargetInstr.op_ne_gas located.instr

theorem TargetProgram.no_gas_opcode_expanded (target : TargetProgram) :
    ∀ located,
      located ∈ target.code →
        located.instr.op ≠ (EvmYul.Operation.GAS : EVMOp) := by
  exact TargetProgram.no_gas_opcode target

/--
Runtime assumptions added when the verified AST-level compiler theorem is used
as a claim about deployed EVM bytecode.

The first two fields are bytecode/EVMYulLean bridge obligations.  The remaining
fields name the semantic choices intentionally not modeled by the gasless source
language: gas accounting, possible out-of-gas interruption, and the gas-erased
state projection. External-facing EVM operations are not abstracted here; they
reuse EVMYulLean's state semantics directly.
-/
structure RuntimeAssumptions
    (program : Program) (target : TargetProgram) (initial : EVMState) :
    Prop where
  decodeSafety : Bytecode.DecodeSafety target
  jumpdestCorrect : Bytecode.JumpdestCorrect target
  gasOracle : GasOracleAssumption program initial
  outOfGasPolicy : OutOfGasPolicyAssumption program initial
  currentContractProjection : CurrentContractProjectionAssumption program initial

namespace RuntimeAssumptions

def noExtraSemanticAssumptions {program : Program} {target : TargetProgram}
    {initial : EVMState}
    (decodeSafety : Bytecode.DecodeSafety target)
    (jumpdestCorrect : Bytecode.JumpdestCorrect target) :
    RuntimeAssumptions program target initial where
  decodeSafety := decodeSafety
  jumpdestCorrect := jumpdestCorrect
  gasOracle := GasOracleAssumption.trivial
  outOfGasPolicy := OutOfGasPolicyAssumption.trivial
  currentContractProjection := CurrentContractProjectionAssumption.trivial

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
          target.GasOpcodeAbsent ∧
            GasOracleAssumption program initial ∧
              OutOfGasPolicyAssumption program initial ∧
                CurrentContractProjectionAssumption program initial ∧
                  ∃ targetFinal,
                    Preservation.BlockTrace program target fuel initial targetFinal ∧
                      eraseGas targetFinal = eraseGas sourceFinal := by
  obtain ⟨hAccepted, targetFinal, hEncoding, hTrace, hErase⟩ :=
    Bytecode.compile_runN_bytecode_bridge_checked hCompile
      hRuntime.decodeSafety hRuntime.jumpdestCorrect hRun
  refine
    ⟨hAccepted, ?_, hEncoding, TargetProgram.no_gas_opcode target,
      hRuntime.gasOracle, hRuntime.outOfGasPolicy,
      hRuntime.currentContractProjection, targetFinal, hTrace, hErase⟩
  simp [Bytecode.compileBytes?, hCompile]

end Assembly
end EvmCompiler
