import EvmCompiler.Assembly.Bytecode

namespace EvmCompiler
namespace Assembly

/--
EVM opcodes that perform inter-contract control transfer or account creation /
destruction.  The minimal assembly layer deliberately has none of these; later
languages can model them by an oracle before lowering into this AST.
-/
def ExternalInteractionOpcode (op : EVMOp) : Prop :=
  op = EvmYul.Operation.CALL ∨
    op = EvmYul.Operation.CALLCODE ∨
    op = EvmYul.Operation.DELEGATECALL ∨
    op = EvmYul.Operation.STATICCALL ∨
    op = EvmYul.Operation.CREATE ∨
    op = EvmYul.Operation.CREATE2 ∨
    op = EvmYul.Operation.SELFDESTRUCT

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

theorem PrimOp.toEVM_not_external_interaction (op : PrimOp) :
    ¬ ExternalInteractionOpcode op.toEVM := by
  cases op <;> simp [ExternalInteractionOpcode, PrimOp.toEVM]

theorem TargetInstr.op_not_external_interaction (instr : TargetInstr) :
    ¬ ExternalInteractionOpcode instr.op := by
  cases instr with
  | push32 value =>
      simp [ExternalInteractionOpcode, TargetInstr.op]
  | jump =>
      simp [ExternalInteractionOpcode, TargetInstr.op]
  | jumpi =>
      simp [ExternalInteractionOpcode, TargetInstr.op]
  | jumpdest =>
      simp [ExternalInteractionOpcode, TargetInstr.op]
  | prim op =>
      simp [TargetInstr.op]
      exact PrimOp.toEVM_not_external_interaction op

def TargetProgram.GasOpcodeAbsent (target : TargetProgram) : Prop :=
  ∀ located,
    located ∈ target.code →
      located.instr.op ≠ (EvmYul.Operation.GAS : EVMOp)

def TargetProgram.ExternalInteractionAbsent (target : TargetProgram) : Prop :=
  ∀ located,
    located ∈ target.code →
      ¬ ExternalInteractionOpcode located.instr.op

theorem TargetProgram.no_gas_opcode (target : TargetProgram) :
    target.GasOpcodeAbsent := by
  intro located _hMem
  exact TargetInstr.op_ne_gas located.instr

theorem TargetProgram.no_external_interaction_opcode (target : TargetProgram) :
    target.ExternalInteractionAbsent := by
  intro located _hMem
  exact TargetInstr.op_not_external_interaction located.instr

theorem TargetProgram.no_gas_opcode_expanded (target : TargetProgram) :
    ∀ located,
      located ∈ target.code →
        located.instr.op ≠ (EvmYul.Operation.GAS : EVMOp) := by
  exact TargetProgram.no_gas_opcode target

theorem TargetProgram.no_external_interaction_opcode_expanded (target : TargetProgram) :
    ∀ located,
      located ∈ target.code →
        ¬ ExternalInteractionOpcode located.instr.op := by
  exact TargetProgram.no_external_interaction_opcode target

/--
Runtime assumptions added when the verified AST-level compiler theorem is used
as a claim about deployed EVM bytecode.

The first two fields are bytecode/EVMYulLean bridge obligations.  The remaining
fields name the semantic choices intentionally not modeled by the gasless source
language: gas accounting, possible out-of-gas interruption, outside-world data,
and the current-contract projection.
-/
structure RuntimeAssumptions
    (program : Program) (target : TargetProgram) (initial : EVMState) :
    Prop where
  decodeSafety : Bytecode.DecodeSafety target
  jumpdestCorrect : Bytecode.JumpdestCorrect target
  gasOracle : GasOracleAssumption program initial
  outsideWorldOracle : OutsideWorldOracleAssumption program initial
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
  outsideWorldOracle := OutsideWorldOracleAssumption.trivial
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
            target.ExternalInteractionAbsent ∧
              GasOracleAssumption program initial ∧
                OutsideWorldOracleAssumption program initial ∧
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
      TargetProgram.no_external_interaction_opcode target,
      hRuntime.gasOracle, hRuntime.outsideWorldOracle, hRuntime.outOfGasPolicy,
      hRuntime.currentContractProjection, targetFinal, hTrace, hErase⟩
  simp [Bytecode.compileBytes?, hCompile]

end Assembly
end EvmCompiler
