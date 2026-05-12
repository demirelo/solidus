import EvmCompiler.Assembly.Assembler
import EvmYul.EVM.State

namespace EvmCompiler
namespace Assembly

namespace PrimOp

/--
Primitive operations whose non-gas behavior is supplied by the shared
EVM/Yul semantics imported from EVMYulLean.

The first assembly layer deliberately has no `GAS`, `CALL`, `CREATE`,
`SELFDESTRUCT`, or exact gas accounting in its syntax. Environment and
state-reading operations can still be treated by later source languages as
oracle inputs; at this layer they are just the same EVMYulLean state
transformers used by the target.
-/
def accepted (_op : PrimOp) : Bool :=
  true

/--
Operations whose result can depend on context outside the current stack/control
state.  This classifier is documentation in code for later compilers that want
to model those values by oracles before lowering into this assembly layer.
-/
def usesOutsideContext : PrimOp → Bool
  | .address | .origin | .caller | .callvalue | .calldataload | .calldatasize
  | .calldatacopy | .gasprice | .returndatasize | .returndatacopy
  | .blockhash | .coinbase | .timestamp | .number | .prevrandao | .gaslimit
  | .chainid | .selfbalance | .basefee | .blobhash | .blobbasefee
  | .sload | .sstore | .tload | .tstore | .log0 | .log1 | .log2 | .log3
  | .log4 | .return | .revert =>
      true
  | _ =>
      false

end PrimOp

namespace Instr

def accepted : Instr → Bool
  | .prim op => op.accepted
  | .label _ | .push _ | .jump _ | .jumpi _ => true

end Instr

namespace Program

def labels : Program → List Label
  | [] => []
  | .label name :: rest => name :: labels rest
  | _ :: rest => labels rest

def noDuplicates {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && noDuplicates xs

def labelsUnique (program : Program) : Bool :=
  noDuplicates program.labels

def instructionsAccepted (program : Program) : Bool :=
  program.all Instr.accepted

/--
The independent accepted-input checker for the labeled assembly IR.

This checker is intentionally separate from assembler success.  It rejects
duplicate labels, verifies that every jump target resolves, and keeps the
primitive-operation boundary centralized.
-/
def accepted (program : Program) : Bool :=
  instructionsAccepted program && labelsUnique program && allTargetsResolve program

end Program

/--
Named boundary for the AST-level verified compiler path.

Future source languages should target `Program` values and prove they satisfy
this predicate independently of the assembler returning `some`.
-/
structure Accepted (program : Program) : Prop where
  checked : Program.accepted program = true

/--
The trusted Lean compiler entry point for this layer: accepted labeled assembly
AST to resolved EVM assembly.
-/
def compile? (program : Program) : Option TargetProgram :=
  if Program.accepted program then
    assemble? program
  else
    none

/--
Gas boundary for the gasless source language.

The assembly AST has no `GAS` instruction.  Full EVM gas accounting is therefore
not part of source semantics; later gas-aware theorems may either assume enough
gas for a run or allow the EVM execution to stop earlier with out-of-gas.
-/
structure GasOracleAssumption (_program : Program) (_initial : EvmYul.EVM.State) :
    Prop where
  gasAccountingIsOutsideSourceSemantics : True

/--
Boundary for environmental values such as caller, calldata, block data, and
return data.  This layer reuses EVMYulLean operations directly; source languages
above it may present those values as explicit oracle inputs before lowering.
-/
structure OutsideWorldOracleAssumption
    (_program : Program) (_initial : EvmYul.EVM.State) : Prop where
  environmentalInputsComeFromStateOrOracle : True

/--
Out-of-gas policy boundary for the full EVM runner.

The checked gasless theorem proves preservation for successful source runs.
When related to gas-aware EVM execution, out-of-gas is an additional behavior:
it can interrupt the deployed bytecode before the gasless run finishes unless a
sufficient-gas premise is provided by a later theorem.
-/
structure OutOfGasPolicyAssumption
    (_program : Program) (_initial : EvmYul.EVM.State) : Prop where
  outOfGasMayInterruptFullEVMExecution : True

/--
Projection boundary for observations of full EVM state.

The current theorem compares states after erasing gas accounting fields.  It
also treats outside contracts and chain context through the EVMYulLean state or
future oracle premises rather than adding them to this assembly semantics.
-/
structure CurrentContractProjectionAssumption
    (_program : Program) (_initial : EvmYul.EVM.State) : Prop where
  compareOnlyGasErasedCurrentExecutionState : True

namespace GasOracleAssumption

def trivial {program : Program} {initial : EvmYul.EVM.State} :
    GasOracleAssumption program initial where
  gasAccountingIsOutsideSourceSemantics := True.intro

end GasOracleAssumption

namespace OutsideWorldOracleAssumption

def trivial {program : Program} {initial : EvmYul.EVM.State} :
    OutsideWorldOracleAssumption program initial where
  environmentalInputsComeFromStateOrOracle := True.intro

end OutsideWorldOracleAssumption

namespace OutOfGasPolicyAssumption

def trivial {program : Program} {initial : EvmYul.EVM.State} :
    OutOfGasPolicyAssumption program initial where
  outOfGasMayInterruptFullEVMExecution := True.intro

end OutOfGasPolicyAssumption

namespace CurrentContractProjectionAssumption

def trivial {program : Program} {initial : EvmYul.EVM.State} :
    CurrentContractProjectionAssumption program initial where
  compareOnlyGasErasedCurrentExecutionState := True.intro

end CurrentContractProjectionAssumption

/--
The extra assumptions needed when moving from the gasless AST theorem to a
gas-aware EVM execution theorem.

No field is a new trusted constant: each later theorem must either require this
structure as a hypothesis or prove the relevant field for a concrete execution.
Keeping the fields here makes the trust boundary for gas, outside context, and
out-of-gas behavior visible to later compiler layers.
-/
structure EVMExecutionAssumptions (program : Program) (initial : EvmYul.EVM.State) : Prop where
  accepted : Accepted program
  gasOracle : GasOracleAssumption program initial
  outsideWorldOracle : OutsideWorldOracleAssumption program initial
  outOfGasPolicy : OutOfGasPolicyAssumption program initial
  currentContractProjection : CurrentContractProjectionAssumption program initial

namespace EVMExecutionAssumptions

def noExtraAssumptions {program : Program} {initial : EvmYul.EVM.State}
    (accepted : Accepted program) : EVMExecutionAssumptions program initial where
  accepted := accepted
  gasOracle := GasOracleAssumption.trivial
  outsideWorldOracle := OutsideWorldOracleAssumption.trivial
  outOfGasPolicy := OutOfGasPolicyAssumption.trivial
  currentContractProjection := CurrentContractProjectionAssumption.trivial

end EVMExecutionAssumptions

end Assembly
end EvmCompiler
