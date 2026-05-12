import EvmYul.Operations
import EvmYul.UInt256

namespace EvmCompiler
namespace Assembly

abbrev Label := String
abbrev Word := EvmYul.UInt256
abbrev EVMOp := EvmYul.Operation EvmYul.OperationType.EVM

/--
Primitive operations admitted directly into the first assembly layer.

Control transfer, labels, and pushes are represented by dedicated assembly
instructions. `GAS` and external-call/create opcodes are intentionally absent
from this verified deterministic slice; they will enter through oracle/refinement
relations rather than by giving the source language gas accounting.
-/
inductive PrimOp where
  | stop
  | add | mul | sub | div | sdiv | mod | smod | addmod | mulmod | exp | signextend
  | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte | shl | shr | sar
  | address | origin | caller | callvalue | calldataload | calldatasize | calldatacopy
  | gasprice | returndatasize | returndatacopy
  | blockhash | coinbase | timestamp | number | prevrandao | gaslimit | chainid
  | selfbalance | basefee | blobhash | blobbasefee
  | pop | mload | mstore | sload | sstore | mstore8 | msize | tload | tstore | mcopy
  | keccak256
  | log0 | log1 | log2 | log3 | log4
  | return | revert | invalid
  deriving DecidableEq, Repr

namespace PrimOp

def toEVM : PrimOp → EVMOp
  | .stop => EvmYul.Operation.STOP
  | .add => EvmYul.Operation.ADD
  | .mul => EvmYul.Operation.MUL
  | .sub => EvmYul.Operation.SUB
  | .div => EvmYul.Operation.DIV
  | .sdiv => EvmYul.Operation.SDIV
  | .mod => EvmYul.Operation.MOD
  | .smod => EvmYul.Operation.SMOD
  | .addmod => EvmYul.Operation.ADDMOD
  | .mulmod => EvmYul.Operation.MULMOD
  | .exp => EvmYul.Operation.EXP
  | .signextend => EvmYul.Operation.SIGNEXTEND
  | .lt => EvmYul.Operation.LT
  | .gt => EvmYul.Operation.GT
  | .slt => EvmYul.Operation.SLT
  | .sgt => EvmYul.Operation.SGT
  | .eq => EvmYul.Operation.EQ
  | .iszero => EvmYul.Operation.ISZERO
  | .and => EvmYul.Operation.AND
  | .or => EvmYul.Operation.OR
  | .xor => EvmYul.Operation.XOR
  | .not => EvmYul.Operation.NOT
  | .byte => EvmYul.Operation.BYTE
  | .shl => EvmYul.Operation.SHL
  | .shr => EvmYul.Operation.SHR
  | .sar => EvmYul.Operation.SAR
  | .address => EvmYul.Operation.ADDRESS
  | .origin => EvmYul.Operation.ORIGIN
  | .caller => EvmYul.Operation.CALLER
  | .callvalue => EvmYul.Operation.CALLVALUE
  | .calldataload => EvmYul.Operation.CALLDATALOAD
  | .calldatasize => EvmYul.Operation.CALLDATASIZE
  | .calldatacopy => EvmYul.Operation.CALLDATACOPY
  | .gasprice => EvmYul.Operation.GASPRICE
  | .returndatasize => EvmYul.Operation.RETURNDATASIZE
  | .returndatacopy => EvmYul.Operation.RETURNDATACOPY
  | .blockhash => EvmYul.Operation.BLOCKHASH
  | .coinbase => EvmYul.Operation.COINBASE
  | .timestamp => EvmYul.Operation.TIMESTAMP
  | .number => EvmYul.Operation.NUMBER
  | .prevrandao => EvmYul.Operation.PREVRANDAO
  | .gaslimit => EvmYul.Operation.GASLIMIT
  | .chainid => EvmYul.Operation.CHAINID
  | .selfbalance => EvmYul.Operation.SELFBALANCE
  | .basefee => EvmYul.Operation.BASEFEE
  | .blobhash => EvmYul.Operation.BLOBHASH
  | .blobbasefee => EvmYul.Operation.BLOBBASEFEE
  | .pop => EvmYul.Operation.POP
  | .mload => EvmYul.Operation.MLOAD
  | .mstore => EvmYul.Operation.MSTORE
  | .sload => EvmYul.Operation.SLOAD
  | .sstore => EvmYul.Operation.SSTORE
  | .mstore8 => EvmYul.Operation.MSTORE8
  | .msize => EvmYul.Operation.MSIZE
  | .tload => EvmYul.Operation.TLOAD
  | .tstore => EvmYul.Operation.TSTORE
  | .mcopy => EvmYul.Operation.MCOPY
  | .keccak256 => EvmYul.Operation.KECCAK256
  | .log0 => EvmYul.Operation.LOG0
  | .log1 => EvmYul.Operation.LOG1
  | .log2 => EvmYul.Operation.LOG2
  | .log3 => EvmYul.Operation.LOG3
  | .log4 => EvmYul.Operation.LOG4
  | .return => EvmYul.Operation.RETURN
  | .revert => EvmYul.Operation.REVERT
  | .invalid => EvmYul.Operation.INVALID

end PrimOp

inductive Instr where
  | label (name : Label)
  | prim (op : PrimOp)
  | push (value : Word)
  | jump (target : Label)
  | jumpi (target : Label)
  deriving DecidableEq, Repr

abbrev Program := List Instr

namespace Instr

def push32Size : Nat := 33
def jumpSize : Nat := push32Size + 1

def byteSize : Instr → Nat
  | .label _ => 1
  | .prim _ => 1
  | .push _ => push32Size
  | .jump _ => jumpSize
  | .jumpi _ => jumpSize

def targets : Instr → List Label
  | .jump target => [target]
  | .jumpi target => [target]
  | _ => []

end Instr

end Assembly
end EvmCompiler

