import EvmCompiler.Assembly

namespace EvmCompiler
namespace Structured

abbrev Word := Assembly.Word
abbrev EVMState := Assembly.EVMState
abbrev EVMException := Assembly.EVMException

/--
Primitive operations admitted as ordinary structured-control statements.

This layer is about structured sequencing and branch/loop lowering, not about
variables or stack scheduling. The primitive surface is the continuing subset
of the labeled assembly layer: it reuses the same EVMYulLean state semantics
for arithmetic, memory, storage, environment, account/code reads, copying, logs,
dup/swap, and `INVALID`. It excludes opcodes that require a separate outcome or
control-transfer model at this layer: `GAS`, `PC`, raw jumps, `STOP`,
`RETURN`/`REVERT`, `SELFDESTRUCT`, and the call/create family.
-/
inductive BasicOp where
  | add | mul | sub | div | sdiv | mod | smod | addmod | mulmod | exp | signextend
  | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte | shl | shr | sar
  | address | balance | origin | caller | callvalue | calldataload | calldatasize
  | calldatacopy | codesize | codecopy | gasprice | extcodesize | extcodecopy
  | returndatasize | returndatacopy | extcodehash
  | blockhash | coinbase | timestamp | number | prevrandao | gaslimit | chainid
  | selfbalance | basefee | blobhash | blobbasefee
  | pop | mload | mstore | sload | sstore | mstore8 | msize | tload | tstore
  | mcopy
  | keccak256
  | dup1 | dup2 | dup3 | dup4 | dup5 | dup6 | dup7 | dup8
  | dup9 | dup10 | dup11 | dup12 | dup13 | dup14 | dup15 | dup16
  | swap1 | swap2 | swap3 | swap4 | swap5 | swap6 | swap7 | swap8
  | swap9 | swap10 | swap11 | swap12 | swap13 | swap14 | swap15 | swap16
  | log0 | log1 | log2 | log3 | log4
  | invalid
  deriving DecidableEq, Repr

namespace BasicOp

def toPrimOp : BasicOp → Assembly.PrimOp
  | .add => .add
  | .mul => .mul
  | .sub => .sub
  | .div => .div
  | .sdiv => .sdiv
  | .mod => .mod
  | .smod => .smod
  | .addmod => .addmod
  | .mulmod => .mulmod
  | .exp => .exp
  | .signextend => .signextend
  | .lt => .lt
  | .gt => .gt
  | .slt => .slt
  | .sgt => .sgt
  | .eq => .eq
  | .iszero => .iszero
  | .and => .and
  | .or => .or
  | .xor => .xor
  | .not => .not
  | .byte => .byte
  | .shl => .shl
  | .shr => .shr
  | .sar => .sar
  | .address => .address
  | .balance => .balance
  | .origin => .origin
  | .caller => .caller
  | .callvalue => .callvalue
  | .calldataload => .calldataload
  | .calldatasize => .calldatasize
  | .calldatacopy => .calldatacopy
  | .codesize => .codesize
  | .codecopy => .codecopy
  | .gasprice => .gasprice
  | .extcodesize => .extcodesize
  | .extcodecopy => .extcodecopy
  | .returndatasize => .returndatasize
  | .returndatacopy => .returndatacopy
  | .extcodehash => .extcodehash
  | .blockhash => .blockhash
  | .coinbase => .coinbase
  | .timestamp => .timestamp
  | .number => .number
  | .prevrandao => .prevrandao
  | .gaslimit => .gaslimit
  | .chainid => .chainid
  | .selfbalance => .selfbalance
  | .basefee => .basefee
  | .blobhash => .blobhash
  | .blobbasefee => .blobbasefee
  | .pop => .pop
  | .mload => .mload
  | .mstore => .mstore
  | .sload => .sload
  | .sstore => .sstore
  | .mstore8 => .mstore8
  | .msize => .msize
  | .tload => .tload
  | .tstore => .tstore
  | .mcopy => .mcopy
  | .keccak256 => .keccak256
  | .dup1 => .dup1
  | .dup2 => .dup2
  | .dup3 => .dup3
  | .dup4 => .dup4
  | .dup5 => .dup5
  | .dup6 => .dup6
  | .dup7 => .dup7
  | .dup8 => .dup8
  | .dup9 => .dup9
  | .dup10 => .dup10
  | .dup11 => .dup11
  | .dup12 => .dup12
  | .dup13 => .dup13
  | .dup14 => .dup14
  | .dup15 => .dup15
  | .dup16 => .dup16
  | .swap1 => .swap1
  | .swap2 => .swap2
  | .swap3 => .swap3
  | .swap4 => .swap4
  | .swap5 => .swap5
  | .swap6 => .swap6
  | .swap7 => .swap7
  | .swap8 => .swap8
  | .swap9 => .swap9
  | .swap10 => .swap10
  | .swap11 => .swap11
  | .swap12 => .swap12
  | .swap13 => .swap13
  | .swap14 => .swap14
  | .swap15 => .swap15
  | .swap16 => .swap16
  | .log0 => .log0
  | .log1 => .log1
  | .log2 => .log2
  | .log3 => .log3
  | .log4 => .log4
  | .invalid => .invalid

end BasicOp

inductive BasicInstr where
  | push (value : Word)
  | op (op : BasicOp)
  deriving DecidableEq, Repr

abbrev Code := List BasicInstr

mutual
  structure Block where
    stmts : List Stmt

  /--
  Structured control over certified straight-line stack code.

  `for_ init cond post body` follows Yul's shape: the condition is code that
  leaves one word on top of the stack, while init/post/body are blocks.
  Variables, block-local scopes, break/continue, switch, leave, and functions
  intentionally belong to later layers.
  -/
  inductive Stmt where
    | code (code : Code)
    | ifElse (cond : Code) (thenBody : Block) (elseBody : Block)
    | for_ (init : Block) (cond : Code) (post : Block) (body : Block)
end

structure Program where
  body : Block

namespace BasicInstr

def toAssembly : BasicInstr → Assembly.Instr
  | .push value => .push value
  | .op basicOp => .prim basicOp.toPrimOp

end BasicInstr

namespace Code

def toAssembly (code : Code) : Assembly.Program :=
  code.map BasicInstr.toAssembly

end Code

end Structured
end EvmCompiler
