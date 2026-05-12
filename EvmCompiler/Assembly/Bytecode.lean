import EvmCompiler.Assembly.Preservation
import EvmYul.EVM.Semantics

namespace EvmCompiler
namespace Assembly

namespace Bytecode

/--
ByteArray constructor used by the verified encoder.

It avoids making the source compiler depend on byte parsing: the source path
ends at the labeled assembly AST.  This file is only the deployable-code bridge
from resolved assembly to EVM bytecode.
-/
def ofList (bytes : List UInt8) : ByteArray :=
  ⟨bytes.toArray⟩

def encodeWord32 (value : Word) : List UInt8 :=
  (EvmYul.toBytes! value).reverse

def encodeInstr : TargetInstr → List UInt8
  | .push32 value =>
      [EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32] ++ encodeWord32 value
  | .jump =>
      [EvmYul.EVM.serializeInstr EvmYul.Operation.JUMP]
  | .jumpi =>
      [EvmYul.EVM.serializeInstr EvmYul.Operation.JUMPI]
  | .jumpdest =>
      [EvmYul.EVM.serializeInstr EvmYul.Operation.JUMPDEST]
  | .prim op =>
      [EvmYul.EVM.serializeInstr op.toEVM]

def encodeLocated (located : LocatedTarget) : List UInt8 :=
  encodeInstr located.instr

def encodeTarget (target : TargetProgram) : ByteArray :=
  ofList (target.code.flatMap encodeLocated)

def compileBytes? (program : Program) : Option ByteArray := do
  let target ← compile? program
  some (encodeTarget target)

def decodeAt (bytes : ByteArray) (pc : Nat) (instr : TargetInstr) : Prop :=
  EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc) =
    some (instr.op, instr.arg)

def jumpdestListed (bytes : ByteArray) (pc : Nat) : Prop :=
  (EvmYul.EVM.D_J bytes (EvmYul.UInt256.ofNat 0)).contains
      (EvmYul.UInt256.ofNat pc) =
    true

/--
The byte-level facts needed to connect the AST-level compiler theorem to
EVMYulLean's bytecode decoder/fetcher.

These are deliberately not a bytecode parser.  They are the proof obligations
for the one-way encoder: the bytes emitted by `encodeTarget` decode at each
located program counter to the target instruction that the AST theorem already
uses, and EVMYul's jumpdest scanner sees every emitted `JUMPDEST`.
-/
structure EncodingCorrect (target : TargetProgram) (bytes : ByteArray) : Prop where
  bytes_eq : bytes = encodeTarget target
  decodes :
    ∀ located, located ∈ target.code → decodeAt bytes located.pc located.instr
  jumpdests :
    ∀ located,
      located ∈ target.code →
        located.instr = TargetInstr.jumpdest →
          jumpdestListed bytes located.pc

theorem decode_jump_encode :
    EvmYul.EVM.decode (ofList (encodeInstr TargetInstr.jump)) (EvmYul.UInt256.ofNat 0) =
      some (EvmYul.Operation.JUMP, none) := by
  rfl

theorem decode_jumpi_encode :
    EvmYul.EVM.decode (ofList (encodeInstr TargetInstr.jumpi)) (EvmYul.UInt256.ofNat 0) =
      some (EvmYul.Operation.JUMPI, none) := by
  rfl

theorem decode_jumpdest_encode :
    EvmYul.EVM.decode (ofList (encodeInstr TargetInstr.jumpdest)) (EvmYul.UInt256.ofNat 0) =
      some (EvmYul.Operation.JUMPDEST, none) := by
  rfl

theorem decode_prim_encode (op : PrimOp) :
    EvmYul.EVM.decode (ofList (encodeInstr (TargetInstr.prim op))) (EvmYul.UInt256.ofNat 0) =
      some (op.toEVM, none) := by
  cases op <;> rfl

/--
Top-level theorem shape for the optional bytecode bridge.

The semantic preservation work is inherited from
`compile_runN_block_trace_projected_sound`; the additional byte-level obligation
is isolated in `EncodingCorrect`, so later work can replace that assumption with
decoder/fetch proofs without changing source-language compilers that target the
assembly AST.
-/
theorem compile_runN_bytecode_bridge {program : Program}
    {target : TargetProgram} {bytes : ByteArray} {fuel : Nat}
    {state sourceState : EVMState}
    (hCompile : compile? program = some target)
    (hBytes : EncodingCorrect target bytes)
    (hRun : Source.runN program fuel state = .ok sourceState) :
    Accepted program ∧
      bytes = encodeTarget target ∧
        ∃ targetState,
          Preservation.BlockTrace program target fuel state targetState ∧
            eraseGas targetState = eraseGas sourceState := by
  obtain ⟨hAccepted, targetState, hTrace, hErase⟩ :=
    Preservation.compile_runN_block_trace_projected_sound hCompile hRun
  exact ⟨hAccepted, hBytes.bytes_eq, targetState, hTrace, hErase⟩

end Bytecode

end Assembly
end EvmCompiler
