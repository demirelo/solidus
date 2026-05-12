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

def toBytesLE : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat value :: toBytesLE width (value / 256)

def encodeWord32 (value : Word) : List UInt8 :=
  (toBytesLE 32 value.toNat).reverse

def encodeInstr : TargetInstr → List UInt8
  | .push32 value =>
      EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 :: encodeWord32 value
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

theorem fromBytes_toBytesLE (width value : Nat) :
    EvmYul.fromBytes' (toBytesLE width value) = value % (256 ^ width) := by
  induction width generalizing value with
  | zero =>
      simp [toBytesLE, EvmYul.fromBytes', Nat.mod_one]
  | succ width ih =>
      simp [toBytesLE, EvmYul.fromBytes', ih, UInt8.size]
      have h := Nat.mod_add_div (value % (256 ^ width * 256)) 256
      rw [Nat.mod_mul_left_mod, Nat.mod_mul_left_div_self] at h
      rw [Nat.pow_succ]
      exact h

theorem toBytesLE_length (width value : Nat) :
    (toBytesLE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [toBytesLE, ih]

theorem encodeWord32_length (value : Word) :
    (encodeWord32 value).length = 32 := by
  simp [encodeWord32, toBytesLE_length]

theorem uint256_ofNat_toNat (value : Word) :
    EvmYul.UInt256.ofNat value.toNat = value := by
  cases value with
  | mk val =>
      unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
      simp
      rfl

theorem uint256_toNat_lt_256_pow_32 (value : Word) :
    value.toNat < 256 ^ 32 := by
  cases value with
  | mk val =>
      unfold EvmYul.UInt256.toNat
      change ↑val < EvmYul.UInt256.size
      exact val.isLt

theorem extract_push32_payload (value : Word) :
    ((ofList
          (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
            encodeWord32 value)).extract' 1 33).data.toList =
      encodeWord32 value := by
  unfold ByteArray.extract' ByteArray.extract ByteArray.copySlice
    ByteArray.empty ByteArray.emptyWithCapacity ofList
  simp [encodeWord32_length]

theorem uint256Of_extract_push32_payload (value : Word) :
    EvmYul.uInt256OfByteArray
        ((ofList
            (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
              encodeWord32 value)).extract' 1 33) =
      value := by
  unfold EvmYul.uInt256OfByteArray
  rw [extract_push32_payload]
  unfold encodeWord32
  simp
  rw [fromBytes_toBytesLE]
  rw [Nat.mod_eq_of_lt (uint256_toNat_lt_256_pow_32 value)]
  exact uint256_ofNat_toNat value

theorem ofList_get?_zero (byte : UInt8) (rest : List UInt8) :
    (ofList (byte :: rest)).get? 0 = some byte := by
  simp [ofList, ByteArray.get?, ByteArray.get, ByteArray.size, List.size_toArray]

theorem decode_push32_encode (value : Word) :
    EvmYul.EVM.decode (ofList (encodeInstr (TargetInstr.push32 value)))
        (EvmYul.UInt256.ofNat 0) =
      some (EvmYul.Operation.PUSH32, some (value, 32)) := by
  unfold EvmYul.EVM.decode encodeInstr
  change
    (do
      let instr ←
        (ofList
            (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
              encodeWord32 value)).get? 0 >>= EvmYul.EVM.parseInstr
      let argWidth := EvmYul.EVM.argOnNBytesOfInstr instr
      some
        (instr,
          if argWidth == 0 then none
          else
            some
              (EvmYul.uInt256OfByteArray
                  ((ofList
                      (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
                        encodeWord32 value)).extract' 1 (1 + argWidth)),
                argWidth))) =
      some (EvmYul.Operation.PUSH32, some (value, 32))
  rw [ofList_get?_zero]
  change
    (do
      let instr ←
        EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32)
      let argWidth := EvmYul.EVM.argOnNBytesOfInstr instr
      some
        (instr,
          if argWidth == 0 then none
          else
            some
              (EvmYul.uInt256OfByteArray
                  ((ofList
                      (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
                        encodeWord32 value)).extract' 1 (1 + argWidth)),
                argWidth))) =
      some (EvmYul.Operation.PUSH32, some (value, 32))
  have hParse :
      EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32) =
        some EvmYul.Operation.PUSH32 := by
    rfl
  rw [hParse]
  simp [EvmYul.EVM.argOnNBytesOfInstr]
  exact uint256Of_extract_push32_payload value

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
