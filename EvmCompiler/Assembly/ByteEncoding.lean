import EvmCompiler.Assembly.Assembler
import EvmYul.EVM.Semantics

namespace EvmCompiler
namespace Assembly

namespace Bytecode

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

def byteSize : TargetInstr → Nat
  | .push32 _ => 33
  | .jump | .jumpi | .jumpdest | .prim _ => 1

def encodeLocated (located : LocatedTarget) : List UInt8 :=
  encodeInstr located.instr

def encodeTarget (target : TargetProgram) : ByteArray :=
  ofList (target.code.flatMap encodeLocated)

def codeByteLength : List LocatedTarget → Nat
  | [] => 0
  | located :: rest => byteSize located.instr + codeByteLength rest

def compileBytes? (program : Program) : Option ByteArray := do
  let target ← assemble? program
  some (encodeTarget target)

end Bytecode

end Assembly
end EvmCompiler
