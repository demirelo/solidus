import EvmCompiler.TypedCfg.Semantics

namespace EvmCompiler
namespace TypedCfg

namespace Instr

def lower? : Instr → Option Assembly.Program
  | .push value => some [.push value]
  | .prim op => some [.prim op]
  | .pop => some [.prim .pop]
  | .dup depth =>
      match depth with
      | 0 => some [.prim .dup1]
      | 1 => some [.prim .dup2]
      | 2 => some [.prim .dup3]
      | 3 => some [.prim .dup4]
      | 4 => some [.prim .dup5]
      | 5 => some [.prim .dup6]
      | 6 => some [.prim .dup7]
      | 7 => some [.prim .dup8]
      | 8 => some [.prim .dup9]
      | 9 => some [.prim .dup10]
      | 10 => some [.prim .dup11]
      | 11 => some [.prim .dup12]
      | 12 => some [.prim .dup13]
      | 13 => some [.prim .dup14]
      | 14 => some [.prim .dup15]
      | 15 => some [.prim .dup16]
      | _ => none
  | .swap depth =>
      match depth with
      | 0 => some [.prim .swap1]
      | 1 => some [.prim .swap2]
      | 2 => some [.prim .swap3]
      | 3 => some [.prim .swap4]
      | 4 => some [.prim .swap5]
      | 5 => some [.prim .swap6]
      | 6 => some [.prim .swap7]
      | 7 => some [.prim .swap8]
      | 8 => some [.prim .swap9]
      | 9 => some [.prim .swap10]
      | 10 => some [.prim .swap11]
      | 11 => some [.prim .swap12]
      | 12 => some [.prim .swap13]
      | 13 => some [.prim .swap14]
      | 14 => some [.prim .swap15]
      | 15 => some [.prim .swap16]
      | _ => none
  | .unwind _target => none

end Instr

namespace Terminator

def lower? : Terminator → Option Assembly.Program
  | .fallthrough => some []
  | .jump target => some [.jump target]
  | .jumpi target next => some [.jumpi target, .jump next]
  | .returnDispatch _ => none
  | .halt kind =>
      match kind with
      | .stop => some [.prim .stop]
      | .return => some [.prim .return]
      | .revert => some [.prim .revert]
      | .selfdestruct => some [.prim .selfdestruct]
  | .invalid => some [.prim .invalid]

end Terminator

namespace Block

def lowerBody? : List Instr → Option Assembly.Program
  | [] => some []
  | instr :: rest => do
      let head ← instr.lower?
      let tail ← lowerBody? rest
      some (head ++ tail)

def lower? (block : Block) : Option Assembly.Program := do
  let body ← lowerBody? block.body
  let term ← block.term.lower?
  some (.label block.label :: body ++ term)

end Block

namespace Program

def lowerBlocks? : List Block → Option Assembly.Program
  | [] => some []
  | block :: rest => do
      let head ← block.lower?
      let tail ← lowerBlocks? rest
      some (head ++ tail)

def lower? (program : Program) : Option Assembly.Program :=
  lowerBlocks? program.blocks

def Lowerable (program : Program) : Prop :=
  ∃ asm, program.lower? = some asm

end Program

end TypedCfg
end EvmCompiler
