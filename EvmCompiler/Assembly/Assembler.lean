import EvmCompiler.Assembly.Syntax

namespace EvmCompiler
namespace Assembly

inductive TargetInstr where
  | push32 (value : Word)
  | jump
  | jumpi
  | jumpdest
  | prim (op : PrimOp)
  deriving DecidableEq, Repr

structure LocatedTarget where
  pc : Nat
  instr : TargetInstr
  deriving DecidableEq, Repr

structure TargetProgram where
  code : List LocatedTarget
  deriving DecidableEq, Repr

namespace TargetInstr

def op : TargetInstr → EVMOp
  | .push32 _ => EvmYul.Operation.PUSH32
  | .jump => EvmYul.Operation.JUMP
  | .jumpi => EvmYul.Operation.JUMPI
  | .jumpdest => EvmYul.Operation.JUMPDEST
  | .prim op => op.toEVM

def arg : TargetInstr → Option (Word × Nat)
  | .push32 value => some (value, 32)
  | .jump | .jumpi | .jumpdest | .prim _ => none

end TargetInstr

namespace Program

def labelPcFrom : Program → Nat → Label → Option Nat
  | [], _, _ => none
  | instr :: rest, pc, target =>
      match instr with
      | .label name =>
          if name = target then
            some pc
          else
            labelPcFrom rest (pc + instr.byteSize) target
      | _ =>
          labelPcFrom rest (pc + instr.byteSize) target

def labelPc (program : Program) (target : Label) : Option Nat :=
  labelPcFrom program 0 target

def instrAtPcFrom : Program → Nat → Nat → Option (Nat × Instr)
  | [], _, _ => none
  | instr :: rest, pc, query =>
      if query = pc then
        some (pc, instr)
      else
        instrAtPcFrom rest (pc + instr.byteSize) query

def instrAtPc (program : Program) (pc : Nat) : Option (Nat × Instr) :=
  instrAtPcFrom program 0 pc

def allTargetsResolve (program : Program) : Bool :=
  program.all fun instr =>
    instr.targets.all fun target =>
      (labelPc program target).isSome

end Program

def emitInstr? (program : Program) (pc : Nat) : Instr → Option (List LocatedTarget)
  | .label _ =>
      some [{ pc := pc, instr := TargetInstr.jumpdest }]
  | .prim op =>
      some [{ pc := pc, instr := TargetInstr.prim op }]
  | .push value =>
      some [{ pc := pc, instr := TargetInstr.push32 value }]
  | .jump target => do
      let dest ← Program.labelPc program target
      some
        [ { pc := pc, instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) }
        , { pc := pc + Instr.push32Size, instr := TargetInstr.jump }
        ]
  | .jumpi target => do
      let dest ← Program.labelPc program target
      some
        [ { pc := pc, instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) }
        , { pc := pc + Instr.push32Size, instr := TargetInstr.jumpi }
        ]

def emitFrom? (program : Program) : Program → Nat → Option (List LocatedTarget)
  | [], _ => some []
  | instr :: rest, pc => do
      let here ← emitInstr? program pc instr
      let there ← emitFrom? program rest (pc + instr.byteSize)
      some (here ++ there)

def emit? (program : Program) : Option (List LocatedTarget) :=
  emitFrom? program program 0

def assemble? (program : Program) : Option TargetProgram := do
  let code ← emit? program
  some { code := code }

namespace TargetProgram

def fetch (target : TargetProgram) (pc : Nat) : Option TargetInstr :=
  match target.code.find? (fun located => located.pc == pc) with
  | some located => some located.instr
  | none => none

end TargetProgram

end Assembly
end EvmCompiler
