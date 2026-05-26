import EvmCompiler.Assembly.Syntax
import EvmYul.EVM.State

namespace EvmCompiler
namespace TypedCfg

abbrev Word := Assembly.Word
abbrev EVMState := EvmYul.EVM.State
abbrev EVMException := EvmYul.EVM.ExecutionException
abbrev Label := Assembly.Label
abbrev Name := String

/--
Symbolic stack slots used by the typed CFG.

The slots are proof-level names for stack positions. They are not runtime
values. A later lowering pass chooses concrete DUP/SWAP/POP/PUSH code that
realizes these symbolic slots on the EVM stack.
-/
inductive Slot where
  | word
  | literal (value : Word)
  | local (name : String)
  | temp (scope : Nat) (index : Nat)
  | returnPC (site : Nat)
  | returnValue (name : String) (index : Nat)
  deriving DecidableEq, Repr

abbrev Shape := List Slot

namespace Shape

def pop (n : Nat) (shape : Shape) : Shape :=
  shape.drop n

def pushWords (n : Nat) (shape : Shape) : Shape :=
  List.replicate n Slot.word ++ shape

def hasPrefix (prefixShape shape : Shape) : Prop :=
  ∃ suffix, shape = prefixShape ++ suffix

def unwindTo (target current : Shape) : Option Shape :=
  if target.length ≤ current.length ∧ current.drop (current.length - target.length) = target then
    some target
  else
    none

@[simp] theorem pushWords_zero (shape : Shape) :
    pushWords 0 shape = shape := by
  simp [pushWords]

@[simp] theorem pop_zero (shape : Shape) :
    pop 0 shape = shape := by
  simp [pop]

end Shape

/--
Primitive instructions in the typed CFG.

Control flow is deliberately not represented by raw `JUMP`/`JUMPI` here.
Transfers are terminators whose targets have declared stack shapes.
-/
inductive Instr where
  | push (value : Word)
  | prim (op : Assembly.PrimOp)
  | pop
  | dup (depth : Nat)
  | swap (depth : Nat)
  | declareLocal (name : String)
  | declareLocals (names : List String)
  | initLocals (names : List String)
  | loadLocal (name : String) (depth : Nat)
  | storeLocal (name : String) (depth : Nat)
  | assignLocals (names : List String)
  | returnLocals (names : List String)
  | unwind (target : Shape)
  deriving DecidableEq, Repr

inductive Terminator where
  | fallthrough
  | jump (target : Label)
  | jumpi (target : Label) (fallthrough : Label)
  | call (name : Name) (returnLabel : Label)
  | ret (name : Name)
  | halt (kind : Assembly.HaltKind)
  | invalid
  deriving DecidableEq, Repr

structure Block where
  label : Label
  input : Shape
  body : List Instr
  term : Terminator
  deriving Repr

structure Procedure where
  name : Name
  entry : Label
  argc : Nat
  retc : Nat
  deriving DecidableEq, Repr

namespace Procedure

def entryShape (proc : Procedure) : Shape :=
  Shape.pushWords proc.argc []

def returnShape (proc : Procedure) : Shape :=
  Shape.pushWords proc.retc []

end Procedure

structure Program where
  entry : Label
  procedures : List Procedure := []
  blocks : List Block
  deriving Repr

namespace Program

def findProc? (program : Program) (name : Name) : Option Procedure :=
  program.procedures.find? (fun proc => proc.name == name)

def findBlock? (program : Program) (label : Label) : Option Block :=
  program.blocks.find? (fun block => block.label == label)

def labelShape? (program : Program) (label : Label) : Option Shape :=
  (program.findBlock? label).map (fun block => block.input)

end Program

end TypedCfg
end EvmCompiler
