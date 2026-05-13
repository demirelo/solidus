import EvmCompiler.Assembly

namespace EvmCompiler
namespace Structured

abbrev Word := Assembly.Word
abbrev EVMState := Assembly.EVMState
abbrev EVMException := Assembly.EVMException

/--
Primitive operations admitted in the first structured-control layer.

This layer is about control flow, not about variables or stack scheduling.  The
expression/code fragments are therefore deliberately tiny and pure enough to be
used as branch conditions without adding memory, storage, calls, or gas.
-/
inductive BasicOp where
  | add
  | sub
  | lt
  | gt
  | eq
  | iszero
  deriving DecidableEq, Repr

namespace BasicOp

def toPrimOp : BasicOp → Assembly.PrimOp
  | .add => .add
  | .sub => .sub
  | .lt => .lt
  | .gt => .gt
  | .eq => .eq
  | .iszero => .iszero

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
