import EvmCompiler.Assembly

namespace EvmCompiler
namespace StackFreeCfg

abbrev Word := Assembly.Word
abbrev EVMException := Assembly.EVMException
abbrev Name := String

/--
Stack-free expressions.

Primitive calls are value-level calls: the arguments are source expressions and
the result is a list of values. Raw stack operations, labels, byte offsets, and
return tokens are not part of this syntax.
-/
inductive Expr where
  | literal (value : Word)
  | var (name : Name)
  | prim (op : Assembly.PrimOp) (args : List Expr)
  deriving Repr

mutual
  structure Block where
    stmts : List Stmt
    deriving Repr

  /--
  The first stack-free CFG source language.

  Procedure calls are statement-level: they evaluate argument expressions,
  execute a named procedure, and assign all return values to explicit targets.
  Yul function-call expressions can lower into temporaries plus this statement
  form in the Yul-to-StackFreeCfg pass.
  -/
  inductive Stmt where
    | expr (expr : Expr)
    | decl (names : List Name) (value? : Option Expr)
    | assign (names : List Name) (value : Expr)
    | block (body : Block)
    | if_ (cond : Expr) (body : Block)
    | switch (scrutinee : Expr) (cases : List (Word × Block))
        (defaultBody : Option Block)
    | for_ (init : Block) (cond : Expr) (post : Block) (body : Block)
    | brk
    | cont
    | leave
    | call (targets : List Name) (functionName : Name) (args : List Expr)
    | terminal (kind : Assembly.HaltKind) (args : List Expr)
    | invalid
    deriving Repr
end

structure Proc where
  name : Name
  params : List Name
  returns : List Name
  body : Block
  deriving Repr

structure Program where
  procs : List Proc := []
  body : Block
  deriving Repr

namespace Program

def findProc? (program : Program) (name : Name) : Option Proc :=
  program.procs.find? (fun proc => proc.name == name)

end Program

end StackFreeCfg
end EvmCompiler
