import EvmCompiler.TypedCfg

namespace EvmCompiler
namespace Control

abbrev Word := Assembly.Word
abbrev EVMState := Assembly.EVMState
abbrev EVMException := Assembly.EVMException
abbrev Name := String

inductive Expr where
  | literal (value : Word)
  | prim (op : Assembly.PrimOp) (args : List Expr)
  deriving Repr

mutual
  structure Block where
    stmts : List Stmt
    deriving Repr

  inductive Stmt where
    | prim (op : Assembly.PrimOp) (args : List Expr)
    | if_ (cond : Expr) (body : Block)
    | switch (scrutinee : Expr) (cases : List (Word × Block))
        (defaultBody : Option Block)
    | for_ (init : Block) (cond : Expr) (post : Block) (body : Block)
    | brk
    | cont
    | leave
    | terminal (kind : Assembly.HaltKind) (args : List Expr)
    deriving Repr
end

structure Program where
  body : Block
  deriving Repr

end Control
end EvmCompiler
