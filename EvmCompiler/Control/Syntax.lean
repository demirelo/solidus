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

mutual
  def Block.wf (canBreak canContinue canLeave : Bool) : Block → Bool
    | ⟨stmts⟩ => StmtList.wf canBreak canContinue canLeave stmts

  def Stmt.wf (canBreak canContinue canLeave : Bool) : Stmt → Bool
    | .prim _ _ => true
    | .if_ _ body => body.wf canBreak canContinue canLeave
    | .switch _ cases defaultBody =>
        SwitchCases.wf canBreak canContinue canLeave cases &&
          SwitchDefault.wf canBreak canContinue canLeave defaultBody
    | .for_ init _ post body =>
        init.wf false false canLeave &&
          post.wf false false canLeave &&
            body.wf true true canLeave
    | .brk => canBreak
    | .cont => canContinue
    | .leave => canLeave
    | .terminal _ _ => true

  def StmtList.wf (canBreak canContinue canLeave : Bool) :
      List Stmt → Bool
    | [] => true
    | stmt :: rest =>
        stmt.wf canBreak canContinue canLeave &&
          StmtList.wf canBreak canContinue canLeave rest

  def SwitchCases.wf (canBreak canContinue canLeave : Bool) :
      List (Word × Block) → Bool
    | [] => true
    | (_value, body) :: rest =>
        body.wf canBreak canContinue canLeave &&
          SwitchCases.wf canBreak canContinue canLeave rest

  def SwitchDefault.wf (canBreak canContinue canLeave : Bool) :
      Option Block → Bool
    | none => true
    | some body => body.wf canBreak canContinue canLeave
end

namespace Program

def accepted? (program : Program) : Bool :=
  program.body.wf false false false

def Accepted (program : Program) : Prop :=
  program.accepted? = true

end Program

end Control
end EvmCompiler
