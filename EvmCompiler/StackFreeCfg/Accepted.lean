import EvmCompiler.StackFreeCfg.Semantics

namespace EvmCompiler
namespace StackFreeCfg

namespace Prim

def isUnsupportedSourceOp : Assembly.PrimOp → Bool
  | .pc
  | .dup1 | .dup2 | .dup3 | .dup4
  | .dup5 | .dup6 | .dup7 | .dup8
  | .dup9 | .dup10 | .dup11 | .dup12
  | .dup13 | .dup14 | .dup15 | .dup16
  | .swap1 | .swap2 | .swap3 | .swap4
  | .swap5 | .swap6 | .swap7 | .swap8
  | .swap9 | .swap10 | .swap11 | .swap12
  | .swap13 | .swap14 | .swap15 | .swap16 => true
  | _ => false

/--
Source-level primitive arity.

`pop(x)` is allowed as a value-level zero-result primitive. Raw `dup`/`swap`
are rejected because they expose stack positions and are not Yul source
constructs. `pc` is rejected because this source layer has no program-counter
semantics; Yul does not expose it, and any future PC-like feature should be an
explicit oracle. Terminal opcodes are represented by `Stmt.terminal`.
-/
def sourceArity? (op : Assembly.PrimOp) : Option (Nat × Nat) :=
  if isUnsupportedSourceOp op || op.haltKind?.isSome then
    none
  else
    op.stackEffect?

end Prim

/--
A source-facing primitive profile.

This is deliberately separate from `PrimitiveSemantics`: acceptedness needs
only arities, while the interpreter is parametric over the actual primitive
meaning. That keeps PC/gas/external-call contracts explicit at the bridge that
chooses the primitive semantics.
-/
structure PrimitiveProfile where
  arity? : Assembly.PrimOp → Option (Nat × Nat) := Prim.sourceArity?
  terminalArity : Assembly.HaltKind → Nat := Assembly.HaltKind.argCount

namespace Signature

structure T where
  name : Name
  params : Nat
  returns : Nat

def ofProc (proc : Proc) : T :=
  { name := proc.name, params := proc.params.length,
    returns := proc.returns.length }

def find? (sigs : List T) (name : Name) : Option T :=
  sigs.find? (fun sig => sig.name == name)

end Signature

namespace Scope

def Contains (env : List Name) (name : Name) : Prop :=
  name ∈ env

def containsAll (env names : List Name) : Prop :=
  ∀ name, name ∈ names → Contains env name

def containsAll? (env names : List Name) : Bool :=
  names.all (fun name => decide (name ∈ env))

def disjoint (left right : List Name) : Prop :=
  ∀ name, name ∈ left → name ∉ right

def disjoint? (left right : List Name) : Bool :=
  left.all (fun name => decide (name ∉ right))

def nonempty? (names : List Name) : Bool :=
  !names.isEmpty

def extend (env names : List Name) : List Name :=
  names ++ env

mutual
  def Expr.Arity (profile : PrimitiveProfile) (env : List Name) :
      Expr → Option Nat
    | .literal _value => some 1
    | .var name =>
        if name ∈ env then some 1 else none
    | .prim op args => do
        let (inputArity, outputArity) ← profile.arity? op
        let argArity ← ExprList.Arity profile env args
        if argArity = inputArity then
          some outputArity
        else
          none

  def ExprList.Arity (profile : PrimitiveProfile) (env : List Name) :
      List Expr → Option Nat
    | [] => some 0
    | expr :: rest => do
        let head ← Expr.Arity profile env expr
        if head = 1 then
          let tail ← ExprList.Arity profile env rest
          some (head + tail)
        else
          none
end

def Expr.One (profile : PrimitiveProfile) (env : List Name)
    (expr : Expr) : Prop :=
  Expr.Arity profile env expr = some 1

def Expr.Zero (profile : PrimitiveProfile) (env : List Name)
    (expr : Expr) : Prop :=
  Expr.Arity profile env expr = some 0

def ExprList.AllOne (profile : PrimitiveProfile) (env : List Name) :
    List Expr → Prop
  | [] => True
  | expr :: rest =>
      Expr.One profile env expr ∧ ExprList.AllOne profile env rest

def Expr.one? (profile : PrimitiveProfile) (env : List Name)
    (expr : Expr) : Bool :=
  decide (Expr.Arity profile env expr = some 1)

def Expr.zero? (profile : PrimitiveProfile) (env : List Name)
    (expr : Expr) : Bool :=
  decide (Expr.Arity profile env expr = some 0)

def Expr.arityIs? (profile : PrimitiveProfile) (env : List Name)
    (expr : Expr) (arity : Nat) : Bool :=
  decide (Expr.Arity profile env expr = some arity)

def ExprList.allOne? (profile : PrimitiveProfile) (env : List Name) :
    List Expr → Bool
  | [] => true
  | expr :: rest =>
      Expr.one? profile env expr && ExprList.allOne? profile env rest

mutual
  def Block.OutEnv (env : List Name) : Block → Option (List Name)
    | ⟨stmts⟩ => StmtList.OutEnv env stmts

  def Stmt.OutEnv (env : List Name) : Stmt → Option (List Name)
    | .decl names _value? =>
        if nonempty? names && decide names.Nodup && disjoint? names env then
          some (extend env names)
        else
          none
    | .callDecl names _functionName _args =>
        if nonempty? names && decide names.Nodup && disjoint? names env then
          some (extend env names)
        else
          none
    | _ => some env

  def StmtList.OutEnv (env : List Name) : List Stmt → Option (List Name)
    | [] => some env
    | stmt :: rest => do
        let env' ← Stmt.OutEnv env stmt
        StmtList.OutEnv env' rest
end

mutual
  def Block.Accepted (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      Block → Prop
    | ⟨stmts⟩ =>
        StmtList.Accepted profile sigs canBreak canContinue canLeave env stmts

  def StmtList.Accepted (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      List Stmt → Prop
    | [] => True
    | stmt :: rest =>
        Stmt.Accepted profile sigs canBreak canContinue canLeave env stmt ∧
          match Stmt.OutEnv env stmt with
          | some env' =>
              StmtList.Accepted profile sigs canBreak canContinue canLeave
                env' rest
          | none => False

  def Stmt.Accepted (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      Stmt → Prop
    | .expr expr =>
        Expr.Zero profile env expr
    | .decl names value? =>
        names ≠ [] ∧ names.Nodup ∧ disjoint names env ∧
          match value? with
          | none => True
          | some value => Expr.Arity profile env value = some names.length
    | .assign names value =>
        names ≠ [] ∧ names.Nodup ∧ containsAll env names ∧
          Expr.Arity profile env value = some names.length
    | .block body =>
        Block.Accepted profile sigs canBreak canContinue canLeave env body
    | .if_ cond body =>
        Expr.One profile env cond ∧
          Block.Accepted profile sigs canBreak canContinue canLeave env body
    | .switch scrutinee cases defaultBody =>
        Expr.One profile env scrutinee ∧
          Cases.Accepted profile sigs canBreak canContinue canLeave env cases ∧
          Default.Accepted profile sigs canBreak canContinue canLeave env
            defaultBody
    | .for_ init cond post body =>
        Block.Accepted profile sigs false false canLeave env init ∧
          match Block.OutEnv env init with
          | some loopEnv =>
              Expr.One profile loopEnv cond ∧
                Block.Accepted profile sigs false false canLeave loopEnv post ∧
                Block.Accepted profile sigs true true canLeave loopEnv body
          | none => False
    | .brk => canBreak = true
    | .cont => canContinue = true
    | .leave => canLeave = true
    | .call targets functionName args =>
        match Signature.find? sigs functionName with
        | none => False
        | some sig =>
            targets.Nodup ∧ containsAll env targets ∧
              targets.length = sig.returns ∧ args.length = sig.params ∧
              ExprList.AllOne profile env args
    | .callDecl names functionName args =>
        match Signature.find? sigs functionName with
        | none => False
        | some sig =>
            names ≠ [] ∧ names.Nodup ∧ disjoint names env ∧
              names.length = sig.returns ∧ args.length = sig.params ∧
              ExprList.AllOne profile env args
    | .terminal kind args =>
        args.length = profile.terminalArity kind ∧
          ExprList.AllOne profile env args
    | .invalid => True

  def Cases.Accepted (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        Block.Accepted profile sigs canBreak canContinue canLeave env body ∧
          Cases.Accepted profile sigs canBreak canContinue canLeave env rest

  def Default.Accepted (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      Option Block → Prop
    | none => True
    | some body =>
        Block.Accepted profile sigs canBreak canContinue canLeave env body
end

mutual
  def Block.accepted? (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      Block → Bool
    | ⟨stmts⟩ =>
        StmtList.accepted? profile sigs canBreak canContinue canLeave env stmts

  def StmtList.accepted? (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      List Stmt → Bool
    | [] => true
    | stmt :: rest =>
        Stmt.accepted? profile sigs canBreak canContinue canLeave env stmt &&
          match Stmt.OutEnv env stmt with
          | some env' =>
              StmtList.accepted? profile sigs canBreak canContinue canLeave
                env' rest
          | none => false

  def Stmt.accepted? (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      Stmt → Bool
    | .expr expr =>
        Expr.zero? profile env expr
    | .decl names value? =>
        nonempty? names && decide names.Nodup && disjoint? names env &&
          match value? with
          | none => true
          | some value => Expr.arityIs? profile env value names.length
    | .assign names value =>
        nonempty? names && decide names.Nodup && containsAll? env names &&
          Expr.arityIs? profile env value names.length
    | .block body =>
        Block.accepted? profile sigs canBreak canContinue canLeave env body
    | .if_ cond body =>
        Expr.one? profile env cond &&
          Block.accepted? profile sigs canBreak canContinue canLeave env body
    | .switch scrutinee cases defaultBody =>
        Expr.one? profile env scrutinee &&
          Cases.accepted? profile sigs canBreak canContinue canLeave env cases &&
          Default.accepted? profile sigs canBreak canContinue canLeave env
            defaultBody
    | .for_ init cond post body =>
        Block.accepted? profile sigs false false canLeave env init &&
          match Block.OutEnv env init with
          | some loopEnv =>
              Expr.one? profile loopEnv cond &&
                Block.accepted? profile sigs false false canLeave loopEnv post &&
                Block.accepted? profile sigs true true canLeave loopEnv body
          | none => false
    | .brk => canBreak
    | .cont => canContinue
    | .leave => canLeave
    | .call targets functionName args =>
        match Signature.find? sigs functionName with
        | none => false
        | some sig =>
            decide targets.Nodup && containsAll? env targets &&
              decide (targets.length = sig.returns) &&
              decide (args.length = sig.params) &&
              ExprList.allOne? profile env args
    | .callDecl names functionName args =>
        match Signature.find? sigs functionName with
        | none => false
        | some sig =>
            nonempty? names && decide names.Nodup && disjoint? names env &&
              decide (names.length = sig.returns) &&
              decide (args.length = sig.params) &&
              ExprList.allOne? profile env args
    | .terminal kind args =>
        decide (args.length = profile.terminalArity kind) &&
          ExprList.allOne? profile env args
    | .invalid => true

  def Cases.accepted? (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      List (Word × Block) → Bool
    | [] => true
    | (_value, body) :: rest =>
        Block.accepted? profile sigs canBreak canContinue canLeave env body &&
          Cases.accepted? profile sigs canBreak canContinue canLeave env rest

  def Default.accepted? (profile : PrimitiveProfile) (sigs : List Signature.T)
      (canBreak canContinue canLeave : Bool) (env : List Name) :
      Option Block → Bool
    | none => true
    | some body =>
        Block.accepted? profile sigs canBreak canContinue canLeave env body
end

end Scope

namespace Proc

def Accepted (profile : PrimitiveProfile) (sigs : List Signature.T)
    (proc : Proc) : Prop :=
  (proc.returns ++ proc.params).Nodup ∧
    Scope.Block.Accepted profile sigs false false true
      (proc.returns ++ proc.params) proc.body

def accepted? (profile : PrimitiveProfile) (sigs : List Signature.T)
    (proc : Proc) : Bool :=
  decide ((proc.returns ++ proc.params).Nodup) &&
    Scope.Block.accepted? profile sigs false false true
      (proc.returns ++ proc.params) proc.body

end Proc

namespace Program

def signatures (program : Program) : List Signature.T :=
  program.procs.map Signature.ofProc

def ProcNamesUnique (program : Program) : Prop :=
  (program.procs.map Proc.name).Nodup

def ProcsAccepted (profile : PrimitiveProfile) (program : Program) : Prop :=
  ∀ proc, proc ∈ program.procs →
    proc.Accepted profile program.signatures

def Accepted (profile : PrimitiveProfile) (program : Program) : Prop :=
  program.ProcNamesUnique ∧
    program.ProcsAccepted profile ∧
    Scope.Block.Accepted profile program.signatures false false false []
      program.body

def acceptedWith? (profile : PrimitiveProfile) (program : Program) : Bool :=
  decide ((program.procs.map Proc.name).Nodup) &&
    program.procs.all (fun proc => proc.accepted? profile program.signatures) &&
    Scope.Block.accepted? profile program.signatures false false false []
      program.body

def accepted? (program : Program) : Bool :=
  acceptedWith? {} program

end Program

end StackFreeCfg
end EvmCompiler
