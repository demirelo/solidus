import EvmCompiler.Functions.Syntax
import EvmCompiler.Locals.Compiler

namespace EvmCompiler
namespace Functions

namespace FunList

def find? (name : Name) : List FunDef → Option FunDef
  | [] => none
  | fn :: rest =>
      if fn.name = name then
        some fn
      else
        find? name rest

end FunList

namespace Lower

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def argExprs : (args : List (Expr 1)) → Locals.ExprSeq args.length
  | [] => .nil
  | arg :: rest =>
      by
        simpa [Nat.add_comm] using
          (Locals.ExprSeq.cons (left := 1) (right := rest.length)
            arg (argExprs rest))

def evalArgs : List (Expr 1) → List Locals.Stmt
  | [] => []
  | arg :: rest => [Locals.Stmt.exprs (argExprs (arg :: rest))]

def returnExprs : (names : List Name) → Locals.ExprSeq names.length
  | [] => .nil
  | name :: rest =>
      by
        simpa [Nat.add_comm] using
          (Locals.ExprSeq.cons (left := 1) (right := rest.length)
            (.var name) (returnExprs rest))

def pushReturns : List Name → List Locals.Stmt
  | [] => []
  | name :: rest => [Locals.Stmt.exprs (returnExprs (name :: rest))]

def initReturns : List Name → List Locals.Stmt
  | [] => []
  | name :: rest => Locals.Stmt.let_ name (.lit zero) :: initReturns rest

def assignReturnedTopsRev : List Name → List Locals.Stmt
  | [] => []
  | name :: rest =>
      Locals.Stmt.assignTopWithOffset rest.length name ::
        assignReturnedTopsRev rest

def assignReturnedTops (targets : List Name) : List Locals.Stmt :=
  assignReturnedTopsRev targets.reverse

end Lower

namespace ExprList

def usesCallCreate : List (Expr 1) → Bool
  | [] => false
  | expr :: rest => expr.usesCallCreate || usesCallCreate rest

end ExprList

mutual
  def Block.usesCallCreate : Block → Bool
    | ⟨stmts⟩ => StmtList.usesCallCreate stmts

  def Stmt.usesCallCreate : Stmt → Bool
    | .expr expr => expr.usesCallCreate
    | .let_ _name value => value.usesCallCreate
    | .assign _name value => value.usesCallCreate
    | .block body => body.usesCallCreate
    | .if_ cond body => cond.usesCallCreate || body.usesCallCreate
    | .switch scrutinee cases defaultBody =>
        scrutinee.usesCallCreate || CaseList.usesCallCreate cases ||
          Default.usesCallCreate defaultBody
    | .for_ init cond post body =>
        init.usesCallCreate || cond.usesCallCreate || post.usesCallCreate ||
          body.usesCallCreate
    | .brk | .cont | .leave | .terminal _ => false
    | .call _ _ args => ExprList.usesCallCreate args
    | .terminalArgs _kind args => args.usesCallCreate

  def StmtList.usesCallCreate : List Stmt → Bool
    | [] => false
    | stmt :: rest => stmt.usesCallCreate || StmtList.usesCallCreate rest

  def CaseList.usesCallCreate : List (Word × Block) → Bool
    | [] => false
    | (_value, body) :: rest =>
        body.usesCallCreate || CaseList.usesCallCreate rest

  def Default.usesCallCreate : Option Block → Bool
    | none => false
    | some body => body.usesCallCreate
end

namespace FunDef

def usesCallCreate (fn : FunDef) : Bool :=
  fn.body.usesCallCreate

end FunDef

namespace FunList

def usesCallCreate : List FunDef → Bool
  | [] => false
  | fn :: rest => fn.usesCallCreate || usesCallCreate rest

end FunList

namespace Program

def usesCallCreate (program : Program) : Bool :=
  FunList.usesCallCreate program.functions || program.body.usesCallCreate

end Program

set_option maxHeartbeats 800000 in
mutual
  def Block.toLocals (returns : List Name) (block : Block) : Locals.Block :=
    match block with
    | ⟨stmts⟩ => { stmts := StmtList.toLocals returns stmts }

  def Stmt.toLocals (returns : List Name) : Stmt → List Locals.Stmt
    | .expr expr => [Locals.Stmt.expr expr]
    | .let_ name value => [Locals.Stmt.let_ name value]
    | .assign name value => [Locals.Stmt.assign name value]
    | .block body => [Locals.Stmt.block (Block.toLocals returns body)]
    | .if_ cond body => [Locals.Stmt.if_ cond (Block.toLocals returns body)]
    | .switch scrutinee cases defaultBody =>
        [Locals.Stmt.switch scrutinee (CaseList.toLocals returns cases)
          (Default.toLocals returns defaultBody)]
    | .for_ init cond post body =>
        [Locals.Stmt.for_ (Block.toLocals returns init) cond
          (Block.toLocals returns post) (Block.toLocals returns body)]
    | .brk => [.brk]
    | .cont => [.cont]
    | .leave => Lower.pushReturns returns ++ [.leave]
    | .call targets functionName args =>
        Lower.evalArgs args ++ [Locals.Stmt.call functionName] ++
          Lower.assignReturnedTops targets
    | .terminal kind => [.terminal kind]
    | .terminalArgs kind args => [.terminalArgs kind args]

  def StmtList.toLocals (returns : List Name) : List Stmt → List Locals.Stmt
    | [] => []
    | stmt :: rest => Stmt.toLocals returns stmt ++ StmtList.toLocals returns rest

  def CaseList.toLocals (returns : List Name) :
      List (Word × Block) → List (Word × Locals.Block)
    | [] => []
    | (value, body) :: rest =>
        (value, Block.toLocals returns body) :: CaseList.toLocals returns rest

  def Default.toLocals (returns : List Name) :
      Option Block → Option Locals.Block
    | none => none
    | some body => some (Block.toLocals returns body)
end


namespace FunDef

def toLocalsProc (fn : FunDef) : Locals.Proc where
  name := fn.name
  argc := fn.params.length
  retc := fn.returns.length
  entryLayout := fn.params.reverse
  body :=
    { stmts :=
        Lower.initReturns fn.returns ++
          StmtList.toLocals fn.returns fn.body.stmts ++
          Lower.pushReturns fn.returns }

end FunDef

namespace FunList

def toLocalsProcs : List FunDef → List Locals.Proc
  | [] => []
  | fn :: rest => fn.toLocalsProc :: toLocalsProcs rest

end FunList

namespace Program

def toLocals (program : Program) : Locals.Program where
  procs := FunList.toLocalsProcs program.functions
  body := Block.toLocals [] program.body

def toLocals? (program : Program) : Option Locals.Program :=
  some program.toLocals

def toExpressions? (program : Program) : Option Expressions.Program :=
  program.toLocals.toExpressions?

def compile? (program : Program) :
    Option Assembly.TargetProgram :=
  program.toLocals.compile?

def Accepted (program : Program) : Prop :=
  program.WF ∧ program.Scoped ∧ program.toLocals.Accepted

def SourceAccepted (program : Program) : Prop :=
  program.WF ∧ program.Scoped

theorem sourceAccepted_of_accepted {program : Program}
    (hAccepted : Accepted program) :
    SourceAccepted program :=
  ⟨hAccepted.1, hAccepted.2.1⟩

end Program


namespace CompilerFacts

theorem exprSeq_cast_usesCallCreate {n m : Nat} (h : n = m)
    (exprs : Locals.ExprSeq n)
    (hExprs : exprs.usesCallCreate = false) :
    Locals.ExprSeq.usesCallCreate
      (cast (congrArg Locals.ExprSeq h) exprs) = false := by
  cases h
  exact hExprs

theorem Locals.StmtList.usesCallCreate_append_eq_false
    {left right : List Locals.Stmt}
    (hLeft : Locals.StmtList.usesCallCreate left = false)
    (hRight : Locals.StmtList.usesCallCreate right = false) :
    Locals.StmtList.usesCallCreate (left ++ right) = false := by
  induction left with
  | nil => simpa using hRight
  | cons head tail ih =>
      have hParts :
          head.usesCallCreate = false ∧
            Locals.StmtList.usesCallCreate tail = false := by
        simpa [Locals.StmtList.usesCallCreate] using hLeft
      simp [Locals.StmtList.usesCallCreate, hParts.1, ih hParts.2]

theorem Lower.returnExprs_noCallCreate (names : List Name) :
    (Lower.returnExprs names).usesCallCreate = false := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      unfold Lower.returnExprs
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons (.var name) (Lower.returnExprs rest)
      have hLen : 1 + rest.length = rest.length + 1 := by omega
      change Locals.ExprSeq.usesCallCreate
        (cast (congrArg Locals.ExprSeq hLen) exprs) = false
      apply exprSeq_cast_usesCallCreate hLen
      change
        (Locals.ExprSeq.cons (.var name)
          (Lower.returnExprs rest)).usesCallCreate = false
      simp [Locals.ExprSeq.usesCallCreate, Locals.Expr.usesCallCreate, ih]

theorem Lower.pushReturns_noCallCreate (names : List Name) :
    Locals.StmtList.usesCallCreate (Lower.pushReturns names) = false := by
  cases names with
  | nil => rfl
  | cons name rest =>
      simp [Lower.pushReturns, Locals.StmtList.usesCallCreate,
        Locals.Stmt.usesCallCreate, Lower.returnExprs_noCallCreate]

theorem Lower.initReturns_noCallCreate (names : List Name) :
    Locals.StmtList.usesCallCreate (Lower.initReturns names) = false := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp [Lower.initReturns, Locals.StmtList.usesCallCreate,
        Locals.Stmt.usesCallCreate, Locals.Expr.usesCallCreate, ih]

theorem Lower.assignReturnedTopsRev_noCallCreate (names : List Name) :
    Locals.StmtList.usesCallCreate
      (Lower.assignReturnedTopsRev names) = false := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp [Lower.assignReturnedTopsRev, Locals.StmtList.usesCallCreate,
        Locals.Stmt.usesCallCreate, ih]

theorem Lower.assignReturnedTops_noCallCreate (names : List Name) :
    Locals.StmtList.usesCallCreate
      (Lower.assignReturnedTops names) = false := by
  simpa [Lower.assignReturnedTops] using
    Lower.assignReturnedTopsRev_noCallCreate names.reverse

theorem Lower.argExprs_noCallCreate :
    ∀ {args : List (Expr 1)},
      ExprList.usesCallCreate args = false →
        (Lower.argExprs args).usesCallCreate = false
  | [], _hArgs => by rfl
  | arg :: rest, hArgs => by
      have hParts :
          arg.usesCallCreate = false ∧
            ExprList.usesCallCreate rest = false := by
        simpa [ExprList.usesCallCreate] using hArgs
      have hRest := Lower.argExprs_noCallCreate hParts.2
      unfold Lower.argExprs
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons arg (Lower.argExprs rest)
      have hLen : 1 + rest.length = rest.length + 1 := by omega
      change Locals.ExprSeq.usesCallCreate
        (cast (congrArg Locals.ExprSeq hLen) exprs) = false
      apply exprSeq_cast_usesCallCreate hLen
      change
        (Locals.ExprSeq.cons arg (Lower.argExprs rest)).usesCallCreate = false
      simp [Locals.ExprSeq.usesCallCreate, hParts.1, hRest]

theorem Lower.evalArgs_noCallCreate :
    ∀ {args : List (Expr 1)},
      ExprList.usesCallCreate args = false →
        Locals.StmtList.usesCallCreate (Lower.evalArgs args) = false
  | [], _hArgs => by rfl
  | arg :: rest, hArgs => by
      have hSeq := Lower.argExprs_noCallCreate hArgs
      simp [Lower.evalArgs, Locals.StmtList.usesCallCreate,
        Locals.Stmt.usesCallCreate, hSeq]

set_option linter.unusedSimpArgs false in
mutual
  theorem Block.toLocals_noCallCreate (returns : List Name)
      (block : Block) (hBlock : block.usesCallCreate = false) :
      (Block.toLocals returns block).usesCallCreate = false := by
    cases block with
    | mk stmts => exact StmtList.toLocals_noCallCreate returns stmts hBlock

  theorem Stmt.toLocals_noCallCreate (returns : List Name)
      (stmt : Stmt) (hStmt : stmt.usesCallCreate = false) :
      Locals.StmtList.usesCallCreate (Stmt.toLocals returns stmt) = false := by
    cases stmt with
    | expr expr =>
        simpa [Stmt.toLocals, Stmt.usesCallCreate,
          Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate] using hStmt
    | let_ name value =>
        simpa [Stmt.toLocals, Stmt.usesCallCreate,
          Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate] using hStmt
    | assign name value =>
        simpa [Stmt.toLocals, Stmt.usesCallCreate,
          Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate] using hStmt
    | block body =>
        have hBody : body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        have hLower := Block.toLocals_noCallCreate returns body hBody
        simp [Stmt.toLocals, Locals.StmtList.usesCallCreate,
          Locals.Stmt.usesCallCreate, hLower]
    | if_ cond body =>
        have hParts :
            cond.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        have hBody := Block.toLocals_noCallCreate returns body hParts.2
        simp [Stmt.toLocals, Locals.StmtList.usesCallCreate,
          Locals.Stmt.usesCallCreate, hParts.1, hBody]
    | switch scrutinee cases defaultBody =>
        have hParts :
            scrutinee.usesCallCreate = false ∧
              CaseList.usesCallCreate cases = false ∧
                Default.usesCallCreate defaultBody = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        have hCases := CaseList.toLocals_noCallCreate returns cases hParts.2.1
        have hDefault :=
          Default.toLocals_noCallCreate returns defaultBody hParts.2.2
        simp [Stmt.toLocals, Locals.StmtList.usesCallCreate,
          Locals.Stmt.usesCallCreate, hParts.1, hCases, hDefault]
    | for_ init cond post body =>
        have hParts :
            init.usesCallCreate = false ∧ cond.usesCallCreate = false ∧
              post.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        have hInit := Block.toLocals_noCallCreate returns init hParts.1
        have hPost := Block.toLocals_noCallCreate returns post hParts.2.2.1
        have hBody := Block.toLocals_noCallCreate returns body hParts.2.2.2
        simp [Stmt.toLocals, Locals.StmtList.usesCallCreate,
          Locals.Stmt.usesCallCreate, hInit, hParts.2.1, hPost, hBody]
    | brk => rfl
    | cont => rfl
    | leave =>
        exact
          Locals.StmtList.usesCallCreate_append_eq_false
            (Lower.pushReturns_noCallCreate returns)
            (by simp [Locals.StmtList.usesCallCreate,
              Locals.Stmt.usesCallCreate])
    | call targets functionName args =>
        have hArgs : ExprList.usesCallCreate args = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        have hEval := Lower.evalArgs_noCallCreate hArgs
        have hCall :
            Locals.StmtList.usesCallCreate
              [Locals.Stmt.call functionName] = false := by
          simp [Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate]
        exact
          Locals.StmtList.usesCallCreate_append_eq_false
            (left := Lower.evalArgs args ++ [Locals.Stmt.call functionName])
            (right := Lower.assignReturnedTops targets)
            (Locals.StmtList.usesCallCreate_append_eq_false
              (left := Lower.evalArgs args)
              (right := [Locals.Stmt.call functionName]) hEval hCall)
            (Lower.assignReturnedTops_noCallCreate targets)
    | terminal kind => rfl
    | terminalArgs kind args =>
        simpa [Stmt.toLocals, Stmt.usesCallCreate,
          Locals.StmtList.usesCallCreate, Locals.Stmt.usesCallCreate] using hStmt

  theorem StmtList.toLocals_noCallCreate (returns : List Name)
      (stmts : List Stmt) (hStmts : StmtList.usesCallCreate stmts = false) :
      Locals.StmtList.usesCallCreate
        (StmtList.toLocals returns stmts) = false := by
    cases stmts with
    | nil => rfl
    | cons stmt rest =>
        have hParts :
            stmt.usesCallCreate = false ∧
              StmtList.usesCallCreate rest = false := by
          simpa [StmtList.usesCallCreate] using hStmts
        have hStmt := Stmt.toLocals_noCallCreate returns stmt hParts.1
        have hRest := StmtList.toLocals_noCallCreate returns rest hParts.2
        exact Locals.StmtList.usesCallCreate_append_eq_false hStmt hRest

  theorem CaseList.toLocals_noCallCreate (returns : List Name)
      (cases : List (Word × Block))
      (hCases : CaseList.usesCallCreate cases = false) :
      Locals.CaseList.usesCallCreate
        (CaseList.toLocals returns cases) = false := by
    cases cases with
    | nil => rfl
    | cons head rest =>
        cases head with
        | mk value body =>
            have hParts :
                body.usesCallCreate = false ∧
                  CaseList.usesCallCreate rest = false := by
              simpa [CaseList.usesCallCreate] using hCases
            have hBody := Block.toLocals_noCallCreate returns body hParts.1
            have hRest := CaseList.toLocals_noCallCreate returns rest hParts.2
            simp [CaseList.toLocals, Locals.CaseList.usesCallCreate,
              hBody, hRest]

  theorem Default.toLocals_noCallCreate (returns : List Name)
      (defaultBody : Option Block)
      (hDefault : Default.usesCallCreate defaultBody = false) :
      Locals.Default.usesCallCreate
        (Default.toLocals returns defaultBody) = false := by
    cases defaultBody with
    | none => rfl
    | some body =>
        have hBody : body.usesCallCreate = false := by
          simpa [Default.usesCallCreate] using hDefault
        exact Block.toLocals_noCallCreate returns body hBody
end

theorem FunDef.toLocalsProc_noCallCreate (fn : FunDef)
    (hFn : fn.usesCallCreate = false) :
    (fn.toLocalsProc).usesCallCreate = false := by
  rcases fn with ⟨name, params, returns, body⟩
  have hBody := StmtList.toLocals_noCallCreate returns body.stmts
    (by
      cases body with
      | mk stmts =>
          simpa [FunDef.usesCallCreate, Block.usesCallCreate] using hFn)
  have hInit := Lower.initReturns_noCallCreate returns
  have hPush := Lower.pushReturns_noCallCreate returns
  simp [FunDef.toLocalsProc, Locals.Proc.usesCallCreate,
    Locals.Block.usesCallCreate]
  exact Locals.StmtList.usesCallCreate_append_eq_false hInit
    (Locals.StmtList.usesCallCreate_append_eq_false hBody hPush)

theorem FunList.toLocalsProcs_noCallCreate :
    ∀ {fns : List FunDef},
      FunList.usesCallCreate fns = false →
        Locals.ProcList.usesCallCreate
          (FunList.toLocalsProcs fns) = false
  | [], _hFns => by rfl
  | fn :: rest, hFns => by
      have hParts :
          fn.usesCallCreate = false ∧
            FunList.usesCallCreate rest = false := by
        simpa [FunList.usesCallCreate] using hFns
      have hFn := FunDef.toLocalsProc_noCallCreate fn hParts.1
      have hRest := FunList.toLocalsProcs_noCallCreate hParts.2
      simp [FunList.toLocalsProcs, Locals.ProcList.usesCallCreate,
        hFn, hRest]

theorem Program.toLocals_noCallCreate (program : Program)
    (hProgram : program.usesCallCreate = false) :
    program.toLocals.usesCallCreate = false := by
  have hParts :
      FunList.usesCallCreate program.functions = false ∧
        program.body.usesCallCreate = false := by
    simpa [Program.usesCallCreate] using hProgram
  have hProcs := FunList.toLocalsProcs_noCallCreate hParts.1
  have hBody := Block.toLocals_noCallCreate [] program.body hParts.2
  simp [Program.toLocals, Locals.Program.usesCallCreate, hProcs, hBody]

end CompilerFacts

namespace Inline

namespace Program

def toLocals? (program : Functions.Program) : Option Locals.Program :=
  Functions.Program.toLocals? program

def toExpressions? (program : Functions.Program) : Option Expressions.Program :=
  Functions.Program.toExpressions? program

def compile? (program : Functions.Program) :
    Option Assembly.TargetProgram :=
  Functions.Program.compile? program

def Accepted (program : Functions.Program) : Prop :=
  Functions.Program.Accepted program

def SourceAccepted (program : Functions.Program) : Prop :=
  Functions.Program.SourceAccepted program

theorem sourceAccepted_of_accepted {program : Functions.Program}
    (hAccepted : Accepted program) :
    SourceAccepted program :=
  Functions.Program.sourceAccepted_of_accepted hAccepted

end Program

end Inline

end Functions
end EvmCompiler
