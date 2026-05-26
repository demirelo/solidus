import EvmCompiler.Functions.SourceSemantics
import EvmCompiler.Functions.Compiler

namespace EvmCompiler
namespace Functions

/-
Source-to-source lowering facts for the function abstraction.

This file is the bridge from the repaired, stack-free `Functions.Source`
interpreter to the lower stack-free locals source interpreter.  The hard
procedure/frame lowering still belongs below this boundary; higher layers
should be able to use these facts without seeing return tokens, stack frames,
layout depths, or cleanup code.

The current checked facts are deliberately for source-owned non-call statements.
`Locals.Source` rejects the low-level `.call` instruction because that form
still uses the procedure stack convention.  Full function-call preservation
therefore must either target the lower procedure backend directly from
`Functions.Source`, or first introduce a separate abstract procedure-call
source interface.
-/
namespace SourceLowering

def Ctx.toLocals (ctx : Source.Ctx) : Locals.Source.Ctx where
  scope := ctx.scope
  breakScope? := ctx.breakScope?
  continueScope? := ctx.continueScope?
  leaveScope? := ctx.leaveScope?

theorem Ctx.toLocals_initial :
    Ctx.toLocals Source.Ctx.initial = Locals.Source.Ctx.initial := by
  rfl

theorem Ctx.toLocals_withoutLoopControl (ctx : Source.Ctx) :
    Ctx.toLocals ctx.withoutLoopControl =
      (Ctx.toLocals ctx).withoutLoopControl := by
  cases ctx
  rfl

theorem Ctx.toLocals_withLoopControl (ctx : Source.Ctx)
    (breakScope continueScope : List Name) :
    Ctx.toLocals (ctx.withLoopControl breakScope continueScope) =
      (Ctx.toLocals ctx).withLoopControl breakScope continueScope := by
  cases ctx
  rfl

theorem Ctx.toLocals_withLeaveScope (ctx : Source.Ctx)
    (leaveScope : List Name) :
    Ctx.toLocals (ctx.withLeaveScope leaveScope) =
      (Ctx.toLocals ctx).withLeaveScope leaveScope := by
  cases ctx
  rfl

theorem Ctx.toLocals_scope_set (ctx : Source.Ctx) (scope : List Name) :
    Ctx.toLocals { ctx with scope := scope } =
      { Ctx.toLocals ctx with scope := scope } := by
  cases ctx
  rfl

namespace SourceToLocals

/--
Atomic function statements whose actual `Stmt.toLocals` output is still inside
the stack-free locals source language.

This is intentionally stricter than "not a user call": a `leave` in a function
with return variables lowers through `Lower.pushReturns`, which uses lower
stack-result plumbing (`exprs`) rather than `Locals.Source`.
-/
def Stmt.AtomicSourceOwned (returns : List Name) : Stmt → Prop
  | .expr expr => Locals.Source.Expr.SourceOwned expr
  | .let_ _name value => Locals.Source.Expr.SourceOwned value
  | .assign _name value => Locals.Source.Expr.SourceOwned value
  | .brk => True
  | .cont => True
  | .leave => returns = []
  | .terminal _kind => True
  | .terminalArgs _kind args => Locals.Source.ExprSeq.SourceOwned args
  | .block _body => False
  | .if_ _cond _body => False
  | .switch _scrutinee _cases _defaultBody => False
  | .for_ _init _cond _post _body => False
  | .call _targets _functionName _args => False

def StmtList.AtomicSourceOwned (returns : List Name) : List Stmt → Prop
  | [] => True
  | stmt :: rest =>
      Stmt.AtomicSourceOwned returns stmt ∧
        StmtList.AtomicSourceOwned returns rest

def Block.AtomicSourceOwned (returns : List Name) : Block → Prop
  | ⟨stmts⟩ => StmtList.AtomicSourceOwned returns stmts

def CaseList.AtomicSourceOwned (returns : List Name) :
    List (Word × Block) → Prop
  | [] => True
  | (_value, body) :: rest =>
      Block.AtomicSourceOwned returns body ∧
        CaseList.AtomicSourceOwned returns rest

def Default.AtomicSourceOwned (returns : List Name) :
    Option Block → Prop
  | none => True
  | some body => Block.AtomicSourceOwned returns body

mutual
  /--
  Recursive function statements whose compiler output stays inside the
  stack-free locals source language.

  Calls and nonempty-return `leave` are deliberately excluded here: they lower
  through procedure return/result-stack machinery, which belongs in the
  function/procedure lowering proof rather than in `Locals.Source`.
  -/
  def Block.SourceOwned (returns : List Name) : Block → Prop
    | ⟨stmts⟩ => StmtList.SourceOwned returns stmts

  def Stmt.SourceOwned (returns : List Name) : Stmt → Prop
    | .expr expr => Locals.Source.Expr.SourceOwned expr
    | .let_ _name value => Locals.Source.Expr.SourceOwned value
    | .assign _name value => Locals.Source.Expr.SourceOwned value
    | .block body => Block.SourceOwned returns body
    | .if_ cond body =>
        Locals.Source.Expr.SourceOwned cond ∧
          Block.SourceOwned returns body
    | .switch scrutinee cases defaultBody =>
        Locals.Source.Expr.SourceOwned scrutinee ∧
          CaseList.SourceOwned returns cases ∧
            Default.SourceOwned returns defaultBody
    | .for_ init cond post body =>
        Block.SourceOwned returns init ∧
          Locals.Source.Expr.SourceOwned cond ∧
            Block.SourceOwned returns post ∧
              Block.SourceOwned returns body
    | .brk => True
    | .cont => True
    | .leave => returns = []
    | .call _targets _functionName _args => False
    | .terminal _kind => True
    | .terminalArgs _kind args => Locals.Source.ExprSeq.SourceOwned args

  def StmtList.SourceOwned (returns : List Name) : List Stmt → Prop
    | [] => True
    | stmt :: rest =>
        Stmt.SourceOwned returns stmt ∧
          StmtList.SourceOwned returns rest

  def CaseList.SourceOwned (returns : List Name) :
      List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        Block.SourceOwned returns body ∧
          CaseList.SourceOwned returns rest

  def Default.SourceOwned (returns : List Name) :
      Option Block → Prop
    | none => True
    | some body => Block.SourceOwned returns body
end

mutual
  def Block.sourceSize : Block → Nat
    | ⟨stmts⟩ => StmtList.sourceSize stmts + 1

  def Stmt.sourceSize : Stmt → Nat
    | .expr _expr => 1
    | .let_ _name _value => 1
    | .assign _name _value => 1
    | .block body => Block.sourceSize body + 1
    | .if_ _cond body => Block.sourceSize body + 1
    | .switch _scrutinee cases defaultBody =>
        CaseList.sourceSize cases + Default.sourceSize defaultBody + 1
    | .for_ init _cond post body =>
        Block.sourceSize init + Block.sourceSize post +
          Block.sourceSize body + 1
    | .brk => 1
    | .cont => 1
    | .leave => 1
    | .call _targets _functionName _args => 1
    | .terminal _kind => 1
    | .terminalArgs _kind _args => 1

  def StmtList.sourceSize : List Stmt → Nat
    | [] => 0
    | stmt :: rest => Stmt.sourceSize stmt + StmtList.sourceSize rest + 1

  def CaseList.sourceSize : List (Word × Block) → Nat
    | [] => 0
    | (_value, body) :: rest =>
        Block.sourceSize body + CaseList.sourceSize rest + 1

  def Default.sourceSize : Option Block → Nat
    | none => 0
    | some body => Block.sourceSize body + 1
end

theorem atomic_toLocals_sourceOwned {returns : List Name} {stmt : Stmt}
    (hOwned : Stmt.AtomicSourceOwned returns stmt) :
    Locals.Source.StmtList.SourceOwned (Stmt.toLocals returns stmt) := by
  cases stmt with
  | expr expr =>
      simpa [Stmt.AtomicSourceOwned, Stmt.toLocals,
        Locals.Source.StmtList.SourceOwned,
        Locals.Source.Stmt.SourceOwned] using hOwned
  | let_ name value =>
      simpa [Stmt.AtomicSourceOwned, Stmt.toLocals,
        Locals.Source.StmtList.SourceOwned,
        Locals.Source.Stmt.SourceOwned] using hOwned
  | assign name value =>
      simpa [Stmt.AtomicSourceOwned, Stmt.toLocals,
        Locals.Source.StmtList.SourceOwned,
        Locals.Source.Stmt.SourceOwned] using hOwned
  | brk =>
      simp [Stmt.AtomicSourceOwned, Stmt.toLocals,
        Locals.Source.StmtList.SourceOwned, Locals.Source.Stmt.SourceOwned]
  | cont =>
      simp [Stmt.AtomicSourceOwned, Stmt.toLocals,
        Locals.Source.StmtList.SourceOwned, Locals.Source.Stmt.SourceOwned]
  | leave =>
      subst returns
      simp [Stmt.AtomicSourceOwned, Stmt.toLocals, Lower.pushReturns,
        Locals.Source.StmtList.SourceOwned, Locals.Source.Stmt.SourceOwned]
  | terminal kind =>
      simp [Stmt.AtomicSourceOwned, Stmt.toLocals,
        Locals.Source.StmtList.SourceOwned, Locals.Source.Stmt.SourceOwned]
  | terminalArgs kind args =>
      simpa [Stmt.AtomicSourceOwned, Stmt.toLocals,
        Locals.Source.StmtList.SourceOwned,
        Locals.Source.Stmt.SourceOwned] using hOwned
  | block body =>
      cases hOwned
  | if_ cond body =>
      cases hOwned
  | switch scrutinee cases defaultBody =>
      cases hOwned
  | for_ init cond post body =>
      cases hOwned
  | call targets functionName args =>
      cases hOwned

theorem localsStmtList_sourceOwned_append {left right : List Locals.Stmt}
    (hLeft : Locals.Source.StmtList.SourceOwned left)
    (hRight : Locals.Source.StmtList.SourceOwned right) :
    Locals.Source.StmtList.SourceOwned (left ++ right) := by
  induction left with
  | nil =>
      simpa [Locals.Source.StmtList.SourceOwned] using hRight
  | cons stmt rest ih =>
      change Locals.Source.Stmt.SourceOwned stmt ∧
        Locals.Source.StmtList.SourceOwned rest at hLeft
      rcases hLeft with ⟨hStmt, hRest⟩
      change Locals.Source.Stmt.SourceOwned stmt ∧
        Locals.Source.StmtList.SourceOwned (rest ++ right)
      exact ⟨hStmt, ih hRest⟩

theorem atomicList_toLocals_sourceOwned {returns : List Name}
    {stmts : List Stmt}
    (hOwned : StmtList.AtomicSourceOwned returns stmts) :
    Locals.Source.StmtList.SourceOwned
      (StmtList.toLocals returns stmts) := by
  induction stmts with
  | nil =>
      simp [StmtList.toLocals, Locals.Source.StmtList.SourceOwned]
  | cons stmt rest ih =>
      rcases hOwned with ⟨hStmt, hRest⟩
      have hStmtOwned := atomic_toLocals_sourceOwned hStmt
      have hRestOwned := ih hRest
      simpa [StmtList.toLocals] using
        localsStmtList_sourceOwned_append hStmtOwned hRestOwned

theorem atomicBlock_toLocals_sourceOwned {returns : List Name}
    {block : Block}
    (hOwned : Block.AtomicSourceOwned returns block) :
    Locals.Source.Block.SourceOwned (Block.toLocals returns block) := by
  cases block with
  | mk stmts =>
      simpa [Block.AtomicSourceOwned, Block.toLocals,
        Locals.Source.Block.SourceOwned] using
        atomicList_toLocals_sourceOwned hOwned

theorem blockStmt_toLocals_sourceOwned {returns : List Name}
    {body : Block}
    (hOwned : Block.AtomicSourceOwned returns body) :
    Locals.Source.StmtList.SourceOwned
      (Stmt.toLocals returns (.block body)) := by
  have hBody := atomicBlock_toLocals_sourceOwned hOwned
  simp [Stmt.toLocals, Locals.Source.StmtList.SourceOwned,
    Locals.Source.Stmt.SourceOwned, hBody]

theorem ifStmt_toLocals_sourceOwned {returns : List Name}
    {cond : Expr 1} {body : Block}
    (hCond : Locals.Source.Expr.SourceOwned cond)
    (hBody : Block.AtomicSourceOwned returns body) :
    Locals.Source.StmtList.SourceOwned
      (Stmt.toLocals returns (.if_ cond body)) := by
  have hBodyOwned := atomicBlock_toLocals_sourceOwned hBody
  simp [Stmt.toLocals, Locals.Source.StmtList.SourceOwned,
    Locals.Source.Stmt.SourceOwned, hCond, hBodyOwned]

theorem caseList_toLocals_sourceOwned {returns : List Name}
    {cases : List (Word × Block)}
    (hOwned : CaseList.AtomicSourceOwned returns cases) :
    Locals.Source.CaseList.SourceOwned
      (CaseList.toLocals returns cases) := by
  induction cases with
  | nil =>
      simp [CaseList.toLocals, Locals.Source.CaseList.SourceOwned]
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      rcases hOwned with ⟨hBody, hRest⟩
      have hBodyOwned := atomicBlock_toLocals_sourceOwned hBody
      have hRestOwned := ih hRest
      simp [CaseList.toLocals, Locals.Source.CaseList.SourceOwned,
        hBodyOwned, hRestOwned]

theorem default_toLocals_sourceOwned {returns : List Name}
    {defaultBody : Option Block}
    (hOwned : Default.AtomicSourceOwned returns defaultBody) :
    match Default.toLocals returns defaultBody with
    | none => True
    | some body => Locals.Source.Block.SourceOwned body := by
  cases defaultBody with
  | none =>
      simp [Default.toLocals]
  | some body =>
      simpa [Default.toLocals, Default.AtomicSourceOwned] using
        atomicBlock_toLocals_sourceOwned hOwned

theorem switchStmt_toLocals_sourceOwned {returns : List Name}
    {scrutinee : Expr 1} {cases : List (Word × Block)}
    {defaultBody : Option Block}
    (hScrutinee : Locals.Source.Expr.SourceOwned scrutinee)
    (hCases : CaseList.AtomicSourceOwned returns cases)
    (hDefault : Default.AtomicSourceOwned returns defaultBody) :
    Locals.Source.StmtList.SourceOwned
      (Stmt.toLocals returns (.switch scrutinee cases defaultBody)) := by
  have hCasesOwned := caseList_toLocals_sourceOwned hCases
  have hDefaultOwned := default_toLocals_sourceOwned hDefault
  cases hDefaultLower : Default.toLocals returns defaultBody with
  | none =>
      simp [Stmt.toLocals, hDefaultLower, Locals.Source.StmtList.SourceOwned,
        Locals.Source.Stmt.SourceOwned, hScrutinee, hCasesOwned]
  | some lowerDefault =>
      have hDefaultBlock : Locals.Source.Block.SourceOwned lowerDefault := by
        simpa [hDefaultLower] using hDefaultOwned
      simp [Stmt.toLocals, hDefaultLower, Locals.Source.StmtList.SourceOwned,
        Locals.Source.Stmt.SourceOwned, hScrutinee, hCasesOwned,
        hDefaultBlock]

theorem switch_select_toLocals (returns : List Name)
    (scrutinee : Word) (cases : List (Word × Block))
    (defaultBody : Option Block) :
    Locals.Source.Switch.select scrutinee (CaseList.toLocals returns cases)
        (Default.toLocals returns defaultBody) =
      Option.map (Block.toLocals returns)
        (Source.Switch.select scrutinee cases defaultBody) := by
  induction cases with
  | nil =>
      cases defaultBody <;> rfl
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      by_cases hEq : value = scrutinee
      · simp [Source.Switch.select, Locals.Source.Switch.select,
          CaseList.toLocals, hEq]
      · simp [Source.Switch.select, Locals.Source.Switch.select,
          CaseList.toLocals, hEq, ih]

theorem forStmt_toLocals_sourceOwned {returns : List Name}
    {init : Block} {cond : Expr 1} {post body : Block}
    (hInit : Block.AtomicSourceOwned returns init)
    (hCond : Locals.Source.Expr.SourceOwned cond)
    (hPost : Block.AtomicSourceOwned returns post)
    (hBody : Block.AtomicSourceOwned returns body) :
    Locals.Source.StmtList.SourceOwned
      (Stmt.toLocals returns (.for_ init cond post body)) := by
  have hInitOwned := atomicBlock_toLocals_sourceOwned hInit
  have hPostOwned := atomicBlock_toLocals_sourceOwned hPost
  have hBodyOwned := atomicBlock_toLocals_sourceOwned hBody
  simp [Stmt.toLocals, Locals.Source.StmtList.SourceOwned,
    Locals.Source.Stmt.SourceOwned, hInitOwned, hCond, hPostOwned, hBodyOwned]

theorem switch_select_sourceOwned {returns : List Name}
    {scrutinee : Word} {cases : List (Word × Block)}
    {defaultBody : Option Block} {body : Block}
    (hCases : CaseList.AtomicSourceOwned returns cases)
    (hDefault : Default.AtomicSourceOwned returns defaultBody)
    (hSelect : Source.Switch.select scrutinee cases defaultBody = some body) :
    Block.AtomicSourceOwned returns body := by
  induction cases with
  | nil =>
      cases defaultBody with
      | none =>
          simp [Source.Switch.select] at hSelect
      | some defaultBlock =>
          simp [Source.Switch.select] at hSelect
          cases hSelect
          simpa [Default.AtomicSourceOwned] using hDefault
  | cons head rest ih =>
      rcases head with ⟨value, caseBody⟩
      rcases hCases with ⟨hCaseBody, hRest⟩
      by_cases hEq : value = scrutinee
      · simp [Source.Switch.select, hEq] at hSelect
        cases hSelect
        exact hCaseBody
      · exact ih hRest (by
          simpa [Source.Switch.select, hEq] using hSelect)

end SourceToLocals

namespace Stmt

theorem expr_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {ctx : Source.Ctx} {fuel : Nat} {expr : Expr 0}
    {state : Source.State} {outcome : Source.Outcome}
    {ctx' : Source.Ctx}
    (hRun :
      Source.Stmt.run prim program ctx fuel (.expr expr) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.expr expr) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases hEval : Locals.Source.Expr.eval prim expr state <;>
    simp [Source.Stmt.run, Locals.Source.Stmt.run, Source.Expr.eval,
      hEval, Ctx.toLocals] at hRun ⊢
  rcases hRun with ⟨hOutcome, hCtx⟩
  cases hCtx
  simp [hOutcome]

theorem let_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {ctx : Source.Ctx} {fuel : Nat} {name : Name} {value : Expr 1}
    {state : Source.State} {outcome : Source.Outcome}
    {ctx' : Source.Ctx}
    (hRun :
      Source.Stmt.run prim program ctx fuel (.let_ name value) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.let_ name value) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases hEval : Locals.Source.Expr.evalOne prim value state <;>
    simp [Source.Stmt.run, Locals.Source.Stmt.run, Source.Expr.evalOne,
      hEval, Ctx.toLocals] at hRun ⊢
  rcases hRun with ⟨hOutcome, hCtx⟩
  cases hCtx
  simp [hOutcome]

theorem assign_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {ctx : Source.Ctx} {fuel : Nat} {name : Name} {value : Expr 1}
    {state : Source.State} {outcome : Source.Outcome}
    {ctx' : Source.Ctx}
    (hRun :
      Source.Stmt.run prim program ctx fuel (.assign name value) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.assign name value) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases hContains : state.vars.contains name with
  | false =>
      simp [Source.Stmt.run, Locals.Source.Stmt.run, hContains,
        Source.invalid, Locals.Source.invalid, Structured.invalid,
        Ctx.toLocals] at hRun
  | true =>
      simp [Source.Stmt.run, Locals.Source.Stmt.run, hContains,
        Ctx.toLocals] at hRun ⊢
      cases hEval : Locals.Source.Expr.evalOne prim value state <;>
        simp [Source.Expr.evalOne, hEval, Ctx.toLocals] at hRun ⊢
      rcases hRun with ⟨hOutcome, hCtx⟩
      cases hCtx
      simp [hOutcome]

theorem brk_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {ctx : Source.Ctx} {fuel : Nat} {state : Source.State}
    {outcome : Source.Outcome} {ctx' : Source.Ctx}
    (hRun :
      Source.Stmt.run prim program ctx fuel .brk state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        Locals.Stmt.brk state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases ctx with
  | mk scope breakScope? continueScope? leaveScope? =>
      cases breakScope? with
      | none =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, Source.invalid,
            Locals.Source.invalid, Structured.invalid, Ctx.toLocals] at hRun
      | some breakScope =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, Ctx.toLocals]
            at hRun ⊢
          rcases hRun with ⟨hOutcome, hCtxEq⟩
          cases hCtxEq
          simp [hOutcome]

theorem cont_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {ctx : Source.Ctx} {fuel : Nat} {state : Source.State}
    {outcome : Source.Outcome} {ctx' : Source.Ctx}
    (hRun :
      Source.Stmt.run prim program ctx fuel .cont state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        Locals.Stmt.cont state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases ctx with
  | mk scope breakScope? continueScope? leaveScope? =>
      cases continueScope? with
      | none =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, Source.invalid,
            Locals.Source.invalid, Structured.invalid, Ctx.toLocals] at hRun
      | some continueScope =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, Ctx.toLocals]
            at hRun ⊢
          rcases hRun with ⟨hOutcome, hCtxEq⟩
          cases hCtxEq
          simp [hOutcome]

theorem leave_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {ctx : Source.Ctx} {fuel : Nat} {state : Source.State}
    {outcome : Source.Outcome} {ctx' : Source.Ctx}
    (hRun :
      Source.Stmt.run prim program ctx fuel .leave state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        Locals.Stmt.leave state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases ctx with
  | mk scope breakScope? continueScope? leaveScope? =>
      cases leaveScope? with
      | none =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, Source.invalid,
            Locals.Source.invalid, Structured.invalid, Ctx.toLocals] at hRun
      | some leaveScope =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, Ctx.toLocals]
            at hRun ⊢
          rcases hRun with ⟨hOutcome, hCtxEq⟩
          cases hCtxEq
          simp [hOutcome]

theorem terminal_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {ctx : Source.Ctx} {fuel : Nat} {kind : Assembly.HaltKind}
    {state : Source.State} {outcome : Source.Outcome}
    {ctx' : Source.Ctx}
    (hRun :
      Source.Stmt.run prim program ctx fuel (.terminal kind) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.terminal kind) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases hTerminal : prim.terminal kind state.shared [] <;>
    simp [Source.Stmt.run, Locals.Source.Stmt.run, hTerminal,
      Ctx.toLocals] at hRun ⊢
  rcases hRun with ⟨hOutcome, hCtx⟩
  cases hCtx
  simp [hOutcome]

theorem terminalArgs_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {ctx : Source.Ctx} {fuel : Nat} {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount} {state : Source.State}
    {outcome : Source.Outcome} {ctx' : Source.Ctx}
    (hRun :
      Source.Stmt.run prim program ctx fuel (.terminalArgs kind args) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.terminalArgs kind args) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases hArgs : Locals.Source.Expr.ExprSeq.eval prim args state <;>
    simp [Source.Stmt.run, Locals.Source.Stmt.run, hArgs, Ctx.toLocals]
      at hRun ⊢
  case ok result =>
    cases hTerminal : prim.terminal kind result.1.shared result.2 <;>
      simp [hTerminal] at hRun ⊢
    rcases hRun with ⟨hOutcome, hCtx⟩
    cases hCtx
    simp [hOutcome]

end Stmt

namespace SourceToLocals

def afterStmtRun (ctx ctx' : Source.Ctx) (outcome : Source.Outcome) :
    Except EVMException (Source.Outcome × Locals.Source.Ctx) :=
  match outcome.mode with
  | .regular => .ok (outcome, Ctx.toLocals ctx')
  | .brk | .cont | .leave | .halt _ => .ok (outcome, Ctx.toLocals ctx)

theorem runOpen_singleton_of_stmt_run {prim : Source.PrimitiveSemantics}
    {lowerProgram : Locals.Program} {ctx ctx' : Source.Ctx}
    {fuel : Nat} {lowerStmt : Locals.Stmt} {state : Source.State}
    {outcome : Source.Outcome}
    (hRun :
      Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx)
          (fuel + 1) lowerStmt state =
        .ok (outcome, Ctx.toLocals ctx')) :
    Locals.Source.Block.runOpen prim lowerProgram (Ctx.toLocals ctx)
        (fuel + 2) { stmts := [lowerStmt] } state =
      afterStmtRun ctx ctx' outcome := by
  cases outcome with
  | mk outcomeState mode =>
      cases mode <;>
        simp [Locals.Source.Block.runOpen, afterStmtRun, hRun,
          Locals.Source.Outcome.regular]

theorem atomic_runOpen_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {stmt : Stmt} {ctx ctx' : Source.Ctx}
    {fuel : Nat} {state : Source.State} {outcome : Source.Outcome}
    (hOwned : Stmt.AtomicSourceOwned returns stmt)
    (hRun :
      Source.Stmt.run prim program ctx (fuel + 1) stmt state =
        .ok (outcome, ctx')) :
    Locals.Source.Block.runOpen prim lowerProgram (Ctx.toLocals ctx)
        (fuel + 2) { stmts := Stmt.toLocals returns stmt } state =
      afterStmtRun ctx ctx' outcome := by
  cases stmt with
  | expr expr =>
      exact runOpen_singleton_of_stmt_run
        (Stmt.expr_toLocals_of_run (lowerProgram := lowerProgram) hRun)
  | let_ name value =>
      exact runOpen_singleton_of_stmt_run
        (Stmt.let_toLocals_of_run (lowerProgram := lowerProgram) hRun)
  | assign name value =>
      exact runOpen_singleton_of_stmt_run
        (Stmt.assign_toLocals_of_run (lowerProgram := lowerProgram) hRun)
  | brk =>
      exact runOpen_singleton_of_stmt_run
        (Stmt.brk_toLocals_of_run (lowerProgram := lowerProgram) hRun)
  | cont =>
      exact runOpen_singleton_of_stmt_run
        (Stmt.cont_toLocals_of_run (lowerProgram := lowerProgram) hRun)
  | leave =>
      subst returns
      simpa [Stmt.toLocals, Lower.pushReturns] using
        (runOpen_singleton_of_stmt_run
          (Stmt.leave_toLocals_of_run (lowerProgram := lowerProgram) hRun))
  | terminal kind =>
      exact runOpen_singleton_of_stmt_run
        (Stmt.terminal_toLocals_of_run (lowerProgram := lowerProgram) hRun)
  | terminalArgs kind args =>
      exact runOpen_singleton_of_stmt_run
        (Stmt.terminalArgs_toLocals_of_run (lowerProgram := lowerProgram) hRun)
  | block body =>
      cases hOwned
  | if_ cond body =>
      cases hOwned
  | switch scrutinee cases defaultBody =>
      cases hOwned
  | for_ init cond post body =>
      cases hOwned
  | call targets functionName args =>
      cases hOwned

theorem atomic_toLocals_stmt_run_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {stmt : Stmt} {ctx ctx' : Source.Ctx}
    {fuel : Nat} {state : Source.State} {outcome : Source.Outcome}
    (hOwned : Stmt.AtomicSourceOwned returns stmt)
    (hRun :
      Source.Stmt.run prim program ctx fuel stmt state =
        .ok (outcome, ctx')) :
    ∃ lowerStmt,
      Stmt.toLocals returns stmt = [lowerStmt] ∧
        Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
            lowerStmt state =
          .ok (outcome, Ctx.toLocals ctx') := by
  cases stmt with
  | expr expr =>
      exact ⟨Locals.Stmt.expr expr, by simp [Stmt.toLocals],
        Stmt.expr_toLocals_of_run (lowerProgram := lowerProgram) hRun⟩
  | let_ name value =>
      exact ⟨Locals.Stmt.let_ name value, by simp [Stmt.toLocals],
        Stmt.let_toLocals_of_run (lowerProgram := lowerProgram) hRun⟩
  | assign name value =>
      exact ⟨Locals.Stmt.assign name value, by simp [Stmt.toLocals],
        Stmt.assign_toLocals_of_run (lowerProgram := lowerProgram) hRun⟩
  | brk =>
      exact ⟨Locals.Stmt.brk, by simp [Stmt.toLocals],
        Stmt.brk_toLocals_of_run (lowerProgram := lowerProgram) hRun⟩
  | cont =>
      exact ⟨Locals.Stmt.cont, by simp [Stmt.toLocals],
        Stmt.cont_toLocals_of_run (lowerProgram := lowerProgram) hRun⟩
  | leave =>
      subst returns
      exact ⟨Locals.Stmt.leave, by simp [Stmt.toLocals, Lower.pushReturns],
        Stmt.leave_toLocals_of_run (lowerProgram := lowerProgram) hRun⟩
  | terminal kind =>
      exact ⟨Locals.Stmt.terminal kind, by simp [Stmt.toLocals],
        Stmt.terminal_toLocals_of_run (lowerProgram := lowerProgram) hRun⟩
  | terminalArgs kind args =>
      exact ⟨Locals.Stmt.terminalArgs kind args, by simp [Stmt.toLocals],
        Stmt.terminalArgs_toLocals_of_run (lowerProgram := lowerProgram) hRun⟩
  | block body =>
      cases hOwned
  | if_ cond body =>
      cases hOwned
  | switch scrutinee cases defaultBody =>
      cases hOwned
  | for_ init cond post body =>
      cases hOwned
  | call targets functionName args =>
      cases hOwned

theorem atomicList_runOpen_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {stmts : List Stmt} {ctx ctx' : Source.Ctx}
    {fuel : Nat} {state : Source.State} {outcome : Source.Outcome}
    (hOwned : StmtList.AtomicSourceOwned returns stmts)
    (hRun :
      Source.Block.runOpen prim program ctx fuel { stmts := stmts } state =
        .ok (outcome, ctx')) :
    Locals.Source.Block.runOpen prim lowerProgram (Ctx.toLocals ctx) fuel
        { stmts := StmtList.toLocals returns stmts } state =
      .ok (outcome, Ctx.toLocals ctx') := by
  induction stmts generalizing ctx ctx' fuel state outcome with
  | nil =>
      cases fuel with
      | zero =>
          simp [Source.Block.runOpen, Source.invalid, Structured.invalid] at hRun
      | succ fuel =>
          simp [Source.Block.runOpen] at hRun
          rcases hRun with ⟨hOutcome, hCtx⟩
          subst outcome
          subst ctx'
          simp [Locals.Source.Block.runOpen, StmtList.toLocals]
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [Source.Block.runOpen, Source.invalid, Structured.invalid] at hRun
      | succ fuel =>
          rcases hOwned with ⟨hStmtOwned, hRestOwned⟩
          cases hStmtRun :
              Source.Stmt.run prim program ctx fuel stmt state with
          | error err =>
              simp [Source.Block.runOpen, hStmtRun] at hRun
          | ok result =>
              rcases result with ⟨stmtOutcome, stmtCtx⟩
              rcases atomic_toLocals_stmt_run_of_run
                  (lowerProgram := lowerProgram) hStmtOwned hStmtRun with
                ⟨lowerStmt, hLowerEq, hLowerRun⟩
              cases stmtOutcome with
              | mk stmtState mode =>
                  cases mode <;>
                    simp [Source.Block.runOpen, Locals.Source.Block.runOpen,
                      StmtList.toLocals, hStmtRun, hLowerEq, hLowerRun] at hRun ⊢
                  · exact ih hRestOwned hRun
                  all_goals
                    rcases hRun with ⟨hOutcome, hCtx⟩
                    exact ⟨hOutcome, congrArg Ctx.toLocals hCtx⟩

theorem atomicBlock_runOpen_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {block : Block} {ctx ctx' : Source.Ctx}
    {fuel : Nat} {state : Source.State} {outcome : Source.Outcome}
    (hOwned : Block.AtomicSourceOwned returns block)
    (hRun :
      Source.Block.runOpen prim program ctx fuel block state =
        .ok (outcome, ctx')) :
    Locals.Source.Block.runOpen prim lowerProgram (Ctx.toLocals ctx) fuel
        (Block.toLocals returns block) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases block with
  | mk stmts =>
      exact atomicList_runOpen_toLocals_of_run hOwned hRun

theorem atomicBlock_runScoped_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {block : Block} {ctx : Source.Ctx}
    {fuel : Nat} {state : Source.State} {outcome : Source.Outcome}
    (hOwned : Block.AtomicSourceOwned returns block)
    (hRun :
      Source.Block.runScoped prim program ctx block fuel state =
        .ok outcome) :
    Locals.Source.Block.runScoped prim lowerProgram (Ctx.toLocals ctx)
        (Block.toLocals returns block) fuel state =
      .ok outcome := by
  cases block with
  | mk stmts =>
      cases hOpen :
          Source.Block.runOpen prim program ctx fuel { stmts := stmts } state with
      | error err =>
          simp [Source.Block.runScoped, hOpen] at hRun
      | ok result =>
          rcases result with ⟨openOutcome, openCtx⟩
          have hLowerOpen :=
            atomicList_runOpen_toLocals_of_run
              (lowerProgram := lowerProgram) hOwned hOpen
          cases openOutcome with
          | mk openState mode =>
              have hLowerOpen' :
                  Locals.Source.Block.runOpen prim lowerProgram
                      { scope := ctx.scope, breakScope? := ctx.breakScope?,
                        continueScope? := ctx.continueScope?,
                        leaveScope? := ctx.leaveScope? }
                      fuel { stmts := StmtList.toLocals returns stmts } state =
                    .ok ({ state := openState, mode := mode },
                      Ctx.toLocals openCtx) := by
                simpa [Ctx.toLocals] using hLowerOpen
              cases mode <;>
                simp [Source.Block.runScoped, Locals.Source.Block.runScoped,
                  Block.toLocals, hOpen, hLowerOpen', Ctx.toLocals] at hRun ⊢
              all_goals simp [hRun]

theorem blockStmt_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {ctx : Source.Ctx} {fuel : Nat}
    {body : Block} {state : Source.State} {outcome : Source.Outcome}
    {ctx' : Source.Ctx}
    (hOwned : Block.AtomicSourceOwned returns body)
    (hRun :
      Source.Stmt.run prim program ctx fuel (.block body) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.block (Block.toLocals returns body)) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases hScoped :
      Source.Block.runScoped prim program ctx body fuel state with
  | error err =>
      simp [Source.Stmt.run, hScoped] at hRun
  | ok scopedOutcome =>
      have hLowerScoped :=
        atomicBlock_runScoped_toLocals_of_run
          (lowerProgram := lowerProgram) hOwned hScoped
      simp [Source.Stmt.run, Locals.Source.Stmt.run, hScoped, hLowerScoped]
        at hRun ⊢
      rcases hRun with ⟨hOutcome, hCtx⟩
      subst outcome
      subst ctx'
      simp

theorem ifStmt_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {ctx : Source.Ctx} {fuel : Nat}
    {cond : Expr 1} {body : Block} {state : Source.State}
    {outcome : Source.Outcome} {ctx' : Source.Ctx}
    (hBody : Block.AtomicSourceOwned returns body)
    (hRun :
      Source.Stmt.run prim program ctx fuel (.if_ cond body) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.if_ cond (Block.toLocals returns body)) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases fuel with
  | zero =>
      simp [Source.Stmt.run, Source.invalid, Structured.invalid] at hRun
  | succ fuel =>
      cases hCond : Source.Expr.evalCondition prim cond state with
      | error err =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, hCond] at hRun
      | ok result =>
          rcases result with ⟨stateAfterCond, condTrue⟩
          cases condTrue with
          | false =>
              simp [Source.Stmt.run, Locals.Source.Stmt.run, hCond,
                Ctx.toLocals] at hRun ⊢
              rcases hRun with ⟨hOutcome, hCtx⟩
              subst outcome
              subst ctx'
              simp
          | true =>
              cases hScoped :
                  Source.Block.runScoped prim program ctx body fuel
                    stateAfterCond with
              | error err =>
                  simp [Source.Stmt.run, Locals.Source.Stmt.run, hCond,
                    hScoped] at hRun
              | ok bodyOutcome =>
                  have hLowerScoped :=
                    atomicBlock_runScoped_toLocals_of_run
                      (lowerProgram := lowerProgram) hBody hScoped
                  simp [Source.Stmt.run, Locals.Source.Stmt.run, hCond,
                    hScoped, hLowerScoped, Ctx.toLocals] at hRun ⊢
                  rcases hRun with ⟨hOutcome, hCtx⟩
                  subst outcome
                  subst ctx'
                  have hLowerScoped' :
                      Locals.Source.Block.runScoped prim lowerProgram
                          { scope := ctx.scope, breakScope? := ctx.breakScope?,
                            continueScope? := ctx.continueScope?,
                            leaveScope? := ctx.leaveScope? }
                          (Block.toLocals returns body) fuel stateAfterCond =
                        .ok bodyOutcome := by
                    simpa [Ctx.toLocals] using hLowerScoped
                  simp [hLowerScoped']

theorem runForLoop_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {loopCtx postBase bodyBase : Source.Ctx}
    {cond : Expr 1} {post body : Block} {fuel : Nat}
    {state : Source.State} {outcome : Source.Outcome}
    (hPost : Block.AtomicSourceOwned returns post)
    (hBody : Block.AtomicSourceOwned returns body)
    (hRun :
      Source.Stmt.runForLoop prim program loopCtx cond postBase post
          bodyBase body fuel state =
        .ok outcome) :
    Locals.Source.Stmt.runForLoop prim lowerProgram (Ctx.toLocals loopCtx)
        cond (Ctx.toLocals postBase) (Block.toLocals returns post)
        (Ctx.toLocals bodyBase) (Block.toLocals returns body) fuel state =
      .ok outcome := by
  induction fuel generalizing state outcome with
  | zero =>
      simp [Source.Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
  | succ fuel ih =>
      cases hCond : Source.Expr.evalCondition prim cond state with
      | error err =>
          simp [Source.Stmt.runForLoop, Locals.Source.Stmt.runForLoop,
            hCond] at hRun
      | ok result =>
          rcases result with ⟨stateAfterCond, condTrue⟩
          cases condTrue with
          | false =>
              simp [Source.Stmt.runForLoop, Locals.Source.Stmt.runForLoop,
                hCond, Ctx.toLocals] at hRun ⊢
              exact hRun
          | true =>
              cases hBodyRun :
                  Source.Block.runScoped prim program bodyBase body fuel
                    stateAfterCond with
              | error err =>
                  simp [Source.Stmt.runForLoop, Locals.Source.Stmt.runForLoop,
                    hCond, hBodyRun] at hRun
              | ok bodyOutcome =>
                  have hLowerBody :=
                    atomicBlock_runScoped_toLocals_of_run
                      (lowerProgram := lowerProgram) hBody hBodyRun
                  cases bodyOutcome with
                  | mk bodyState bodyMode =>
                      have hLowerBody' :
                          Locals.Source.Block.runScoped prim lowerProgram
                              { scope := bodyBase.scope,
                                breakScope? := bodyBase.breakScope?,
                                continueScope? := bodyBase.continueScope?,
                                leaveScope? := bodyBase.leaveScope? }
                              (Block.toLocals returns body) fuel
                              stateAfterCond =
                            .ok { state := bodyState, mode := bodyMode } := by
                        simpa [Ctx.toLocals] using hLowerBody
                      cases bodyMode with
                      | brk =>
                          simp [Source.Stmt.runForLoop,
                            Locals.Source.Stmt.runForLoop, hCond, hBodyRun,
                            hLowerBody', Ctx.toLocals] at hRun ⊢
                          exact hRun
                      | regular =>
                          cases hPostRun :
                              Source.Block.runScoped prim program postBase post
                                fuel bodyState with
                          | error err =>
                              simp [Source.Stmt.runForLoop, hCond, hBodyRun,
                                hPostRun] at hRun
                          | ok postOutcome =>
                              have hLowerPost :=
                                atomicBlock_runScoped_toLocals_of_run
                                  (lowerProgram := lowerProgram) hPost hPostRun
                              cases postOutcome with
                              | mk postState postMode =>
                                  have hLowerPost' :
                                      Locals.Source.Block.runScoped prim
                                          lowerProgram
                                          { scope := postBase.scope,
                                            breakScope? := postBase.breakScope?,
                                            continueScope? :=
                                              postBase.continueScope?,
                                            leaveScope? := postBase.leaveScope? }
                                          (Block.toLocals returns post) fuel
                                          bodyState =
                                        .ok (Locals.Source.Outcome.mk
                                          postState postMode) := by
                                    simpa [Ctx.toLocals] using hLowerPost
                                  cases postMode with
                                  | regular =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Ctx.toLocals] at hRun ⊢
                                      exact ih hRun
                                  | brk =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Source.invalid,
                                        Locals.Source.invalid,
                                        Structured.invalid, Ctx.toLocals]
                                        at hRun
                                  | cont =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Source.invalid,
                                        Locals.Source.invalid,
                                        Structured.invalid, Ctx.toLocals]
                                        at hRun
                                  | leave =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Ctx.toLocals] at hRun ⊢
                                      exact hRun
                                  | halt kind =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Ctx.toLocals] at hRun ⊢
                                      exact hRun
                      | cont =>
                          cases hPostRun :
                              Source.Block.runScoped prim program postBase post
                                fuel bodyState with
                          | error err =>
                              simp [Source.Stmt.runForLoop, hCond, hBodyRun,
                                hPostRun] at hRun
                          | ok postOutcome =>
                              have hLowerPost :=
                                atomicBlock_runScoped_toLocals_of_run
                                  (lowerProgram := lowerProgram) hPost hPostRun
                              cases postOutcome with
                              | mk postState postMode =>
                                  have hLowerPost' :
                                      Locals.Source.Block.runScoped prim
                                          lowerProgram
                                          { scope := postBase.scope,
                                            breakScope? := postBase.breakScope?,
                                            continueScope? :=
                                              postBase.continueScope?,
                                            leaveScope? := postBase.leaveScope? }
                                          (Block.toLocals returns post) fuel
                                          bodyState =
                                        .ok (Locals.Source.Outcome.mk
                                          postState postMode) := by
                                    simpa [Ctx.toLocals] using hLowerPost
                                  cases postMode with
                                  | regular =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Ctx.toLocals] at hRun ⊢
                                      exact ih hRun
                                  | brk =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Source.invalid,
                                        Locals.Source.invalid,
                                        Structured.invalid, Ctx.toLocals]
                                        at hRun
                                  | cont =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Source.invalid,
                                        Locals.Source.invalid,
                                        Structured.invalid, Ctx.toLocals]
                                        at hRun
                                  | leave =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Ctx.toLocals] at hRun ⊢
                                      exact hRun
                                  | halt kind =>
                                      simp [Source.Stmt.runForLoop,
                                        Locals.Source.Stmt.runForLoop, hCond,
                                        hBodyRun, hLowerBody', hPostRun,
                                        hLowerPost', Ctx.toLocals] at hRun ⊢
                                      exact hRun
                      | leave =>
                          simp [Source.Stmt.runForLoop,
                            Locals.Source.Stmt.runForLoop, hCond, hBodyRun,
                            hLowerBody', Ctx.toLocals] at hRun ⊢
                          exact hRun
                      | halt kind =>
                          simp [Source.Stmt.runForLoop,
                            Locals.Source.Stmt.runForLoop, hCond, hBodyRun,
                            hLowerBody', Ctx.toLocals] at hRun ⊢
                          exact hRun

theorem forStmt_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {ctx : Source.Ctx} {fuel : Nat}
    {init : Block} {cond : Expr 1} {post body : Block}
    {state : Source.State} {outcome : Source.Outcome} {ctx' : Source.Ctx}
    (hInit : Block.AtomicSourceOwned returns init)
    (hPost : Block.AtomicSourceOwned returns post)
    (hBody : Block.AtomicSourceOwned returns body)
    (hRun :
      Source.Stmt.run prim program ctx fuel
          (.for_ init cond post body) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.for_ (Block.toLocals returns init) cond
          (Block.toLocals returns post) (Block.toLocals returns body)) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases fuel with
  | zero =>
      simp [Source.Stmt.run, Source.invalid, Structured.invalid] at hRun
  | succ fuel =>
      let initBase := ctx.withoutLoopControl
      cases hInitRun :
          Source.Block.runOpen prim program initBase fuel init state with
      | error err =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, initBase,
            hInitRun] at hRun
      | ok initResult =>
          rcases initResult with ⟨initOutcome, initCtx⟩
          have hLowerInit :=
            atomicBlock_runOpen_toLocals_of_run
              (lowerProgram := lowerProgram) hInit hInitRun
          cases initOutcome with
          | mk initState initMode =>
              have hLowerInit' :
                  Locals.Source.Block.runOpen prim lowerProgram
                      ((Ctx.toLocals ctx).withoutLoopControl) fuel
                      (Block.toLocals returns init) state =
                    .ok ({ state := initState, mode := initMode },
                      Ctx.toLocals initCtx) := by
                simpa [initBase, Ctx.toLocals_withoutLoopControl] using
                  hLowerInit
              cases initMode with
              | regular =>
                  let postBase := initCtx.withoutLoopControl
                  let bodyBase :=
                    initCtx.withLoopControl initCtx.scope initCtx.scope
                  cases hLoopRun :
                      Source.Stmt.runForLoop prim program initCtx cond
                        postBase post bodyBase body fuel initState with
                  | error err =>
                      simp [Source.Stmt.run, Locals.Source.Stmt.run, initBase,
                        postBase, bodyBase, hInitRun, hLoopRun] at hRun
                  | ok loopOutcome =>
                      have hLowerLoop :=
                        runForLoop_toLocals_of_run
                          (lowerProgram := lowerProgram) (returns := returns)
                          hPost hBody hLoopRun
                      cases loopOutcome with
                      | mk loopState loopMode =>
                          have hLowerLoop' :
                              Locals.Source.Stmt.runForLoop prim lowerProgram
                                  (Ctx.toLocals initCtx) cond
                                  ((Ctx.toLocals initCtx).withoutLoopControl)
                                  (Block.toLocals returns post)
                                  ((Ctx.toLocals initCtx).withLoopControl
                                    initCtx.scope initCtx.scope)
                                  (Block.toLocals returns body) fuel
                                  initState =
                                .ok { state := loopState, mode := loopMode } := by
                            simpa [postBase, bodyBase,
                              Ctx.toLocals_withoutLoopControl,
                              Ctx.toLocals_withLoopControl] using hLowerLoop
                          have hLowerLoopScoped :
                              Locals.Source.Stmt.runForLoop prim lowerProgram
                                  (Ctx.toLocals initCtx) cond
                                  ((Ctx.toLocals initCtx).withoutLoopControl)
                                  (Block.toLocals returns post)
                                  ((Ctx.toLocals initCtx).withLoopControl
                                    (Ctx.toLocals initCtx).scope
                                    (Ctx.toLocals initCtx).scope)
                                  (Block.toLocals returns body) fuel
                                  initState =
                                .ok { state := loopState, mode := loopMode } := by
                            simpa [Ctx.toLocals] using hLowerLoop'
                          cases loopMode with
                          | regular =>
                              simp [Source.Stmt.run, Locals.Source.Stmt.run,
                                initBase, postBase, bodyBase, hInitRun,
                                hLowerInit', hLoopRun, hLowerLoopScoped] at hRun ⊢
                              rcases hRun with ⟨hOutcome, hCtx⟩
                              subst outcome
                              subst ctx'
                              simpa [Ctx.toLocals]
                          | brk =>
                              simp [Source.Stmt.run, Locals.Source.Stmt.run,
                                initBase, postBase, bodyBase, hInitRun,
                                hLoopRun, Source.invalid, Structured.invalid]
                                at hRun
                          | cont =>
                              simp [Source.Stmt.run, Locals.Source.Stmt.run,
                                initBase, postBase, bodyBase, hInitRun,
                                hLoopRun, Source.invalid, Structured.invalid]
                                at hRun
                          | leave =>
                              simp [Source.Stmt.run, Locals.Source.Stmt.run,
                                initBase, postBase, bodyBase, hInitRun,
                                hLowerInit', hLoopRun, hLowerLoopScoped] at hRun ⊢
                              rcases hRun with ⟨hOutcome, hCtx⟩
                              subst outcome
                              subst ctx'
                              simpa [Ctx.toLocals]
                          | halt kind =>
                              simp [Source.Stmt.run, Locals.Source.Stmt.run,
                                initBase, postBase, bodyBase, hInitRun,
                                hLowerInit', hLoopRun, hLowerLoopScoped] at hRun ⊢
                              rcases hRun with ⟨hOutcome, hCtx⟩
                              subst outcome
                              subst ctx'
                              simpa [Ctx.toLocals]
              | brk =>
                  simp [Source.Stmt.run, Locals.Source.Stmt.run, initBase,
                    hInitRun, Source.invalid, Structured.invalid] at hRun
              | cont =>
                  simp [Source.Stmt.run, Locals.Source.Stmt.run, initBase,
                    hInitRun, Source.invalid, Structured.invalid] at hRun
              | leave =>
                  simp [Source.Stmt.run, Locals.Source.Stmt.run, initBase,
                    hInitRun, hLowerInit'] at hRun ⊢
                  rcases hRun with ⟨hOutcome, hCtx⟩
                  subst outcome
                  subst ctx'
                  constructor <;> rfl
              | halt kind =>
                  simp [Source.Stmt.run, Locals.Source.Stmt.run, initBase,
                    hInitRun, hLowerInit'] at hRun ⊢
                  rcases hRun with ⟨hOutcome, hCtx⟩
                  subst outcome
                  subst ctx'
                  constructor <;> rfl

theorem switchStmt_toLocals_of_run {prim : Source.PrimitiveSemantics}
    {program : Program} {lowerProgram : Locals.Program}
    {returns : List Name} {ctx : Source.Ctx} {fuel : Nat}
    {scrutinee : Expr 1} {cases : List (Word × Block)}
    {defaultBody : Option Block} {state : Source.State}
    {outcome : Source.Outcome} {ctx' : Source.Ctx}
    (hCases : CaseList.AtomicSourceOwned returns cases)
    (hDefault : Default.AtomicSourceOwned returns defaultBody)
    (hRun :
      Source.Stmt.run prim program ctx fuel
          (.switch scrutinee cases defaultBody) state =
        .ok (outcome, ctx')) :
    Locals.Source.Stmt.run prim lowerProgram (Ctx.toLocals ctx) fuel
        (Locals.Stmt.switch scrutinee (CaseList.toLocals returns cases)
          (Default.toLocals returns defaultBody)) state =
      .ok (outcome, Ctx.toLocals ctx') := by
  cases fuel with
  | zero =>
      simp [Source.Stmt.run, Source.invalid, Structured.invalid] at hRun
  | succ fuel =>
      cases hScrutinee :
          Source.Expr.evalOne prim scrutinee state with
      | error err =>
          simp [Source.Stmt.run, Locals.Source.Stmt.run, hScrutinee] at hRun
      | ok result =>
          rcases result with ⟨stateAfterScrutinee, value⟩
          have hSelectEq :=
            switch_select_toLocals returns value cases defaultBody
          cases hSelect :
              Source.Switch.select value cases defaultBody with
          | none =>
              have hLowerSelect :
                  Locals.Source.Switch.select value
                      (CaseList.toLocals returns cases)
                      (Default.toLocals returns defaultBody) = none := by
                simpa [hSelect] using hSelectEq
              simp [Source.Stmt.run, Locals.Source.Stmt.run, hScrutinee,
                hSelect, hLowerSelect, Ctx.toLocals] at hRun ⊢
              rcases hRun with ⟨hOutcome, hCtx⟩
              subst outcome
              subst ctx'
              simp
          | some body =>
              have hLowerSelect :
                  Locals.Source.Switch.select value
                      (CaseList.toLocals returns cases)
                      (Default.toLocals returns defaultBody) =
                    some (Block.toLocals returns body) := by
                simpa [hSelect] using hSelectEq
              have hBodyOwned :
                  Block.AtomicSourceOwned returns body :=
                switch_select_sourceOwned hCases hDefault hSelect
              cases hScoped :
                  Source.Block.runScoped prim program ctx body fuel
                    stateAfterScrutinee with
              | error err =>
                  simp [Source.Stmt.run, Locals.Source.Stmt.run, hScrutinee,
                    hSelect, hScoped] at hRun
              | ok bodyOutcome =>
                  have hLowerScoped :=
                    atomicBlock_runScoped_toLocals_of_run
                      (lowerProgram := lowerProgram) hBodyOwned hScoped
                  simp [Source.Stmt.run, Locals.Source.Stmt.run, hScrutinee,
                    hSelect, hLowerSelect, hScoped, hLowerScoped,
                    Ctx.toLocals] at hRun ⊢
                  rcases hRun with ⟨hOutcome, hCtx⟩
                  subst outcome
                  subst ctx'
                  have hLowerScoped' :
                      Locals.Source.Block.runScoped prim lowerProgram
                          { scope := ctx.scope, breakScope? := ctx.breakScope?,
                            continueScope? := ctx.continueScope?,
                            leaveScope? := ctx.leaveScope? }
                          (Block.toLocals returns body) fuel
                          stateAfterScrutinee =
                        .ok bodyOutcome := by
                    simpa [Ctx.toLocals] using hLowerScoped
                  simp [hLowerScoped']

end SourceToLocals

end SourceLowering

end Functions
end EvmCompiler
