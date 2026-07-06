import EvmCompiler.VerityBridge.ExecAgreesFamily

/-!
# PART B proper — the ∃-fuel bridge family as independently committable case lemmas

The ratified bridge form (commit 6769774bf) is the unbounded ∃-fuel statement

  ∀ n, Bridge* prog → ∃ m, DoneAgrees (native.f n …) (ours.f m …)

proved by strong induction on the native fuel `n`. `BridgeAgreesAt n` bundles the
eight per-function agreement statements at native fuel `n`; `BridgeIH n` is the
strong-induction hypothesis (agreement at every strictly smaller native fuel).

This file commits:

* the `BridgeAgreesAt` / `BridgeIH` Prop scaffolding (Step 1 — no proofs, trivially
  green);
* the native one-step equation lemmas for `exec`/`execSeq`/`call`/`loop` in the
  `Native.*` style of `ExecAgrees.lean` (the expression-side `Native.*` lemmas —
  `evalValues_*`, `eval_eq`, `evalArgs_*`, `evalTail_*` — already live there). These
  never unfold `primCall`.

## Same-level dependency graph (discovered against the native definitions)

At native fuel `n = k + 1` the native kernel decrements to `k` for almost every
recursive call, so `BridgeIH n` suffices. The **only** two same-level edges are:

* `eval n expr = head' (evalValues n expr)` — `eval` calls `evalValues` at the
  *same* fuel `n`;
* `exec n (.ExprStmtCall (.Call (.inl prim) args))` = `multifill' [] (evalValues n
  (.Call (.inl prim) args))` — the primitive expression-statement calls
  `evalValues` at the *same* fuel `n` (native routes through `execPrimCall`, which
  reuses the exec fuel).

`evalValues n` itself depends only on `BridgeIH n` (`evalArgs` and `call` at `n-1`),
so it is a leaf at level `n`. The DAG is therefore

  evalValues(n)  ←  eval(n)
  evalValues(n)  ←  exec(n, ExprStmtCall prim)

and the case lemmas resolve it by having `caseEval` / the `caseExec` primitive arm
invoke `caseEvalValues n ih` directly (never the reverse).

## OPEN BOUNDARY — `CodeBridge` preservation (see PROGRESS_LOG, tag `bottleneck`)

Native `call` demands `s.sharedState.accountMap.find? s.executionEnv.codeOwner ≠
none` **even when `codeOverride = some c`** (it only consumes the found contract via
`getD`, but the `match` still requires presence, else `.MissingContract`). Our
`resolveActiveCode? s (some c) = some c` never inspects the account map. So
`DoneAgrees` for `call` is *false* unless the account is present — a genuinely
state-dependent precondition (`CodeBridge` below). Because every fragment
expression can reach an internal call (`BridgeExpr` admits `.Call (.inr fn) args`),
this precondition must be *preserved* through `eval`/`evalArgs`/`exec` state
threading — which reduces at the primitive leaf to "a `BridgeOp` `primCall`
preserves `codeOwner`'s account entry". That is **false in general** (`SELFDESTRUCT`
is a `BridgeOp` and removes the account) and, even where true, provable only by
opening `primCall` — the per-opcode zoo W2 sealed. The `CodeBridge` hypotheses below
record the intended precondition shape; discharging/preserving them is the plan-owner
decision that blocks the case-lemma proofs.
-/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

section Bundle

open EvmYul.Yul.Ast
open InteractionSemantics

/-! ## The active-code bridge precondition (intended shape; see boundary note) -/

/-- The contract native `call` resolves at `s` for the given override: `none`
exactly when native would raise `.MissingContract`. -/
def nativeActiveCode (code : Option YulContract) (s : State) : Option YulContract :=
  match s.sharedState.accountMap.find? s.executionEnv.codeOwner with
  | none => none
  | some yulContract => some (code.getD yulContract.code)

/-- Both interpreters resolve the *same* active contract at `s`, and it is
request-free. This is the state-dependent precondition native `call` forces (and
the open preservation obligation described in the module docstring). -/
def CodeBridge (code : Option YulContract) (s : State) : Prop :=
  ∃ c, nativeActiveCode code s = some c ∧
    Yul.Source.Effectful.resolveActiveCode? s code = some c ∧
    BridgeContract c

/-! ## The per-fuel agreement bundle -/

/-- The eight per-function ∃-fuel agreement statements at native fuel `n`. -/
structure BridgeAgreesAt (n : Nat) : Prop where
  /-- `evalTail` takes agreeing prior result pairs (M3.2 handoff form). The
  `CodeBridge`-at-prior-state hypothesis is what the internal `evalArgs` recursion
  (over the prior `.ok` state) consumes. -/
  evalTail : ∀ (args : List Expr) (code : Option YulContract)
      (nr : Except EvmYul.Yul.Exception (State × Word)) (or : Open (State × Word)),
      BridgeExprs args → (∀ p, nr = .ok p → CodeBridge code p.1) → DoneAgrees nr or →
      ∃ m, DoneAgrees (EvmYul.Yul.evalTail n args code nr) (evalTail m args code or)
  evalArgs : ∀ (args : List Expr) (code : Option YulContract) (s : State),
      BridgeExprs args → CodeBridge code s →
      ∃ m, DoneAgrees (EvmYul.Yul.evalArgs n args code s) (evalArgs m args code s)
  evalValues : ∀ (expr : Expr) (code : Option YulContract) (s : State),
      BridgeExpr expr → CodeBridge code s →
      ∃ m, DoneAgrees (EvmYul.Yul.evalValues n expr code s) (evalValues m expr code s)
  eval : ∀ (expr : Expr) (code : Option YulContract) (s : State),
      BridgeExpr expr → CodeBridge code s →
      ∃ m, DoneAgrees (EvmYul.Yul.eval n expr code s) (eval m expr code s)
  call : ∀ (args : List Word) (fn? : Option YulFunctionName)
      (code : Option YulContract) (s : State),
      CodeBridge code s →
      ∃ m, DoneAgrees (EvmYul.Yul.call n args fn? code s) (call m args fn? code s)
  execSeq : ∀ (stmts : List Stmt) (code : Option YulContract) (s : State),
      BridgeStmts stmts → CodeBridge code s →
      ∃ m, DoneAgrees (EvmYul.Yul.execSeq n stmts code s) (execSeq m stmts code s)
  exec : ∀ (stmt : Stmt) (code : Option YulContract) (s : State),
      BridgeStmt stmt → CodeBridge code s →
      ∃ m, DoneAgrees (EvmYul.Yul.exec n stmt code s) (exec m stmt code s)
  loop : ∀ (cond : Expr) (post body : List Stmt) (code : Option YulContract)
      (s : State),
      BridgeExpr cond → BridgeStmts post → BridgeStmts body → CodeBridge code s →
      ∃ m, DoneAgrees (EvmYul.Yul.loop n cond post body code s) (loop m cond post body code s)

/-- Strong-induction hypothesis: agreement at every strictly smaller native fuel. -/
abbrev BridgeIH (n : Nat) : Prop := ∀ k, k < n → BridgeAgreesAt k

end Bundle

/-! ## Native one-step equation lemmas for `exec`/`execSeq`/`call`/`loop`

Mirror of the expression-side `Native.*` lemmas in `ExecAgrees.lean` and of our
side's `InteractionSemantics.{Exec,ExecSeq,Call}.*`. All are `rw`/`simp only`
definitional unfoldings; `primCall` is never unfolded. -/

namespace Native

-- The uniform `rw [f]; repeat' first | rfl | split` closer sometimes discharges a
-- lemma with `rfl` alone (leaving `split` unreached) and sometimes needs `split`;
-- both linters would otherwise flag the unused branch on the `rfl`-only lemmas.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open EvmYul.Yul EvmYul.Yul.Ast

variable (fuel : Nat) (code : Option YulContract) (s : State)

/-! ### `execSeq` -/

theorem execSeq_zero (stmts : List Stmt) :
    execSeq 0 stmts code s = .error .OutOfFuel := by rw [execSeq]; repeat' first | rfl | split

theorem execSeq_nil : execSeq (fuel + 1) [] code s = .ok s := by rw [execSeq]; repeat' first | rfl | split

theorem execSeq_cons (stmt : Stmt) (rest : List Stmt) :
    execSeq (fuel + 1) (stmt :: rest) code s =
      (match exec fuel stmt code s with
       | .error e => .error e
       | .ok s₁ =>
           match s₁ with
           | .Ok _ _ => execSeq fuel rest code s₁
           | .OutOfFuel => .ok s₁
           | .Checkpoint _ => .ok s₁) := by
  rw [execSeq]; repeat' first | rfl | split

/-! ### `exec` -/

theorem exec_zero (stmt : Stmt) :
    exec 0 stmt code s = .error .OutOfFuel := by rw [exec]; repeat' first | rfl | split

theorem exec_block (body : List Stmt) :
    exec (fuel + 1) (.Block body) code s =
      (match execSeq fuel body code s with
       | .error e => .error e
       | .ok s₁ => .ok (s₁.restrictStoreTo s.store)) := by rw [exec]; repeat' first | rfl | split

theorem exec_let_none (names : List EvmYul.Identifier) :
    exec (fuel + 1) (.Let names none) code s =
      (match checkDeclaration s names with
       | .error e => .error e
       | .ok () => .ok (s.zeroFill names)) := by rw [exec]; repeat' first | rfl | split

theorem exec_let_some (names : List EvmYul.Identifier) (expr : Expr) :
    exec (fuel + 1) (.Let names (some expr)) code s =
      (match checkDeclaration s names with
       | .error e => .error e
       | .ok () => multifill' names (evalValues fuel expr code s)) := by rw [exec]; repeat' first | rfl | split

theorem exec_assign (names : List EvmYul.Identifier) (expr : Expr) :
    exec (fuel + 1) (.Assign names expr) code s =
      (match checkAssignment s names with
       | .error e => .error e
       | .ok () => multifill' names (evalValues fuel expr code s)) := by rw [exec]; repeat' first | rfl | split

theorem exec_if (cond : Expr) (body : List Stmt) :
    exec (fuel + 1) (.If cond body) code s =
      (match eval fuel cond code s with
       | .error e => .error e
       | .ok (s, c) =>
           if c ≠ ⟨0⟩ then exec fuel (.Block body) code s else .ok s) := by
  rw [exec]; repeat' first | rfl | split

theorem exec_switch (cond : Expr) (cases : List (Literal × List Stmt))
    (defaultBody : List Stmt) :
    exec (fuel + 1) (.Switch cond cases defaultBody) code s =
      (match eval fuel cond code s with
       | .error e => .error e
       | .ok (s₁, c) =>
           exec fuel (.Block (selectSwitchCase c defaultBody cases)) code s₁) := by
  rw [exec]; repeat' first | rfl | split

theorem exec_for (cond : Expr) (post body : List Stmt) :
    exec (fuel + 1) (.For cond post body) code s =
      loop fuel cond post body code s := by rw [exec]; repeat' first | rfl | split

theorem exec_expr_prim (prim : EvmYul.Operation .Yul) (args : List Expr) :
    exec (fuel + 1) (.ExprStmtCall (.Call (.inl prim) args)) code s =
      execPrimCall fuel prim [] (reverse' (evalArgs fuel args.reverse code s)) := by
  rw [exec]; repeat' first | rfl | split

theorem exec_expr_internal (fn : YulFunctionName) (args : List Expr) :
    exec (fuel + 1) (.ExprStmtCall (.Call (.inr fn) args)) code s =
      execCall fuel fn [] code (reverse' (evalArgs fuel args.reverse code s)) := by
  rw [exec]; repeat' first | rfl | split

theorem exec_continue :
    exec (fuel + 1) .Continue code s = .ok s.setContinue := by rw [exec]; repeat' first | rfl | split

theorem exec_break :
    exec (fuel + 1) .Break code s = .ok s.setBreak := by rw [exec]; repeat' first | rfl | split

theorem exec_leave :
    exec (fuel + 1) .Leave code s = .ok s.setLeave := by rw [exec]; repeat' first | rfl | split

/-! ### `call` -/

theorem call_zero (args : List Word) (fn? : Option YulFunctionName) :
    call 0 args fn? code s = .error .OutOfFuel := by rw [call]; repeat' first | rfl | split

theorem call_succ (args : List Word) (fn? : Option YulFunctionName) :
    call (fuel + 1) args fn? code s =
      (match s.sharedState.accountMap.find? s.executionEnv.codeOwner with
       | .none => .error (.MissingContract (s!"{s.executionEnv.codeOwner}"))
       | .some yulContract =>
           let c : YulContract := code.getD yulContract.code
           match (match fn? with
                  | .none => some (FunctionDefinition.Def [] [] [c.dispatcher])
                  | .some f => c.functions.lookup f) with
           | .none => .error (.MissingContractFunction (fn?.getD ".none"))
           | .some f =>
               let s₁ := EvmYul.Yul.State.mkOk (s.initcall f.params f.rets args)
               match exec fuel (.Block f.body) code s₁ with
               | .error e => .error e
               | .ok s₂ =>
                   let s₃ := (s₂.reviveJump.overwrite? s).setStore s
                   .ok (s₃, List.map s₂.lookup! f.rets)) := by
  rw [call]; repeat' first | rfl | split

/-! ### `loop` -/

theorem loop_zero (cond : Expr) (post body : List Stmt) :
    loop 0 cond post body code s = .error .OutOfFuel := by rw [loop]; repeat' first | rfl | split

theorem loop_one (cond : Expr) (post body : List Stmt) :
    loop 1 cond post body code s = .error .OutOfFuel := by rw [loop]; repeat' first | rfl | split

/-! ### `callDispatcher` -/

theorem callDispatcher_zero :
    callDispatcher 0 code s = .error .OutOfFuel := by rw [callDispatcher]; repeat' first | rfl | split

theorem callDispatcher_succ :
    callDispatcher (fuel + 1) code s =
      (let f := FunctionDefinition.Def [] [] [s.executionEnv.code.dispatcher]
       let s₁ := EvmYul.Yul.State.mkOk (s.initcall f.params f.rets [])
       match exec fuel (.Block f.body) code s₁ with
       | .error e => .error e
       | .ok s₂ =>
           let s₃ := (s₂.reviveJump.overwrite? s).setStore s
           .ok (s₃, List.map s₂.lookup! f.rets)) := by
  rw [callDispatcher]; repeat' first | rfl | split

end Native

end VerityBridge
end Yul
end EvmCompiler
