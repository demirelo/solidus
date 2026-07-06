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

## RESOLVED BOUNDARY — `CodeBridge` preservation (ratified, commit 282ca375b)

Native `call` demands `s.sharedState.accountMap.find? s.executionEnv.codeOwner ≠
none` **even when `codeOverride = some c`** (it only consumes the found contract via
`getD`, but the `match` still requires presence, else `.MissingContract`). Our
`resolveActiveCode? s (some c) = some c` never inspects the account map. So
`DoneAgrees` for `call` is *false* unless the account is present — a genuinely
state-dependent precondition (`CodeBridge` below). Because every fragment
expression can reach an internal call (`BridgeExpr` admits `.Call (.inr fn) args`),
this precondition must be *preserved* through `eval`/`evalArgs`/`exec` state
threading — which reduces at the primitive leaf to "a `BridgeOp` `primCall`
preserves `codeOwner`'s account entry".

The earlier worry that this is *false* (via `SELFDESTRUCT`) was a
misreading: Yul `SELFDESTRUCT`/`RETURN`/`REVERT`/`STOP` all return `.error`
(terminal), so their `.ok` arm is vacuous; the only account-map-mutating
`BridgeOp`s are `SSTORE`/`TSTORE`, both of which `insert` the `codeOwner` key
(presence preserved) and never touch `executionEnv`. This is captured once, inside
the `primCall` black box, by `primCall_preserves_codeBridge` (PrimAgrees.lean).
Part B0 lifts it through the native mutual structure. -/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

section Bundle

open EvmYul.Yul.Ast
open InteractionSemantics

/-! ## The active-code bridge preconditions (ratified presence/override split)

Commit 282ca375b ratified `CodeBridge` down to **presence only**, split off from
the (invariant) bridge-ness of the code override. The former is the *only*
state-dependent obligation and is what Part B0 preserves through state threading;
the latter (`BridgeCode`) never changes across the whole run (`codeOverride` is
threaded unchanged), so it needs no preservation lemma at all — this is the
"fewer obligations downstream" the ratification calls for.

The pre-ratification `CodeBridge` additionally asserted resolution *agreement*
(native `code.getD (find? codeOwner).code` = our `resolveActiveCode?`) and
`BridgeContract` of the resolved contract. Both are now derived rather than
assumed: agreement follows from presence alone (in the `some c` route both sides
resolve to `c`; in the `none` route both resolve to the account's contract given
presence), and bridge-ness of the executed bodies comes from `BridgeCode`. -/

/-- The contract native `call` resolves at `s` for the given override: `none`
exactly when native would raise `.MissingContract`. Retained as documentation of
the native resolution (used by Part B0 / the `call` case). -/
def nativeActiveCode (code : Option YulContract) (s : State) : Option YulContract :=
  match s.sharedState.accountMap.find? s.executionEnv.codeOwner with
  | none => none
  | some yulContract => some (code.getD yulContract.code)

/-- **Presence only** (ratified). Native `call (fuel+1)` matches
`s.sharedState.accountMap.find? s.executionEnv.codeOwner` and raises
`.MissingContract` on `none` even under `codeOverride = some c`; our
`resolveActiveCode?` never inspects the map. So `DoneAgrees` for `call` needs the
owner account present. This is the state-dependent precondition Part B0 preserves
through eval/exec state threading (its leaf is `primCall_preserves_codeBridge`). -/
def CodeBridge (s : State) : Prop :=
  s.sharedState.accountMap.find? s.executionEnv.codeOwner ≠ none

/-- The **invariant** override-bridge hypothesis: the resolved active program is a
`BridgeContract`. `codeOverride` is threaded unchanged through every recursive
call, so this never needs preservation. Stated for the `some c` route only — the
`none` route never occurs in the real spine (`compile_correct`/`callDispatcher`
always supply `some contract`), and native `call`'s body in the `some c` route is
taken from `c` itself (via `code.getD`), so `BridgeContract c` bounds every
executed body (dispatcher and each `functions.lookup`). -/
def BridgeCode (code : Option YulContract) : Prop :=
  ∃ c, code = some c ∧ BridgeContract c

/-! ## The per-fuel agreement bundle -/

/-- The eight per-function ∃-fuel agreement statements at native fuel `n`.

Each field carries: the structural `Bridge*` hypothesis (bounds the AST executed
directly), `BridgeCode code` (invariant; bounds bodies reached via internal
calls), and `CodeBridge` at the input state (presence; re-established at derived
states via Part B0). -/
structure BridgeAgreesAt (n : Nat) : Prop where
  /-- `evalTail` takes agreeing prior result pairs (M3.2 handoff form). The
  `CodeBridge`-at-prior-state hypothesis is what the internal `evalArgs` recursion
  (over the prior `.ok` state) consumes. -/
  evalTail : ∀ (args : List Expr) (code : Option YulContract)
      (nr : Except EvmYul.Yul.Exception (State × Word)) (or : Open (State × Word)),
      BridgeExprs args → BridgeCode code →
      (∀ p, nr = .ok p → CodeBridge p.1) → DoneAgrees nr or →
      ∃ m, DoneAgrees (EvmYul.Yul.evalTail n args code nr) (evalTail m args code or)
  evalArgs : ∀ (args : List Expr) (code : Option YulContract) (s : State),
      BridgeExprs args → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.evalArgs n args code s) (evalArgs m args code s)
  evalValues : ∀ (expr : Expr) (code : Option YulContract) (s : State),
      BridgeExpr expr → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.evalValues n expr code s) (evalValues m expr code s)
  eval : ∀ (expr : Expr) (code : Option YulContract) (s : State),
      BridgeExpr expr → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.eval n expr code s) (eval m expr code s)
  call : ∀ (args : List Word) (fn? : Option YulFunctionName)
      (code : Option YulContract) (s : State),
      BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.call n args fn? code s) (call m args fn? code s)
  execSeq : ∀ (stmts : List Stmt) (code : Option YulContract) (s : State),
      BridgeStmts stmts → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.execSeq n stmts code s) (execSeq m stmts code s)
  exec : ∀ (stmt : Stmt) (code : Option YulContract) (s : State),
      BridgeStmt stmt → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.exec n stmt code s) (exec m stmt code s)
  loop : ∀ (cond : Expr) (post body : List Stmt) (code : Option YulContract)
      (s : State),
      BridgeExpr cond → BridgeStmts post → BreakContinueFreeStmts post →
      BridgeStmts body → BridgeCode code → CodeBridge s →
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

theorem exec_expr_var (id : EvmYul.Identifier) :
    exec (fuel + 1) (.ExprStmtCall (.Var id)) code s = .error .InvalidExpression := by
  rw [exec]; repeat' first | rfl | split
  all_goals exact fun _ _ h => Expr.noConfusion h

theorem exec_expr_lit (v : EvmYul.Literal) :
    exec (fuel + 1) (.ExprStmtCall (.Lit v)) code s = .error .InvalidExpression := by
  rw [exec]; repeat' first | rfl | split
  all_goals exact fun _ _ h => Expr.noConfusion h

theorem exec_continue :
    exec (fuel + 1) .Continue code s = .ok s.setContinue := by rw [exec]; repeat' first | rfl | split

theorem exec_break :
    exec (fuel + 1) .Break code s = .ok s.setBreak := by rw [exec]; repeat' first | rfl | split

theorem exec_leave :
    exec (fuel + 1) .Leave code s = .ok s.setLeave := by rw [exec]; repeat' first | rfl | split

/-! ### `execPrimCall` / `execCall` (the `ExprStmtCall` helpers) -/

theorem execPrimCall_error (prim : EvmYul.Operation .Yul)
    (vars : List EvmYul.Identifier) (e : EvmYul.Yul.Exception) :
    execPrimCall fuel prim vars (.error e) = .error e := by
  rw [execPrimCall]

theorem execPrimCall_ok (prim : EvmYul.Operation .Yul)
    (vars : List EvmYul.Identifier) (st : State) (vals : List Word) :
    execPrimCall fuel prim vars (.ok (st, vals)) =
      multifill' vars (primCall fuel st prim vals) := by
  rw [execPrimCall]

theorem execCall_error (fn : YulFunctionName)
    (vars : List EvmYul.Identifier) (e : EvmYul.Yul.Exception) :
    execCall fuel fn vars code (.error e) = .error e := by
  rw [execCall]

theorem execCall_ok_zero (fn : YulFunctionName)
    (vars : List EvmYul.Identifier) (st : State) (vals : List Word) :
    execCall 0 fn vars code (.ok (st, vals)) = .error .OutOfFuel := by
  rw [execCall]

theorem execCall_ok_succ (fn : YulFunctionName)
    (vars : List EvmYul.Identifier) (st : State) (vals : List Word) :
    execCall (fuel + 1) fn vars code (.ok (st, vals)) =
      multifill' vars (call fuel vals (some fn) code st) := by
  rw [execCall]

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

theorem loop_succ_succ (cond : Expr) (post body : List Stmt) :
    loop (fuel + 1 + 1) cond post body code s =
      (match eval fuel cond code s.mkOk with
       | .error e => .error e
       | .ok (s₁, x) =>
           if x = ⟨0⟩ then .ok (s₁.overwrite? s)
           else
             match exec fuel (.Block body) code s₁ with
             | .error e => .error e
             | .ok s₂ =>
                 match s₂ with
                 | .OutOfFuel => .ok (s₂.overwrite? s)
                 | .Checkpoint (.Break _ _) => .ok (s₂.reviveJump.overwrite? s)
                 | .Checkpoint (.Leave _ _) => .ok (s₂.overwrite? s)
                 | .Checkpoint (.Continue _ _) | _ =>
                     match exec fuel (.Block post) code s₂.reviveJump with
                     | .error e => .error e
                     | .ok s₃ =>
                         match s₃ with
                         | .OutOfFuel => .ok (s₃.overwrite? s)
                         | .Checkpoint (.Leave _ _) => .ok (s₃.overwrite? s)
                         | _ =>
                             match exec fuel (.For cond post body) code
                                 (s₃.overwrite? s) with
                             | .error e => .error e
                             | .ok s₅ => .ok (s₅.overwrite? s)) := by
  rw [loop]; repeat' first | rfl | split

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

/-! ## Part B0 — native-side `CodeBridge` preservation

The case lemmas re-establish `CodeBridge` at derived states via this bundle:
for Bridge* programs (with a `BridgeCode` override), every native `.ok` result
carries the owner-account presence forward. The primitive leaf is
`primCall_preserves_codeBridge` (PrimAgrees.lean — the one file allowed to open
`primCall`); everything else is structural.

Two refinements over raw presence:

* statement-level results (`exec`/`execSeq`/`loop`) may be `Checkpoint` states,
  whose `sharedState`/`executionEnv` *getters* return `default` — presence must
  be tracked in the shared state the `Jump` constructor *carries*
  (`StateBridge`); `reviveJump`/`overwrite?` later move it back into an `Ok`.
* the loop poison (see `breakContinueFree?` in RequestFree.lean): the bundle
  additionally proves a `BreakContinueFreeStmts` post/statement never produces a
  `Break`/`Continue` checkpoint (`¬ IsJumpBC`), so `loop`'s tail recursion
  `exec (.For …)` always restarts from an `Ok`-or-`Leave`-free state. -/

section PartB0

open EvmYul.Yul.Ast
open InteractionSemantics

/-- The code owner's account is present in a shared state. -/
def OwnerPresent (shared : EvmYul.SharedState .Yul) : Prop :=
  shared.accountMap.find? shared.executionEnv.codeOwner ≠ none

/-- The default (empty-map) shared state has no owner account. -/
theorem not_ownerPresent_default : ¬ OwnerPresent default := fun h => h rfl

/-- `CodeBridge` forces the state to be `Ok` (the non-`Ok` getters default to the
empty account map). -/
theorem codeBridge_ok {s : State} (h : CodeBridge s) :
    ∃ shared store, s = EvmYul.Yul.State.Ok shared store ∧ OwnerPresent shared := by
  cases s with
  | Ok shared store => exact ⟨shared, store, rfl, h⟩
  | OutOfFuel => exact absurd h (fun h => h rfl)
  | Checkpoint j => exact absurd h (fun h => h rfl)

theorem codeBridge_okState {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore} (h : OwnerPresent shared) :
    CodeBridge (EvmYul.Yul.State.Ok shared store) := h

/-- Result-state invariant for the statement layer: presence of the owner account
in the shared state the constructor *carries* (`OutOfFuel` is unreachable from
`CodeBridge` entries). -/
def StateBridge : State → Prop
  | .Ok shared _ => OwnerPresent shared
  | .OutOfFuel => False
  | .Checkpoint (.Break shared _) => OwnerPresent shared
  | .Checkpoint (.Continue shared _) => OwnerPresent shared
  | .Checkpoint (.Leave shared _) => OwnerPresent shared

/-- `Break`/`Continue` checkpoint states (the loop-recursion poison). -/
def IsJumpBC : State → Prop
  | .Checkpoint (.Break _ _) => True
  | .Checkpoint (.Continue _ _) => True
  | _ => False

theorem stateBridge_of_codeBridge {s : State} (h : CodeBridge s) : StateBridge s := by
  obtain ⟨shared, store, rfl, hp⟩ := codeBridge_ok h
  exact hp

theorem not_isJumpBC_of_codeBridge {s : State} (h : CodeBridge s) : ¬ IsJumpBC s := by
  obtain ⟨shared, store, rfl, -⟩ := codeBridge_ok h
  exact fun hbc => hbc

/-- `reviveJump` turns any `StateBridge` state into a `CodeBridge` (`Ok`) state. -/
theorem codeBridge_reviveJump {s : State} (h : StateBridge s) :
    CodeBridge s.reviveJump := by
  cases s with
  | Ok shared store => exact h
  | OutOfFuel => exact h.elim
  | Checkpoint j => cases j <;> exact h

/-- The caller-frame restoration of `call`/`callDispatcher` preserves presence:
the result shared state is the one `reviveJump` recovers from the body result. -/
theorem codeBridge_callResult {s₂ s : State} (h₂ : StateBridge s₂)
    (hs : CodeBridge s) :
    CodeBridge ((s₂.reviveJump.overwrite? s).setStore s) := by
  obtain ⟨shared, store, rfl, -⟩ := codeBridge_ok hs
  cases s₂ with
  | Ok shared₂ store₂ => exact h₂
  | OutOfFuel => exact h₂.elim
  | Checkpoint j => cases j <;> exact h₂

/-! ### Var-store-only state operations preserve the carried shared state -/

private theorem foldr_insert_ok {α : Type}
    (ff : α → State → State)
    (hff : ∀ (a : α) (shared : EvmYul.SharedState .Yul)
      (store : EvmYul.Yul.VarStore),
      ∃ store', ff a (.Ok shared store) = .Ok shared store')
    (l : List α) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    ∃ store', l.foldr ff (EvmYul.Yul.State.Ok shared store) = .Ok shared store' := by
  induction l with
  | nil => exact ⟨store, rfl⟩
  | cons a l ih =>
      obtain ⟨store', h⟩ := ih
      obtain ⟨store'', h'⟩ := hff a shared store'
      exact ⟨store'', by rw [List.foldr_cons, h, h']⟩

theorem multifill_ok (vars : List EvmYul.Identifier) (vals : List Word)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore) :
    ∃ store', EvmYul.Yul.State.multifill vars vals (.Ok shared store) =
      .Ok shared store' := by
  unfold EvmYul.Yul.State.multifill
  exact foldr_insert_ok _ (fun p sh st => ⟨st.insert p.1 p.2, by cases p; rfl⟩)
    (List.zip vars vals) shared store

theorem zeroFill_ok (vars : List EvmYul.Identifier)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore) :
    ∃ store', EvmYul.Yul.State.zeroFill vars (.Ok shared store) =
      .Ok shared store' := by
  unfold EvmYul.Yul.State.zeroFill
  exact foldr_insert_ok _ (fun v sh st => ⟨st.insert v ⟨0⟩, rfl⟩) vars shared store

theorem stateBridge_restrictStoreTo {s : State} (scope : EvmYul.Yul.VarStore)
    (h : StateBridge s) : StateBridge (s.restrictStoreTo scope) := by
  cases s with
  | Ok shared store => exact h
  | OutOfFuel => exact h.elim
  | Checkpoint j => cases j <;> exact h

theorem not_isJumpBC_restrictStoreTo {s : State} (scope : EvmYul.Yul.VarStore)
    (h : ¬ IsJumpBC s) : ¬ IsJumpBC (s.restrictStoreTo scope) := by
  cases s with
  | Ok shared store => exact fun hbc => hbc
  | OutOfFuel => exact fun hbc => hbc
  | Checkpoint j => cases j <;> exact h

/-- The `call` entry state (`mkOk` after `initcall`) keeps the caller's shared
state, hence its presence. -/
theorem codeBridge_initcall {s : State} (h : CodeBridge s)
    (params rets : List EvmYul.Identifier) (args : List Word) :
    CodeBridge (EvmYul.Yul.State.mkOk (s.initcall params rets args)) := by
  obtain ⟨shared, store, rfl, hp⟩ := codeBridge_ok h
  show CodeBridge (EvmYul.Yul.State.mkOk
    (EvmYul.Yul.State.multifill params args
      (EvmYul.Yul.State.zeroFill rets
        ((EvmYul.Yul.State.Ok shared store).setStore default))))
  obtain ⟨store₁, h₁⟩ := zeroFill_ok rets shared
    ((default : EvmYul.Yul.State).store)
  obtain ⟨store₂, h₂⟩ := multifill_ok params args shared store₁
  rw [show (EvmYul.Yul.State.Ok shared store).setStore default =
      EvmYul.Yul.State.Ok shared ((default : EvmYul.Yul.State).store) from rfl,
    h₁, h₂]
  exact hp

/-! ### Fragment-predicate transport through native selection helpers -/

theorem bridgeStmts_selectSwitchCase {cases : List (Literal × List Stmt)}
    {defaultBody : List Stmt}
    (hCases : bridgeCases? cases = true) (hDefault : BridgeStmts defaultBody)
    (c : Literal) :
    BridgeStmts (EvmYul.Yul.selectSwitchCase c defaultBody cases) := by
  induction cases with
  | nil => exact hDefault
  | cons hd tl ih =>
      obtain ⟨val, body⟩ := hd
      rw [EvmYul.Yul.selectSwitchCase]
      simp only [bridgeCases?, Bool.and_eq_true] at hCases
      by_cases hv : val = c
      · rw [if_pos hv]; exact hCases.1
      · rw [if_neg hv]; exact ih hCases.2

theorem breakContinueFreeStmts_selectSwitchCase
    {cases : List (Literal × List Stmt)} {defaultBody : List Stmt}
    (hCases : breakContinueFreeCases? cases = true)
    (hDefault : BreakContinueFreeStmts defaultBody) (c : Literal) :
    BreakContinueFreeStmts (EvmYul.Yul.selectSwitchCase c defaultBody cases) := by
  induction cases with
  | nil => exact hDefault
  | cons hd tl ih =>
      obtain ⟨val, body⟩ := hd
      rw [EvmYul.Yul.selectSwitchCase]
      simp only [breakContinueFreeCases?, Bool.and_eq_true] at hCases
      by_cases hv : val = c
      · rw [if_pos hv]; exact hCases.1
      · rw [if_neg hv]; exact ih hCases.2

/-- Every function a `BridgeContract` resolves by name has a bridge body. -/
theorem bridgeContract_lookup {c : YulContract} (hc : BridgeContract c)
    {fn : YulFunctionName} {f : FunctionDefinition}
    (hlk : c.functions.lookup fn = some f) : bridgeFunction? f = true := by
  have hall : c.functions.all (fun _ f => bridgeFunction? f) = true := by
    have h := hc
    simp only [BridgeContract, bridgeContract?, Bool.and_eq_true] at h
    exact h.2
  have hmem : (Sigma.mk fn f) ∈ c.functions.entries :=
    Finmap.lookup_eq_some_iff.mp hlk
  -- `Finmap.all` is a `&&`-foldl over the entries multiset.
  haveI : RightCommutative
      (fun (b : Bool) (p : (_ : YulFunctionName) × FunctionDefinition) =>
        b && bridgeFunction? p.2) :=
    ⟨fun b p q => Bool.and_right_comm b _ _⟩
  have haux : ∀ (m : Multiset ((_ : YulFunctionName) × FunctionDefinition))
      (b : Bool),
      m.foldl (fun b p => b && bridgeFunction? p.2) b = true →
        b = true ∧ ∀ x ∈ m, bridgeFunction? x.2 = true := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
        intro b hb
        refine ⟨by simpa using hb, ?_⟩
        intro x hx
        exact absurd hx (Multiset.notMem_zero x)
    | cons a m ih =>
        intro b hb
        rw [Multiset.foldl_cons] at hb
        obtain ⟨hba, hall'⟩ := ih (b && bridgeFunction? a.2) hb
        simp only [Bool.and_eq_true] at hba
        refine ⟨hba.1, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx'
        · exact hba.2
        · exact hall' x hx'
  have : (true : Bool) = true ∧
      ∀ x ∈ c.functions.entries, bridgeFunction? x.2 = true := by
    refine haux c.functions.entries true ?_
    simpa only [Finmap.all, Finmap.foldl] using hall
  exact this.2 ⟨fn, f⟩ hmem

/-! ### The Part B0 bundle -/

/-- Native-side preservation at native fuel `n`: from a `CodeBridge` state, every
`.ok` result of a Bridge* run keeps the owner account present. Statement-layer
conclusions are `StateBridge` (checkpoint-carrying) plus the break/continue-free
outcome guarantee the loop recursion consumes. -/
structure NativePreservesAt (n : Nat) : Prop where
  evalTail : ∀ (args : List Expr) (code : Option YulContract)
      (nr : Except EvmYul.Yul.Exception (State × Word)),
      BridgeExprs args → BridgeCode code →
      (∀ p, nr = .ok p → CodeBridge p.1) →
      ∀ s' out, EvmYul.Yul.evalTail n args code nr = .ok (s', out) → CodeBridge s'
  evalArgs : ∀ (args : List Expr) (code : Option YulContract) (s : State),
      BridgeExprs args → BridgeCode code → CodeBridge s →
      ∀ s' out, EvmYul.Yul.evalArgs n args code s = .ok (s', out) → CodeBridge s'
  evalValues : ∀ (expr : Expr) (code : Option YulContract) (s : State),
      BridgeExpr expr → BridgeCode code → CodeBridge s →
      ∀ s' out, EvmYul.Yul.evalValues n expr code s = .ok (s', out) → CodeBridge s'
  eval : ∀ (expr : Expr) (code : Option YulContract) (s : State),
      BridgeExpr expr → BridgeCode code → CodeBridge s →
      ∀ s' w, EvmYul.Yul.eval n expr code s = .ok (s', w) → CodeBridge s'
  call : ∀ (args : List Word) (fn? : Option YulFunctionName)
      (code : Option YulContract) (s : State),
      BridgeCode code → CodeBridge s →
      ∀ s' out, EvmYul.Yul.call n args fn? code s = .ok (s', out) → CodeBridge s'
  execSeq : ∀ (stmts : List Stmt) (code : Option YulContract) (s : State),
      BridgeStmts stmts → BridgeCode code → CodeBridge s →
      ∀ r, EvmYul.Yul.execSeq n stmts code s = .ok r →
        StateBridge r ∧ (BreakContinueFreeStmts stmts → ¬ IsJumpBC r)
  exec : ∀ (stmt : Stmt) (code : Option YulContract) (s : State),
      BridgeStmt stmt → BridgeCode code → CodeBridge s →
      ∀ r, EvmYul.Yul.exec n stmt code s = .ok r →
        StateBridge r ∧ (breakContinueFree? stmt = true → ¬ IsJumpBC r)
  loop : ∀ (cond : Expr) (post body : List Stmt) (code : Option YulContract)
      (s : State),
      BridgeExpr cond → BridgeStmts post → BreakContinueFreeStmts post →
      BridgeStmts body → BridgeCode code → CodeBridge s →
      ∀ r, EvmYul.Yul.loop n cond post body code s = .ok r →
        StateBridge r ∧ ¬ IsJumpBC r

/-! ### The Part B0 preservation mutual -/

private theorem bridgeExprs?_all (l : List Expr) :
    bridgeExprs? l = l.all bridgeExpr? := by
  induction l with
  | nil => rfl
  | cons e es ih => simp only [bridgeExprs?, List.all_cons, ih]

theorem bridgeExprs?_reverse {args : List Expr}
    (h : bridgeExprs? args = true) : bridgeExprs? args.reverse = true := by
  rw [bridgeExprs?_all] at h ⊢
  simpa only [List.all_reverse] using h

/-- The shared post/For tail of one native `loop` iteration, factored so both the
`Continue`-checkpoint and fall-through (`Ok`) body outcomes reuse it. -/
private theorem loopPostTail (j : Nat) (ihj : NativePreservesAt j)
    (cond : Expr) (post body : List Stmt) (code : Option YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hCond : BridgeExpr cond) (hPost : BridgeStmts post)
    (hPostBC : BreakContinueFreeStmts post) (hBody : BridgeStmts body)
    (hCode : BridgeCode code) (entry : State) (hEntry : CodeBridge entry)
    (r : State)
    (hEq : (match EvmYul.Yul.exec j (.Block post) code entry with
            | .error e => (.error e : Except EvmYul.Yul.Exception State)
            | .ok s₃ =>
                match s₃ with
                | .OutOfFuel => .ok (s₃.overwrite? (EvmYul.Yul.State.Ok shared store))
                | .Checkpoint (.Leave _ _) =>
                    .ok (s₃.overwrite? (EvmYul.Yul.State.Ok shared store))
                | _ =>
                    match EvmYul.Yul.exec j (.For cond post body) code
                        (s₃.overwrite? (EvmYul.Yul.State.Ok shared store)) with
                    | .error e => .error e
                    | .ok s₅ =>
                        .ok (s₅.overwrite? (EvmYul.Yul.State.Ok shared store))) = .ok r) :
    StateBridge r ∧ ¬ IsJumpBC r := by
  cases hpx : EvmYul.Yul.exec j (.Block post) code entry with
  | error e =>
      rw [hpx] at hEq
      exact nomatch hEq
  | ok s₃ =>
      rw [hpx] at hEq
      have h₃ := ihj.exec (.Block post) code entry hPost hCode hEntry s₃ hpx
      have hnbc : ¬ IsJumpBC s₃ := h₃.2 hPostBC
      cases s₃ with
      | OutOfFuel => exact ((h₃.1 : False)).elim
      | Checkpoint jj =>
          cases jj with
          | Break sh₃ st₃ => exact absurd trivial hnbc
          | Continue sh₃ st₃ => exact absurd trivial hnbc
          | Leave sh₃ st₃ =>
              have hEq' : (Except.ok
                  (EvmYul.Yul.State.Checkpoint (.Leave sh₃ st₃)) :
                    Except EvmYul.Yul.Exception State) = .ok r := hEq
              simp only [Except.ok.injEq] at hEq'
              subst hEq'
              exact ⟨h₃.1, fun hbc => hbc⟩
      | Ok sh₃ st₃ =>
          have hEq' : (match EvmYul.Yul.exec j (.For cond post body) code
                  (EvmYul.Yul.State.Ok sh₃ st₃) with
              | .error e => (.error e : Except EvmYul.Yul.Exception State)
              | .ok s₅ =>
                  .ok (s₅.overwrite? (EvmYul.Yul.State.Ok shared store))) = .ok r := hEq
          have hFor : BridgeStmt (.For cond post body) := by
            show bridgeStmt? (.For cond post body) = true
            simp only [bridgeStmt?, Bool.and_eq_true]
            exact ⟨⟨⟨hCond, hPost⟩, hPostBC⟩, hBody⟩
          cases hfx : EvmYul.Yul.exec j (.For cond post body) code
              (EvmYul.Yul.State.Ok sh₃ st₃) with
          | error e =>
              rw [hfx] at hEq'
              exact nomatch hEq'
          | ok s₅ =>
              rw [hfx] at hEq'
              have h₅ := ihj.exec (.For cond post body) code (EvmYul.Yul.State.Ok sh₃ st₃)
                hFor hCode h₃.1 s₅ hfx
              have hEq'' : (Except.ok s₅ : Except EvmYul.Yul.Exception State) =
                  .ok r := hEq'
              simp only [Except.ok.injEq] at hEq''
              subst hEq''
              exact ⟨h₅.1, h₅.2 rfl⟩

/-- Part B0, parameterized by the primitive boundary fact (discharged by
`primCall_preserves_codeBridge` once PrimAgrees lands). -/
theorem nativePreservesAt_of_prim
    (hPrim : ∀ {op : EvmYul.Operation .Yul}, BridgeOp op →
      ∀ (fuel : Nat) (s : State) (args : List Word) (s' : State) (out : List Word),
        EvmYul.Yul.primCall fuel s op args = .ok (s', out) →
        CodeBridge s → CodeBridge s') :
    ∀ n, NativePreservesAt n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro args code nr _ _ _ s' out hEq
          cases nr with
          | ok p =>
              rw [Native.evalTail_zero_ok] at hEq
              exact nomatch hEq
          | error e =>
              rw [Native.evalTail_error] at hEq
              exact nomatch hEq
        · intro args code s _ _ _ s' out hEq
          rw [Native.evalArgs_zero] at hEq
          exact nomatch hEq
        · intro expr code s _ _ _ s' out hEq
          rw [Native.evalValues_zero] at hEq
          exact nomatch hEq
        · intro expr code s _ _ _ s' w hEq
          rw [Native.eval_eq, Native.evalValues_zero] at hEq
          exact nomatch hEq
        · intro args fn? code s _ _ s' out hEq
          rw [Native.call_zero] at hEq
          exact nomatch hEq
        · intro stmts code s _ _ _ r hEq
          rw [Native.execSeq_zero] at hEq
          exact nomatch hEq
        · intro stmt code s _ _ _ r hEq
          rw [Native.exec_zero] at hEq
          exact nomatch hEq
        · intro cond post body code s _ _ _ _ _ _ r hEq
          rw [Native.loop_zero] at hEq
          exact nomatch hEq
    | k + 1 =>
        have ihk : NativePreservesAt k := ih k (Nat.lt_succ_self k)
        -- `evalTail (k+1)` — cons' over `evalArgs k` after a good prior result.
        have hEvalTail : ∀ (args : List Expr) (code : Option YulContract)
            (nr : Except EvmYul.Yul.Exception (State × Word)),
            BridgeExprs args → BridgeCode code →
            (∀ p, nr = .ok p → CodeBridge p.1) →
            ∀ s' out, EvmYul.Yul.evalTail (k + 1) args code nr = .ok (s', out) →
              CodeBridge s' := by
          intro args code nr hArgs hCode hnr s' out hEq
          cases nr with
          | error e =>
              rw [Native.evalTail_error] at hEq
              exact nomatch hEq
          | ok p =>
              rw [Native.evalTail_ok] at hEq
              cases hA : EvmYul.Yul.evalArgs k args code p.1 with
              | error e =>
                  rw [hA] at hEq
                  exact nomatch hEq
              | ok q =>
                  obtain ⟨qs, qv⟩ := q
                  rw [hA] at hEq
                  have hEq' : (Except.ok (qs, p.2 :: qv) :
                      Except EvmYul.Yul.Exception (State × List Word)) =
                        .ok (s', out) := hEq
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hEq'
                  obtain ⟨rfl, rfl⟩ := hEq'
                  exact ihk.evalArgs args code p.1 hArgs hCode (hnr p rfl) qs qv hA
        -- `evalArgs (k+1)` — head expression, then the tail.
        have hEvalArgs : ∀ (args : List Expr) (code : Option YulContract) (s : State),
            BridgeExprs args → BridgeCode code → CodeBridge s →
            ∀ s' out, EvmYul.Yul.evalArgs (k + 1) args code s = .ok (s', out) →
              CodeBridge s' := by
          intro args code s hArgs hCode hCB s' out hEq
          cases args with
          | nil =>
              rw [Native.evalArgs_nil] at hEq
              have hEq' : (Except.ok (s, ([] : List Word)) :
                  Except EvmYul.Yul.Exception (State × List Word)) =
                    .ok (s', out) := hEq
              simp only [Except.ok.injEq, Prod.mk.injEq] at hEq'
              obtain ⟨rfl, rfl⟩ := hEq'
              exact hCB
          | cons arg rest =>
              rw [Native.evalArgs_cons] at hEq
              have hS : bridgeExpr? arg = true ∧ bridgeExprs? rest = true := by
                have h : bridgeExprs? (arg :: rest) = true := hArgs
                simpa only [bridgeExprs?, Bool.and_eq_true] using h
              exact ihk.evalTail rest code (EvmYul.Yul.eval k arg code s) hS.2 hCode
                (fun p hp => ihk.eval arg code s hS.1 hCode hCB p.1 p.2 hp)
                s' out hEq
        -- `evalValues (k+1)` — the four expression constructors.
        have hEvalValues : ∀ (expr : Expr) (code : Option YulContract) (s : State),
            BridgeExpr expr → BridgeCode code → CodeBridge s →
            ∀ s' out, EvmYul.Yul.evalValues (k + 1) expr code s = .ok (s', out) →
              CodeBridge s' := by
          intro expr code s hExpr hCode hCB s' out hEq
          cases expr with
          | Var id =>
              rw [Native.evalValues_var] at hEq
              cases hlk : s.lookup? id with
              | none =>
                  rw [hlk] at hEq
                  exact nomatch hEq
              | some v =>
                  rw [hlk] at hEq
                  have hEq' : (Except.ok (s, [v]) :
                      Except EvmYul.Yul.Exception (State × List Word)) =
                        .ok (s', out) := hEq
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hEq'
                  obtain ⟨rfl, rfl⟩ := hEq'
                  exact hCB
          | Lit v =>
              rw [Native.evalValues_lit] at hEq
              have hEq' : (Except.ok (s, [v]) :
                  Except EvmYul.Yul.Exception (State × List Word)) =
                    .ok (s', out) := hEq
              simp only [Except.ok.injEq, Prod.mk.injEq] at hEq'
              obtain ⟨rfl, rfl⟩ := hEq'
              exact hCB
          | Call sop args =>
              cases sop with
              | inl op =>
                  rw [Native.evalValues_prim] at hEq
                  have hS : bridgeOp? op = true ∧ bridgeExprs? args = true := by
                    have h : bridgeExpr? (.Call (.inl op) args) = true := hExpr
                    simpa only [bridgeExpr?, Bool.and_eq_true] using h
                  cases hargs : EvmYul.Yul.evalArgs k args.reverse code s with
                  | error e =>
                      rw [hargs] at hEq
                      exact nomatch hEq
                  | ok p =>
                      obtain ⟨ps, pv⟩ := p
                      rw [hargs] at hEq
                      have hEq' : EvmYul.Yul.primCall k ps op pv.reverse =
                          .ok (s', out) := hEq
                      have hps := ihk.evalArgs args.reverse code s
                        (bridgeExprs?_reverse hS.2) hCode hCB ps pv hargs
                      exact hPrim ((bridgeOp?_iff op).mp hS.1) k ps pv.reverse
                        s' out hEq' hps
              | inr fn =>
                  rw [Native.evalValues_call] at hEq
                  have hS : bridgeExprs? args = true := hExpr
                  cases hargs : EvmYul.Yul.evalArgs k args.reverse code s with
                  | error e =>
                      rw [hargs] at hEq
                      exact nomatch hEq
                  | ok p =>
                      obtain ⟨ps, pv⟩ := p
                      rw [hargs] at hEq
                      have hEq' : EvmYul.Yul.call k pv.reverse (some fn) code ps =
                          .ok (s', out) := hEq
                      have hps := ihk.evalArgs args.reverse code s
                        (bridgeExprs?_reverse hS) hCode hCB ps pv hargs
                      exact ihk.call pv.reverse (some fn) code ps hCode hps
                        s' out hEq'
        -- `eval (k+1)` — same-level `head'` wrapper over `evalValues (k+1)`.
        have hEval : ∀ (expr : Expr) (code : Option YulContract) (s : State),
            BridgeExpr expr → BridgeCode code → CodeBridge s →
            ∀ s' w, EvmYul.Yul.eval (k + 1) expr code s = .ok (s', w) →
              CodeBridge s' := by
          intro expr code s hExpr hCode hCB s' w hEq
          rw [Native.eval_eq] at hEq
          cases hev : EvmYul.Yul.evalValues (k + 1) expr code s with
          | error e =>
              rw [hev] at hEq
              exact nomatch hEq
          | ok p =>
              obtain ⟨ps, pv⟩ := p
              rw [hev] at hEq
              have hEq' : (Except.ok (ps, pv.head!) :
                  Except EvmYul.Yul.Exception (State × Word)) = .ok (s', w) := hEq
              simp only [Except.ok.injEq, Prod.mk.injEq] at hEq'
              obtain ⟨rfl, rfl⟩ := hEq'
              exact hEvalValues expr code s hExpr hCode hCB ps pv hev
        -- `call (k+1)` — presence gives the account; `BridgeCode` the program.
        have hCall : ∀ (args : List Word) (fn? : Option YulFunctionName)
            (code : Option YulContract) (s : State),
            BridgeCode code → CodeBridge s →
            ∀ s' out, EvmYul.Yul.call (k + 1) args fn? code s = .ok (s', out) →
              CodeBridge s' := by
          intro args fn? code s hCode hCB s' out hEq
          obtain ⟨c, rfl, hc⟩ := hCode
          rw [Native.call_succ] at hEq
          cases hf : s.sharedState.accountMap.find? s.executionEnv.codeOwner with
          | none => exact absurd hf hCB
          | some yc =>
              rw [hf] at hEq
              cases fn? with
              | none =>
                  have hEq' :
                      (match EvmYul.Yul.exec k (.Block [c.dispatcher]) (some c)
                          (EvmYul.Yul.State.mkOk (s.initcall [] [] args)) with
                       | .error e => (.error e :
                           Except EvmYul.Yul.Exception (State × List Word))
                       | .ok s₂ => .ok ((s₂.reviveJump.overwrite? s).setStore s,
                           List.map s₂.lookup! [])) = .ok (s', out) := hEq
                  cases hex : EvmYul.Yul.exec k (.Block [c.dispatcher]) (some c)
                      (EvmYul.Yul.State.mkOk (s.initcall [] [] args)) with
                  | error e =>
                      rw [hex] at hEq'
                      exact nomatch hEq'
                  | ok s₂ =>
                      rw [hex] at hEq'
                      have hEq'' : (Except.ok
                          ((s₂.reviveJump.overwrite? s).setStore s,
                            List.map s₂.lookup! ([] : List EvmYul.Identifier)) :
                          Except EvmYul.Yul.Exception (State × List Word)) =
                            .ok (s', out) := hEq'
                      simp only [Except.ok.injEq, Prod.mk.injEq] at hEq''
                      obtain ⟨rfl, rfl⟩ := hEq''
                      have hc' := hc
                      simp only [BridgeContract, bridgeContract?,
                        Bool.and_eq_true] at hc'
                      have hdisp : BridgeStmt (.Block [c.dispatcher]) := by
                        show bridgeStmts? [c.dispatcher] = true
                        simp only [bridgeStmts?, Bool.and_eq_true]
                        exact ⟨hc'.1, trivial⟩
                      have h₂ := ihk.exec (.Block [c.dispatcher]) (some c) _ hdisp
                        ⟨c, rfl, hc⟩ (codeBridge_initcall hCB [] [] args) s₂ hex
                      exact codeBridge_callResult h₂.1 hCB
              | some fnName =>
                  have hEq₀ :
                      (match c.functions.lookup fnName with
                       | .none => (.error (.MissingContractFunction fnName) :
                           Except EvmYul.Yul.Exception (State × List Word))
                       | .some f =>
                           match EvmYul.Yul.exec k (.Block f.body) (some c)
                               (EvmYul.Yul.State.mkOk
                                 (s.initcall f.params f.rets args)) with
                           | .error e => .error e
                           | .ok s₂ => .ok ((s₂.reviveJump.overwrite? s).setStore s,
                               List.map s₂.lookup! f.rets)) = .ok (s', out) := hEq
                  cases hlk : c.functions.lookup fnName with
                  | none =>
                      rw [hlk] at hEq₀
                      exact nomatch hEq₀
                  | some f =>
                      rw [hlk] at hEq₀
                      cases f with
                      | Def params rets body =>
                          have hEq₁ :
                              (match EvmYul.Yul.exec k (.Block body) (some c)
                                  (EvmYul.Yul.State.mkOk
                                    (s.initcall params rets args)) with
                               | .error e => (.error e :
                                   Except EvmYul.Yul.Exception (State × List Word))
                               | .ok s₂ =>
                                   .ok ((s₂.reviveJump.overwrite? s).setStore s,
                                     List.map s₂.lookup! rets)) = .ok (s', out) := hEq₀
                          cases hex : EvmYul.Yul.exec k (.Block body) (some c)
                              (EvmYul.Yul.State.mkOk (s.initcall params rets args)) with
                          | error e =>
                              rw [hex] at hEq₁
                              exact nomatch hEq₁
                          | ok s₂ =>
                              rw [hex] at hEq₁
                              have hEq₂ : (Except.ok
                                  ((s₂.reviveJump.overwrite? s).setStore s,
                                    List.map s₂.lookup! rets) :
                                  Except EvmYul.Yul.Exception (State × List Word)) =
                                    .ok (s', out) := hEq₁
                              simp only [Except.ok.injEq, Prod.mk.injEq] at hEq₂
                              obtain ⟨rfl, rfl⟩ := hEq₂
                              have h₂ := ihk.exec (.Block body) (some c) _
                                (bridgeContract_lookup hc hlk) ⟨c, rfl, hc⟩
                                (codeBridge_initcall hCB params rets args) s₂ hex
                              exact codeBridge_callResult h₂.1 hCB
        -- `execSeq (k+1)` — statement then guarded continuation.
        have hExecSeq : ∀ (stmts : List Stmt) (code : Option YulContract) (s : State),
            BridgeStmts stmts → BridgeCode code → CodeBridge s →
            ∀ r, EvmYul.Yul.execSeq (k + 1) stmts code s = .ok r →
              StateBridge r ∧ (BreakContinueFreeStmts stmts → ¬ IsJumpBC r) := by
          intro stmts code s hStmts hCode hCB r hEq
          cases stmts with
          | nil =>
              rw [Native.execSeq_nil] at hEq
              have hEq' : (Except.ok s : Except EvmYul.Yul.Exception State) =
                  .ok r := hEq
              simp only [Except.ok.injEq] at hEq'
              subst hEq'
              exact ⟨stateBridge_of_codeBridge hCB,
                fun _ => not_isJumpBC_of_codeBridge hCB⟩
          | cons stmt rest =>
              have hS : bridgeStmt? stmt = true ∧ bridgeStmts? rest = true := by
                have h : bridgeStmts? (stmt :: rest) = true := hStmts
                simpa only [bridgeStmts?, Bool.and_eq_true] using h
              rw [Native.execSeq_cons] at hEq
              cases hex : EvmYul.Yul.exec k stmt code s with
              | error e =>
                  rw [hex] at hEq
                  exact nomatch hEq
              | ok s₁ =>
                  rw [hex] at hEq
                  have h₁ := ihk.exec stmt code s hS.1 hCode hCB s₁ hex
                  cases s₁ with
                  | Ok shared₁ store₁ =>
                      have hEq' : EvmYul.Yul.execSeq k rest code
                          (.Ok shared₁ store₁) = .ok r := hEq
                      have h₂ := ihk.execSeq rest code (EvmYul.Yul.State.Ok shared₁ store₁)
                        hS.2 hCode h₁.1 r hEq'
                      refine ⟨h₂.1, fun hbc => ?_⟩
                      have hb : breakContinueFree? stmt = true ∧
                          breakContinueFreeStmts? rest = true := by
                        have h : breakContinueFreeStmts? (stmt :: rest) = true := hbc
                        simpa only [breakContinueFreeStmts?, Bool.and_eq_true] using h
                      exact h₂.2 hb.2
                  | OutOfFuel => exact ((h₁.1 : False)).elim
                  | Checkpoint j =>
                      have hEq' : (Except.ok (EvmYul.Yul.State.Checkpoint j) :
                          Except EvmYul.Yul.Exception State) = .ok r := hEq
                      simp only [Except.ok.injEq] at hEq'
                      subst hEq'
                      refine ⟨h₁.1, fun hbc => ?_⟩
                      have hb : breakContinueFree? stmt = true ∧
                          breakContinueFreeStmts? rest = true := by
                        have h : breakContinueFreeStmts? (stmt :: rest) = true := hbc
                        simpa only [breakContinueFreeStmts?, Bool.and_eq_true] using h
                      exact h₁.2 hb.1
        -- `exec (k+1)` — the eleven statement constructors.
        have hExec : ∀ (stmt : Stmt) (code : Option YulContract) (s : State),
            BridgeStmt stmt → BridgeCode code → CodeBridge s →
            ∀ r, EvmYul.Yul.exec (k + 1) stmt code s = .ok r →
              StateBridge r ∧ (breakContinueFree? stmt = true → ¬ IsJumpBC r) := by
          intro stmt code s hStmt hCode hCB r hEq
          cases stmt with
          | Block body =>
              rw [Native.exec_block] at hEq
              cases hseq : EvmYul.Yul.execSeq k body code s with
              | error e =>
                  rw [hseq] at hEq
                  exact nomatch hEq
              | ok s₁ =>
                  rw [hseq] at hEq
                  have hEq' : (Except.ok (s₁.restrictStoreTo s.store) :
                      Except EvmYul.Yul.Exception State) = .ok r := hEq
                  simp only [Except.ok.injEq] at hEq'
                  subst hEq'
                  have h₁ := ihk.execSeq body code s hStmt hCode hCB s₁ hseq
                  exact ⟨stateBridge_restrictStoreTo _ h₁.1,
                    fun hbc => not_isJumpBC_restrictStoreTo _ (h₁.2 hbc)⟩
          | Let names expr? =>
              cases expr? with
              | none =>
                  rw [Native.exec_let_none] at hEq
                  cases hck : EvmYul.Yul.checkDeclaration s names with
                  | error e =>
                      rw [hck] at hEq
                      exact nomatch hEq
                  | ok u =>
                      cases u
                      rw [hck] at hEq
                      have hEq' : (Except.ok (s.zeroFill names) :
                          Except EvmYul.Yul.Exception State) = .ok r := hEq
                      simp only [Except.ok.injEq] at hEq'
                      subst hEq'
                      obtain ⟨shared, store, rfl, hp⟩ := codeBridge_ok hCB
                      obtain ⟨store', hzf⟩ := zeroFill_ok names shared store
                      rw [hzf]
                      exact ⟨hp, fun _ hbc => hbc⟩
              | some expr =>
                  rw [Native.exec_let_some] at hEq
                  cases hck : EvmYul.Yul.checkDeclaration s names with
                  | error e =>
                      rw [hck] at hEq
                      exact nomatch hEq
                  | ok u =>
                      cases u
                      rw [hck] at hEq
                      have hEq' : EvmYul.Yul.multifill' names
                          (EvmYul.Yul.evalValues k expr code s) = .ok r := hEq
                      cases hev : EvmYul.Yul.evalValues k expr code s with
                      | error e =>
                          rw [hev] at hEq'
                          exact nomatch hEq'
                      | ok p =>
                          obtain ⟨ps, pv⟩ := p
                          rw [hev] at hEq'
                          have hEq'' : (Except.ok
                              (EvmYul.Yul.State.multifill names pv ps) :
                              Except EvmYul.Yul.Exception State) = .ok r := hEq'
                          simp only [Except.ok.injEq] at hEq''
                          subst hEq''
                          have hps := ihk.evalValues expr code s hStmt hCode hCB
                            ps pv hev
                          obtain ⟨shared₁, store₁, rfl, hp₁⟩ := codeBridge_ok hps
                          obtain ⟨store', hmf⟩ := multifill_ok names pv shared₁ store₁
                          rw [hmf]
                          exact ⟨hp₁, fun _ hbc => hbc⟩
          | Assign names expr =>
              rw [Native.exec_assign] at hEq
              cases hck : EvmYul.Yul.checkAssignment s names with
              | error e =>
                  rw [hck] at hEq
                  exact nomatch hEq
              | ok u =>
                  cases u
                  rw [hck] at hEq
                  have hEq' : EvmYul.Yul.multifill' names
                      (EvmYul.Yul.evalValues k expr code s) = .ok r := hEq
                  cases hev : EvmYul.Yul.evalValues k expr code s with
                  | error e =>
                      rw [hev] at hEq'
                      exact nomatch hEq'
                  | ok p =>
                      obtain ⟨ps, pv⟩ := p
                      rw [hev] at hEq'
                      have hEq'' : (Except.ok
                          (EvmYul.Yul.State.multifill names pv ps) :
                          Except EvmYul.Yul.Exception State) = .ok r := hEq'
                      simp only [Except.ok.injEq] at hEq''
                      subst hEq''
                      have hps := ihk.evalValues expr code s hStmt hCode hCB ps pv hev
                      obtain ⟨shared₁, store₁, rfl, hp₁⟩ := codeBridge_ok hps
                      obtain ⟨store', hmf⟩ := multifill_ok names pv shared₁ store₁
                      rw [hmf]
                      exact ⟨hp₁, fun _ hbc => hbc⟩
          | If cond body =>
              rw [Native.exec_if] at hEq
              have hS : bridgeExpr? cond = true ∧ bridgeStmts? body = true := by
                have h : bridgeStmt? (.If cond body) = true := hStmt
                simpa only [bridgeStmt?, Bool.and_eq_true] using h
              cases hev : EvmYul.Yul.eval k cond code s with
              | error e =>
                  rw [hev] at hEq
                  exact nomatch hEq
              | ok p =>
                  obtain ⟨ps, pc⟩ := p
                  rw [hev] at hEq
                  have hps := ihk.eval cond code s hS.1 hCode hCB ps pc hev
                  have hEq' : (if pc ≠ (⟨0⟩ : Word) then
                      EvmYul.Yul.exec k (.Block body) code ps
                    else (Except.ok ps : Except EvmYul.Yul.Exception State)) =
                      .ok r := hEq
                  by_cases hc : pc ≠ (⟨0⟩ : Word)
                  · rw [if_pos hc] at hEq'
                    have h₁ := ihk.exec (.Block body) code ps hS.2 hCode hps r hEq'
                    exact ⟨h₁.1, fun hbc => h₁.2 hbc⟩
                  · rw [if_neg hc] at hEq'
                    simp only [Except.ok.injEq] at hEq'
                    subst hEq'
                    exact ⟨stateBridge_of_codeBridge hps,
                      fun _ => not_isJumpBC_of_codeBridge hps⟩
          | ExprStmtCall e =>
              cases e with
              | Var id =>
                  rw [Native.exec_expr_var] at hEq
                  exact nomatch hEq
              | Lit v =>
                  rw [Native.exec_expr_lit] at hEq
                  exact nomatch hEq
              | Call sop args =>
                  cases sop with
                  | inl op =>
                      rw [Native.exec_expr_prim] at hEq
                      have hS : bridgeOp? op = true ∧ bridgeExprs? args = true := by
                        have h : bridgeStmt?
                            (.ExprStmtCall (.Call (.inl op) args)) = true := hStmt
                        simpa only [bridgeStmt?, bridgeExpr?, Bool.and_eq_true] using h
                      cases hargs : EvmYul.Yul.evalArgs k args.reverse code s with
                      | error e =>
                          rw [hargs, show EvmYul.Yul.reverse' (Except.error e :
                            Except EvmYul.Yul.Exception (State × List Word)) =
                              .error e from rfl, Native.execPrimCall_error] at hEq
                          exact nomatch hEq
                      | ok p =>
                          obtain ⟨ps, pv⟩ := p
                          rw [hargs, show EvmYul.Yul.reverse' (Except.ok (ps, pv) :
                            Except EvmYul.Yul.Exception (State × List Word)) =
                              .ok (ps, pv.reverse) from rfl,
                            Native.execPrimCall_ok] at hEq
                          have hEq' : EvmYul.Yul.multifill' []
                              (EvmYul.Yul.primCall k ps op pv.reverse) = .ok r := hEq
                          have hps : CodeBridge ps := ihk.evalArgs args.reverse code s
                            (bridgeExprs?_reverse hS.2) hCode hCB ps pv hargs
                          cases hpc : EvmYul.Yul.primCall k ps op pv.reverse with
                          | error e =>
                              rw [hpc] at hEq'
                              exact nomatch hEq'
                          | ok q =>
                              obtain ⟨qs, qv⟩ := q
                              rw [hpc] at hEq'
                              have hEq'' : (Except.ok
                                  (EvmYul.Yul.State.multifill [] qv qs) :
                                  Except EvmYul.Yul.Exception State) = .ok r := hEq'
                              simp only [Except.ok.injEq] at hEq''
                              subst hEq''
                              have hqs : CodeBridge qs :=
                                hPrim ((bridgeOp?_iff op).mp hS.1) k ps pv.reverse
                                  qs qv hpc hps
                              obtain ⟨shared₂, store₂, rfl, hp₂⟩ := codeBridge_ok hqs
                              obtain ⟨store', hmf⟩ := multifill_ok [] qv shared₂ store₂
                              rw [hmf]
                              exact ⟨hp₂, fun _ hbc => hbc⟩
                  | inr fn =>
                      rw [Native.exec_expr_internal] at hEq
                      have hS : bridgeExprs? args = true := hStmt
                      cases hargs : EvmYul.Yul.evalArgs k args.reverse code s with
                      | error e =>
                          rw [hargs, show EvmYul.Yul.reverse' (Except.error e :
                            Except EvmYul.Yul.Exception (State × List Word)) =
                              .error e from rfl, Native.execCall_error] at hEq
                          exact nomatch hEq
                      | ok p =>
                          obtain ⟨ps, pv⟩ := p
                          rw [hargs, show EvmYul.Yul.reverse' (Except.ok (ps, pv) :
                            Except EvmYul.Yul.Exception (State × List Word)) =
                              .ok (ps, pv.reverse) from rfl] at hEq
                          have hps : CodeBridge ps := ihk.evalArgs args.reverse code s
                            (bridgeExprs?_reverse hS) hCode hCB ps pv hargs
                          cases k with
                          | zero =>
                              rw [Native.execCall_ok_zero] at hEq
                              exact nomatch hEq
                          | succ j =>
                              rw [Native.execCall_ok_succ] at hEq
                              have hEq' : EvmYul.Yul.multifill' []
                                  (EvmYul.Yul.call j pv.reverse (some fn) code ps) =
                                    .ok r := hEq
                              cases hcl : EvmYul.Yul.call j pv.reverse (some fn)
                                  code ps with
                              | error e =>
                                  rw [hcl] at hEq'
                                  exact nomatch hEq'
                              | ok q =>
                                  obtain ⟨qs, qv⟩ := q
                                  rw [hcl] at hEq'
                                  have hEq'' : (Except.ok
                                      (EvmYul.Yul.State.multifill [] qv qs) :
                                      Except EvmYul.Yul.Exception State) = .ok r := hEq'
                                  simp only [Except.ok.injEq] at hEq''
                                  subst hEq''
                                  have hqs : CodeBridge qs :=
                                    (ih j (by omega)).call pv.reverse (some fn)
                                      code ps hCode hps qs qv hcl
                                  obtain ⟨shared₂, store₂, rfl, hp₂⟩ :=
                                    codeBridge_ok hqs
                                  obtain ⟨store', hmf⟩ :=
                                    multifill_ok [] qv shared₂ store₂
                                  rw [hmf]
                                  exact ⟨hp₂, fun _ hbc => hbc⟩
          | Switch cond cases' default' =>
              rw [Native.exec_switch] at hEq
              have hS : (bridgeExpr? cond = true ∧ bridgeCases? cases' = true) ∧
                  bridgeStmts? default' = true := by
                have h : bridgeStmt? (.Switch cond cases' default') = true := hStmt
                simpa only [bridgeStmt?, Bool.and_eq_true] using h
              cases hev : EvmYul.Yul.eval k cond code s with
              | error e =>
                  rw [hev] at hEq
                  exact nomatch hEq
              | ok p =>
                  obtain ⟨ps, pc⟩ := p
                  rw [hev] at hEq
                  have hEq' : EvmYul.Yul.exec k
                      (.Block (EvmYul.Yul.selectSwitchCase pc default' cases'))
                      code ps = .ok r := hEq
                  have hps := ihk.eval cond code s hS.1.1 hCode hCB ps pc hev
                  have hsel : BridgeStmts
                      (EvmYul.Yul.selectSwitchCase pc default' cases') :=
                    bridgeStmts_selectSwitchCase hS.1.2 hS.2 pc
                  have h₁ := ihk.exec (.Block _) code ps hsel hCode hps r hEq'
                  refine ⟨h₁.1, fun hbc => ?_⟩
                  have hb : breakContinueFreeCases? cases' = true ∧
                      breakContinueFreeStmts? default' = true := by
                    have h : breakContinueFree? (.Switch cond cases' default') =
                        true := hbc
                    simpa only [breakContinueFree?, Bool.and_eq_true] using h
                  exact h₁.2 (breakContinueFreeStmts_selectSwitchCase hb.1 hb.2 pc)
          | For cond post body =>
              rw [Native.exec_for] at hEq
              have h4 : ((bridgeExpr? cond = true ∧ bridgeStmts? post = true) ∧
                  breakContinueFreeStmts? post = true) ∧
                    bridgeStmts? body = true := by
                have h : bridgeStmt? (.For cond post body) = true := hStmt
                simpa only [bridgeStmt?, Bool.and_eq_true] using h
              have h₁ := ihk.loop cond post body code s h4.1.1.1 h4.1.1.2 h4.1.2
                h4.2 hCode hCB r hEq
              exact ⟨h₁.1, fun _ => h₁.2⟩
          | Continue =>
              rw [Native.exec_continue] at hEq
              have hEq' : (Except.ok s.setContinue :
                  Except EvmYul.Yul.Exception State) = .ok r := hEq
              simp only [Except.ok.injEq] at hEq'
              subst hEq'
              obtain ⟨shared, store, rfl, hp⟩ := codeBridge_ok hCB
              exact ⟨hp, fun hbc => Bool.noConfusion hbc⟩
          | Break =>
              rw [Native.exec_break] at hEq
              have hEq' : (Except.ok s.setBreak :
                  Except EvmYul.Yul.Exception State) = .ok r := hEq
              simp only [Except.ok.injEq] at hEq'
              subst hEq'
              obtain ⟨shared, store, rfl, hp⟩ := codeBridge_ok hCB
              exact ⟨hp, fun hbc => Bool.noConfusion hbc⟩
          | Leave =>
              rw [Native.exec_leave] at hEq
              have hEq' : (Except.ok s.setLeave :
                  Except EvmYul.Yul.Exception State) = .ok r := hEq
              simp only [Except.ok.injEq] at hEq'
              subst hEq'
              obtain ⟨shared, store, rfl, hp⟩ := codeBridge_ok hCB
              exact ⟨hp, fun _ hbc => hbc⟩
        -- `loop (k+1)` — one iteration; the post tail via `loopPostTail`.
        have hLoop : ∀ (cond : Expr) (post body : List Stmt)
            (code : Option YulContract) (s : State),
            BridgeExpr cond → BridgeStmts post → BreakContinueFreeStmts post →
            BridgeStmts body → BridgeCode code → CodeBridge s →
            ∀ r, EvmYul.Yul.loop (k + 1) cond post body code s = .ok r →
              StateBridge r ∧ ¬ IsJumpBC r := by
          intro cond post body code s hCond hPost hPostBC hBody hCode hCB r hEq
          cases k with
          | zero =>
              rw [Native.loop_one] at hEq
              exact nomatch hEq
          | succ j =>
              have ihj : NativePreservesAt j := ih j (by omega)
              rw [Native.loop_succ_succ] at hEq
              obtain ⟨shared, store, rfl, hp⟩ := codeBridge_ok hCB
              rw [show EvmYul.Yul.State.mkOk (EvmYul.Yul.State.Ok shared store) =
                  EvmYul.Yul.State.Ok shared store from rfl] at hEq
              cases hev : EvmYul.Yul.eval j cond code
                  (EvmYul.Yul.State.Ok shared store) with
              | error e =>
                  rw [hev] at hEq
                  exact nomatch hEq
              | ok p =>
                  obtain ⟨s₁, x⟩ := p
                  rw [hev] at hEq
                  have hs₁ : CodeBridge s₁ :=
                    ihj.eval cond code (EvmYul.Yul.State.Ok shared store)
                      hCond hCode hp s₁ x hev
                  have hEq' :
                      (if x = (⟨0⟩ : Word) then
                        (Except.ok (s₁.overwrite? (EvmYul.Yul.State.Ok shared store)) :
                          Except EvmYul.Yul.Exception State)
                      else
                        match EvmYul.Yul.exec j (.Block body) code s₁ with
                        | .error e => .error e
                        | .ok s₂ =>
                            match s₂ with
                            | .OutOfFuel =>
                                .ok (s₂.overwrite? (EvmYul.Yul.State.Ok shared store))
                            | .Checkpoint (.Break _ _) =>
                                .ok (s₂.reviveJump.overwrite?
                                  (EvmYul.Yul.State.Ok shared store))
                            | .Checkpoint (.Leave _ _) =>
                                .ok (s₂.overwrite? (EvmYul.Yul.State.Ok shared store))
                            | .Checkpoint (.Continue _ _) | _ =>
                                match EvmYul.Yul.exec j (.Block post) code
                                    s₂.reviveJump with
                                | .error e => .error e
                                | .ok s₃ =>
                                    match s₃ with
                                    | .OutOfFuel =>
                                        .ok (s₃.overwrite?
                                          (EvmYul.Yul.State.Ok shared store))
                                    | .Checkpoint (.Leave _ _) =>
                                        .ok (s₃.overwrite?
                                          (EvmYul.Yul.State.Ok shared store))
                                    | _ =>
                                        match EvmYul.Yul.exec j
                                            (.For cond post body) code
                                            (s₃.overwrite?
                                              (EvmYul.Yul.State.Ok shared store)) with
                                        | .error e => .error e
                                        | .ok s₅ =>
                                            .ok (s₅.overwrite?
                                              (EvmYul.Yul.State.Ok shared store))) =
                        .ok r := hEq
                  by_cases hx : x = (⟨0⟩ : Word)
                  · rw [if_pos hx] at hEq'
                    have hEq'' : (Except.ok s₁ :
                        Except EvmYul.Yul.Exception State) = .ok r := hEq'
                    simp only [Except.ok.injEq] at hEq''
                    subst hEq''
                    exact ⟨stateBridge_of_codeBridge hs₁,
                      not_isJumpBC_of_codeBridge hs₁⟩
                  · rw [if_neg hx] at hEq'
                    cases hbx : EvmYul.Yul.exec j (.Block body) code s₁ with
                    | error e =>
                        rw [hbx] at hEq'
                        exact nomatch hEq'
                    | ok s₂ =>
                        rw [hbx] at hEq'
                        have h₂ := ihj.exec (.Block body) code s₁ hBody hCode hs₁
                          s₂ hbx
                        cases s₂ with
                        | OutOfFuel => exact ((h₂.1 : False)).elim
                        | Ok sh₂ st₂ =>
                            exact loopPostTail j ihj cond post body code shared store
                              hCond hPost hPostBC hBody hCode
                              (EvmYul.Yul.State.Ok sh₂ st₂) h₂.1 r hEq'
                        | Checkpoint jj =>
                            cases jj with
                            | Break sh₂ st₂ =>
                                have hEq'' : (Except.ok
                                    (EvmYul.Yul.State.Ok sh₂ st₂) :
                                    Except EvmYul.Yul.Exception State) = .ok r := hEq'
                                simp only [Except.ok.injEq] at hEq''
                                subst hEq''
                                exact ⟨h₂.1, fun hbc => hbc⟩
                            | Leave sh₂ st₂ =>
                                have hEq'' : (Except.ok
                                    (EvmYul.Yul.State.Checkpoint (.Leave sh₂ st₂)) :
                                    Except EvmYul.Yul.Exception State) = .ok r := hEq'
                                simp only [Except.ok.injEq] at hEq''
                                subst hEq''
                                exact ⟨h₂.1, fun hbc => hbc⟩
                            | Continue sh₂ st₂ =>
                                exact loopPostTail j ihj cond post body code
                                  shared store hCond hPost hPostBC hBody hCode
                                  (EvmYul.Yul.State.Ok sh₂ st₂) h₂.1 r hEq'
        exact ⟨hEvalTail, hEvalArgs, hEvalValues, hEval, hCall, hExecSeq,
          hExec, hLoop⟩

end PartB0

/-! ## PART B proper — the eight case lemmas, the knot, the public corollaries

Each `caseF hPrim n ih` proves the `BridgeAgreesAt.F` conjunct at native fuel `n`
from the strong-induction hypothesis `ih : BridgeIH n` (agreement at every
`k < n`). `hPrim` is the primitive boundary fact (`primCall_preserves_codeBridge`,
PrimAgrees.lean); `nativePreservesAt_of_prim hPrim` is Part B0, consumed to
re-establish `CodeBridge` at threaded states. -/

section KnotProper

open EvmYul.Yul.Ast
open InteractionSemantics
open Simulation (Interaction)

/-! ### Local our-side bind-form equations

Restated here (rather than imported from `FuelMono`) so this section builds
against the current olean set even while `PrimAgrees`/`FuelMono` are mid-rebuild;
all are `rfl`/`simp only` unfoldings identical to the `FuelMono` originals. -/

private theorem eqEvalTail_zero (args : List Expr) (code : Option YulContract)
    (result : Open (State × Word)) :
    evalTail 0 args code result =
      Interaction.bind result (fun p =>
        InteractionSemantics.Primitive.fail p.1 .OutOfFuel) := by
  unfold evalTail Yul.Source.Canonical.evalTail Yul.Source.Effectful.evalTail
  rfl

private theorem eqEvalTail_succ (k : Nat) (args : List Expr)
    (code : Option YulContract) (result : Open (State × Word)) :
    evalTail (k + 1) args code result =
      Interaction.bind result (fun p =>
        Interaction.bind (evalArgs k args code p.1)
          (fun q => Interaction.pure (q.1, p.2 :: q.2))) := by
  unfold evalTail Yul.Source.Canonical.evalTail Yul.Source.Effectful.evalTail
  rfl

private theorem eqEvalArgs_cons (k : Nat) (a : Expr) (as : List Expr)
    (code : Option YulContract) (s : State) :
    evalArgs (k + 1) (a :: as) code s =
      evalTail k as code (eval k a code s) := by
  unfold evalArgs Yul.Source.Canonical.evalArgs Yul.Source.Effectful.evalArgs
  rfl

private theorem eqEvalValues_prim (k : Nat) (op : EvmYul.Operation .Yul)
    (args : List Expr) (code : Option YulContract) (s : State) :
    evalValues (k + 1) (.Call (.inl op) args) code s =
      Interaction.bind (evalArgs k args.reverse code s)
        (fun r => InteractionSemantics.Primitive.openEval k r.1 op r.2.reverse) := by
  simp only [evalValues, Yul.Source.Canonical.evalValues,
    Yul.Source.Effectful.evalValues]
  rfl

private theorem eqEvalValues_var (k : Nat) (id : EvmYul.Identifier)
    (code : Option YulContract) (s : State) :
    evalValues (k + 1) (.Var id) code s =
      (match s.lookup? id with
       | some v => Interaction.pure (s, [v])
       | none => InteractionSemantics.Primitive.fail s (.UnknownIdentifier id)) := by
  simp only [evalValues, Yul.Source.Canonical.evalValues,
    Yul.Source.Effectful.evalValues, stateModel, id_eq,
    Yul.Source.Effectful.Control.fail]
  rfl

private theorem eqEvalValues_lit (k : Nat) (v : EvmYul.Literal)
    (code : Option YulContract) (s : State) :
    evalValues (k + 1) (.Lit v) code s = Interaction.pure (s, [v]) := by
  simp only [evalValues, Yul.Source.Canonical.evalValues,
    Yul.Source.Effectful.evalValues]
  rfl

private theorem eqEvalValues_internal (k : Nat) (fn : YulFunctionName)
    (args : List Expr) (code : Option YulContract) (s : State) :
    evalValues (k + 1) (.Call (.inr fn) args) code s =
      Interaction.bind (evalArgs k args.reverse code s)
        (fun r => call k r.2.reverse (some fn) code r.1) := by
  simp only [evalValues, Yul.Source.Canonical.evalValues,
    Yul.Source.Effectful.evalValues]
  rfl

private theorem eqCall_succ (k : Nat) (args : List Word)
    (fn? : Option YulFunctionName)
    (code : Option YulContract) (s : State) :
    call (k + 1) args fn? code s =
      (match Yul.Source.Effectful.resolveActiveCode? s code with
       | none => Yul.Source.Effectful.Control.fail s
           (.MissingContract (s!"{s.executionEnv.codeOwner}"))
       | some c =>
           match (match fn? with
                  | none => some (FunctionDefinition.Def [] [] [c.dispatcher])
                  | some f => c.functions.lookup f) with
           | none => Yul.Source.Effectful.Control.fail s
               (.MissingContractFunction (fn?.getD ".none"))
           | some function =>
               match function with
               | .Def params rets body =>
                   Interaction.bind
                     (exec k (.Block body) code
                       (EvmYul.Yul.State.mkOk (s.initcall params rets args)))
                     (fun sab => Interaction.pure
                       ((sab.reviveJump.overwrite? s).setStore s,
                         List.map sab.lookup! rets))) := by
  simp only [call, Yul.Source.Canonical.call, Yul.Source.Effectful.call, stateModel,
    id_eq]
  rfl

/-! ### Local one-step closers (the `bind`/`wrap`/`pure` closers live in
`ExecAgreesFamily`; these are the extra native-combinator-shaped ones). -/

/-- `cons'`-shaped closer (native side is literally `cons'`, so no matcher-defeq
against a rewritten form is needed). -/
private theorem doneAgrees_cons' {w : Word}
    {na : Except EvmYul.Yul.Exception (State × List Word)}
    {oa : Open (State × List Word)} (h : DoneAgrees na oa) :
    DoneAgrees (EvmYul.Yul.cons' w na)
      (Interaction.bind oa (fun q => Interaction.pure (q.1, w :: q.2))) := by
  obtain ⟨r, hr, hRA⟩ := h
  subst hr
  cases na with
  | ok a =>
      cases r with
      | ok b =>
          have hb : b = a := hRA
          subst b
          cases a with
          | mk s as =>
              rw [Interaction.bind_done_ok]
              exact ⟨.ok (s, w :: as), rfl, rfl⟩
      | error f => exact (hRA : False).elim
  | error e =>
      cases r with
      | ok b => exact (hRA : False).elim
      | error f => rw [Interaction.bind_done_error]; exact ⟨.error f, rfl, hRA⟩

private theorem multifill'_nil_eq
    (X : Except EvmYul.Yul.Exception (State × List Word)) :
    EvmYul.Yul.multifill' [] X =
      (match X with
       | .ok a => .ok (EvmYul.Yul.State.multifill [] a.2 a.1)
       | .error e => .error e) := by
  cases X with
  | ok a => cases a; rfl
  | error e => rfl

private theorem doneAgrees_errorFail {α : Type} {e : EvmYul.Yul.Exception}
    (s : State) :
    DoneAgrees (α := α) (.error e) (InteractionSemantics.Primitive.fail s e) :=
  ⟨.error { exception := e, state := s }, rfl, rfl⟩

/-- The primitive boundary fact the whole knot is parameterized by. -/
abbrev PrimBoundary : Prop :=
  ∀ {op : EvmYul.Operation .Yul}, BridgeOp op →
    ∀ (fuel : Nat) (s : State) (args : List Word) (s' : State) (out : List Word),
      EvmYul.Yul.primCall fuel s op args = .ok (s', out) → CodeBridge s → CodeBridge s'

theorem caseEvalTail (hPrim : PrimBoundary) (n : Nat) (ih : BridgeIH n) :
    ∀ (args : List Expr) (code : Option YulContract)
      (nr : Except EvmYul.Yul.Exception (State × Word)) (or : Open (State × Word)),
      BridgeExprs args → BridgeCode code →
      (∀ p, nr = .ok p → CodeBridge p.1) → DoneAgrees nr or →
      ∃ m, DoneAgrees (EvmYul.Yul.evalTail n args code nr) (evalTail m args code or) := by
  intro args code nr or hArgs hCode hPres hDA
  match n with
  | 0 =>
    refine ⟨0, ?_⟩
    obtain ⟨r, hor, hRA⟩ := hDA
    subst hor
    cases nr with
    | error e =>
        cases r with
        | ok b => exact (hRA : False).elim
        | error f =>
            rw [Native.evalTail_error, eqEvalTail_zero,
              Simulation.Interaction.bind_done_error]
            exact ⟨.error f, rfl, hRA⟩
    | ok p =>
        cases r with
        | error f => exact (hRA : False).elim
        | ok b =>
            have hb : b = p := hRA
            subst b
            rw [Native.evalTail_zero_ok, eqEvalTail_zero,
              Simulation.Interaction.bind_done_ok]
            exact doneAgrees_fail_outOfFuel _
  | k + 1 =>
    have ihk : BridgeAgreesAt k := ih k (Nat.lt_succ_self k)
    obtain ⟨r, hor, hRA⟩ := hDA
    subst hor
    cases nr with
    | error e =>
        refine ⟨1, ?_⟩
        cases r with
        | ok b => exact (hRA : False).elim
        | error f =>
            rw [Native.evalTail_error, eqEvalTail_succ,
              Simulation.Interaction.bind_done_error]
            exact ⟨.error f, rfl, hRA⟩
    | ok p =>
        cases r with
        | error f => exact (hRA : False).elim
        | ok b =>
            have hb : b = p := hRA
            subst b
            have hCB : CodeBridge p.1 := hPres p rfl
            obtain ⟨m₂, hEA⟩ := ihk.evalArgs args code p.1 hArgs hCode hCB
            refine ⟨m₂ + 1, ?_⟩
            rw [Native.evalTail_ok, eqEvalTail_succ,
              Simulation.Interaction.bind_done_ok]
            exact doneAgrees_cons' hEA

/-- Shared close for one internal-call body: wrap the agreeing `exec` of the
selected body into the caller-frame restoration pair. Inlined concrete casing so
the native side stays `call`-shaped (no matcher-defeq against a rewritten form). -/
private theorem callBodyClose {k m : Nat} {c : YulContract} {s init : State}
    {rets : List EvmYul.Identifier} {body : List Stmt}
    (hex : DoneAgrees (EvmYul.Yul.exec k (.Block body) (some c) init)
      (exec m (.Block body) (some c) init)) :
    DoneAgrees
      (match EvmYul.Yul.exec k (.Block body) (some c) init with
       | .error e => .error e
       | .ok s₂ => .ok ((s₂.reviveJump.overwrite? s).setStore s,
           List.map s₂.lookup! rets))
      (Interaction.bind (exec m (.Block body) (some c) init)
        (fun sab => Interaction.pure
          ((sab.reviveJump.overwrite? s).setStore s, List.map sab.lookup! rets))) := by
  obtain ⟨r, hr, hRA⟩ := hex
  rw [hr]
  cases hnex : EvmYul.Yul.exec k (.Block body) (some c) init with
  | error e =>
      rw [hnex] at hRA
      cases r with
      | ok b => exact (hRA : False).elim
      | error f => rw [Interaction.bind_done_error]; exact ⟨.error f, rfl, hRA⟩
  | ok s₂ =>
      rw [hnex] at hRA
      cases r with
      | error f => exact (hRA : False).elim
      | ok b =>
          have hb : b = s₂ := hRA
          subst b
          rw [Interaction.bind_done_ok]
          exact ⟨.ok _, rfl, rfl⟩

theorem caseCall (hPrim : PrimBoundary) (n : Nat) (ih : BridgeIH n) :
    ∀ (args : List Word) (fn? : Option YulFunctionName)
      (code : Option YulContract) (s : State),
      BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.call n args fn? code s) (call m args fn? code s) := by
  intro args fn? code s hCode hCB
  match n with
  | 0 =>
      exact ⟨0, by rw [Native.call_zero, Call.zero]; exact doneAgrees_errorFail s⟩
  | k + 1 =>
      have ihk : BridgeAgreesAt k := ih k (Nat.lt_succ_self k)
      obtain ⟨c, rfl, hc⟩ := hCode
      have hc' := hc
      simp only [BridgeContract, bridgeContract?, Bool.and_eq_true] at hc'
      cases hf : s.sharedState.accountMap.find? s.executionEnv.codeOwner with
      | none => exact absurd hf hCB
      | some yc =>
          cases fn? with
          | none =>
              have hbody : BridgeStmt (.Block [c.dispatcher]) := by
                show bridgeStmts? [c.dispatcher] = true
                simp only [bridgeStmts?, Bool.and_eq_true]; exact ⟨hc'.1, trivial⟩
              obtain ⟨m, hex⟩ := ihk.exec (.Block [c.dispatcher]) (some c)
                (EvmYul.Yul.State.mkOk (s.initcall [] [] args)) hbody ⟨c, rfl, hc⟩
                (codeBridge_initcall hCB [] [] args)
              refine ⟨m + 1, ?_⟩
              rw [Native.call_succ, hf, eqCall_succ, Yul.Source.Effectful.resolveActiveCode?_some]
              dsimp only [Option.getD_some]
              exact callBodyClose (rets := []) (s := s) hex
          | some fnName =>
              cases hlk : c.functions.lookup fnName with
              | none =>
                  refine ⟨1, ?_⟩
                  rw [Native.call_succ, hf, eqCall_succ,
                    Yul.Source.Effectful.resolveActiveCode?_some]
                  dsimp only [Option.getD_some]
                  rw [hlk]
                  dsimp only [Option.getD_some]
                  exact doneAgrees_errorFail s
              | some f =>
                  cases f with
                  | Def params rets body =>
                      have hbody : BridgeStmt (.Block body) :=
                        bridgeContract_lookup hc hlk
                      obtain ⟨m, hex⟩ := ihk.exec (.Block body) (some c)
                        (EvmYul.Yul.State.mkOk (s.initcall params rets args)) hbody
                        ⟨c, rfl, hc⟩ (codeBridge_initcall hCB params rets args)
                      refine ⟨m + 1, ?_⟩
                      rw [Native.call_succ, hf, eqCall_succ,
                        Yul.Source.Effectful.resolveActiveCode?_some]
                      dsimp only [Option.getD_some]
                      rw [hlk]
                      dsimp only [Option.getD_some]
                      exact callBodyClose (rets := rets) (s := s) hex

theorem caseEvalArgs (hPrim : PrimBoundary) (n : Nat) (ih : BridgeIH n) :
    ∀ (args : List Expr) (code : Option YulContract) (s : State),
      BridgeExprs args → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.evalArgs n args code s) (evalArgs m args code s) := by
  intro args code s hArgs hCode hCB
  match n with
  | 0 =>
      refine ⟨0, ?_⟩
      rw [Native.evalArgs_zero, EvalArgs.zero]
      exact doneAgrees_fail_outOfFuel s
  | k + 1 =>
      have ihk : BridgeAgreesAt k := ih k (Nat.lt_succ_self k)
      match args with
      | [] =>
          refine ⟨k + 1, ?_⟩
          rw [Native.evalArgs_nil, EvalArgs.nil_succ]
          exact doneAgrees_pure _
      | a :: as =>
          simp only [BridgeExprs, bridgeExprs?, Bool.and_eq_true] at hArgs
          have hBA : BridgeExpr a := hArgs.1
          have hBAs : BridgeExprs as := hArgs.2
          obtain ⟨m₁, hd⟩ := ihk.eval a code s hBA hCode hCB
          obtain ⟨m₂, ht⟩ := ihk.evalTail as code (EvmYul.Yul.eval k a code s)
            (eval m₁ a code s) hBAs hCode
            (fun p hp => (nativePreservesAt_of_prim hPrim k).eval a code s hBA hCode
              hCB p.1 p.2 hp) hd
          rw [← Native.evalArgs_cons] at ht
          by_cases hNa : NativeSettled (EvmYul.Yul.evalArgs (k + 1) (a :: as) code s)
          · have hNe : NativeSettled (EvmYul.Yul.eval k a code s) := by
              intro e he
              rintro rfl
              exact (hNa .OutOfFuel (by rw [Native.evalArgs_cons, he,
                Native.evalTail_error])) rfl
            have hSe : Settled (eval m₁ a code s) := settled_of_doneAgrees hNe hd
            have hSt : Settled (evalTail m₂ as code (eval m₁ a code s)) :=
              settled_of_doneAgrees hNa ht
            refine ⟨max m₁ m₂ + 1, ?_⟩
            rw [eqEvalArgs_cons, eval_mono (le_max_left m₁ m₂) a code s hSe,
              evalTail_mono (le_max_right m₁ m₂) as code (eval m₁ a code s) hSt]
            exact ht
          · refine ⟨0, ?_⟩
            rw [EvalArgs.zero]
            simp only [NativeSettled, not_forall, not_not] at hNa
            obtain ⟨e, he, rfl⟩ := hNa
            rw [he]
            exact doneAgrees_fail_outOfFuel s

/-! ### `caseEvalValues` / `caseEval` -/

/-- Combinator for the `evalValues` call arms: native `reverse'`-then-leaf vs our
`bind`-then-leaf (the leaf reverses the argument list itself). -/
private theorem doneAgrees_revBind {k F : Nat}
    {code : Option YulContract} {s : State} {args : List Expr}
    {nleaf : State → List Word → Except EvmYul.Yul.Exception (State × List Word)}
    {oleaf : State → List Word → Open (State × List Word)}
    (hE : DoneAgrees (EvmYul.Yul.evalArgs k args.reverse code s)
      (evalArgs F args.reverse code s))
    (hleaf : ∀ s' a, EvmYul.Yul.evalArgs k args.reverse code s = .ok (s', a) →
      DoneAgrees (nleaf s' a.reverse) (oleaf s' a.reverse)) :
    DoneAgrees
      (match EvmYul.Yul.reverse' (EvmYul.Yul.evalArgs k args.reverse code s) with
       | .ok (s', a) => nleaf s' a
       | .error e => .error e)
      (Interaction.bind (evalArgs F args.reverse code s)
        (fun r => oleaf r.1 r.2.reverse)) := by
  obtain ⟨r, hr, hRA⟩ := hE
  rw [hr]
  cases hnEA : EvmYul.Yul.evalArgs k args.reverse code s with
  | error e =>
      rw [hnEA] at hRA
      cases r with
      | ok b => exact (hRA : False).elim
      | error f =>
          rw [Simulation.Interaction.bind_done_error]
          simp only [EvmYul.Yul.reverse']
          exact ⟨.error f, rfl, hRA⟩
  | ok p =>
      rw [hnEA] at hRA
      cases r with
      | error f => exact (hRA : False).elim
      | ok b =>
          have hbp : b = p := hRA
          subst b
          rw [Simulation.Interaction.bind_done_ok]
          obtain ⟨s', a⟩ := p
          simp only [EvmYul.Yul.reverse']
          exact hleaf s' a hnEA

theorem caseEvalValues (hPrim : PrimBoundary) (n : Nat) (ih : BridgeIH n) :
    ∀ (expr : Expr) (code : Option YulContract) (s : State),
      BridgeExpr expr → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.evalValues n expr code s) (evalValues m expr code s) := by
  intro expr code s hExpr hCode hCB
  match n with
  | 0 => exact ⟨0, by rw [Native.evalValues_zero, EvalValues.zero]; exact doneAgrees_errorFail s⟩
  | k + 1 =>
    have ihk : BridgeAgreesAt k := ih k (Nat.lt_succ_self k)
    have hB0 := nativePreservesAt_of_prim hPrim
    cases expr with
    | Var id =>
        refine ⟨1, ?_⟩
        rw [Native.evalValues_var, eqEvalValues_var]
        cases s.lookup? id with
        | some v => exact doneAgrees_pure _
        | none => exact doneAgrees_errorFail _
    | Lit v =>
        exact ⟨1, by rw [Native.evalValues_lit, eqEvalValues_lit]; exact doneAgrees_pure _⟩
    | Call sop args =>
        cases sop with
        | inl op =>
            have hbe : bridgeExpr? (.Call (.inl op) args) = true := hExpr
            simp only [bridgeExpr?, Bool.and_eq_true, bridgeOp?_iff] at hbe
            have hOp : BridgeOp op := hbe.1
            have hBArgs : BridgeExprs args.reverse := bridgeExprs?_reverse hbe.2
            cases k with
            | zero =>
                refine ⟨0, ?_⟩
                have hw : EvmYul.Yul.evalValues 1 (.Call (.inl op) args) code s =
                    .error .OutOfFuel := by
                  simp only [Native.evalValues_prim, Native.evalArgs_zero,
                    EvmYul.Yul.reverse']
                rw [hw, EvalValues.zero]; exact doneAgrees_fail_outOfFuel s
            | succ k' =>
                obtain ⟨m₁, hE⟩ := ihk.evalArgs args.reverse code s hBArgs hCode hCB
                by_cases hNe :
                    NativeSettled (EvmYul.Yul.evalArgs (k' + 1) args.reverse code s)
                · have hEl : DoneAgrees (EvmYul.Yul.evalArgs (k' + 1) args.reverse code s)
                      (evalArgs (m₁ + 2) args.reverse code s) :=
                    evalArgs_lift hNe (Nat.le_add_right m₁ 2) hE
                  refine ⟨m₁ + 2 + 1, ?_⟩
                  rw [Native.evalValues_prim, eqEvalValues_prim]
                  refine doneAgrees_revBind
                    (nleaf := fun s' a => EvmYul.Yul.primCall (k' + 1) s' op a)
                    (oleaf := fun s' l => InteractionSemantics.Primitive.openEval (m₁ + 2) s' op l)
                    hEl ?_
                  intro s' a _
                  show DoneAgrees (EvmYul.Yul.primCall (k' + 1) s' op a.reverse)
                    (InteractionSemantics.Primitive.openEval (m₁ + 2) s' op a.reverse)
                  have hfi : EvmYul.Yul.primCall (k' + 1) s' op a.reverse =
                      EvmYul.Yul.primCall (m₁ + 1) s' op a.reverse :=
                    primCall_fuel_insensitive hOp k' m₁ s' a.reverse
                  rw [hfi]
                  exact doneAgrees_openEval_shift hOp (m₁ + 1) s' a.reverse
                · refine ⟨0, ?_⟩
                  simp only [NativeSettled, not_forall, not_not] at hNe
                  obtain ⟨e, he, rfl⟩ := hNe
                  have hw : EvmYul.Yul.evalValues (k' + 1 + 1) (.Call (.inl op) args) code s =
                      .error .OutOfFuel := by
                    simp only [Native.evalValues_prim, he, EvmYul.Yul.reverse']
                  rw [hw, EvalValues.zero]; exact doneAgrees_fail_outOfFuel s
        | inr fn =>
            have hbe : bridgeExpr? (.Call (.inr fn) args) = true := hExpr
            simp only [bridgeExpr?, Bool.and_eq_true] at hbe
            have hBArgs : BridgeExprs args.reverse := bridgeExprs?_reverse hbe
            obtain ⟨m₁, hE⟩ := ihk.evalArgs args.reverse code s hBArgs hCode hCB
            by_cases hNe :
                NativeSettled (EvmYul.Yul.evalValues (k + 1) (.Call (.inr fn) args) code s)
            · have hNea : NativeSettled (EvmYul.Yul.evalArgs k args.reverse code s) := by
                intro e he; rintro rfl
                exact (hNe .OutOfFuel (by
                  simp only [Native.evalValues_call, he, EvmYul.Yul.reverse'])) rfl
              cases hns : EvmYul.Yul.evalArgs k args.reverse code s with
              | error e =>
                  refine ⟨m₁ + 1, ?_⟩
                  rw [Native.evalValues_call, eqEvalValues_internal]
                  exact doneAgrees_revBind
                    (nleaf := fun ss aa => EvmYul.Yul.call k aa (some fn) code ss)
                    (oleaf := fun ss ll => call m₁ ll (some fn) code ss)
                    (evalArgs_lift hNea (Nat.le_refl _) hE)
                    (fun s' a hh => by rw [hns] at hh; exact nomatch hh)
              | ok p =>
                  obtain ⟨s', a⟩ := p
                  have hCBs' : CodeBridge s' :=
                    (hB0 k).evalArgs args.reverse code s hBArgs hCode hCB s' a (by rw [hns])
                  obtain ⟨m₂, hc⟩ := ihk.call a.reverse (some fn) code s' hCode hCBs'
                  have hNc : NativeSettled (EvmYul.Yul.call k a.reverse (some fn) code s') := by
                    intro e he; rintro rfl
                    exact (hNe .OutOfFuel (by
                      simp only [Native.evalValues_call, hns, EvmYul.Yul.reverse', he])) rfl
                  refine ⟨max m₁ m₂ + 1, ?_⟩
                  rw [Native.evalValues_call, eqEvalValues_internal]
                  refine doneAgrees_revBind
                    (nleaf := fun ss aa => EvmYul.Yul.call k aa (some fn) code ss)
                    (oleaf := fun ss ll => call (max m₁ m₂) ll (some fn) code ss)
                    (evalArgs_lift hNea (le_max_left _ _) hE) ?_
                  intro s'' a'' hh
                  rw [hns] at hh
                  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj hh
                  exact call_lift hNc (le_max_right _ _) hc
            · refine ⟨0, ?_⟩
              simp only [NativeSettled, not_forall, not_not] at hNe
              obtain ⟨e, he, rfl⟩ := hNe
              rw [EvalValues.zero, he]; exact doneAgrees_fail_outOfFuel s

private theorem doneAgrees_head' {nEV : Except EvmYul.Yul.Exception (State × List Word)}
    {oEV : Open (State × List Word)} (h : DoneAgrees nEV oEV) :
    DoneAgrees (EvmYul.Yul.head' nEV)
      (Interaction.bind oEV (fun r => Interaction.pure (r.1, r.2.head!))) := by
  obtain ⟨r, hr, hRA⟩ := h
  rw [hr]
  cases hn : nEV with
  | error e =>
      rw [hn] at hRA
      cases r with
      | ok b => exact (hRA : False).elim
      | error f =>
          rw [Simulation.Interaction.bind_done_error]
          simp only [EvmYul.Yul.head']
          exact ⟨.error f, rfl, hRA⟩
  | ok p =>
      rw [hn] at hRA
      cases r with
      | error f => exact (hRA : False).elim
      | ok b =>
          have hbp : b = p := hRA
          subst b
          rw [Simulation.Interaction.bind_done_ok]
          obtain ⟨s', l⟩ := p
          simp only [EvmYul.Yul.head']
          exact ⟨.ok (s', l.head!), rfl, rfl⟩

theorem caseEval (hPrim : PrimBoundary) (n : Nat) (ih : BridgeIH n) :
    ∀ (expr : Expr) (code : Option YulContract) (s : State),
      BridgeExpr expr → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.eval n expr code s) (eval m expr code s) := by
  intro expr code s hExpr hCode hCB
  obtain ⟨m, hv⟩ := caseEvalValues hPrim n ih expr code s hExpr hCode hCB
  refine ⟨m, ?_⟩
  rw [Native.eval_eq, eval_eq_bind]
  exact doneAgrees_head' hv

/-! ### `caseExecSeq` -/

/-- Combinator for the `execSeq` cons step (native nested-match vs our bind), at
a common fuel `m` for the head `exec` and the tail `execSeq`. Mirrors
`callBodyClose`'s inlined casing to sidestep matcher-defeq. -/
private theorem execSeqConsClose {k m : Nat} {stmt : Stmt} {rest : List Stmt}
    {code : Option YulContract} {s : State}
    (h₁ : DoneAgrees (EvmYul.Yul.exec k stmt code s) (exec m stmt code s))
    (hrec : ∀ sh vs, EvmYul.Yul.exec k stmt code s = .ok (.Ok sh vs) →
      DoneAgrees (EvmYul.Yul.execSeq k rest code (.Ok sh vs))
        (execSeq m rest code (.Ok sh vs))) :
    DoneAgrees (EvmYul.Yul.execSeq (k + 1) (stmt :: rest) code s)
      (execSeq (m + 1) (stmt :: rest) code s) := by
  rw [Native.execSeq_cons, ExecSeq.cons_succ]
  obtain ⟨r, hr, hRA⟩ := h₁
  rw [hr]
  cases hnex : EvmYul.Yul.exec k stmt code s with
  | error e =>
      rw [hnex] at hRA
      cases r with
      | ok b => exact (hRA : False).elim
      | error f => rw [Simulation.Interaction.bind_done_error]; exact ⟨.error f, rfl, hRA⟩
  | ok s₁ =>
      rw [hnex] at hRA
      cases r with
      | error f => exact (hRA : False).elim
      | ok b =>
          have hbeq : b = s₁ := hRA
          subst b
          rw [Simulation.Interaction.bind_done_ok]
          cases s₁ with
          | OutOfFuel => exact ⟨.ok _, rfl, rfl⟩
          | Checkpoint j => exact ⟨.ok _, rfl, rfl⟩
          | Ok sh vs => exact hrec sh vs hnex

theorem caseExecSeq (hPrim : PrimBoundary) (n : Nat) (ih : BridgeIH n) :
    ∀ (stmts : List Stmt) (code : Option YulContract) (s : State),
      BridgeStmts stmts → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.execSeq n stmts code s) (execSeq m stmts code s) := by
  intro stmts code s hStmts hCode hCB
  match n with
  | 0 => exact ⟨0, by rw [Native.execSeq_zero, ExecSeq.zero]; exact doneAgrees_errorFail s⟩
  | k + 1 =>
    have ihk : BridgeAgreesAt k := ih k (Nat.lt_succ_self k)
    have hB0 := nativePreservesAt_of_prim hPrim
    cases stmts with
    | nil => exact ⟨1, by rw [Native.execSeq_nil, ExecSeq.nil_succ]; exact doneAgrees_pure s⟩
    | cons stmt rest =>
      have hb : bridgeStmts? (stmt :: rest) = true := hStmts
      simp only [bridgeStmts?, Bool.and_eq_true] at hb
      obtain ⟨m₁, h₁⟩ := ihk.exec stmt code s hb.1 hCode hCB
      have hsub : NativeSettled (EvmYul.Yul.exec k stmt code s) ∨
          EvmYul.Yul.exec k stmt code s = .error .OutOfFuel := by
        by_cases hh : EvmYul.Yul.exec k stmt code s = .error .OutOfFuel
        · exact Or.inr hh
        · exact Or.inl (fun e he => by rintro rfl; exact hh he)
      cases hsub with
      | inr hh =>
          have hw : EvmYul.Yul.execSeq (k + 1) (stmt :: rest) code s = .error .OutOfFuel := by
            simp only [Native.execSeq_cons, hh]
          exact ⟨0, by rw [ExecSeq.zero, hw]; exact doneAgrees_fail_outOfFuel s⟩
      | inl hNs =>
          cases hns : EvmYul.Yul.exec k stmt code s with
          | error e =>
              exact ⟨m₁ + 1, execSeqConsClose h₁
                (fun sh vs h => by simp only [hns, reduceCtorEq] at h)⟩
          | ok s₁ =>
              cases s₁ with
              | OutOfFuel =>
                  exact ⟨m₁ + 1, execSeqConsClose h₁
                    (fun sh vs h => by simp only [hns, Except.ok.injEq, reduceCtorEq] at h)⟩
              | Checkpoint j =>
                  exact ⟨m₁ + 1, execSeqConsClose h₁
                    (fun sh vs h => by simp only [hns, Except.ok.injEq, reduceCtorEq] at h)⟩
              | Ok sh vs =>
                  have hSB : StateBridge (EvmYul.Yul.State.Ok sh vs) :=
                    ((hB0 k).exec stmt code s hb.1 hCode hCB _ (by rw [hns])).1
                  have hCB₁ : CodeBridge (EvmYul.Yul.State.Ok sh vs) := codeBridge_okState hSB
                  have hrec0 := ihk.execSeq rest code (.Ok sh vs) hb.2 hCode hCB₁
                  by_cases hrs : NativeSettled (EvmYul.Yul.execSeq k rest code (.Ok sh vs))
                  · obtain ⟨m₂, h₂⟩ := hrec0
                    refine ⟨max m₁ m₂ + 1, execSeqConsClose
                      (exec_lift hNs (le_max_left _ _) h₁) (fun sh' vs' h => ?_)⟩
                    rw [hns] at h
                    have hEq : EvmYul.Yul.State.Ok sh vs = EvmYul.Yul.State.Ok sh' vs' :=
                      Except.ok.inj h
                    cases hEq
                    exact execSeq_lift hrs (le_max_right _ _) h₂
                  · refine ⟨0, ?_⟩
                    simp only [NativeSettled, not_forall, not_not] at hrs
                    obtain ⟨e, he, rfl⟩ := hrs
                    have hw : EvmYul.Yul.execSeq (k + 1) (stmt :: rest) code s =
                        .error .OutOfFuel := by
                      simp only [Native.execSeq_cons, hns, he]
                    rw [ExecSeq.zero, hw]
                    exact doneAgrees_fail_outOfFuel s

/-! ### `caseExec` — the eleven statement constructors

Structure mirrors `caseExecSeq`: at native fuel `n = k + 1`, unfold one native step
(`Native.exec_*`), reduce our side (`Exec.*`), and combine IH witnesses. The
`.error`-first / pair-destructured native matches (`exec_if`, `exec_switch`,
`exec_expr_internal`) don't unify with `doneAgrees_bind`'s `.ok`-first conclusion,
so those arms use dedicated manual-casing closers named by AST constructor
(`exec_if_close`, `exec_switch_close`, `exec_exprInternal_close`), exactly as
`execSeqConsClose`/`callBodyClose` do. -/

/-- Wrap an agreeing `Except`-of-`(State × List Word)` result into the
`multifill'` writeback (native) versus our `bind`-then-`pure`-multifill. Mirrors
`doneAgrees_cons'`. `stateModel.multifill names st vals = st.multifill names vals`
by definition, so the `.ok` values coincide. -/
private theorem doneAgrees_multifill (names : List EvmYul.Identifier)
    {nEV : Except EvmYul.Yul.Exception (State × List Word)}
    {oEV : Open (State × List Word)} (h : DoneAgrees nEV oEV) :
    DoneAgrees (EvmYul.Yul.multifill' names nEV)
      (Interaction.bind oEV
        (fun result => Interaction.pure (stateModel.multifill names result.1 result.2))) := by
  obtain ⟨r, hr, hRA⟩ := h
  rw [hr]
  cases hn : nEV with
  | error e =>
      rw [hn] at hRA
      cases r with
      | ok b => exact (hRA : False).elim
      | error f =>
          rw [Simulation.Interaction.bind_done_error]
          simp only [EvmYul.Yul.multifill']
          exact ⟨.error f, rfl, hRA⟩
  | ok p =>
      rw [hn] at hRA
      cases r with
      | error f => exact (hRA : False).elim
      | ok b =>
          have hbp : b = p := hRA
          subst b
          rw [Simulation.Interaction.bind_done_ok]
          obtain ⟨st, vals⟩ := p
          simp only [EvmYul.Yul.multifill']
          exact ⟨.ok _, rfl, rfl⟩

/-! #### Our-side one-step equations for the check-error / invalid-expression arms

Native's `exec_let_*`/`exec_assign` keep the `checkDeclaration`/`checkAssignment`
match `.error`-first; on the error branch our side `fail`s with the same
exception. `exec_expr_var`/`exec_expr_lit` are the `InvalidExpression` leaves. -/

private theorem our_let_none_fail (fuel : Nat) (names : List EvmYul.Identifier)
    (code : Option YulContract) (s : State) (e : EvmYul.Yul.Exception)
    (hCk : EvmYul.Yul.checkDeclaration s names = .error e) :
    exec (fuel + 1) (.Let names none) code s =
      InteractionSemantics.Primitive.fail s e := by
  simp only [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec, hCk,
    stateModel, id_eq, Yul.Source.Effectful.Control.fail,
    InteractionSemantics.Primitive.fail]
  rfl

private theorem our_let_some_fail (fuel : Nat) (names : List EvmYul.Identifier)
    (expr : Expr) (code : Option YulContract) (s : State) (e : EvmYul.Yul.Exception)
    (hCk : EvmYul.Yul.checkDeclaration s names = .error e) :
    exec (fuel + 1) (.Let names (some expr)) code s =
      InteractionSemantics.Primitive.fail s e := by
  simp only [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec, hCk,
    stateModel, id_eq, Yul.Source.Effectful.Control.fail,
    InteractionSemantics.Primitive.fail]
  rfl

private theorem our_assign_fail (fuel : Nat) (names : List EvmYul.Identifier)
    (expr : Expr) (code : Option YulContract) (s : State) (e : EvmYul.Yul.Exception)
    (hCk : EvmYul.Yul.checkAssignment s names = .error e) :
    exec (fuel + 1) (.Assign names expr) code s =
      InteractionSemantics.Primitive.fail s e := by
  simp only [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec, hCk,
    stateModel, id_eq, Yul.Source.Effectful.Control.fail,
    InteractionSemantics.Primitive.fail]
  rfl

private theorem our_expr_var_fail (fuel : Nat) (id : EvmYul.Identifier)
    (code : Option YulContract) (s : State) :
    exec (fuel + 1) (.ExprStmtCall (.Var id)) code s =
      InteractionSemantics.Primitive.fail s .InvalidExpression := by
  simp only [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    stateModel, Yul.Source.Effectful.Control.fail,
    InteractionSemantics.Primitive.fail]
  rfl

private theorem our_expr_lit_fail (fuel : Nat) (v : EvmYul.Literal)
    (code : Option YulContract) (s : State) :
    exec (fuel + 1) (.ExprStmtCall (.Lit v)) code s =
      InteractionSemantics.Primitive.fail s .InvalidExpression := by
  simp only [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    stateModel, Yul.Source.Effectful.Control.fail,
    InteractionSemantics.Primitive.fail]
  rfl

/-- Native derived identity: a primitive expression-statement is value
evaluation followed by the empty-destination writeback, at the *same* fuel. -/
private theorem exec_exprPrim_eq (k : Nat) (op : EvmYul.Operation .Yul)
    (args : List Expr) (code : Option YulContract) (s : State) :
    EvmYul.Yul.exec (k + 1) (.ExprStmtCall (.Call (.inl op) args)) code s =
      EvmYul.Yul.multifill' [] (EvmYul.Yul.evalValues (k + 1) (.Call (.inl op) args) code s) := by
  rw [Native.exec_expr_prim, Native.evalValues_prim]
  cases EvmYul.Yul.reverse' (EvmYul.Yul.evalArgs k args.reverse code s) with
  | error e => simp only [Native.execPrimCall_error, EvmYul.Yul.multifill']
  | ok p => obtain ⟨st, vals⟩ := p; simp only [Native.execPrimCall_ok]

/-- Manual-casing closer for the `If` arm: eval-then-block, bridging the native
`⟨0⟩` and our `UInt256.ofNat 0` zero literals (defeq). -/
private theorem exec_if_close {k m : Nat} {cond : Expr} {body : List Stmt}
    {code : Option YulContract} {s : State}
    (h₁ : DoneAgrees (EvmYul.Yul.eval k cond code s) (eval m cond code s))
    (hrec : ∀ s' c, EvmYul.Yul.eval k cond code s = .ok (s', c) → c ≠ (⟨0⟩ : Word) →
      DoneAgrees (EvmYul.Yul.exec k (.Block body) code s')
        (exec m (.Block body) code s')) :
    DoneAgrees (EvmYul.Yul.exec (k + 1) (.If cond body) code s)
      (exec (m + 1) (.If cond body) code s) := by
  rw [Native.exec_if, Exec.if_succ]
  obtain ⟨r, hr, hRA⟩ := h₁
  rw [hr]
  cases hnE : EvmYul.Yul.eval k cond code s with
  | error e =>
      rw [hnE] at hRA
      cases r with
      | ok b => exact (hRA : False).elim
      | error f => rw [Simulation.Interaction.bind_done_error]; exact ⟨.error f, rfl, hRA⟩
  | ok p =>
      rw [hnE] at hRA
      cases r with
      | error f => exact (hRA : False).elim
      | ok b =>
          have hbp : b = p := hRA
          subst b
          obtain ⟨s', c⟩ := p
          simp only [Simulation.Interaction.bind_done_ok,
            show EvmYul.UInt256.ofNat 0 = (⟨0⟩ : Word) from rfl]
          split_ifs with h
          · exact hrec s' c hnE h
          · exact ⟨.ok s', rfl, rfl⟩

/-- Manual-casing closer for the `Switch` arm: eval-then-selected-block. -/
private theorem exec_switch_close {k m : Nat} {cond : Expr}
    {cases : List (Literal × List Stmt)} {defaultBody : List Stmt}
    {code : Option YulContract} {s : State}
    (h₁ : DoneAgrees (EvmYul.Yul.eval k cond code s) (eval m cond code s))
    (hrec : ∀ s' c, EvmYul.Yul.eval k cond code s = .ok (s', c) →
      DoneAgrees (EvmYul.Yul.exec k (.Block (EvmYul.Yul.selectSwitchCase c defaultBody cases)) code s')
        (exec m (.Block (EvmYul.Yul.selectSwitchCase c defaultBody cases)) code s')) :
    DoneAgrees (EvmYul.Yul.exec (k + 1) (.Switch cond cases defaultBody) code s)
      (exec (m + 1) (.Switch cond cases defaultBody) code s) := by
  rw [Native.exec_switch, Exec.switch_succ]
  obtain ⟨r, hr, hRA⟩ := h₁
  rw [hr]
  cases hnE : EvmYul.Yul.eval k cond code s with
  | error e =>
      rw [hnE] at hRA
      cases r with
      | ok b => exact (hRA : False).elim
      | error f => rw [Simulation.Interaction.bind_done_error]; exact ⟨.error f, rfl, hRA⟩
  | ok p =>
      rw [hnE] at hRA
      cases r with
      | error f => exact (hRA : False).elim
      | ok b =>
          have hbp : b = p := hRA
          subst b
          obtain ⟨s', c⟩ := p
          rw [Simulation.Interaction.bind_done_ok]
          exact hrec s' c hnE

/-- Manual-casing closer for the internal-call expression-statement arm. Native
`exec (j+2)` runs `evalArgs (j+1)` then `call j` then the empty writeback; our
`exec (m+2)` mirrors it via `Exec.expr_internal_succ`. -/
private theorem exec_exprInternal_close {j m : Nat} {fn : YulFunctionName}
    {args : List Expr} {code : Option YulContract} {s : State}
    (hE : DoneAgrees (EvmYul.Yul.evalArgs (j + 1) args.reverse code s)
      (evalArgs (m + 1) args.reverse code s))
    (hrec : ∀ st a, EvmYul.Yul.evalArgs (j + 1) args.reverse code s = .ok (st, a) →
      DoneAgrees (EvmYul.Yul.call j a.reverse (some fn) code st)
        (call m a.reverse (some fn) code st)) :
    DoneAgrees (EvmYul.Yul.exec (j + 2) (.ExprStmtCall (.Call (.inr fn) args)) code s)
      (exec (m + 2) (.ExprStmtCall (.Call (.inr fn) args)) code s) := by
  rw [show j + 2 = (j + 1) + 1 from rfl, Native.exec_expr_internal, Exec.expr_internal_succ]
  obtain ⟨r, hr, hRA⟩ := hE
  rw [hr]
  cases hnEA : EvmYul.Yul.evalArgs (j + 1) args.reverse code s with
  | error e =>
      rw [hnEA] at hRA
      cases r with
      | ok b => exact (hRA : False).elim
      | error f =>
          rw [Simulation.Interaction.bind_done_error]
          simp only [EvmYul.Yul.reverse']
          rw [Native.execCall_error]
          exact ⟨.error f, rfl, hRA⟩
  | ok p =>
      rw [hnEA] at hRA
      cases r with
      | error f => exact (hRA : False).elim
      | ok b =>
          have hbp : b = p := hRA
          subst b
          obtain ⟨st, a⟩ := p
          rw [Simulation.Interaction.bind_done_ok]
          simp only [EvmYul.Yul.reverse']
          rw [Native.execCall_ok_succ]
          exact doneAgrees_multifill [] (hrec st a hnEA)

theorem caseExec (hPrim : PrimBoundary) (n : Nat) (ih : BridgeIH n) :
    ∀ (stmt : Stmt) (code : Option YulContract) (s : State),
      BridgeStmt stmt → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.exec n stmt code s) (exec m stmt code s) := by
  intro stmt code s hStmt hCode hCB
  match n with
  | 0 => exact ⟨0, by rw [Native.exec_zero, Exec.zero]; exact doneAgrees_errorFail s⟩
  | k + 1 =>
    have ihk : BridgeAgreesAt k := ih k (Nat.lt_succ_self k)
    have hB0 := nativePreservesAt_of_prim hPrim
    cases stmt with
    | Block body =>
        obtain ⟨m, hs⟩ := ihk.execSeq body code s hStmt hCode hCB
        refine ⟨m + 1, ?_⟩
        rw [Native.exec_block, Exec.block_succ]
        obtain ⟨r, hr, hRA⟩ := hs
        rw [hr]
        cases hns : EvmYul.Yul.execSeq k body code s with
        | error e =>
            rw [hns] at hRA
            cases r with
            | ok b => exact (hRA : False).elim
            | error f => rw [Simulation.Interaction.bind_done_error]; exact ⟨.error f, rfl, hRA⟩
        | ok s₁ =>
            rw [hns] at hRA
            cases r with
            | error f => exact (hRA : False).elim
            | ok b =>
                have hb : b = s₁ := hRA
                subst b
                rw [Simulation.Interaction.bind_done_ok]
                exact ⟨.ok (s₁.restrictStoreTo s.store), rfl, rfl⟩
    | Let names expr? =>
        cases expr? with
        | none =>
            cases hck : EvmYul.Yul.checkDeclaration s names with
            | error e =>
                refine ⟨1, ?_⟩
                rw [Native.exec_let_none, hck, our_let_none_fail 0 names code s e hck]
                exact doneAgrees_errorFail s
            | ok u =>
                cases u
                refine ⟨1, ?_⟩
                rw [Native.exec_let_none, hck, Exec.let_none_succ 0 names code s hck]
                exact doneAgrees_pure _
        | some expr =>
            have hE : BridgeExpr expr := hStmt
            cases hck : EvmYul.Yul.checkDeclaration s names with
            | error e =>
                refine ⟨1, ?_⟩
                rw [Native.exec_let_some, hck, our_let_some_fail 0 names expr code s e hck]
                exact doneAgrees_errorFail s
            | ok u =>
                cases u
                obtain ⟨m, hv⟩ := ihk.evalValues expr code s hE hCode hCB
                refine ⟨m + 1, ?_⟩
                rw [Native.exec_let_some, hck, Exec.let_some_succ m names expr code s hck]
                exact doneAgrees_multifill names hv
    | Assign names expr =>
        have hE : BridgeExpr expr := hStmt
        cases hck : EvmYul.Yul.checkAssignment s names with
        | error e =>
            refine ⟨1, ?_⟩
            rw [Native.exec_assign, hck, our_assign_fail 0 names expr code s e hck]
            exact doneAgrees_errorFail s
        | ok u =>
            cases u
            obtain ⟨m, hv⟩ := ihk.evalValues expr code s hE hCode hCB
            refine ⟨m + 1, ?_⟩
            rw [Native.exec_assign, hck, Exec.assign_succ m names expr code s hck]
            exact doneAgrees_multifill names hv
    | If cond body =>
        have hS : bridgeExpr? cond = true ∧ bridgeStmts? body = true := by
          have h : bridgeStmt? (.If cond body) = true := hStmt
          simpa only [bridgeStmt?, Bool.and_eq_true] using h
        obtain ⟨m₁, h₁⟩ := ihk.eval cond code s hS.1 hCode hCB
        by_cases hNe : NativeSettled (EvmYul.Yul.exec (k + 1) (.If cond body) code s)
        · have hNev : NativeSettled (EvmYul.Yul.eval k cond code s) := by
            intro e he; rintro rfl
            exact (hNe .OutOfFuel (by rw [Native.exec_if, he])) rfl
          cases hev : EvmYul.Yul.eval k cond code s with
          | error e =>
              refine ⟨m₁ + 1, exec_if_close (eval_lift hNev (Nat.le_refl _) h₁)
                (fun s' c hh => by rw [hev] at hh; exact nomatch hh)⟩
          | ok p =>
              obtain ⟨s', c⟩ := p
              have hCBs' : CodeBridge s' :=
                (hB0 k).eval cond code s hS.1 hCode hCB s' c (by rw [hev])
              by_cases hc0 : c = (⟨0⟩ : Word)
              · -- condition is zero: native `If` returns `.ok s'`, body unreached.
                refine ⟨m₁ + 1, exec_if_close (eval_lift hNev (Nat.le_refl _) h₁)
                  (fun s'' c'' hh hne => ?_)⟩
                rw [hev] at hh
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj hh
                exact absurd hc0 hne
              · obtain ⟨m₂, h₂⟩ := ihk.exec (.Block body) code s' hS.2 hCode hCBs'
                by_cases hrs : NativeSettled (EvmYul.Yul.exec k (.Block body) code s')
                · refine ⟨max m₁ m₂ + 1, exec_if_close
                    (eval_lift hNev (le_max_left _ _) h₁) (fun s'' c'' hh _ => ?_)⟩
                  rw [hev] at hh
                  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj hh
                  exact exec_lift hrs (le_max_right _ _) h₂
                · refine ⟨0, ?_⟩
                  simp only [NativeSettled, not_forall, not_not] at hrs
                  obtain ⟨e, he, rfl⟩ := hrs
                  have hw : EvmYul.Yul.exec (k + 1) (.If cond body) code s = .error .OutOfFuel := by
                    simp only [Native.exec_if, hev]
                    rw [if_pos (show c ≠ (⟨0⟩ : Word) from hc0), he]
                  rw [Exec.zero, hw]
                  exact doneAgrees_fail_outOfFuel s
        · refine ⟨0, ?_⟩
          simp only [NativeSettled, not_forall, not_not] at hNe
          obtain ⟨e, he, rfl⟩ := hNe
          rw [Exec.zero, he]
          exact doneAgrees_fail_outOfFuel s
    | ExprStmtCall e =>
        cases e with
        | Var id =>
            refine ⟨1, ?_⟩
            rw [Native.exec_expr_var, our_expr_var_fail 0 id code s]
            exact doneAgrees_error s
        | Lit v =>
            refine ⟨1, ?_⟩
            rw [Native.exec_expr_lit, our_expr_lit_fail 0 v code s]
            exact doneAgrees_error s
        | Call sop args =>
            cases sop with
            | inl op =>
                have hE : BridgeExpr (.Call (.inl op) args) := hStmt
                obtain ⟨m, hv⟩ := caseEvalValues hPrim (k + 1) ih (.Call (.inl op) args) code s hE hCode hCB
                refine ⟨m, ?_⟩
                rw [exec_exprPrim_eq, Exec.expr_primitive]
                exact doneAgrees_multifill [] hv
            | inr fn =>
                have hBArgs : BridgeExprs args.reverse := bridgeExprs?_reverse hStmt
                cases k with
                | zero =>
                    refine ⟨0, ?_⟩
                    have hw : EvmYul.Yul.exec 1 (.ExprStmtCall (.Call (.inr fn) args)) code s = .error .OutOfFuel := by
                      rw [Native.exec_expr_internal, Native.evalArgs_zero]
                      simp only [EvmYul.Yul.reverse']
                      rw [Native.execCall_error]
                    rw [Exec.zero, hw]
                    exact doneAgrees_fail_outOfFuel s
                | succ j =>
                    obtain ⟨m₁, hE⟩ := ihk.evalArgs args.reverse code s hBArgs hCode hCB
                    by_cases hNe : NativeSettled (EvmYul.Yul.exec (j + 2) (.ExprStmtCall (.Call (.inr fn) args)) code s)
                    · have hNea : NativeSettled (EvmYul.Yul.evalArgs (j + 1) args.reverse code s) := by
                        intro e he; rintro rfl
                        refine (hNe .OutOfFuel ?_) rfl
                        rw [show j + 2 = (j + 1) + 1 from rfl, Native.exec_expr_internal, he]
                        simp only [EvmYul.Yul.reverse']
                        rw [Native.execCall_error]
                      cases hns : EvmYul.Yul.evalArgs (j + 1) args.reverse code s with
                      | error e =>
                          refine ⟨m₁ + 2, exec_exprInternal_close
                            (evalArgs_lift hNea (Nat.le_succ m₁) hE)
                            (fun st a hh => by rw [hns] at hh; exact nomatch hh)⟩
                      | ok p =>
                          obtain ⟨st, a⟩ := p
                          have hCBst : CodeBridge st :=
                            (hB0 (j + 1)).evalArgs args.reverse code s hBArgs hCode hCB st a (by rw [hns])
                          obtain ⟨m₂, hc⟩ := (ih j (by omega)).call a.reverse (some fn) code st hCode hCBst
                          have hNc : NativeSettled (EvmYul.Yul.call j a.reverse (some fn) code st) := by
                            intro e he; rintro rfl
                            refine (hNe .OutOfFuel ?_) rfl
                            rw [show j + 2 = (j + 1) + 1 from rfl, Native.exec_expr_internal, hns]
                            simp only [EvmYul.Yul.reverse']
                            rw [Native.execCall_ok_succ, he]
                            simp only [EvmYul.Yul.multifill']
                          refine ⟨max m₁ m₂ + 2, exec_exprInternal_close
                            (evalArgs_lift hNea (by omega) hE) (fun st' a' hh => ?_)⟩
                          rw [hns] at hh
                          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj hh
                          exact call_lift hNc (le_max_right _ _) hc
                    · refine ⟨0, ?_⟩
                      simp only [NativeSettled, not_forall, not_not] at hNe
                      obtain ⟨e, he, rfl⟩ := hNe
                      rw [Exec.zero, he]
                      exact doneAgrees_fail_outOfFuel s
    | Switch cond cases' default' =>
        have hS : (bridgeExpr? cond = true ∧ bridgeCases? cases' = true) ∧
            bridgeStmts? default' = true := by
          have h : bridgeStmt? (.Switch cond cases' default') = true := hStmt
          simpa only [bridgeStmt?, Bool.and_eq_true] using h
        obtain ⟨m₁, h₁⟩ := ihk.eval cond code s hS.1.1 hCode hCB
        by_cases hNe : NativeSettled (EvmYul.Yul.exec (k + 1) (.Switch cond cases' default') code s)
        · have hNev : NativeSettled (EvmYul.Yul.eval k cond code s) := by
            intro e he; rintro rfl
            exact (hNe .OutOfFuel (by rw [Native.exec_switch, he])) rfl
          cases hev : EvmYul.Yul.eval k cond code s with
          | error e =>
              refine ⟨m₁ + 1, exec_switch_close (eval_lift hNev (Nat.le_refl _) h₁)
                (fun s' c hh => by rw [hev] at hh; exact nomatch hh)⟩
          | ok p =>
              obtain ⟨s', c⟩ := p
              have hCBs' : CodeBridge s' :=
                (hB0 k).eval cond code s hS.1.1 hCode hCB s' c (by rw [hev])
              have hsel : BridgeStmts (EvmYul.Yul.selectSwitchCase c default' cases') :=
                bridgeStmts_selectSwitchCase hS.1.2 hS.2 c
              obtain ⟨m₂, h₂⟩ := ihk.exec (.Block (EvmYul.Yul.selectSwitchCase c default' cases'))
                code s' hsel hCode hCBs'
              by_cases hrs : NativeSettled (EvmYul.Yul.exec k
                  (.Block (EvmYul.Yul.selectSwitchCase c default' cases')) code s')
              · refine ⟨max m₁ m₂ + 1, exec_switch_close
                  (eval_lift hNev (le_max_left _ _) h₁) (fun s'' c'' hh => ?_)⟩
                rw [hev] at hh
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj hh
                exact exec_lift hrs (le_max_right _ _) h₂
              · refine ⟨0, ?_⟩
                simp only [NativeSettled, not_forall, not_not] at hrs
                obtain ⟨e, he, rfl⟩ := hrs
                have hw : EvmYul.Yul.exec (k + 1) (.Switch cond cases' default') code s = .error .OutOfFuel := by
                  simp only [Native.exec_switch, hev]; rw [he]
                rw [Exec.zero, hw]
                exact doneAgrees_fail_outOfFuel s
        · refine ⟨0, ?_⟩
          simp only [NativeSettled, not_forall, not_not] at hNe
          obtain ⟨e, he, rfl⟩ := hNe
          rw [Exec.zero, he]
          exact doneAgrees_fail_outOfFuel s
    | For cond post body =>
        have h4 : ((bridgeExpr? cond = true ∧ bridgeStmts? post = true) ∧
            breakContinueFreeStmts? post = true) ∧ bridgeStmts? body = true := by
          have h : bridgeStmt? (.For cond post body) = true := hStmt
          simpa only [bridgeStmt?, Bool.and_eq_true] using h
        obtain ⟨m, hl⟩ := ihk.loop cond post body code s h4.1.1.1 h4.1.1.2 h4.1.2 h4.2 hCode hCB
        refine ⟨m + 1, ?_⟩
        rw [Native.exec_for, Exec.for_succ]
        exact hl
    | Continue =>
        refine ⟨1, ?_⟩
        rw [Native.exec_continue, Exec.cont_succ 0 code s]
        exact doneAgrees_pure _
    | Break =>
        refine ⟨1, ?_⟩
        rw [Native.exec_break, Exec.brk_succ 0 code s]
        exact doneAgrees_pure _
    | Leave =>
        refine ⟨1, ?_⟩
        rw [Native.exec_leave, Exec.leave_succ 0 code s]
        exact doneAgrees_pure _

/-! ### `caseLoop`

Mirrors native `loop_succ_succ` / our `Exec.loop_succ_succ`. `loopGlue` glues one
iteration at a common our fuel `M`, taking the four leaf agreements (eval /
body-exec / post-exec / For-exec) as conditional functions and using Part B0
(`nativePreservesAt_of_prim`) to prune the impossible checkpoint arms
(`OutOfFuel`-state, and — via `BreakContinueFreeStmts post` — a `Break`/`Continue`
post result). `caseLoop` descends the native `.ok` chain obtaining and lifting
those witnesses. -/

/-- Body-result states from which native `loop` actually runs the post block (all
other outcomes are settled leaves). Lets `loopGlue`'s post agreement be demanded
only where it is used. -/
def IsPostReaching : State → Prop
  | .Ok _ _ => True
  | .Checkpoint (.Continue _ _) => True
  | _ => False

/-- Post-result states from which native `loop` runs the recursive `For` step. -/
def IsForReaching : State → Prop
  | .Ok _ _ => True
  | _ => False

private theorem loopGlue {j M : Nat} {cond : Expr} {post body : List Stmt}
    {code : Option YulContract} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (hPrim : PrimBoundary) (hCond : BridgeExpr cond) (hPost : BridgeStmts post)
    (hPostBC : BreakContinueFreeStmts post) (hBody : BridgeStmts body)
    (hCode : BridgeCode code) (hp : OwnerPresent shared)
    (hE : DoneAgrees (EvmYul.Yul.eval j cond code (.Ok shared store))
      (eval M cond code (.Ok shared store)))
    (hBfun : ∀ s₁ x, EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁, x) →
      x ≠ (⟨0⟩ : Word) →
      DoneAgrees (EvmYul.Yul.exec j (.Block body) code s₁) (exec M (.Block body) code s₁))
    (hPfun : ∀ s₁ x s₂, EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁, x) →
      x ≠ (⟨0⟩ : Word) →
      EvmYul.Yul.exec j (.Block body) code s₁ = .ok s₂ → IsPostReaching s₂ →
      DoneAgrees (EvmYul.Yul.exec j (.Block post) code s₂.reviveJump)
        (exec M (.Block post) code s₂.reviveJump))
    (hFfun : ∀ s₁ x s₂ s₃, EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁, x) →
      x ≠ (⟨0⟩ : Word) →
      EvmYul.Yul.exec j (.Block body) code s₁ = .ok s₂ → IsPostReaching s₂ →
      EvmYul.Yul.exec j (.Block post) code s₂.reviveJump = .ok s₃ → IsForReaching s₃ →
      DoneAgrees
        (EvmYul.Yul.exec j (.For cond post body) code (s₃.overwrite? (.Ok shared store)))
        (exec M (.For cond post body) code (s₃.overwrite? (.Ok shared store)))) :
    DoneAgrees (EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store))
      (loop (M + 1 + 1) cond post body code (.Ok shared store)) := by
  have ihj : NativePreservesAt j := nativePreservesAt_of_prim hPrim j
  have hCB0 : CodeBridge (EvmYul.Yul.State.Ok shared store) := codeBridge_okState hp
  rw [Native.loop_succ_succ, Exec.loop_succ_succ M]
  simp only [stateModel, id_eq,
    show EvmYul.Yul.State.mkOk (EvmYul.Yul.State.Ok shared store) =
      EvmYul.Yul.State.Ok shared store from rfl]
  obtain ⟨rE, hrE, hRAE⟩ := hE
  rw [hrE]
  cases hev : EvmYul.Yul.eval j cond code (.Ok shared store) with
  | error e =>
      rw [hev] at hRAE
      cases rE with
      | ok b => exact (hRAE : False).elim
      | error f => simp only [Simulation.Interaction.bind_done_error]; exact ⟨.error f, rfl, hRAE⟩
  | ok p =>
      rw [hev] at hRAE
      cases rE with
      | error f => exact (hRAE : False).elim
      | ok b =>
          have hbp : b = p := hRAE
          subst b
          obtain ⟨s₁, x⟩ := p
          have hCBs₁ : CodeBridge s₁ := ihj.eval cond code _ hCond hCode hCB0 s₁ x hev
          simp only [Simulation.Interaction.bind_done_ok]
          simp only [show EvmYul.UInt256.ofNat 0 = (⟨0⟩ : Word) from rfl]
          by_cases hx : x = (⟨0⟩ : Word)
          · simp only [if_pos hx]
            exact ⟨.ok _, rfl, rfl⟩
          · simp only [if_neg hx]
            -- body bind
            obtain ⟨rB, hrB, hRAB⟩ := hBfun s₁ x hev hx
            rw [hrB]
            cases hbd : EvmYul.Yul.exec j (.Block body) code s₁ with
            | error e =>
                rw [hbd] at hRAB
                cases rB with
                | ok b => exact (hRAB : False).elim
                | error f => simp only [Simulation.Interaction.bind_done_error]; exact ⟨.error f, rfl, hRAB⟩
            | ok s₂ =>
                rw [hbd] at hRAB
                cases rB with
                | error f => exact (hRAB : False).elim
                | ok b =>
                    have hbeq : b = s₂ := hRAB
                    subst b
                    simp only [Simulation.Interaction.bind_done_ok]
                    have hSB₂ := (ihj.exec (.Block body) code s₁ hBody hCode hCBs₁ s₂ hbd).1
                    cases s₂ with
                    | OutOfFuel => exact (hSB₂ : False).elim
                    | Checkpoint jj =>
                        cases jj with
                        | Break sh st => exact ⟨.ok _, rfl, rfl⟩
                        | Leave sh st => exact ⟨.ok _, rfl, rfl⟩
                        | Continue sh st =>
                            obtain ⟨rP, hrP, hRAP⟩ := hPfun s₁ x _ hev hx hbd trivial
                            rw [hrP]
                            have hCBentry : CodeBridge
                                (EvmYul.Yul.State.Checkpoint (.Continue sh st)).reviveJump :=
                              codeBridge_reviveJump hSB₂
                            cases hpo : EvmYul.Yul.exec j (.Block post) code
                                (EvmYul.Yul.State.Checkpoint (.Continue sh st)).reviveJump with
                            | error e =>
                                rw [hpo] at hRAP
                                cases rP with
                                | ok b => exact (hRAP : False).elim
                                | error f =>
                                    simp only [Simulation.Interaction.bind_done_error]
                                    exact ⟨.error f, rfl, hRAP⟩
                            | ok s₃ =>
                                rw [hpo] at hRAP
                                cases rP with
                                | error f => exact (hRAP : False).elim
                                | ok b =>
                                    have hb3 : b = s₃ := hRAP
                                    subst b
                                    simp only [Simulation.Interaction.bind_done_ok]
                                    have hpres := ihj.exec (.Block post) code _ hPost hCode
                                      hCBentry s₃ hpo
                                    have hnbc₃ := hpres.2 hPostBC
                                    cases s₃ with
                                    | OutOfFuel => exact (hpres.1 : False).elim
                                    | Checkpoint jj2 =>
                                        cases jj2 with
                                        | Break _ _ => exact absurd trivial hnbc₃
                                        | Continue _ _ => exact absurd trivial hnbc₃
                                        | Leave _ _ => exact ⟨.ok _, rfl, rfl⟩
                                    | Ok sh3 st3 =>
                                        obtain ⟨rF, hrF, hRAF⟩ :=
                                          hFfun s₁ x _ (EvmYul.Yul.State.Ok sh3 st3) hev hx hbd trivial hpo trivial
                                        rw [hrF]
                                        cases hfr : EvmYul.Yul.exec j (.For cond post body) code
                                            ((EvmYul.Yul.State.Ok sh3 st3).overwrite?
                                              (EvmYul.Yul.State.Ok shared store)) with
                                        | error e =>
                                            rw [hfr] at hRAF
                                            cases rF with
                                            | ok b => exact (hRAF : False).elim
                                            | error f =>
                                                simp only [Simulation.Interaction.bind_done_error]
                                                exact ⟨.error f, rfl, hRAF⟩
                                        | ok s₅ =>
                                            rw [hfr] at hRAF
                                            cases rF with
                                            | error f => exact (hRAF : False).elim
                                            | ok b =>
                                                have hb5 : b = s₅ := hRAF
                                                subst b
                                                simp only [Simulation.Interaction.bind_done_ok]
                                                exact ⟨.ok _, rfl, rfl⟩
                    | Ok sh st =>
                        obtain ⟨rP, hrP, hRAP⟩ := hPfun s₁ x _ hev hx hbd trivial
                        rw [hrP]
                        have hCBentry : CodeBridge (EvmYul.Yul.State.Ok sh st).reviveJump :=
                          codeBridge_reviveJump hSB₂
                        cases hpo : EvmYul.Yul.exec j (.Block post) code
                            (EvmYul.Yul.State.Ok sh st).reviveJump with
                        | error e =>
                            rw [hpo] at hRAP
                            cases rP with
                            | ok b => exact (hRAP : False).elim
                            | error f =>
                                simp only [Simulation.Interaction.bind_done_error]
                                exact ⟨.error f, rfl, hRAP⟩
                        | ok s₃ =>
                            rw [hpo] at hRAP
                            cases rP with
                            | error f => exact (hRAP : False).elim
                            | ok b =>
                                have hb3 : b = s₃ := hRAP
                                subst b
                                simp only [Simulation.Interaction.bind_done_ok]
                                have hpres := ihj.exec (.Block post) code _ hPost hCode
                                  hCBentry s₃ hpo
                                have hnbc₃ := hpres.2 hPostBC
                                cases s₃ with
                                | OutOfFuel => exact (hpres.1 : False).elim
                                | Checkpoint jj2 =>
                                    cases jj2 with
                                    | Break _ _ => exact absurd trivial hnbc₃
                                    | Continue _ _ => exact absurd trivial hnbc₃
                                    | Leave _ _ => exact ⟨.ok _, rfl, rfl⟩
                                | Ok sh3 st3 =>
                                    obtain ⟨rF, hrF, hRAF⟩ :=
                                      hFfun s₁ x _ (EvmYul.Yul.State.Ok sh3 st3) hev hx hbd trivial hpo trivial
                                    rw [hrF]
                                    cases hfr : EvmYul.Yul.exec j (.For cond post body) code
                                        ((EvmYul.Yul.State.Ok sh3 st3).overwrite?
                                          (EvmYul.Yul.State.Ok shared store)) with
                                    | error e =>
                                        rw [hfr] at hRAF
                                        cases rF with
                                        | ok b => exact (hRAF : False).elim
                                        | error f =>
                                            simp only [Simulation.Interaction.bind_done_error]
                                            exact ⟨.error f, rfl, hRAF⟩
                                    | ok s₅ =>
                                        rw [hfr] at hRAF
                                        cases rF with
                                        | error f => exact (hRAF : False).elim
                                        | ok b =>
                                            have hb5 : b = s₅ := hRAF
                                            subst b
                                            simp only [Simulation.Interaction.bind_done_ok]
                                            exact ⟨.ok _, rfl, rfl⟩

/-- Show the whole native loop is `OutOfFuel` from any reached sub being
`OutOfFuel`; used to route those paths to the witness-`0` (`Exec.loop_zero`) leaf. -/
private theorem loop_oof_of_eval {j : Nat} {cond : Expr} {post body : List Stmt}
    {code : Option YulContract} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (he : EvmYul.Yul.eval j cond code (.Ok shared store) = .error .OutOfFuel) :
    EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store) = .error .OutOfFuel := by
  rw [Native.loop_succ_succ,
    show EvmYul.Yul.State.mkOk (EvmYul.Yul.State.Ok shared store) =
      EvmYul.Yul.State.Ok shared store from rfl, he]

private theorem loop_oof_of_body {j : Nat} {cond : Expr} {post body : List Stmt}
    {code : Option YulContract} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore} {s₁ : State} {x : Word}
    (hev : EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁, x))
    (hx : x ≠ (⟨0⟩ : Word))
    (hb : EvmYul.Yul.exec j (.Block body) code s₁ = .error .OutOfFuel) :
    EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store) = .error .OutOfFuel := by
  rw [Native.loop_succ_succ,
    show EvmYul.Yul.State.mkOk (EvmYul.Yul.State.Ok shared store) =
      EvmYul.Yul.State.Ok shared store from rfl, hev]
  simp only [hx, if_false, hb, reduceIte]

private theorem loop_oof_of_post {j : Nat} {cond : Expr} {post body : List Stmt}
    {code : Option YulContract} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore} {s₁ : State} {x : Word} {s₂ : State}
    (hev : EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁, x))
    (hx : x ≠ (⟨0⟩ : Word))
    (hb : EvmYul.Yul.exec j (.Block body) code s₁ = .ok s₂)
    (hpr : IsPostReaching s₂)
    (hp : EvmYul.Yul.exec j (.Block post) code s₂.reviveJump = .error .OutOfFuel) :
    EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store) = .error .OutOfFuel := by
  rw [Native.loop_succ_succ,
    show EvmYul.Yul.State.mkOk (EvmYul.Yul.State.Ok shared store) =
      EvmYul.Yul.State.Ok shared store from rfl, hev]
  simp only [hx, reduceIte, hb]
  cases s₂ with
  | OutOfFuel => exact hpr.elim
  | Ok sh st => simp only [hp]
  | Checkpoint jj =>
      cases jj with
      | Continue sh st => simp only [hp]
      | Break sh st => exact hpr.elim
      | Leave sh st => exact hpr.elim

private theorem loop_oof_of_for {j : Nat} {cond : Expr} {post body : List Stmt}
    {code : Option YulContract} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore} {s₁ : State} {x : Word} {s₂ s₃ : State}
    (hev : EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁, x))
    (hx : x ≠ (⟨0⟩ : Word))
    (hb : EvmYul.Yul.exec j (.Block body) code s₁ = .ok s₂)
    (hpr : IsPostReaching s₂)
    (hp : EvmYul.Yul.exec j (.Block post) code s₂.reviveJump = .ok s₃)
    (hfr : IsForReaching s₃)
    (hf : EvmYul.Yul.exec j (.For cond post body) code (s₃.overwrite? (.Ok shared store)) =
      .error .OutOfFuel) :
    EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store) = .error .OutOfFuel := by
  have hpostFor :
      (match EvmYul.Yul.exec j (.Block post) code s₂.reviveJump with
       | .error e => (.error e : Except EvmYul.Yul.Exception State)
       | .ok s₃ => match s₃ with
           | .OutOfFuel => .ok (s₃.overwrite? (.Ok shared store))
           | .Checkpoint (.Leave _ _) => .ok (s₃.overwrite? (.Ok shared store))
           | _ => match EvmYul.Yul.exec j (.For cond post body) code
                     (s₃.overwrite? (.Ok shared store)) with
               | .error e => .error e
               | .ok s₅ => .ok (s₅.overwrite? (.Ok shared store))) = .error .OutOfFuel := by
    rw [hp]
    cases s₃ with
    | OutOfFuel => exact hfr.elim
    | Ok sh st => simp only [hf]
    | Checkpoint jj => cases jj <;> exact hfr.elim
  rw [Native.loop_succ_succ,
    show EvmYul.Yul.State.mkOk (EvmYul.Yul.State.Ok shared store) =
      EvmYul.Yul.State.Ok shared store from rfl, hev]
  simp only [hx, reduceIte, hb]
  cases s₂ with
  | OutOfFuel => exact hpr.elim
  | Ok sh st => exact hpostFor
  | Checkpoint jj =>
      cases jj with
      | Continue sh st => exact hpostFor
      | Break sh st => exact hpr.elim
      | Leave sh st => exact hpr.elim

theorem caseLoop (hPrim : PrimBoundary) (n : Nat) (ih : BridgeIH n) :
    ∀ (cond : Expr) (post body : List Stmt) (code : Option YulContract) (s : State),
      BridgeExpr cond → BridgeStmts post → BreakContinueFreeStmts post →
      BridgeStmts body → BridgeCode code → CodeBridge s →
      ∃ m, DoneAgrees (EvmYul.Yul.loop n cond post body code s) (loop m cond post body code s) := by
  intro cond post body code s hCond hPost hPostBC hBody hCode hCB
  match n with
  | 0 => exact ⟨0, by rw [Native.loop_zero, Exec.loop_zero]; exact doneAgrees_errorFail s⟩
  | 1 => exact ⟨0, by rw [Native.loop_one, Exec.loop_zero]; exact doneAgrees_errorFail s⟩
  | j + 1 + 1 =>
      have hj : j < j + 1 + 1 := by omega
      have hB0 : ∀ k, NativePreservesAt k := nativePreservesAt_of_prim hPrim
      obtain ⟨shared, store, rfl, hp⟩ := codeBridge_ok hCB
      have hCB0 : CodeBridge (EvmYul.Yul.State.Ok shared store) := codeBridge_okState hp
      have hForB : BridgeStmt (.For cond post body) := by
        show bridgeStmt? (.For cond post body) = true
        simp only [bridgeStmt?, Bool.and_eq_true]; exact ⟨⟨⟨hCond, hPost⟩, hPostBC⟩, hBody⟩
      have oof : EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store) =
            .error .OutOfFuel →
          ∃ m, DoneAgrees (EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store))
            (loop m cond post body code (.Ok shared store)) :=
        fun hw => ⟨0, by rw [Exec.loop_zero, hw]; exact doneAgrees_fail_outOfFuel _⟩
      obtain ⟨mE, hE0⟩ := (ih j hj).eval cond code (.Ok shared store) hCond hCode hCB0
      by_cases hEs : NativeSettled (EvmYul.Yul.eval j cond code (.Ok shared store))
      case neg =>
        simp only [NativeSettled, not_forall, not_not] at hEs
        obtain ⟨e, he, rfl⟩ := hEs
        exact oof (loop_oof_of_eval he)
      -- eval settled.
      cases hev : EvmYul.Yul.eval j cond code (.Ok shared store) with
      | error e =>
          exact ⟨mE + 1 + 1, loopGlue hPrim hCond hPost hPostBC hBody hCode hp hE0
            (fun _ _ heq _ => by simp only [hev, reduceCtorEq] at heq)
            (fun _ _ _ heq _ _ _ => by simp only [hev, reduceCtorEq] at heq)
            (fun _ _ _ _ heq _ _ _ _ _ => by simp only [hev, reduceCtorEq] at heq)⟩
      | ok p =>
          obtain ⟨s₁, x⟩ := p
          have hCBs₁ : CodeBridge s₁ := (hB0 j).eval cond code _ hCond hCode hCB0 s₁ x hev
          have hES : NativeSettled (EvmYul.Yul.eval j cond code (.Ok shared store)) := by
            rw [hev]; exact NativeSettled.ok _
          by_cases hx0 : x = (⟨0⟩ : Word)
          · -- x = 0: eval leaf; all sub-funs excluded by their `x ≠ 0` hypothesis.
            refine ⟨mE + 1 + 1, loopGlue hPrim hCond hPost hPostBC hBody hCode hp hE0
              (fun s₁' x' heq hx' => by
                rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                exact absurd hx0 hx')
              (fun s₁' x' _ heq hx' _ _ => by
                rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                exact absurd hx0 hx')
              (fun s₁' x' _ _ heq hx' _ _ _ _ => by
                rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                exact absurd hx0 hx')⟩
          · -- x ≠ 0: run body.
            obtain ⟨mB, hB0'⟩ := (ih j hj).exec (.Block body) code s₁ hBody hCode hCBs₁
            by_cases hBs : NativeSettled (EvmYul.Yul.exec j (.Block body) code s₁)
            case neg =>
              simp only [NativeSettled, not_forall, not_not] at hBs
              obtain ⟨e, he, rfl⟩ := hBs
              exact oof (loop_oof_of_body hev hx0 he)
            -- body settled; the shared eval+body agreements at fuel `mB` slack.
            have hEb : ∀ s₁' x', EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁', x') →
                x' ≠ (⟨0⟩ : Word) →
                DoneAgrees (EvmYul.Yul.exec j (.Block body) code s₁')
                  (exec (max mE mB) (.Block body) code s₁') := by
              intro s₁' x' heq _
              rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
              exact exec_lift hBs (by omega) hB0'
            cases hbd : EvmYul.Yul.exec j (.Block body) code s₁ with
            | error e =>
                exact ⟨max mE mB + 1 + 1, loopGlue hPrim hCond hPost hPostBC hBody hCode hp
                  (eval_lift hES (by omega) hE0) hEb
                  (fun s₁' x' s₂ heq _ hbd' _ => by
                    rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                    rw [hbd] at hbd'; exact nomatch hbd')
                  (fun s₁' x' s₂ s₃ heq _ hbd' _ _ _ => by
                    rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                    rw [hbd] at hbd'; exact nomatch hbd')⟩
            | ok s₂ =>
                have hSB₂ := ((hB0 j).exec (.Block body) code s₁ hBody hCode hCBs₁ s₂ hbd).1
                -- Break / Leave: settled leaf, post/For excluded by `IsPostReaching`.
                have leafBL : ¬ IsPostReaching s₂ →
                    ∃ m, DoneAgrees (EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store))
                      (loop m cond post body code (.Ok shared store)) := by
                  intro hnr
                  exact ⟨max mE mB + 1 + 1, loopGlue hPrim hCond hPost hPostBC hBody hCode hp
                    (eval_lift hES (by omega) hE0) hEb
                    (fun s₁' x' s₂' heq _ hbd' hr => by
                      rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                      rw [hbd] at hbd'; obtain rfl := Except.ok.inj hbd'; exact absurd hr hnr)
                    (fun s₁' x' s₂' s₃ heq _ hbd' hr _ _ => by
                      rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                      rw [hbd] at hbd'; obtain rfl := Except.ok.inj hbd'; exact absurd hr hnr)⟩
                have hCBrev : CodeBridge s₂.reviveJump := codeBridge_reviveJump hSB₂
                obtain ⟨mP, hP0⟩ := (ih j hj).exec (.Block post) code s₂.reviveJump hPost hCode hCBrev
                have hPreach : IsPostReaching s₂ →
                    ∃ m, DoneAgrees (EvmYul.Yul.loop (j + 1 + 1) cond post body code (.Ok shared store))
                      (loop m cond post body code (.Ok shared store)) := by
                  intro hReach
                  by_cases hPs : NativeSettled (EvmYul.Yul.exec j (.Block post) code s₂.reviveJump)
                  case neg =>
                    simp only [NativeSettled, not_forall, not_not] at hPs
                    obtain ⟨e, he, rfl⟩ := hPs
                    exact oof (loop_oof_of_post hev hx0 hbd hReach he)
                  have hEb' : ∀ s₁' x', EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁', x') →
                      x' ≠ (⟨0⟩ : Word) →
                      DoneAgrees (EvmYul.Yul.exec j (.Block body) code s₁')
                        (exec (max (max mE mB) mP) (.Block body) code s₁') := by
                    intro s₁' x' heq _
                    rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                    exact exec_lift hBs (by omega) hB0'
                  have hPeq : ∀ s₁' x' s₂', EvmYul.Yul.eval j cond code (.Ok shared store) = .ok (s₁', x') →
                      x' ≠ (⟨0⟩ : Word) → EvmYul.Yul.exec j (.Block body) code s₁' = .ok s₂' →
                      IsPostReaching s₂' →
                      DoneAgrees (EvmYul.Yul.exec j (.Block post) code s₂'.reviveJump)
                        (exec (max (max mE mB) mP) (.Block post) code s₂'.reviveJump) := by
                    intro s₁' x' s₂' heq _ hbd' _
                    rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                    rw [hbd] at hbd'; obtain rfl := Except.ok.inj hbd'
                    exact exec_lift hPs (by omega) hP0
                  cases hpo : EvmYul.Yul.exec j (.Block post) code s₂.reviveJump with
                  | error e =>
                      exact ⟨max (max mE mB) mP + 1 + 1, loopGlue hPrim hCond hPost hPostBC hBody
                        hCode hp (eval_lift hES (by omega) hE0) hEb' hPeq
                        (fun s₁' x' s₂' s₃ heq _ hbd' _ hpo' _ => by
                          rw [hev] at heq; obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                          rw [hbd] at hbd'; obtain rfl := Except.ok.inj hbd'
                          rw [hpo] at hpo'; exact nomatch hpo')⟩
                  | ok s₃ =>
                      have hpres3 := (hB0 j).exec (.Block post) code s₂.reviveJump hPost hCode
                        hCBrev s₃ hpo
                      have hSB₃ := hpres3.1
                      have hnbc₃ := hpres3.2 hPostBC
                      cases s₃ with
                      | OutOfFuel => exact (hSB₃ : False).elim
                      | Checkpoint jj =>
                          cases jj with
                          | Break sh st => exact absurd trivial hnbc₃
                          | Continue sh st => exact absurd trivial hnbc₃
                          | Leave sh st =>
                              -- `Leave` post result: the loop is a settled leaf; For excluded.
                              exact ⟨max (max mE mB) mP + 1 + 1, loopGlue hPrim hCond hPost hPostBC
                                hBody hCode hp (eval_lift hES (by omega) hE0) hEb' hPeq
                                (fun s₁' x' s₂' s₃' heq _ hbd' _ hpo' hfr => by
                                  rw [hev] at heq
                                  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                                  rw [hbd] at hbd'; obtain rfl := Except.ok.inj hbd'
                                  rw [hpo] at hpo'; obtain rfl := Except.ok.inj hpo'
                                  exact hfr.elim)⟩
                      | Ok sh3 st3 =>
                          have hCBfor : CodeBridge
                              ((EvmYul.Yul.State.Ok sh3 st3).overwrite? (.Ok shared store)) := hSB₃
                          obtain ⟨mF, hF0⟩ := (ih j hj).exec (.For cond post body) code
                            ((EvmYul.Yul.State.Ok sh3 st3).overwrite? (.Ok shared store)) hForB hCode
                            hCBfor
                          by_cases hFs : NativeSettled (EvmYul.Yul.exec j (.For cond post body) code
                              ((EvmYul.Yul.State.Ok sh3 st3).overwrite? (.Ok shared store)))
                          case neg =>
                            simp only [NativeSettled, not_forall, not_not] at hFs
                            obtain ⟨e, he, rfl⟩ := hFs
                            exact oof (loop_oof_of_for hev hx0 hbd hReach hpo trivial he)
                          exact ⟨max (max mE mB) (max mP mF) + 1 + 1, loopGlue hPrim hCond hPost
                            hPostBC hBody hCode hp (eval_lift hES (by omega) hE0)
                            (fun s₁' x' heq _ => by
                              rw [hev] at heq
                              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                              exact exec_lift hBs (by omega) hB0')
                            (fun s₁' x' s₂' heq _ hbd' _ => by
                              rw [hev] at heq
                              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                              rw [hbd] at hbd'; obtain rfl := Except.ok.inj hbd'
                              exact exec_lift hPs (by omega) hP0)
                            (fun s₁' x' s₂' s₃' heq _ hbd' _ hpo' _ => by
                              rw [hev] at heq
                              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj heq
                              rw [hbd] at hbd'; obtain rfl := Except.ok.inj hbd'
                              rw [hpo] at hpo'; obtain rfl := Except.ok.inj hpo'
                              exact exec_lift hFs (by omega) hF0)⟩
                -- dispatch on whether s₂ reaches the post block.
                cases s₂ with
                | OutOfFuel => exact (hSB₂ : False).elim
                | Ok sh st => exact hPreach trivial
                | Checkpoint jj =>
                    cases jj with
                    | Continue sh st => exact hPreach trivial
                    | Break sh st => exact leafBL (by intro h; exact h)
                    | Leave sh st => exact leafBL (by intro h; exact h)

end KnotProper

end VerityBridge
end Yul
end EvmCompiler
