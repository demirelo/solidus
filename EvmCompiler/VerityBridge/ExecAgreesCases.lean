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

end PartB0

end VerityBridge
end Yul
end EvmCompiler
