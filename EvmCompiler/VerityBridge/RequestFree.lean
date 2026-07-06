import EvmCompiler.Yul.InteractionSemantics

/-!
# Request-free (bridge) op surface for the Verity interpreter-equivalence bridge

This file freezes the predicates and outcome relations for Phase 3 (workstreams
W0/W1 of `VERITY_PHASE3.md`).

The bridge is a *request-free degeneration* theorem, not a simulation: on the
fragment Verity emits, `Primitive.openEval` never `.request`s, so our interaction
tree is a single `.done` leaf whose value mirrors native `EvmYul.Yul.primCall`.

`BridgeOp` (naming per the plan's "naming honesty" note — it excludes more than
requests) is the set of ops that `openEval` answers as a native-agreeing `.done`:

* not an external call/create kind (`Simulation.ExternalKind.ofYulOperation? = none`)
  — those `.request` an external world exchange;
* not `GAS`/`MSIZE` — those `.request .resource`;
* not `EXTCODEHASH` — `closedEval` overrides it via `CodeErasedState.extCodeHash`,
  so it is request-free but NOT native-agreeing (folded into the predicate, never
  special-cased in a proof).
-/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

open EvmYul (Operation)

/-! ## The primitive-op predicate and its computable twin -/

/-- Ops `openEval` answers with a native-agreeing `.done` leaf. -/
def BridgeOp (op : Operation .Yul) : Prop :=
  Simulation.ExternalKind.ofYulOperation? op = none ∧
    op ≠ .StackMemFlow .GAS ∧
    op ≠ .StackMemFlow .MSIZE ∧
    op ≠ .Env .EXTCODEHASH

/-- Computable twin of `BridgeOp`. -/
def bridgeOp? (op : Operation .Yul) : Bool :=
  (Simulation.ExternalKind.ofYulOperation? op).isNone &&
    decide (op ≠ .StackMemFlow .GAS) &&
    decide (op ≠ .StackMemFlow .MSIZE) &&
    decide (op ≠ .Env .EXTCODEHASH)

@[simp] theorem bridgeOp?_iff (op : Operation .Yul) :
    bridgeOp? op = true ↔ BridgeOp op := by
  simp only [bridgeOp?, BridgeOp, Bool.and_eq_true, Option.isNone_iff_eq_none,
    decide_eq_true_eq]
  tauto

instance (op : Operation .Yul) : Decidable (BridgeOp op) :=
  decidable_of_iff _ (bridgeOp?_iff op)

/-! ## Structural lifts over the Yul AST

Bool twins are the primitive definitions; the `Prop` lifts are their `= true`
graphs, so each `iff` lemma is definitional. This keeps the W3 induction free to
unfold either layer with `simp`. -/

open EvmYul.Yul.Ast

/-! ### Break/continue-free loop posts

Discovered boundary (stage 5): when a For-loop's *post* block yields a
`Break`/`Continue` checkpoint, native `loop` recurses into `exec (.For …)` from
that **Checkpoint** state; the recursion restarts from `mkOk Checkpoint =
default`, whose account map is empty — so native `call` raises
`.MissingContract` while our `resolveActiveCode?` proceeds with the override.
The bridge agreement is therefore *false* for such programs, and they are
compiler-rejected Yul anyway ("a Break or Continue in the pre or post is a
compiler error" — Interpreter.lean). The fragment predicate excludes them: a
For statement additionally requires its post to be break/continue-free.

`Leave` is deliberately allowed (native `loop` returns on a `Leave` post
outcome without recursing), and a nested `For` swallows its own body/post
jumps, so its presence is fine. -/

mutual

/-- No `Break`/`Continue` *outcome* can escape this statement (syntactic
over-approximation: no `.Break`/`.Continue` outside nested `For` loops). -/
def breakContinueFree? : Stmt → Bool
  | .Block stmts => breakContinueFreeStmts? stmts
  | .Let _ _ => true
  | .Assign _ _ => true
  | .ExprStmtCall _ => true
  | .Switch _ cases default =>
      breakContinueFreeCases? cases && breakContinueFreeStmts? default
  | .For _ _ _ => true
  | .If _ body => breakContinueFreeStmts? body
  | .Continue => false
  | .Break => false
  | .Leave => true

def breakContinueFreeStmts? : List Stmt → Bool
  | [] => true
  | s :: ss => breakContinueFree? s && breakContinueFreeStmts? ss

def breakContinueFreeCases? : List (Literal × List Stmt) → Bool
  | [] => true
  | (_, body) :: rest =>
      breakContinueFreeStmts? body && breakContinueFreeCases? rest

end

mutual

/-- Every op reachable in an expression is a `BridgeOp`. -/
def bridgeExpr? : Expr → Bool
  | .Call (.inl op) args => bridgeOp? op && bridgeExprs? args
  | .Call (.inr _) args => bridgeExprs? args
  | .Var _ => true
  | .Lit _ => true

def bridgeExprs? : List Expr → Bool
  | [] => true
  | e :: es => bridgeExpr? e && bridgeExprs? es

def bridgeStmt? : Stmt → Bool
  | .Block stmts => bridgeStmts? stmts
  | .Let _ none => true
  | .Let _ (some e) => bridgeExpr? e
  | .Assign _ e => bridgeExpr? e
  | .ExprStmtCall e => bridgeExpr? e
  | .Switch cond cases default =>
      bridgeExpr? cond && bridgeCases? cases && bridgeStmts? default
  | .For cond post body =>
      bridgeExpr? cond && bridgeStmts? post && breakContinueFreeStmts? post &&
        bridgeStmts? body
  | .If cond body => bridgeExpr? cond && bridgeStmts? body
  | .Continue => true
  | .Break => true
  | .Leave => true

def bridgeStmts? : List Stmt → Bool
  | [] => true
  | s :: ss => bridgeStmt? s && bridgeStmts? ss

def bridgeCases? : List (Literal × List Stmt) → Bool
  | [] => true
  | (_, body) :: rest => bridgeStmts? body && bridgeCases? rest

end

/-- Function bodies are request-free. -/
def bridgeFunction? : FunctionDefinition → Bool
  | .Def _ _ body => bridgeStmts? body

/-- The dispatcher and every declared function body are request-free. -/
def bridgeContract? (c : YulContract) : Bool :=
  bridgeStmt? c.dispatcher && c.functions.all (fun _ f => bridgeFunction? f)

/-- `Prop` lift: no `Break`/`Continue` outcome escapes these statements. -/
def BreakContinueFreeStmts (ss : List Stmt) : Prop :=
  breakContinueFreeStmts? ss = true

@[simp] theorem breakContinueFreeStmts?_iff (ss : List Stmt) :
    breakContinueFreeStmts? ss = true ↔ BreakContinueFreeStmts ss := Iff.rfl

/-- `Prop` lift: every op in `e` is a `BridgeOp`. -/
def BridgeExpr (e : Expr) : Prop := bridgeExpr? e = true
def BridgeExprs (es : List Expr) : Prop := bridgeExprs? es = true
def BridgeStmt (s : Stmt) : Prop := bridgeStmt? s = true
def BridgeStmts (ss : List Stmt) : Prop := bridgeStmts? ss = true
def BridgeContract (c : YulContract) : Prop := bridgeContract? c = true

@[simp] theorem bridgeExpr?_iff (e : Expr) : bridgeExpr? e = true ↔ BridgeExpr e :=
  Iff.rfl
@[simp] theorem bridgeExprs?_iff (es : List Expr) :
    bridgeExprs? es = true ↔ BridgeExprs es := Iff.rfl
@[simp] theorem bridgeStmt?_iff (s : Stmt) : bridgeStmt? s = true ↔ BridgeStmt s :=
  Iff.rfl
@[simp] theorem bridgeStmts?_iff (ss : List Stmt) :
    bridgeStmts? ss = true ↔ BridgeStmts ss := Iff.rfl
@[simp] theorem bridgeContract?_iff (c : YulContract) :
    bridgeContract? c = true ↔ BridgeContract c := Iff.rfl

instance (e : Expr) : Decidable (BridgeExpr e) := by unfold BridgeExpr; infer_instance
instance (s : Stmt) : Decidable (BridgeStmt s) := by unfold BridgeStmt; infer_instance
instance (ss : List Stmt) : Decidable (BridgeStmts ss) := by
  unfold BridgeStmts; infer_instance
instance (c : YulContract) : Decidable (BridgeContract c) := by
  unfold BridgeContract; infer_instance

/-! ## Outcome relations (thin by design)

Native `EvmYul.Yul.exec` returns `Except EvmYul.Yul.Exception α`; ours returns an
`Open α` whose error payload is a `Failure` carrying a site-local `state` beside
the `exception`. The W1 downstream audit (see `PROGRESS_LOG.md`, tag
`theorem-boundary`) confirms every consumer of our source-side done payload
(`FunctionsInteractionPrimitive.ErrorRel`/`Truncated`, hence
`VerifiedStackObjectPrefixDoneRel`) reads only `Failure.exception`, never
`Failure.state`. So exception equality on the error side suffices. -/

/-- Native/our outcome agreement: equal `.ok` values; equal exceptions on error
(the site-local `Failure.state` is provably irrelevant downstream). -/
def ResultAgrees {α : Type}
    (native : Except EvmYul.Yul.Exception α)
    (ours : Except InteractionSemantics.Failure α) : Prop :=
  match native, ours with
  | .ok a, .ok b => b = a
  | .error e, .error f => f.exception = e
  | _, _ => False

/-- Our open computation is a `.done` leaf agreeing with the native result. -/
def DoneAgrees {α : Type}
    (native : Except EvmYul.Yul.Exception α)
    (ours : InteractionSemantics.Open α) : Prop :=
  ∃ r, ours = .done r ∧ ResultAgrees native r

theorem ResultAgrees.ok {α : Type} {a b : α}
    (h : b = a) :
    ResultAgrees (α := α) (.ok a) (.ok b) := h

theorem ResultAgrees.error {α : Type}
    {e : EvmYul.Yul.Exception} {f : InteractionSemantics.Failure}
    (h : f.exception = e) :
    ResultAgrees (α := α) (.error e) (.error f) := h

theorem DoneAgrees.mk {α : Type}
    {native : Except EvmYul.Yul.Exception α} {r : Except InteractionSemantics.Failure α}
    (h : ResultAgrees native r) :
    DoneAgrees native (.done r) := ⟨r, rfl, h⟩

end VerityBridge
end Yul
end EvmCompiler
