import EvmCompiler.VerityBridge.PrimAgrees

/-!
# PART A — our-side fuel monotonicity for the Verity bridge

The Verity interpreter-equivalence bridge is stated in the **unbounded ∃-fuel**
form (ratified, commit 6769774bf): for every native fuel there exists *some* our
fuel at which the two interpreters agree. Combining the per-subterm witnesses
that the mutual induction produces into a single our-side run requires lifting
each witness to a common fuel — which is exactly this file's monotonicity:

> if `f` at fuel `m` produces a **settled** result (a `.done` leaf that is not the
> `OutOfFuel` failure), then `f` at any fuel `m' ≥ m` produces the *same* result.

## Design choices (recorded per the W3b brief)

* **No `Bridge*` hypothesis.** `Settled` requires a `.done` leaf; a request node
  makes `Simulation.Interaction.bind` a request (never `.done`), so a settled
  composite already forces every leading subcomputation to be a `.done` leaf.
  Monotonicity therefore holds for *all* programs, request-bearing or not — the
  request case is vacuous because it is never settled.
* **`OutOfFuel` is the only unstable outcome.** On these interpreters `OutOfFuel`
  is always a meta-fuel-exhaustion artifact; every other outcome (`.ok`, or any
  non-`OutOfFuel` exception, whose site-local `Failure.state` is fixed by the
  deterministic path taken) is reached without spending the residual fuel and is
  preserved verbatim. `Settled` excludes exactly `OutOfFuel`.
* **Induction shape.** A single one-step bundle `MonoStep m` over the eight
  mutually-recursive kernel functions (`evalTail`/`evalArgs`/`evalValues`/`eval`/
  `call`/`execSeq`/`exec`/`loop`), proved by strong induction on `m`; the general
  `m ≤ m'` form follows by `Nat.le_induction`. `callDispatcher` is a corollary of
  `exec`. This is the "fuel-strong-induction wrapper" of the plan's R3 mitigation
  (semantically identical to a measure-mirroring mutual induction, structurally
  simpler because the two fuels are handled by one well-founded recursion).
-/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

open EvmYul.Yul.Ast

/-! ## The `Settled` predicate -/

/-- A `.done` leaf whose result, if it is an error, is not `OutOfFuel`. This is
the class of outcomes that increasing the fuel cannot change. -/
def Settled {α : Type} (x : InteractionSemantics.Open α) : Prop :=
  ∃ r, x = .done r ∧ ∀ f : InteractionSemantics.Failure, r = .error f →
    f.exception ≠ .OutOfFuel

theorem Settled.done_ok {α : Type} (v : α) :
    Settled (α := α) (.done (.ok v)) :=
  ⟨.ok v, rfl, by rintro f ⟨⟩⟩

theorem Settled.done_error {α : Type} {f : InteractionSemantics.Failure}
    (h : f.exception ≠ .OutOfFuel) :
    Settled (α := α) (.done (.error f)) :=
  ⟨.error f, rfl, by rintro g hg; injection hg with hg'; subst hg'; exact h⟩

/-- The `OutOfFuel` failure leaf is never settled. -/
theorem not_settled_fail_outOfFuel {α : Type} (state : InteractionSemantics.State) :
    ¬ Settled (α := α) (InteractionSemantics.Primitive.fail state .OutOfFuel) := by
  rintro ⟨r, hEq, hNOOF⟩
  rw [InteractionSemantics.Primitive.fail] at hEq
  cases hEq
  exact hNOOF _ rfl rfl

/-! ## Inversion of a settled `bind`

If `bind x k` is settled then `x` is a `.done` leaf: either a `.ok` value whose
continuation `k v` is itself settled, or a non-`OutOfFuel` error that `bind`
propagates unchanged. -/

theorem settled_bind {α β : Type}
    {x : InteractionSemantics.Open α}
    {k : α → InteractionSemantics.Open β}
    (h : Settled (Simulation.Interaction.bind x k)) :
    (∃ v, x = .done (.ok v) ∧ Settled (k v)) ∨
      (∃ f : InteractionSemantics.Failure,
        x = .done (.error f) ∧ f.exception ≠ .OutOfFuel) := by
  rcases h with ⟨r, hEq, hNOOF⟩
  cases x with
  | done o =>
      cases o with
      | ok v =>
          rw [Simulation.Interaction.bind_done_ok] at hEq
          exact Or.inl ⟨v, rfl, r, hEq, hNOOF⟩
      | error f =>
          rw [Simulation.Interaction.bind_done_error] at hEq
          cases hEq
          exact Or.inr ⟨f, rfl, hNOOF _ rfl⟩
  | request q resume =>
      rw [Simulation.Interaction.bind_request] at hEq
      exact absurd hEq (by rintro ⟨⟩)

/-! ## `openEval` monotonicity

`openEval` uses its fuel only through the `closedEval` (primitive) branch; the
external-call / create / resource branches are fuel-free. On the `closedEval`
branch the op is a `BridgeOp` (or `EXTCODEHASH`), for which `primCall` (resp. the
`extCodeHash` override) is fuel-insensitive above the exhaustion boundary. Hence a
settled `openEval` is stable under more fuel. -/

open EvmYul (Operation)

/-- `openEval` at positive fuel with a non-external, non-`GAS`/`MSIZE` op delegates
to `closedEval`. Mirror of `openEval_agrees` without the `EXTCODEHASH` exclusion
(so it also fires on the `EXTCODEHASH` override). -/
private theorem openEval_succ_closedEval {op : Operation .Yul}
    (hExt : Simulation.ExternalKind.ofYulOperation? op = none)
    (hGas : op ≠ .StackMemFlow .GAS) (hMsize : op ≠ .StackMemFlow .MSIZE)
    (fuel : Nat) (s : InteractionSemantics.State) (args : List Word) :
    InteractionSemantics.Primitive.openEval (fuel + 1) s op args =
      InteractionSemantics.Primitive.closedEval fuel s op args := by
  unfold InteractionSemantics.Primitive.openEval
  rw [hExt]
  split <;> first | rfl | (rename_i heq; simp_all)

private theorem extCodeHash_ext : Simulation.ExternalKind.ofYulOperation?
    (Operation.Env .EXTCODEHASH) = none := rfl

/-- One-fuel step of `openEval` monotonicity: a settled result is preserved when
the fuel is increased by one. -/
theorem openEval_mono_step (m : Nat) (s : InteractionSemantics.State)
    (op : Operation .Yul) (args : List Word)
    (h : Settled (InteractionSemantics.Primitive.openEval m s op args)) :
    InteractionSemantics.Primitive.openEval (m + 1) s op args =
      InteractionSemantics.Primitive.openEval m s op args := by
  cases m with
  | zero => exact absurd h (not_settled_fail_outOfFuel s)
  | succ k =>
      by_cases hBridge : BridgeOp op
      · -- primitive (BridgeOp) branch: primCall is fuel-insensitive above `0`
        rw [openEval_agrees hBridge (k + 1) s args, openEval_agrees hBridge k s args,
          closedEval_agrees hBridge (k + 1) s args, closedEval_agrees hBridge k s args]
        rw [openEval_agrees hBridge k s args, closedEval_agrees hBridge k s args] at h
        cases k with
        | zero =>
            exfalso
            have hp : EvmYul.Yul.primCall 0 s op args = .error .OutOfFuel := by
              conv_lhs => rw [EvmYul.Yul.primCall]
            rw [hp] at h
            exact not_settled_fail_outOfFuel _ h
        | succ j =>
            rw [primCall_fuel_insensitive hBridge (j + 1) j s args]
      · by_cases hHash : op = .Env .EXTCODEHASH
        · -- EXTCODEHASH override: `extCodeHash` is fuel-free above `0`
          subst hHash
          rw [openEval_succ_closedEval extCodeHash_ext (by decide) (by decide) (k + 1) s args,
            openEval_succ_closedEval extCodeHash_ext (by decide) (by decide) k s args]
          rw [openEval_succ_closedEval extCodeHash_ext (by decide) (by decide) k s args] at h
          cases k with
          | zero =>
              exfalso
              simp only [InteractionSemantics.Primitive.closedEval] at h
              exact not_settled_fail_outOfFuel _ h
          | succ j =>
              rfl
        · -- external / GAS / MSIZE: fuel-free branch
          cases hK : Simulation.ExternalKind.ofYulOperation? op with
          | some ek =>
              cases ek <;> simp only [InteractionSemantics.Primitive.openEval, hK]
          | none =>
              have hGM : op = .StackMemFlow .GAS ∨ op = .StackMemFlow .MSIZE := by
                by_contra hc
                push_neg at hc
                exact hBridge ⟨hK, hc.1, hc.2, hHash⟩
              rcases hGM with rfl | rfl <;>
                simp only [InteractionSemantics.Primitive.openEval, hK]

/-- General `openEval` monotonicity: a settled result is preserved at any larger
fuel. -/
theorem openEval_mono {m m' : Nat} (hle : m ≤ m')
    (s : InteractionSemantics.State) (op : Operation .Yul) (args : List Word)
    (h : Settled (InteractionSemantics.Primitive.openEval m s op args)) :
    InteractionSemantics.Primitive.openEval m' s op args =
      InteractionSemantics.Primitive.openEval m s op args := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [openEval_mono_step n s op args (by rw [ih]; exact h), ih]

/-! ## Uniform combinators for the mutual bundle

Every case of the mutual monotonicity is `f (k+1) = bind sub K` versus
`f (k+2) = bind sub' K'`, where `sub' = sub` by the inductive hypothesis on the
leading subterm and `K'` agrees with `K` on every settled `.ok` continuation. The
two lemmas below discharge that shape once and for all. -/

open Simulation (Interaction)

/-- A settled `bind` has a settled head. -/
theorem settled_of_bind {α β : Type}
    {x : InteractionSemantics.Open α}
    {k : α → InteractionSemantics.Open β}
    (h : Settled (Interaction.bind x k)) : Settled x := by
  rcases settled_bind h with ⟨v, hv, _⟩ | ⟨f, hf, hne⟩
  · rw [hv]; exact Settled.done_ok v
  · rw [hf]; exact Settled.done_error hne

/-- Monotonicity of a `bind`: if the head is preserved and the continuation
agrees on the (settled) `.ok` value actually taken, the whole `bind` is
preserved. -/
theorem bind_mono {α β : Type}
    {subA subB : InteractionSemantics.Open α}
    {kA kB : α → InteractionSemantics.Open β}
    (hSub : subB = subA)
    (h : Settled (Interaction.bind subA kA))
    (hK : ∀ v, subA = .done (.ok v) → Settled (kA v) → kB v = kA v) :
    Interaction.bind subB kB = Interaction.bind subA kA := by
  subst hSub
  rcases settled_bind h with ⟨v, hv, hs⟩ | ⟨f, hf, _⟩
  · rw [hv, Interaction.bind_done_ok, Interaction.bind_done_ok]
    exact hK v hv hs
  · rw [hf, Interaction.bind_done_error, Interaction.bind_done_error]

/-! ## Missing one-step equation lemmas (bind form)

`InteractionSemantics` already exposes clean equation lemmas for most functions.
These fill the gaps the bundle needs: `evalTail`, primitive `evalValues`, and the
general `call`. All are `rfl`/`simp only` after unfolding the canonical evaluator. -/

open InteractionSemantics (State Open eval evalArgs evalValues call exec execSeq loop stateModel
  primitiveSemantics)

/-- `evalTail` as a canonical kernel term (mirrors `InteractionSemantics.evalArgs`
etc.). -/
abbrev evalTail := Yul.Source.Canonical.evalTail stateModel primitiveSemantics

private theorem evalTail_succ (k : Nat) (args : List Expr)
    (code : Option YulContract) (result : Open (State × Word)) :
    evalTail (k + 1) args code result =
      Interaction.bind result (fun p =>
        Interaction.bind (evalArgs k args code p.1)
          (fun q => Interaction.pure (q.1, p.2 :: q.2))) := by
  unfold evalTail Yul.Source.Canonical.evalTail Yul.Source.Effectful.evalTail
  rfl

private theorem evalArgs_cons_eq (k : Nat) (a : Expr) (as : List Expr)
    (code : Option YulContract) (s : State) :
    evalArgs (k + 1) (a :: as) code s =
      evalTail k as code (eval k a code s) := by
  unfold evalArgs Yul.Source.Canonical.evalArgs Yul.Source.Effectful.evalArgs
  rfl

private theorem evalValues_prim_succ (k : Nat) (op : EvmYul.Operation .Yul)
    (args : List Expr) (code : Option YulContract) (s : State) :
    evalValues (k + 1) (.Call (.inl op) args) code s =
      Interaction.bind (evalArgs k args.reverse code s)
        (fun r => InteractionSemantics.Primitive.openEval k r.1 op r.2.reverse) := by
  simp only [evalValues, Yul.Source.Canonical.evalValues,
    Yul.Source.Effectful.evalValues]
  rfl

private theorem call_succ (k : Nat) (args : List Word)
    (fn? : Option EvmYul.Yul.Ast.YulFunctionName)
    (code : Option YulContract) (s : State) :
    call (k + 1) args fn? code s =
      (match Yul.Source.Effectful.resolveActiveCode? s code with
       | none => Yul.Source.Effectful.Control.fail s
           (.MissingContract (s!"{s.executionEnv.codeOwner}"))
       | some c =>
           match (match fn? with
                  | none => some (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
                      [c.dispatcher])
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

private theorem evalTail_zero (args : List Expr)
    (code : Option YulContract) (result : Open (State × Word)) :
    evalTail 0 args code result =
      Interaction.bind result (fun p =>
        InteractionSemantics.Primitive.fail p.1 .OutOfFuel) := by
  unfold evalTail Yul.Source.Canonical.evalTail Yul.Source.Effectful.evalTail
  rfl

/-- Every `evalTail` is a `bind` of its input result, so a settled `evalTail` has
a settled argument computation. -/
private theorem settled_evalTail_arg {fuel : Nat} {args : List Expr}
    {code : Option YulContract} {result : Open (State × Word)}
    (h : Settled (evalTail fuel args code result)) : Settled result := by
  cases fuel with
  | zero => rw [evalTail_zero] at h; exact settled_of_bind h
  | succ k => rw [evalTail_succ] at h; exact settled_of_bind h

/-! ## The mutual monotonicity bundle -/

open InteractionSemantics

/-- One-fuel monotonicity for all eight mutually-recursive kernel functions at a
fixed fuel `m`. -/
structure MonoStep (m : Nat) : Prop where
  evalTail : ∀ (args : List Expr) (code : Option YulContract)
      (result : Open (State × Word)),
      Settled (evalTail m args code result) →
        evalTail (m + 1) args code result = evalTail m args code result
  evalArgs : ∀ (args : List Expr) (code : Option YulContract) (s : State),
      Settled (evalArgs m args code s) →
        evalArgs (m + 1) args code s = evalArgs m args code s
  evalValues : ∀ (expr : Expr) (code : Option YulContract) (s : State),
      Settled (evalValues m expr code s) →
        evalValues (m + 1) expr code s = evalValues m expr code s
  eval : ∀ (expr : Expr) (code : Option YulContract) (s : State),
      Settled (eval m expr code s) →
        eval (m + 1) expr code s = eval m expr code s
  call : ∀ (args : List Word) (fn? : Option EvmYul.Yul.Ast.YulFunctionName)
      (code : Option YulContract) (s : State),
      Settled (call m args fn? code s) →
        call (m + 1) args fn? code s = call m args fn? code s
  execSeq : ∀ (stmts : List Stmt) (code : Option YulContract) (s : State),
      Settled (execSeq m stmts code s) →
        execSeq (m + 1) stmts code s = execSeq m stmts code s
  exec : ∀ (stmt : Stmt) (code : Option YulContract) (s : State),
      Settled (exec m stmt code s) →
        exec (m + 1) stmt code s = exec m stmt code s
  loop : ∀ (cond : Expr) (post body : List Stmt) (code : Option YulContract)
      (s : State),
      Settled (loop m cond post body code s) →
        loop (m + 1) cond post body code s = loop m cond post body code s

theorem monoStep : ∀ m, MonoStep m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro args code result h
          rw [evalTail_succ 0, evalTail_zero]
          rw [evalTail_zero] at h
          exact bind_mono rfl h (fun v _ hs => absurd hs (not_settled_fail_outOfFuel _))
        · intro args code s h
          rw [EvalArgs.zero] at h; exact absurd h (not_settled_fail_outOfFuel _)
        · intro expr code s h
          rw [EvalValues.zero] at h; exact absurd h (not_settled_fail_outOfFuel _)
        · intro expr code s h
          rw [eval_eq_bind, EvalValues.zero, Primitive.bind_fail] at h
          exact absurd h (not_settled_fail_outOfFuel _)
        · intro args fn? code s h
          rw [Call.zero] at h; exact absurd h (not_settled_fail_outOfFuel _)
        · intro stmts code s h
          rw [ExecSeq.zero] at h; exact absurd h (not_settled_fail_outOfFuel _)
        · intro stmt code s h
          rw [Exec.zero] at h; exact absurd h (not_settled_fail_outOfFuel _)
        · intro cond post body code s h
          rw [Exec.loop_zero] at h; exact absurd h (not_settled_fail_outOfFuel _)
    | k + 1 =>
        have ihk : MonoStep k := ih k (Nat.lt_succ_self k)
        -- Expression third (M3.2 focus).
        have hEvalTail : ∀ (args : List Expr) (code : Option YulContract)
            (result : Open (State × Word)),
            Settled (evalTail (k + 1) args code result) →
              evalTail (k + 2) args code result =
                evalTail (k + 1) args code result := by
          intro args code result h
          rw [evalTail_succ (k + 1), evalTail_succ k]
          rw [evalTail_succ k] at h
          refine bind_mono rfl h ?_
          intro v _ hs
          refine bind_mono (ihk.evalArgs args code v.1 (settled_of_bind hs)) hs ?_
          intro w _ _; rfl
        have hEvalArgs : ∀ (args : List Expr) (code : Option YulContract)
            (s : State), Settled (evalArgs (k + 1) args code s) →
              evalArgs (k + 2) args code s = evalArgs (k + 1) args code s := by
          intro args code s h
          cases args with
          | nil => rw [EvalArgs.nil_succ (k + 1), EvalArgs.nil_succ k]
          | cons a as =>
              rw [evalArgs_cons_eq (k + 1), evalArgs_cons_eq k]
              rw [evalArgs_cons_eq k] at h
              have hArg : Settled (eval k a code s) := settled_evalTail_arg h
              rw [ihk.eval a code s hArg]
              exact ihk.evalTail as code (eval k a code s) h
        have hEvalValues : ∀ (expr : Expr) (code : Option YulContract) (s : State),
            Settled (evalValues (k + 1) expr code s) →
              evalValues (k + 2) expr code s = evalValues (k + 1) expr code s := by
          intro expr code s h
          cases expr with
          | Call sop args =>
              cases sop with
              | inl op =>
                  rw [evalValues_prim_succ (k + 1), evalValues_prim_succ k]
                  rw [evalValues_prim_succ k] at h
                  refine bind_mono
                    (ihk.evalArgs args.reverse code s (settled_of_bind h)) h ?_
                  intro v _ hs
                  exact openEval_mono (Nat.le_succ k) v.1 op v.2.reverse hs
              | inr fn =>
                  rw [EvalValues.internal_succ (k + 1), EvalValues.internal_succ k]
                  rw [EvalValues.internal_succ k] at h
                  refine bind_mono
                    (ihk.evalArgs args.reverse code s (settled_of_bind h)) h ?_
                  intro v _ hs
                  exact ihk.call v.2.reverse (some fn) code v.1 hs
          | Var id =>
              simp only [evalValues, Yul.Source.Canonical.evalValues,
                Yul.Source.Effectful.evalValues]
          | Lit value =>
              simp only [evalValues, Yul.Source.Canonical.evalValues,
                Yul.Source.Effectful.evalValues]
        have hEval : ∀ (expr : Expr) (code : Option YulContract) (s : State),
            Settled (eval (k + 1) expr code s) →
              eval (k + 2) expr code s = eval (k + 1) expr code s := by
          intro expr code s h
          rw [eval_eq_bind (k + 2), eval_eq_bind (k + 1)]
          rw [eval_eq_bind (k + 1)] at h
          refine bind_mono (hEvalValues expr code s (settled_of_bind h)) h ?_
          intro v _ _; rfl
        -- Statement third (filled below).
        have hCall : ∀ (args : List Word)
            (fn? : Option EvmYul.Yul.Ast.YulFunctionName)
            (code : Option YulContract) (s : State),
            Settled (call (k + 1) args fn? code s) →
              call (k + 2) args fn? code s = call (k + 1) args fn? code s := by
          intro args fn? code s h
          rw [call_succ (k + 1), call_succ k]
          rw [call_succ k] at h
          generalize hRes : Yul.Source.Effectful.resolveActiveCode? s code = rc
            at h ⊢
          cases rc with
          | none => rfl
          | some c =>
              dsimp only at h ⊢
              generalize hFn : (match fn? with
                  | none => some (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
                      [c.dispatcher])
                  | some f => c.functions.lookup f) = fo at h ⊢
              cases fo with
              | none => rfl
              | some function =>
                  dsimp only at h ⊢
                  cases function with
                  | Def params rets body =>
                      refine bind_mono (ihk.exec (.Block body) code
                        (EvmYul.Yul.State.mkOk (s.initcall params rets args))
                        (settled_of_bind h)) h ?_
                      intro v _ _; rfl
        have hExecSeq : ∀ (stmts : List Stmt) (code : Option YulContract)
            (s : State), Settled (execSeq (k + 1) stmts code s) →
              execSeq (k + 2) stmts code s = execSeq (k + 1) stmts code s := by
          intro stmts code s h
          cases stmts with
          | nil => rw [ExecSeq.nil_succ (k + 1), ExecSeq.nil_succ k]
          | cons stmt rest =>
              rw [ExecSeq.cons_succ (k + 1), ExecSeq.cons_succ k]
              rw [ExecSeq.cons_succ k] at h
              refine bind_mono (ihk.exec stmt code s (settled_of_bind h)) h ?_
              intro v _ hs
              cases v with
              | Ok sh vs => exact ihk.execSeq rest code (.Ok sh vs) hs
              | OutOfFuel => rfl
              | Checkpoint jmp => rfl
        have hLoop : ∀ (cond : Expr) (post body : List Stmt)
            (code : Option YulContract) (s : State),
            Settled (loop (k + 1) cond post body code s) →
              loop (k + 2) cond post body code s =
                loop (k + 1) cond post body code s := by
          intro cond post body code s h
          cases k with
          | zero =>
              rw [Exec.loop_one] at h
              exact absurd h (not_settled_fail_outOfFuel _)
          | succ j =>
              have ihj : MonoStep j := ih j (by omega)
              -- The post/For tail is shared by the `Continue` and fall-through
              -- (`Ok`) arms; factor it once.
              have hPost : ∀ (entry : State),
                  Settled (Interaction.bind (exec j (.Block post) code entry)
                    (fun stateAfterPost =>
                      match stateModel.source stateAfterPost with
                      | .OutOfFuel =>
                          Interaction.pure (stateModel.withSource stateAfterPost
                            ((stateModel.source stateAfterPost).overwrite?
                              (stateModel.source s)))
                      | .Checkpoint (.Leave _ _) =>
                          Interaction.pure (stateModel.withSource stateAfterPost
                            ((stateModel.source stateAfterPost).overwrite?
                              (stateModel.source s)))
                      | _ =>
                          Interaction.bind
                            (exec j (.For cond post body) code
                              (stateModel.withSource stateAfterPost
                                ((stateModel.source stateAfterPost).overwrite?
                                  (stateModel.source s))))
                            (fun stateAfterLoop =>
                              Interaction.pure (stateModel.withSource stateAfterLoop
                                ((stateModel.source stateAfterLoop).overwrite?
                                  (stateModel.source s)))))) →
                  (Interaction.bind (exec (j + 1) (.Block post) code entry)
                    (fun stateAfterPost =>
                      match stateModel.source stateAfterPost with
                      | .OutOfFuel =>
                          Interaction.pure (stateModel.withSource stateAfterPost
                            ((stateModel.source stateAfterPost).overwrite?
                              (stateModel.source s)))
                      | .Checkpoint (.Leave _ _) =>
                          Interaction.pure (stateModel.withSource stateAfterPost
                            ((stateModel.source stateAfterPost).overwrite?
                              (stateModel.source s)))
                      | _ =>
                          Interaction.bind
                            (exec (j + 1) (.For cond post body) code
                              (stateModel.withSource stateAfterPost
                                ((stateModel.source stateAfterPost).overwrite?
                                  (stateModel.source s))))
                            (fun stateAfterLoop =>
                              Interaction.pure (stateModel.withSource stateAfterLoop
                                ((stateModel.source stateAfterLoop).overwrite?
                                  (stateModel.source s)))))) =
                  (Interaction.bind (exec j (.Block post) code entry)
                    (fun stateAfterPost =>
                      match stateModel.source stateAfterPost with
                      | .OutOfFuel =>
                          Interaction.pure (stateModel.withSource stateAfterPost
                            ((stateModel.source stateAfterPost).overwrite?
                              (stateModel.source s)))
                      | .Checkpoint (.Leave _ _) =>
                          Interaction.pure (stateModel.withSource stateAfterPost
                            ((stateModel.source stateAfterPost).overwrite?
                              (stateModel.source s)))
                      | _ =>
                          Interaction.bind
                            (exec j (.For cond post body) code
                              (stateModel.withSource stateAfterPost
                                ((stateModel.source stateAfterPost).overwrite?
                                  (stateModel.source s))))
                            (fun stateAfterLoop =>
                              Interaction.pure (stateModel.withSource stateAfterLoop
                                ((stateModel.source stateAfterLoop).overwrite?
                                  (stateModel.source s)))))) := by
                intro entry hp
                refine bind_mono (ihj.exec (.Block post) code entry
                  (settled_of_bind hp)) hp ?_
                intro sap _ hsp
                cases sap with
                | OutOfFuel => rfl
                | Ok psh pvs =>
                    dsimp only [stateModel, id_eq] at hsp ⊢
                    refine bind_mono (ihj.exec (.For cond post body) code _
                      (settled_of_bind hsp)) hsp ?_
                    intro sal _ _; rfl
                | Checkpoint jmp =>
                    cases jmp with
                    | Leave _ _ => rfl
                    | Break _ _ =>
                        dsimp only [stateModel, id_eq] at hsp ⊢
                        refine bind_mono (ihj.exec (.For cond post body) code _
                          (settled_of_bind hsp)) hsp ?_
                        intro sal _ _; rfl
                    | Continue _ _ =>
                        dsimp only [stateModel, id_eq] at hsp ⊢
                        refine bind_mono (ihj.exec (.For cond post body) code _
                          (settled_of_bind hsp)) hsp ?_
                        intro sal _ _; rfl
              rw [Exec.loop_succ_succ (j + 1), Exec.loop_succ_succ j]
              rw [Exec.loop_succ_succ j] at h
              refine bind_mono (ihj.eval cond code _ (settled_of_bind h)) h ?_
              intro r _ hs
              by_cases hz : r.2 = EvmYul.UInt256.ofNat 0
              · rw [if_pos hz, if_pos hz]
              · rw [if_neg hz, if_neg hz]
                rw [if_neg hz] at hs
                refine bind_mono (ihj.exec (.Block body) code _
                  (settled_of_bind hs)) hs ?_
                intro sab _ hsb
                cases sab with
                | OutOfFuel => rfl
                | Ok bsh bvs =>
                    dsimp only [stateModel, id_eq] at hsb ⊢
                    exact hPost _ hsb
                | Checkpoint jmp =>
                    cases jmp with
                    | Break _ _ => rfl
                    | Leave _ _ => rfl
                    | Continue _ _ =>
                        dsimp only [stateModel, id_eq] at hsb ⊢
                        exact hPost _ hsb
        have hExec : ∀ (stmt : Stmt) (code : Option YulContract) (s : State),
            Settled (exec (k + 1) stmt code s) →
              exec (k + 2) stmt code s = exec (k + 1) stmt code s := by
          intro stmt code s h
          cases stmt with
          | Block stmts =>
              rw [Exec.block_succ (k + 1), Exec.block_succ k]
              rw [Exec.block_succ k] at h
              refine bind_mono (ihk.execSeq stmts code s (settled_of_bind h)) h ?_
              intro v _ _; rfl
          | Let names expr? =>
              cases expr? with
              | none =>
                  simp only [exec, Yul.Source.Canonical.exec,
                    Yul.Source.Effectful.exec]
              | some e =>
                  cases hCk : EvmYul.Yul.checkDeclaration s names with
                  | error err =>
                      simp only [exec, Yul.Source.Canonical.exec,
                        Yul.Source.Effectful.exec, stateModel, id_eq, hCk]
                  | ok u =>
                      cases u
                      rw [Exec.let_some_succ (k + 1) names e code s hCk,
                        Exec.let_some_succ k names e code s hCk]
                      rw [Exec.let_some_succ k names e code s hCk] at h
                      refine bind_mono
                        (ihk.evalValues e code s (settled_of_bind h)) h ?_
                      intro v _ _; rfl
          | Assign names e =>
              cases hCk : EvmYul.Yul.checkAssignment s names with
              | error err =>
                  simp only [exec, Yul.Source.Canonical.exec,
                    Yul.Source.Effectful.exec, stateModel, id_eq, hCk]
              | ok u =>
                  cases u
                  rw [Exec.assign_succ (k + 1) names e code s hCk,
                    Exec.assign_succ k names e code s hCk]
                  rw [Exec.assign_succ k names e code s hCk] at h
                  refine bind_mono
                    (ihk.evalValues e code s (settled_of_bind h)) h ?_
                  intro v _ _; rfl
          | If cond body =>
              rw [Exec.if_succ (k + 1), Exec.if_succ k]
              rw [Exec.if_succ k] at h
              refine bind_mono (ihk.eval cond code s (settled_of_bind h)) h ?_
              intro v _ hs
              by_cases hc : v.2 ≠ EvmYul.UInt256.ofNat 0
              · rw [if_pos hc, if_pos hc]; rw [if_pos hc] at hs
                exact ihk.exec (.Block body) code v.1 hs
              · rw [if_neg hc, if_neg hc]
          | ExprStmtCall e =>
              cases e with
              | Call sop args =>
                  cases sop with
                  | inl op =>
                      rw [Exec.expr_primitive (k + 2), Exec.expr_primitive (k + 1)]
                      rw [Exec.expr_primitive (k + 1)] at h
                      refine bind_mono
                        (hEvalValues (.Call (.inl op) args) code s
                          (settled_of_bind h)) h ?_
                      intro v _ _; rfl
                  | inr fn =>
                      cases k with
                      | zero =>
                          rw [Exec.expr_internal_one] at h
                          exact absurd h (not_settled_fail_outOfFuel _)
                      | succ j =>
                          have ihj : MonoStep j := ih j (by omega)
                          rw [Exec.expr_internal_succ (j + 1),
                            Exec.expr_internal_succ j]
                          rw [Exec.expr_internal_succ j] at h
                          refine bind_mono
                            (ihk.evalArgs args.reverse code s
                              (settled_of_bind h)) h ?_
                          intro ar _ hs
                          refine bind_mono
                            (ihj.call ar.2.reverse (some fn) code ar.1
                              (settled_of_bind hs)) hs ?_
                          intro cr _ _; rfl
              | Var id =>
                  simp only [exec, Yul.Source.Canonical.exec,
                    Yul.Source.Effectful.exec]
              | Lit value =>
                  simp only [exec, Yul.Source.Canonical.exec,
                    Yul.Source.Effectful.exec]
          | Switch cond cases default =>
              rw [Exec.switch_succ (k + 1), Exec.switch_succ k]
              rw [Exec.switch_succ k] at h
              refine bind_mono (ihk.eval cond code s (settled_of_bind h)) h ?_
              intro v _ hs
              exact ihk.exec
                (.Block (EvmYul.Yul.selectSwitchCase v.2 default cases))
                code v.1 hs
          | For cond post body =>
              rw [Exec.for_succ (k + 1), Exec.for_succ k]
              rw [Exec.for_succ k] at h
              exact ihk.loop cond post body code s h
          | Continue => rw [Exec.cont_succ (k + 1) code s, Exec.cont_succ k code s]
          | Break => rw [Exec.brk_succ (k + 1) code s, Exec.brk_succ k code s]
          | Leave => rw [Exec.leave_succ (k + 1) code s, Exec.leave_succ k code s]
        exact ⟨hEvalTail, hEvalArgs, hEvalValues, hEval, hCall, hExecSeq,
          hExec, hLoop⟩

/-! ## General monotonicity corollaries (`m ≤ m'` form)

Each is `Nat.le_induction` over the one-step bundle `monoStep`. These are the
lemmas PART B consumes when lifting per-subterm witnesses to a common fuel. -/

theorem evalTail_mono {m m' : Nat} (hle : m ≤ m') (args : List Expr)
    (code : Option YulContract) (result : Open (State × Word))
    (h : Settled (evalTail m args code result)) :
    evalTail m' args code result = evalTail m args code result := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [(monoStep n).evalTail args code result (by rw [ih]; exact h), ih]

theorem evalArgs_mono {m m' : Nat} (hle : m ≤ m') (args : List Expr)
    (code : Option YulContract) (s : State)
    (h : Settled (evalArgs m args code s)) :
    evalArgs m' args code s = evalArgs m args code s := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [(monoStep n).evalArgs args code s (by rw [ih]; exact h), ih]

theorem evalValues_mono {m m' : Nat} (hle : m ≤ m') (expr : Expr)
    (code : Option YulContract) (s : State)
    (h : Settled (evalValues m expr code s)) :
    evalValues m' expr code s = evalValues m expr code s := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [(monoStep n).evalValues expr code s (by rw [ih]; exact h), ih]

theorem eval_mono {m m' : Nat} (hle : m ≤ m') (expr : Expr)
    (code : Option YulContract) (s : State)
    (h : Settled (eval m expr code s)) :
    eval m' expr code s = eval m expr code s := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [(monoStep n).eval expr code s (by rw [ih]; exact h), ih]

theorem call_mono {m m' : Nat} (hle : m ≤ m') (args : List Word)
    (fn? : Option EvmYul.Yul.Ast.YulFunctionName) (code : Option YulContract)
    (s : State) (h : Settled (call m args fn? code s)) :
    call m' args fn? code s = call m args fn? code s := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [(monoStep n).call args fn? code s (by rw [ih]; exact h), ih]

theorem execSeq_mono {m m' : Nat} (hle : m ≤ m') (stmts : List Stmt)
    (code : Option YulContract) (s : State)
    (h : Settled (execSeq m stmts code s)) :
    execSeq m' stmts code s = execSeq m stmts code s := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [(monoStep n).execSeq stmts code s (by rw [ih]; exact h), ih]

theorem exec_mono {m m' : Nat} (hle : m ≤ m') (stmt : Stmt)
    (code : Option YulContract) (s : State)
    (h : Settled (exec m stmt code s)) :
    exec m' stmt code s = exec m stmt code s := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [(monoStep n).exec stmt code s (by rw [ih]; exact h), ih]

theorem loop_mono {m m' : Nat} (hle : m ≤ m') (cond : Expr)
    (post body : List Stmt) (code : Option YulContract) (s : State)
    (h : Settled (loop m cond post body code s)) :
    loop m' cond post body code s = loop m cond post body code s := by
  induction m', hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [(monoStep n).loop cond post body code s (by rw [ih]; exact h), ih]

end VerityBridge
end Yul
end EvmCompiler
