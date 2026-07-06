import EvmCompiler.VerityBridge.FuelMono
import EvmCompiler.VerityBridge.ExecAgrees

/-!
# PART B foundation — the reusable helpers for the ∃-fuel bridge family

The bridge family is the ratified unbounded ∃-fuel form (commit 6769774bf):

  ∀ n, Bridge* … → ∃ m, DoneAgrees (native.f n …) (InteractionSemantics.f m …)

This file provides the two helper lemmas the plan owner's steer calls out, plus
the per-function witness-lifting combinators, so that the main mutual induction
(strong induction on native fuel `n`, PART B proper) reduces uniformly to:

  IH witnesses → common fuel via `liftMax`/`*_lift` → reduce our side → simp.

## The two load-bearing facts (steer #2)

* `settled_of_doneAgrees` — when the native result is **not** the `OutOfFuel`
  exception (`NativeSettled`), agreement forces our witness to be `Settled`
  (PART A's predicate), so PART A monotonicity applies. This is the *only* place
  monotonicity is ever needed: on the settled prefix that the native run is being
  cased on.
* `doneAgrees_fail_outOfFuel` — the uniform native-`OutOfFuel` case: our side at
  fuel `0` fails `OutOfFuel` immediately, which agrees with a native `OutOfFuel`
  error under the (thin, exception-only) `ResultAgrees`. No monotonicity needed;
  the whole native computation short-circuits here.

## Witness lifting (steer #3)

`liftMax` promotes a settled our-side agreement at `m` to any `M ≥ m`; the
per-function `*_lift` corollaries specialise it through PART A's `*_mono`. The
main induction combines 2–3 sub-witnesses by taking `max` (plus arbitrary slack)
and lifting each, keeping each case flat.
-/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

open EvmYul.Yul.Ast
open InteractionSemantics

/-! ## Native-settledness (the non-`OutOfFuel` predicate on the native result) -/

/-- A native result that is not the `OutOfFuel` exception (i.e. `.ok`, or a
non-`OutOfFuel` error). Past such a result the native computation does not
short-circuit on fuel, so the corresponding our-side witness is `Settled`. -/
def NativeSettled {α : Type} (r : Except EvmYul.Yul.Exception α) : Prop :=
  ∀ e, r = .error e → e ≠ .OutOfFuel

theorem NativeSettled.ok {α : Type} (a : α) : NativeSettled (.ok a) := by
  rintro e ⟨⟩

theorem NativeSettled.error {α : Type} {e : EvmYul.Yul.Exception}
    (h : e ≠ .OutOfFuel) : NativeSettled (α := α) (.error e) := by
  rintro e' he; injection he with he'; subst he'; exact h

/-- Agreement with a native-settled result makes the our-side witness `Settled`,
so PART A monotonicity applies to it. -/
theorem settled_of_doneAgrees {α : Type}
    {native : Except EvmYul.Yul.Exception α} {ours : Open α}
    (hN : NativeSettled native) (h : DoneAgrees native ours) : Settled ours := by
  obtain ⟨r, hEq, hRA⟩ := h
  subst hEq
  cases native with
  | ok a =>
      cases r with
      | ok b => exact Settled.done_ok b
      | error f => exact (hRA : False).elim
  | error e =>
      cases r with
      | ok b => exact (hRA : False).elim
      | error f =>
          have hfe : f.exception = e := hRA
          exact Settled.done_error (by rw [hfe]; exact hN e rfl)

/-! ## The uniform native-`OutOfFuel` leaf -/

/-- Our side at fuel `0` fails `OutOfFuel`, which agrees (exception-only) with a
native `OutOfFuel` error. This closes every native-`OutOfFuel` case at witness
`m = 0`. -/
theorem doneAgrees_fail_outOfFuel {α : Type} (s : State) :
    DoneAgrees (α := α) (.error .OutOfFuel)
      (InteractionSemantics.Primitive.fail s .OutOfFuel) :=
  ⟨.error { exception := .OutOfFuel, state := s }, rfl, rfl⟩

/-! ## The one-step `bind` combinator

Every case of the mutual family is "native match-and-propagate versus our
`Interaction.bind`" after unfolding one step on each side. `doneAgrees_bind`
closes that shape from sub-agreement plus continuation agreement on the actual
`.ok` value; `doneAgrees_wrap` is the pure-continuation special case. -/

theorem doneAgrees_bind {α β : Type}
    {nsub : Except EvmYul.Yul.Exception α} {osub : Open α}
    {nk : α → Except EvmYul.Yul.Exception β} {oK : α → Open β}
    (hSub : DoneAgrees nsub osub)
    (hK : ∀ a, nsub = .ok a → DoneAgrees (nk a) (oK a)) :
    DoneAgrees
      (match nsub with | .ok a => nk a | .error e => .error e)
      (Simulation.Interaction.bind osub oK) := by
  obtain ⟨r, hEq, hRA⟩ := hSub
  subst hEq
  cases nsub with
  | ok a =>
      cases r with
      | ok b =>
          have hb : b = a := hRA
          rw [Simulation.Interaction.bind_done_ok, hb]
          exact hK a rfl
      | error f => exact (hRA : False).elim
  | error e =>
      cases r with
      | ok b => exact (hRA : False).elim
      | error f =>
          rw [Simulation.Interaction.bind_done_error]
          exact ⟨.error f, rfl, hRA⟩

theorem doneAgrees_wrap {α β : Type}
    {nsub : Except EvmYul.Yul.Exception α} {osub : Open α}
    (g : α → β) (h : DoneAgrees nsub osub) :
    DoneAgrees
      (match nsub with | .ok a => .ok (g a) | .error e => .error e)
      (Simulation.Interaction.bind osub
        (fun a => Simulation.Interaction.pure (g a))) :=
  doneAgrees_bind h (fun a _ => ⟨.ok (g a), rfl, rfl⟩)

theorem doneAgrees_pure {α : Type} (a : α) :
    DoneAgrees (.ok a) (Simulation.Interaction.pure a) := ⟨.ok a, rfl, rfl⟩

theorem doneAgrees_error {α : Type} {e : EvmYul.Yul.Exception} (s : State) :
    DoneAgrees (α := α) (.error e) (InteractionSemantics.Primitive.fail s e) :=
  ⟨.error { exception := e, state := s }, rfl, rfl⟩

/-! ## Witness lifting (PART A monotonicity, per function) -/

/-- Generic lift: a settled our-side agreement survives more fuel, given a
monotonicity rewrite for the underlying function. -/
theorem liftMax {α : Type} {native : Except EvmYul.Yul.Exception α}
    { oursSmall oursLarge : Open α}
    (hN : NativeSettled native)
    (h : DoneAgrees native oursSmall)
    (hMono : Settled oursSmall → oursLarge = oursSmall) :
    DoneAgrees native oursLarge := by
  rw [hMono (settled_of_doneAgrees hN h)]; exact h

theorem exec_lift {native : Except EvmYul.Yul.Exception State}
    {m M : Nat} {stmt : Stmt} {code : Option YulContract} {s : State}
    (hN : NativeSettled native) (hle : m ≤ M)
    (h : DoneAgrees native (exec m stmt code s)) :
    DoneAgrees native (exec M stmt code s) :=
  liftMax hN h (fun hs => exec_mono hle stmt code s hs)

theorem execSeq_lift {native : Except EvmYul.Yul.Exception State}
    {m M : Nat} {stmts : List Stmt} {code : Option YulContract} {s : State}
    (hN : NativeSettled native) (hle : m ≤ M)
    (h : DoneAgrees native (execSeq m stmts code s)) :
    DoneAgrees native (execSeq M stmts code s) :=
  liftMax hN h (fun hs => execSeq_mono hle stmts code s hs)

theorem eval_lift {native : Except EvmYul.Yul.Exception (State × Word)}
    {m M : Nat} {expr : Expr} {code : Option YulContract} {s : State}
    (hN : NativeSettled native) (hle : m ≤ M)
    (h : DoneAgrees native (eval m expr code s)) :
    DoneAgrees native (eval M expr code s) :=
  liftMax hN h (fun hs => eval_mono hle expr code s hs)

theorem evalArgs_lift {native : Except EvmYul.Yul.Exception (State × List Word)}
    {m M : Nat} {args : List Expr} {code : Option YulContract} {s : State}
    (hN : NativeSettled native) (hle : m ≤ M)
    (h : DoneAgrees native (evalArgs m args code s)) :
    DoneAgrees native (evalArgs M args code s) :=
  liftMax hN h (fun hs => evalArgs_mono hle args code s hs)

theorem evalValues_lift {native : Except EvmYul.Yul.Exception (State × List Word)}
    {m M : Nat} {expr : Expr} {code : Option YulContract} {s : State}
    (hN : NativeSettled native) (hle : m ≤ M)
    (h : DoneAgrees native (evalValues m expr code s)) :
    DoneAgrees native (evalValues M expr code s) :=
  liftMax hN h (fun hs => evalValues_mono hle expr code s hs)

theorem call_lift {native : Except EvmYul.Yul.Exception (State × List Word)}
    {m M : Nat} {args : List Word}
    {fn? : Option EvmYul.Yul.Ast.YulFunctionName} {code : Option YulContract}
    {s : State}
    (hN : NativeSettled native) (hle : m ≤ M)
    (h : DoneAgrees native (call m args fn? code s)) :
    DoneAgrees native (call M args fn? code s) :=
  liftMax hN h (fun hs => call_mono hle args fn? code s hs)

theorem loop_lift {native : Except EvmYul.Yul.Exception State}
    {m M : Nat} {cond : Expr} {post body : List Stmt}
    {code : Option YulContract} {s : State}
    (hN : NativeSettled native) (hle : m ≤ M)
    (h : DoneAgrees native (loop m cond post body code s)) :
    DoneAgrees native (loop M cond post body code s) :=
  liftMax hN h (fun hs => loop_mono hle cond post body code s hs)

end VerityBridge
end Yul
end EvmCompiler
