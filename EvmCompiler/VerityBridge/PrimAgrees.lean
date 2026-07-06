import EvmCompiler.VerityBridge.RequestFree

/-!
# W2 — the primitive layer of the Verity interpreter-equivalence bridge

For a `BridgeOp`, our `InteractionSemantics.Primitive.openEval` degenerates to a native-agreeing
`.done` leaf:

* `closedEval_agrees` — `closedEval` is native `primCall` wrapped through `toResult`
  (the `EXTCODEHASH` override is excluded by `BridgeOp`);
* `openEval_agrees` — `openEval (fuel+1)` burns one tick and delegates to
  `closedEval fuel` (external/GAS/MSIZE branches excluded by `BridgeOp`);
* `primCall_fuel_insensitive` — the W0 same-fuel lemma: native `primCall` uses its
  fuel only for the external call recursions (out of fragment), so on a `BridgeOp`
  it is constant above 1;
* `doneAgrees_openEval_shift` / `doneAgrees_openEval` — the boundary corollaries
  the W3 mutual induction consumes.
-/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

open EvmYul (Operation)

/-- Native error payloads gain the site-local bookkeeping `Failure` carries. -/
def toResult (s : InteractionSemantics.State) :
    Except EvmYul.Yul.Exception (InteractionSemantics.State × List Word) →
      Except InteractionSemantics.Failure (InteractionSemantics.State × List Word)
  | .ok v => .ok v
  | .error e => .error { exception := e, state := s.afterException e }

/-- `toResult` always agrees with the native result it wraps. -/
theorem resultAgrees_toResult (s : InteractionSemantics.State)
    (r : Except EvmYul.Yul.Exception (InteractionSemantics.State × List Word)) :
    ResultAgrees r (toResult s r) := by
  cases r with
  | ok v => exact rfl
  | error e => exact rfl

/-! ## `closedEval` is native `primCall` wrapped -/

theorem closedEval_agrees {op : Operation .Yul} (hOp : BridgeOp op)
    (fuel : Nat) (s : InteractionSemantics.State) (args : List Word) :
    InteractionSemantics.Primitive.closedEval fuel s op args =
      .done (toResult s (EvmYul.Yul.primCall fuel s op args)) := by
  have hHash : op ≠ .Env .EXTCODEHASH := hOp.2.2.2
  unfold InteractionSemantics.Primitive.closedEval
  -- The `op, fuel` match hits the default arm (op ≠ EXTCODEHASH).
  split
  · exact absurd rfl hHash
  · exact absurd rfl hHash
  · -- default arm: `match primCall … with | .ok … | .error …`
    cases h : EvmYul.Yul.primCall fuel s op args with
    | ok v => rfl
    | error e => rfl

/-! ## `openEval (fuel+1)` delegates to `closedEval fuel` -/

theorem openEval_agrees {op : Operation .Yul} (hOp : BridgeOp op)
    (fuel : Nat) (s : InteractionSemantics.State) (args : List Word) :
    InteractionSemantics.Primitive.openEval (fuel + 1) s op args =
      InteractionSemantics.Primitive.closedEval fuel s op args := by
  have hExt : Simulation.ExternalKind.ofYulOperation? op = none := hOp.1
  have hGas : op ≠ .StackMemFlow .GAS := hOp.2.1
  have hMsize : op ≠ .StackMemFlow .MSIZE := hOp.2.2.1
  unfold InteractionSemantics.Primitive.openEval
  rw [hExt]
  -- `match op with | GAS | MSIZE | _ => closedEval fuel …`
  split <;> first | rfl | (rename_i heq; simp_all)

/-! ## W0 fuel-insensitivity (same-fuel decision)

Native `primCall` consumes its fuel only inside the CALL/CALLCODE/DELEGATECALL/
STATICCALL arms (the concrete external-call recursion). `BridgeOp` excludes every
one of those, so `primCall` is constant in fuel above `1`. -/

private theorem callKind_none_of_bridge {op : Operation .Yul} (hOp : BridgeOp op) :
    Simulation.CallKind.ofYulOperation? op = none := by
  have hExt : Simulation.ExternalKind.ofYulOperation? op = none := hOp.1
  unfold Simulation.ExternalKind.ofYulOperation? at hExt
  cases hc : Simulation.CallKind.ofYulOperation? op with
  | none => rfl
  | some k => rw [hc] at hExt; simp at hExt

theorem primCall_fuel_insensitive {op : Operation .Yul} (hOp : BridgeOp op)
    (n m : Nat) (s : InteractionSemantics.State) (args : List Word) :
    EvmYul.Yul.primCall (n + 1) s op args =
      EvmYul.Yul.primCall (m + 1) s op args := by
  have hCall : Simulation.CallKind.ofYulOperation? op = none :=
    callKind_none_of_bridge hOp
  cases op with
  | System sop =>
      cases sop <;>
        first
          | (rw [EvmYul.Yul.primCall.eq_def, EvmYul.Yul.primCall.eq_def]; done)
          | exact absurd hCall (by simp [Simulation.CallKind.ofYulOperation?])
  | _ => rw [EvmYul.Yul.primCall.eq_def, EvmYul.Yul.primCall.eq_def]

/-! ## Boundary corollaries for the W3 mutual induction -/

/-- Off-by-one form (definitional, holds at every fuel): our `openEval (n+1)`
agrees with native `primCall n`. -/
theorem doneAgrees_openEval_shift {op : Operation .Yul} (hOp : BridgeOp op)
    (n : Nat) (s : InteractionSemantics.State) (args : List Word) :
    DoneAgrees (EvmYul.Yul.primCall n s op args)
      (InteractionSemantics.Primitive.openEval (n + 1) s op args) := by
  rw [openEval_agrees hOp, closedEval_agrees hOp]
  exact DoneAgrees.mk (resultAgrees_toResult s _)

/-- Same-fuel form (requires `2 ≤ fuel`, the residue of the primitive off-by-one):
native `primCall (n+2)` agrees with our `openEval (n+2)`. This is the shape the W3
induction consumes at expression/statement primitive sites. -/
theorem doneAgrees_openEval {op : Operation .Yul} (hOp : BridgeOp op)
    (n : Nat) (s : InteractionSemantics.State) (args : List Word) :
    DoneAgrees (EvmYul.Yul.primCall (n + 2) s op args)
      (InteractionSemantics.Primitive.openEval (n + 2) s op args) := by
  have hFuel : EvmYul.Yul.primCall (n + 2) s op args =
      EvmYul.Yul.primCall (n + 1) s op args :=
    primCall_fuel_insensitive hOp (n + 1) n s args
  rw [hFuel]
  exact doneAgrees_openEval_shift hOp (n + 1) s args

end VerityBridge
end Yul
end EvmCompiler
