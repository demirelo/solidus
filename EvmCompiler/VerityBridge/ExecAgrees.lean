import EvmCompiler.VerityBridge.PrimAgrees

/-!
# W3a — expression third of the Verity interpreter-equivalence bridge

**Status: the expression theorem family is BLOCKED on a fuel-form decision that is
above this workstream's pay grade (see the boundary section below and the
`theorem-boundary` / `architecture-risk` entries in `PROGRESS_LOG.md`).**

This file commits the parts of W3a that are true independent of that decision:

* the ~13 native one-step equation lemmas (`native_*`), the mirror of our-side
  `EvalArgs.*` / `EvalValues.*` / `eval_eq_bind` family in `InteractionSemantics`;
* two sorry-free, axiom-clean boundary witnesses that pin down exactly why the
  planned same-fuel (and the fallback fixed-shift) `DoneAgrees` families are
  *false*, not merely awkward.

## The fuel-form boundary (why the mutual family is not yet stated)

The two interpreters are in exact fuel lockstep **except at the primitive leaf**:

* native `evalValues (f'+1) (.Call (.inl op) …)` calls `primCall f'` directly, and
  native `primCall` does **not** consume fuel for a fragment (`BridgeOp`) op — it
  is fuel-insensitive above `0` (`primCall_fuel_insensitive`). So native spends
  exactly **one** fuel unit to execute a fragment primitive.
* our `evalValues (f'+1) (.Call (.inl op) …)` calls `openEval f'`, and `openEval`
  **decrements again** (`openEval (g+1) = closedEval g = primCall g` wrapped). So
  our side spends **two** fuel units to execute the same primitive.

Consequently our side is strictly fuel-hungrier at every primitive, by exactly
one unit per primitive on the evaluation path. No *constant* fuel offset relates
the two interpreters:

* **Same-fuel is false.** `native_evalValues_stable_of_bridge` +
  `our_openEval_one_bridge_outOfFuel` witness it: at `evalValues` fuel `2` with a
  nullary `BridgeOp` (e.g. `CALLER`, whose args evaluate to `[]` at fuel `1` on
  both sides), native reduces to `primCall 1` — a stable, fuel-insensitive,
  non-`OutOfFuel` computation — while our side is forced to `fail OutOfFuel`
  (its `openEval 1` double-decrements to `primCall 0`). So
  `DoneAgrees (native.evalValues 2 …) (our.evalValues 2 …)` is refuted for every
  state on which `caller()` succeeds.
* **Fixed shift is false too.** `DoneAgrees (native.evalValues n …)
  (our.evalValues (n+1) …)` fails at `n = 0` on a *leaf* (`.Var`/`.Lit`, and
  `evalArgs []`): native `evalValues 0` is `OutOfFuel` while our `evalValues 1`
  already does the real lookup/return. The `+1` is right for the primitive path
  but over-shoots the cheap leaves, which do not spend the extra `openEval` tick.
  Symmetric `n+1`-native-more fails the same way with roles reversed.

The relationship is therefore expression-*structure* dependent (primitive = +1,
leaf = +0), so the correct statement is one of:

1. an **∃-fuel** family (`∀ n, ∃ m ≤ 2·n, DoneAgrees (native … n) (ours … m)`),
   discharged with our-side and native-side **fuel monotonicity** — this is the
   plan's R1 mitigation / W5 packaging, pulled earlier; or
2. a **weakened outcome relation** that is vacuous when our side is
   `fail OutOfFuel` (i.e. "whenever our side finishes, it agrees"), which is
   same-fuel and threads, but changes the *frozen* `DoneAgrees` from stage 1.

Both are bridge-architecture decisions the plan owner must ratify (the W3a brief
forbids inventing a new bridge architecture unilaterally). W3b should resolve the
fuel form first, then state the mutual family; every lemma below is reusable
unchanged in either resolution.

The intended `AgreesBelow` bundle design (for whichever form is chosen) is a
single structure carrying statement-level agreement (`exec`/`execSeq`/`call`/
`loop`) at strictly smaller fuel, so the expression lemmas close as theorems
"expression agreement at fuel, GIVEN statement agreement strictly below fuel",
and W3b ties the knot by strong induction on fuel. The only statement-level
field the expression family actually consumes is `call` (via `evalValues`'s
`.Call (.inr _)` arm); everything else in the expression family recurses at
strictly smaller fuel and is handled by the strong-induction hypothesis.
-/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

/-! ## Native one-step equation lemmas

Paired with our-side `InteractionSemantics.EvalArgs.*` / `.EvalValues.*` /
`eval_eq_bind`. These unfold exactly one native step; `primCall` is never
unfolded (PrimAgrees seals it). All are `rfl`/`rw`-definitional. -/

namespace Native

open EvmYul.Yul EvmYul.Yul.Ast

variable (fuel : Nat) (code : Option YulContract) (s : State)

/-- `evalValues` at exhausted fuel. -/
theorem evalValues_zero (expr : Expr) :
    evalValues 0 expr code s = .error .OutOfFuel := by rw [evalValues]

/-- `evalValues` on a primitive call: ordered args (reversed) then `primCall`. -/
theorem evalValues_prim (prim : EvmYul.Operation .Yul) (args : List Expr) :
    evalValues (fuel + 1) (.Call (.inl prim) args) code s =
      (match reverse' (evalArgs fuel args.reverse code s) with
       | .ok (s, args) => primCall fuel s prim args
       | .error e => .error e) := by
  rw [evalValues]; cases reverse' (evalArgs fuel args.reverse code s) <;> rfl

/-- `evalValues` on a user-function call: ordered args (reversed) then `call`. -/
theorem evalValues_call (fn : YulFunctionName) (args : List Expr) :
    evalValues (fuel + 1) (.Call (.inr fn) args) code s =
      (match reverse' (evalArgs fuel args.reverse code s) with
       | .ok (s, args) => call fuel args (some fn) code s
       | .error e => .error e) := by
  rw [evalValues]; cases reverse' (evalArgs fuel args.reverse code s) <;> rfl

/-- `evalValues` on a variable reference. -/
theorem evalValues_var (id : EvmYul.Identifier) :
    evalValues (fuel + 1) (.Var id) code s =
      (match s.lookup? id with
       | some v => .ok (s, [v])
       | none => .error (.UnknownIdentifier id)) := by
  rw [evalValues]; cases s.lookup? id <;> rfl

/-- `evalValues` on a literal. -/
theorem evalValues_lit (v : EvmYul.Literal) :
    evalValues (fuel + 1) (.Lit v) code s = .ok (s, [v]) := by rw [evalValues]

/-- `eval` wraps `evalValues` with `head'`. -/
theorem eval_eq (expr : Expr) :
    eval fuel expr code s = head' (evalValues fuel expr code s) := by rw [eval]

/-- `evalArgs` at exhausted fuel. -/
theorem evalArgs_zero (args : List Expr) :
    evalArgs 0 args code s = .error .OutOfFuel := by rw [evalArgs]

/-- `evalArgs` on the empty argument list. -/
theorem evalArgs_nil : evalArgs (fuel + 1) [] code s = .ok (s, []) := by rw [evalArgs]

/-- `evalArgs` on a nonempty argument list: head value then tail threading. -/
theorem evalArgs_cons (arg : Expr) (args : List Expr) :
    evalArgs (fuel + 1) (arg :: args) code s =
      evalTail fuel args code (eval fuel arg code s) := by rw [evalArgs]

/-- `evalTail` at exhausted fuel on a successful prior result. -/
theorem evalTail_zero_ok (args : List Expr) (p : State × EvmYul.Literal) :
    evalTail 0 args code (.ok p) = .error .OutOfFuel := by rw [evalTail]

/-- `evalTail` propagates a prior error unchanged. -/
theorem evalTail_error (args : List Expr) (e : EvmYul.Yul.Exception) :
    evalTail fuel args code (.error e) = .error e := by rw [evalTail]

/-- `evalTail` conses the prior value onto the remaining evaluated args. -/
theorem evalTail_ok (args : List Expr) (p : State × EvmYul.Literal) :
    evalTail (fuel + 1) args code (.ok p) =
      cons' p.2 (evalArgs fuel args code p.1) := by rw [evalTail]

end Native

/-! ## Boundary witnesses (sorry-free, axioms = standard three)

These pin down the fuel-form obstruction described in the module docstring. They
are also directly reusable in either resolution to discharge the fuel-1 primitive
`OutOfFuel` cases. -/

/-- Our `openEval` at fuel `1` is *always* `OutOfFuel` for a `BridgeOp`: it
double-decrements (`openEval 1 → closedEval 0 → primCall 0 = OutOfFuel`). This is
the source of the +1 fuel gap versus native `primCall`, which does real work at
fuel `1`. -/
theorem our_openEval_one_bridge_outOfFuel {op : EvmYul.Operation .Yul}
    (hOp : BridgeOp op) (s : InteractionSemantics.State) (args : List Word) :
    InteractionSemantics.Primitive.openEval 1 s op args =
      InteractionSemantics.Primitive.fail (s.afterException .OutOfFuel) .OutOfFuel := by
  have hPrim : EvmYul.Yul.primCall 0 s op args = .error .OutOfFuel := by
    conv_lhs => rw [EvmYul.Yul.primCall]
  rw [show (1 : Nat) = 0 + 1 from rfl, openEval_agrees hOp, closedEval_agrees hOp, hPrim]
  rfl

/-- Native `primCall` on a nullary `BridgeOp` is fuel-insensitive above `0`
(`primCall 1 = primCall 2 = …`): its fuel-1 value is the stable *real* result,
not the fuel-0 `OutOfFuel`. Contrast `our_openEval_one_bridge_outOfFuel`: at the
same top-level `evalValues` fuel `2`, native computes this stable result while our
side is forced to `OutOfFuel`. Hence same-fuel `DoneAgrees` is refuted. -/
theorem native_evalValues_stable_of_bridge {op : EvmYul.Operation .Yul}
    (hOp : BridgeOp op) (m n : Nat) (s : EvmYul.Yul.State) (args : List Word) :
    EvmYul.Yul.primCall (m + 1) s op args = EvmYul.Yul.primCall (n + 1) s op args :=
  primCall_fuel_insensitive hOp m n s args

end VerityBridge
end Yul
end EvmCompiler
