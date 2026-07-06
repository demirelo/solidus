# Phase 3 Deep Dive: the interpreter-equivalence bridge

Annex to `VERITY_ROADMAP.md`. Workflow: `$verified-compiler-lab`.
Recon performed 2026-07-05 directly against the code on both sides.

## STATUS (2026-07-06): PHASE 3 COMPLETE

The interpreter-equivalence bridge is finished, `sorry`/`admit`/`axiom`-free, on
branch `verity-composition`. `#print axioms` on every public theorem of the seven
`VerityBridge` modules is a subset of `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`, no stray axiom); the public spine below prints exactly those three.

**Final public theorems (`EvmCompiler.Yul.VerityBridge`):**
- The eight unconditional agreement corollaries: `evalTail_agrees`,
  `evalArgs_agrees`, `evalValues_agrees`, `eval_agrees`, `call_agrees`,
  `execSeq_agrees`, `exec_agrees`, `loop_agrees` — each
  `∀ n …, ∃ m, DoneAgrees (native.f n …) (ours.f m …)` under the relevant
  `Bridge*` predicate + `BridgeCode` + `CodeBridge`.
- The knot `bridgeAgreesAt : PrimBoundary → ∀ n, BridgeAgreesAt n`, discharged by
  `primBoundary` (= `primCall_preserves_codeBridge`) into `bridgeAgrees`.
- W4 `callDispatcher_agrees` and the **W5 endpoint**
  `native_run_to_interaction_run (n) (contract) (s) : BridgeContract contract →
  s.executionEnv.code = contract → CodeBridge s → ∃ m, DoneAgrees
  (EvmYul.Yul.callDispatcher n (some contract) s)
  (InteractionSemantics.Program.openRun m contract s)`.

Files: `RequestFree`, `PrimAgrees`, `ExecAgrees`, `FuelMono`, `ExecAgreesFamily`,
`ExecAgreesCases` (case lemmas + knot + corollaries), `NativeRun` (W4/W5).

---

## Historical status (2026-07-06, stage 5 of PART B)

The ratified **unbounded ∃-fuel** bridge form (commit 6769774bf) is the vehicle;
PART A (our-side fuel monotonicity), the primitive layer (W2), and the native
equation lemmas are all committed green. Stage 5 landed the two ratified
corrections and the mechanical core:

**Two ratified/discovered corrections (binding):**
1. `CodeBridge` = **presence only** (`accountMap.find? codeOwner ≠ none`), split
   from the invariant `BridgeCode` (override bridge-ness). Native `call` demands
   the owner account present even under `codeOverride = some c`; ours does not —
   so agreement needs presence, threaded/preserved by Part B0. (ratified
   282ca375b)
2. **For-post break/continue exclusion** (discovered stage 5): a For-loop *post*
   yielding a `Break`/`Continue` checkpoint makes both interpreters recurse from
   `mkOk Checkpoint = default` (empty account map), where native `call` raises
   `MissingContract` but ours proceeds — agreement is *false* there. Such posts
   are compiler-rejected Yul; the fragment predicate now excludes them
   (`breakContinueFree?` in RequestFree.lean; the `loop` conjunct carries
   `BreakContinueFreeStmts post`).

**Landed green (theorem names):**
- `primCall_preserves_codeBridge` (PrimAgrees) — the ratified boundary leaf: a
  `BridgeOp` `primCall` returning `.ok` preserves owner presence and `codeOwner`.
  Empirically refutes the old SELFDESTRUCT worry (it is terminal `.error`; only
  SSTORE/TSTORE mutate the map, both by `insert`).
- `nativePreservesAt_of_prim` (ExecAgreesCases) — Part B0, native-side
  `CodeBridge` preservation mutual (`StateBridge`/`IsJumpBC`).
- `doneAgrees_bind`/`wrap`/`pure`/`error` (ExecAgreesFamily) — the one-step closer.
- `caseEvalTail` + the `KnotProper` infrastructure (equation restatements,
  `PrimBoundary`, closers).

**In progress / remaining for Phase-3 exit:** the seven combining case lemmas
(`caseEvalArgs/…/caseLoop`, via the settled/`_lift` monotonicity recipe), the
strong-induction knot `bridgeAgreesAt`, the eight unconditional public
corollaries (`exec_agrees` etc., instantiating `hPrim := primCall_preserves_codeBridge`),
`callDispatcher_agrees` (native `callDispatcher (some contract) s` = native
`call [] none (some contract) s` under the harness installation + `CodeBridge`,
then `call_agrees`; our dispatcher run is `Program.openRun = call [] none (some
code)`), the W5 `native_run_to_interaction_run` endpoint, and the `#print axioms`
audit.

---

## 1. What the recon changed

The roadmap assumed Phase 3 was a semantic bridge between two towers. The
code says it is much less than that:

- **F1 — the kernel is a clause-for-clause mirror.** `Yul.Source.Effectful`
  (EffectSemantics.lean:85–401) is a monadic generalization of the native
  interpreter `EvmYul.Yul.exec` mutual block (Interpreter.lean:240–774):
  identical clause structure per constructor (Block/Let/Assign/If/
  ExprStmtCall/Switch/For/Continue/Break/Leave), identical helper reuse
  (`EvmYul.Yul.checkDeclaration`, `checkAssignment`, `selectSwitchCase`,
  `initcall`, `reviveJump`, `overwrite?`, `setStore`, `restrictStoreTo`,
  `zeroFill`), identical arg-reversal discipline, identical loop checkpoint
  dance (OutOfFuel/Break/Leave/Continue arms in the same order), and the
  same fuel-decrement pattern per clause. `Canonical` (line 3130) is abbrevs
  over `Effectful`; `InteractionSemantics.exec` = `Canonical.exec` at
  `M = Open`, `σ = EvmYul.Yul.State`, `stateModel = id/id`.
- **F2 — the primitive layer literally delegates to native.**
  `Primitive.openEval` (InteractionSemantics.lean:164) branches:
  external call/create kinds → `.request`; GAS/MSIZE → `.request .resource`;
  EVERYTHING else → `closedEval` = native `EvmYul.Yul.primCall` wrapped in
  `.done` (with one EXTCODEHASH override via `CodeErasedState.extCodeHash`).
  On a request-free op surface the two primitive semantics are the same
  function up to the `.done` wrapper and error-state bookkeeping.
- **F3 — the state types are identical** (`InteractionSemantics.State :=
  EvmYul.Yul.State`), so there is no state relation: the bridge invariant is
  raw equality on `.ok` results.
- **F4 — failure payloads differ only in bookkeeping.** Native returns
  `.error (e : Yul.Exception)`; ours returns `.error {exception := e,
  state := σ}` where σ is site-local. The observable final states for
  halting exceptions travel INSIDE the exception constructors
  (`.YulHalt final _`, `.Revert final`) identically on both sides, so a
  thin relation (exception equality) suffices downstream.
- **F5 — fuel skew is at most a primitive off-by-one.** At equal top-level
  fuel, our `openEval` burns one tick before calling `primCall fuel'` where
  native calls `primCall fuel'` directly. Native `primCall` uses its fuel
  only for the concrete external-call recursion (Interpreter.lean:247ff) —
  out of fragment. So fragment ops are fuel-insensitive above 1 and
  same-fuel equality is available (W0 confirms).
- **F6 — the prior 72k-line failure is not on main.** `Yul/Reference.lean`
  exists only in the `no-gas-accepted-yul` worktree. Optional salvage of
  single-step unfold lemmas; nothing to clean up on this branch.

Consequence: **the bridge is a request-free-degeneration theorem, not a
simulation.** On fragment programs, our interaction tree never branches; it
IS a `.done` leaf whose value mirrors the native result.

## 2. Frozen bridge statement (write and typecheck BEFORE any proof)

Definitions (new file `EvmCompiler/VerityBridge/RequestFree.lean`):

```lean
/-- Ops that make `Primitive.openEval` answer without a `.request`:
not an external call/create kind, not GAS, not MSIZE.
(EXTCODEHASH additionally excluded from the *fragment* because closedEval
overrides it; it is request-free but not native-agreeing.) -/
def RequestFreeOp (op : EvmYul.Operation .Yul) : Prop := ...
def requestFreeOp? : EvmYul.Operation .Yul → Bool := ...   -- computable twin
-- Lift structurally: RequestFreeExpr / RequestFreeStmt / RequestFreeStmts /
-- RequestFreeContract (every function body + dispatcher), with a decidable
-- twin each and `requestFree?_iff` equivalences. Phase 1's Fragment implies
-- RequestFreeContract.
```

Outcome relation (thin by design — F4):

```lean
def ResultAgrees (native : Except EvmYul.Yul.Exception α)
    (ours : Except (Failure State) α) : Prop :=
  match native, ours with
  | .ok a, .ok b => b = a
  | .error e, .error f => f.exception = e
  | _, _ => False

def DoneAgrees (native : Except EvmYul.Yul.Exception α)
    (ours : Open α) : Prop :=
  ∃ r, ours = .done r ∧ ResultAgrees native r
```

The mutual bridge family (new file `EvmCompiler/VerityBridge/ExecAgrees.lean`)
— one theorem per kernel function, same-fuel form (fallback: `∃ fuel' ≤ 2*fuel`
if W0 falsifies F5):

```lean
theorem exec_agrees (fuel) (stmt) (code?) (s : EvmYul.Yul.State)
    (hStmt : RequestFreeStmt stmt) (hCode : RequestFreeCode? code? s) :
    DoneAgrees (EvmYul.Yul.exec fuel stmt code? s)
      (InteractionSemantics.exec fuel stmt code? s)
-- + evalArgs_agrees, evalTail_agrees, evalValues_agrees, eval_agrees,
--   call_agrees, execSeq_agrees, loop_agrees  (one mutual induction), and
--   callDispatcher_agrees as a corollary.
```

`RequestFreeCode?` covers the active code resolution (`resolveActiveCode?`):
the override contract and (for `none`) the code-owner account's contract are
request-free — in practice always the `some contract` route used by
`compile_correct`, so state it for `code? = some c` first and add the
account-lookup form only if composition needs it (it shouldn't).

Statement-truth checks done at freeze time:
- fuel = 0 on both sides → both `.error OutOfFuel` (ResultAgrees holds). ✓
- `State.OutOfFuel`/`Checkpoint` propagation through `execSeq` matches
  native (`model.source` = id here). ✓ by clause inspection.
- `head!`/`lookup!` partiality: identical on both sides (same functions on
  same values once `.ok` states are equal). ✓
- EXTCODEHASH: request-free but NOT native-agreeing (override) — must be
  excluded by `RequestFreeOp` (fold into the predicate, do not special-case
  the proof). Naming honesty: predicate name should be `BridgeOp` if it
  excludes more than requests — decide at freeze.

## 3. Workstreams

### W0 — Recon closure (½ day, blocking)
- Verify F5 mechanically: for every fragment op, `primCall (fuel+1) … =
  primCall (fuel'+1) …` (state a `primCall_fuel_insensitive` lemma per
  family; try `decide`-free structural proof; if any fragment op is
  fuel-sensitive, switch the family to the ∃-fuel form — decision recorded
  in PROGRESS_LOG as `theorem-boundary`).
- Enumerate the exact op set Verity's fragment emits (their builtin table ∩
  emitted corpus of the 8 artifacts) and check it against `requestFreeOp?`.
- Confirm `compile_correct`'s source run always supplies `some contract`
  (it does — `(some artifact...contract)`) so `RequestFreeCode?` can be the
  trivial `some` form.

### W1 — Definitions + downstream-consumption check (1 day)
- `RequestFree*` + computable twins + `Fragment → RequestFree` lemma.
- `ResultAgrees`/`DoneAgrees`.
- CHECK (blocking for Phase 5, cheap now): every consumer of our exec's
  failure payload on the compile_correct source side
  (`VerifiedStackObjectPrefixDoneRel`, `ObservableDoneRel`, `ExceptionRel`)
  reads only `Failure.exception` (and the states carried INSIDE
  YulHalt/Revert), never `Failure.state` — else strengthen `ResultAgrees`
  for exactly those constructors. Log result.

### W2 — Primitive layer (2–4 days)
- `closedEval_agrees`: for `RequestFreeOp op`,
  `closedEval fuel s op args = .done (toResult (primCall fuel s op args))`
  where `toResult` maps errors through `afterException` — near-definitional;
  one lemma, cases on the primCall result.
- `openEval_agrees`: `RequestFreeOp op → openEval (fuel+1) s op args =
  closedEval fuel s op args` — definitional by the match; plus the
  fuel-alignment lemma from W0 to restore same-fuel form.
- NO per-opcode proofs. The case split is over the three openEval branches,
  not over 60 opcodes. If a per-opcode obligation appears anywhere except
  inside `primCall_fuel_insensitive` families, stop (anti-zoo tripwire).

### W3 — The mutual induction (2–4 weeks; the core)
One file, one `mutual` block of eight theorems, induction by the SAME
lexicographic measure the definitions use: `(fuel, tag, sizeOf ast)`.
Per-case recipe (uniform, mechanical):
1. Unfold one step on each side via paired one-step equation lemmas
   (`exec_succ_block`, native `exec_succ_block`, …) — write these ~20
   equation lemmas FIRST (they are `rfl`-or-`simp only` facts; our side
   partially exists: `eval_eq_bind` family in InteractionSemantics.lean).
2. Case on the native subresult; apply the IH to convert our subterm to
   `.done`; reduce the Interaction bind with the existing simp set
   (`bind_fail`, done-bind lemmas in Simulation/Interaction.lean + the
   `result_*` simp lemmas at EffectSemantics.lean:403–430).
3. Error cases short-circuit identically (ResultAgrees exception equality).
Proof-engineering rules (Lean blowup discipline):
- `simp only` with a curated local simp set; never `simp_all` across both
  interpreters; never unfold `primCall` (W2 seals it).
- Each mutual case that exceeds ~80 lines gets its own private helper lemma
  named by AST constructor (NOT by program shape).
- Build narrowly: `lake env lean EvmCompiler/VerityBridge/ExecAgrees.lean`.
Anti-zoo tripwires (hard stops, log `architecture-risk`):
- any lemma named after a statement COMBINATION (if-in-for, let-then-call);
- any lemma family enumerated over opcodes outside W0's fuel lemmas;
- the file growing >5k lines or any single case >300 lines.
Expected size: 1.5–3k lines total including equation lemmas. The prior
72k-line failure attempted per-shape terminal wrappers without the mutual
statement; this plan writes the mutual statement first and only accepts
leaves the induction demands.

### W4 — Entry adapter (2–4 days)
- `callDispatcher_agrees` corollary of the mutual family (both sides define
  callDispatcher as the same wrapper: FunctionDefinition.Def [] []
  [dispatcher] + initcall + revive/overwrite/setStore).
- Handshake lemma toward Verity: from
  `EvmYul.Yul.callDispatcher fuel none s = result` (their harness form,
  code resolved via `s.executionEnv.code`) to our
  `exec fuel (.Block [dispatcher]) (some contract) s' ~ result` where
  s'/s differ only by the initcall bookkeeping — reconcile the `none`
  codeOverride: their harness installs the contract in `executionEnv.code`
  AND the account; native `call`/dispatcher reads `executionEnv.code`
  directly, ours resolves `some contract`. State the lemma with both
  installations equal (they are, by their `initialState` construction).
- This is the ONLY place their harness conventions are touched; keep
  Verity-side imports confined to this file.

### W5 — Fuel adequacy + packaging (3–5 days)
- If same-fuel holds (expected): nothing to do beyond W0's lemmas.
- Else: monotonicity for native exec (new lemmas about the pinned dep,
  living in our repo) + ours (extend FunctionsInteractionFuel patterns),
  and the ∃-fuel corollary.
- Package the Phase-5-facing endpoint:
  `theorem native_run_to_interaction_run` — exactly the fact Phase 5's
  composition consumes, stated over `DoneAgrees` + `callDispatcher`.
- Audit gate: `#print axioms` on the mutual family = standard three;
  PROGRESS_LOG `audit` entry; commit.

## 4. Risk register
- **R1 (low): fuel skew is worse than off-by-one somewhere** (e.g. the
  ExprStmtCall user-call double-match exists on BOTH sides — checked — but
  W0 may find another). Mitigation: ∃-fuel fallback form; cost ≈ +1 week.
- **R2 (low-medium): a downstream done-relation reads `Failure.state`**
  beyond YulHalt/Revert payloads → strengthen ResultAgrees on exactly the
  constructors involved (W1 discovers this in a day, not in week 3).
- **R3 (medium): mutual-induction termination friction in Lean** (the
  theorems recurse along the same measure as the defs; `decreasing_by`
  should mirror the defs' `omega` script). Mitigation: state theorems as a
  single mutual block with explicit `termination_by`; if Lean fights,
  fall back to a fuel-strong-induction wrapper (induction on fuel with a
  ∀-AST inner statement) — semantically identical, structurally simpler.
- **R4 (low): native-side one-step equation lemmas churn** if EVMYulLean pin
  moves — single-pin invariant already frozen in the roadmap.
- **R5 (external): Verity fragment emits an op outside RequestFree** (gas?
  msize? codesize?) — W0 enumerates; any hit goes to the Phase 1 fragment
  gate, NOT into the bridge.

## 5. Milestones & gates
- M3.0: W0+W1 done; bridge statements typecheck (`sorry`-free defs,
  statements with `sorry` bodies allowed ONLY on a scratch branch, never
  committed to the campaign branch). Gate: statement review (adversarial
  self-review; oracle if re-enabled) BEFORE W3 starts.
- M3.1: W2 committed green.
- M3.2: first third of W3 (expressions: evalArgs/evalTail/evalValues/eval)
  green — this de-risks the whole approach; re-estimate here.
- M3.3: W3 complete (statements/loops/call), W4 corollaries green.
- M3.4: W5 packaging + audit gate; Phase 3 exit.

Total estimate: **3–6 weeks** solo-agent effort, front-loaded risk retired
at M3.2. This supersedes the roadmap's "60–70% of campaign" sizing: with F1–F5
confirmed, Phase 3 is closer to 40–50% and the plan above is the whole of it.
