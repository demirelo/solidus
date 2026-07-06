# Verity Composition Roadmap

Campaign home: branch `verity-composition` (this worktree). Workflow:
`$verified-compiler-lab`. The Verity 4.28 port lives at `external/verity`
(fork `danrobinson/verity`, branch `evmyul-pin-align` @ `03a4f711`, EVMYulLean
pin aligned to main's `3c5c44a6`, full build clean).

## Objective (the crown)

One Lean theorem, in spec vocabulary only:

> For every Verity contract spec in the frozen supported fragment, if
> `compileVerity? spec = some bytes`, then for every normalized transaction,
> guard-safe dispatch, and initial EVM state publicly described by
> (code = bytes, pc = 0, empty stack, world encoding of the contract storage,
> gas = g), the pinned `EvmYul.EVM.X` run of `bytes` yields an outcome in
> `VerityOutcome`: **completed** with Verity's denoted result (success flag,
> return word, event series, storage on the declared observable slots) |
> **source-demanded revert** with the denoted failure | **committal
> out-of-gas** with pinned rollback — nothing else.

Trusted base afterwards: Lean kernel + pinned EvmYul interpreter + the frozen
spec files (Verity `Core` denotation, our `Solidus` observation vocabulary,
the composed `VerityOutcome` relation). Eliminated: solc from Verity's TCB,
all text/JSON transport, the two-toolchain gap.

Spec-vocabulary rule (binding): the crown may mention Verity's
CompilationModel/denotation, `EvmYul.EVM.X`/`D_J`, output bytes, tx/world
encodings, `VerityOutcome`, and resource premises. No pass names, no fuel
arithmetic, no artifact projections, no installed-state constructors.

## Established facts the plan builds on (verified 2026-07-05)

- Both towers now share one universe: Lean 4.28, same mathlib line, same
  EVMYulLean commit. `lake build` green on both.
- **Shared syntax and state**: our `Yul.AstContract :=
  EvmYul.Yul.Ast.YulContract` (Yul/Syntax.lean:14) is the exact type Verity's
  native lowering emits; our `InteractionSemantics.State := EvmYul.Yul.State`
  is the exact state type native `EvmYul.Yul.exec` runs on. The semantic
  bridge is interpreter agreement over shared syntax/state, not a
  cross-representation simulation.
- **Events already observable**: `Simulation.OpenWorld` carries `substate`
  (OpenWorld.lean:255), so `FinalStateObs.world` pins the log series; no
  strengthening of our crown's observation surface is required.
- **Primitive prior art**: `Yul/FunctionsInteractionClosedPrimitive.lean`
  already relates our primitive interpretation to native
  `EvmYul.Yul.execUnOp/BinOp/TriOp/executionEnvOp`.
- Verity's endpoint: `sourceResultMatchesNativeOn observableSlots` (success,
  returnValue, events, storage on declared slots) against native
  `callDispatcher` in a closed one-account world, gasless (gasAvailable = 0),
  no external calls in fragment (their #1737), dispatch-guard and
  tx-normalization premises.
- Our endpoint: `Solidus.compile_correct` from `Solidity.Frontend.Object`
  (JSON decode is OUTSIDE the theorem), source run in
  `Yul.InteractionSemantics.exec`, target = gasful `RunRefinesOpenTotal`.
- Anti-goal on record: the Yul/Reference.lean failure (72k lines of per-shape
  terminal wrappers, recursion never inhabited). Phase 3 mandates the generic
  mutual induction FIRST; any per-shape wrapper family is a stop-and-
  consolidate event.

## Phases

### Phase 0 — Substrate & governance (mostly done; finish: ~days)
- [x] Toolchain + EVMYulLean pin alignment (`03a4f711`, zero repairs).
- [ ] Lake wiring: this branch `require verity` (local path `external/verity`
      for dev; git pin once `evmyul-pin-align` is pushed to the fork — USER
      ACTION: push or approve local-path pin for the campaign).
- [ ] Verify residual transitive pins (batteries/aesop/Cli) unify under lake.
- [ ] Early answers needed (affects fragment freeze):
      (a) does Verity's emitted fragment code ever read `gas`/`msize`?
      (b) exact `success = false` ↔ revert-bytes mapping incl. their
          pre-encoded revert-string mstore words;
      (c) whose Yul WF/acceptance is stronger on the shared fragment;
      (d) their harness `perm := true` vs our static-context handling.
- Gate: both packages build in one `lake build`; `#print axioms` on both
  existing crowns unchanged.

### Phase 1 — Fragment freeze + envelope gate (~days, theorem-truth work)
- Define `Verity.Fragment`: decidable predicate over their emitted YulObject
  (and/or CompilationModel) freezing v1 scope:
  runtime dispatch only (creation deferred to Phase 6); no external calls
  (inherited from their fragment); no linked libraries; no
  `verbatim_*`/`pc`/`setimmutable`; no `gas`/`msize` reads (pending 0(a));
  fixed two-level object shape; scalar events only (their current wrapper
  surface).
- Computable envelope checker `emissionInEnvelope? : YulObject → Bool`
  (computable-twin pattern; the generic "codegen always in envelope" theorem
  is Phase 6, the runtime gate is fail-closed until then — scaffold named).
- Counterexample hunt (log `theorem-boundary`): dispatch-guard preconditions
  vs our calldata encoding; msg.value word normalization; their Nat words vs
  our UInt256; selector shift width; empty-calldata behavior (receive/
  fallback are OUT of fragment — confirm their dispatcher's default arm
  reverts and ours agrees).
- Gate: fragment inventory table — every Verity construct classified
  covered / rejected-by-gate / out-of-scope-named.

### Phase 2 — Structured entry + AST seam (~days)
- `Solidus.compileVerityFromYul? (o : YulObject) : Option (List UInt8)` :=
  translate `o` → `Solidity.Frontend.Object` → existing
  `compileVerifiedStackObjectArtifactWithLinkerSymbols? []` → headroom cert →
  **AST-agreement gate**: decidable check
  `artifact.codeArtifact.ordered.program.contract == lowerNative o`
  (their lowering vs what our own frontend lowering produced). Route A: this
  executed equality makes the AST seam sound per-compile with zero generic
  proof. Route B (Phase 6): the generic theorem
  `toFrontendObject/lowering agreement on Fragment`, replacing the gate.
- No unproven output path: `compileVerity?` is the ONLY emitting entry for
  Verity artifacts; wired through the gate from day one.
- Gate: all 8 Verity artifacts compile; bytes identical to the PoC
  (Python-translator) route; commit.

### Phase 3 — Interpreter-equivalence bridge (THE campaign: est. 60–70%)
Target theorem (adjacent, implementation vocabulary):
```
theorem native_exec_agrees_interaction
    (hFrag : Fragment.contractOk contract) (hWF : …)
    (hNative : EvmYul.Yul.exec fuel code state = nativeResult) :
    ∃ fuel', OutcomeAgrees nativeResult
      (InteractionSemantics.exec fuel' code (some contract) state)
```
Same AST, same `EvmYul.Yul.State`; deterministic fueled functions both sides.
Sub-plan, in order:
- 3a. `OutcomeAgrees`: map their exception/halt encodings to our
      Failure/exception constructors (reuse the frozen YulHalt three-way
      honesty note from Solidus.Defs).
- 3b. Primitive families: extend FunctionsInteractionClosedPrimitive to a
      complete per-FAMILY agreement surface (arith/env-read/memory/storage/
      transient/log/keccak). Family classifiers, not per-opcode proofs.
- 3c. Control kernel: ONE mutual structural induction over
      Stmt/Expr/Block/Case/FunctionDef × outcome axis
      (regular/break/continue/leave/exception). Write the mutual statement
      first; add only the leaves the induction demands. Per-shape wrapper
      families = stop, log `architecture-risk`, consolidate.
- 3d. Scoping: reconcile VarStoreRestriction vs native scoping under the
      stronger WF (Phase 0(c) answer); differences gated by Fragment.
- 3e. Fuel adequacy/monotonicity lemmas both sides (∃-fuel shape).
- 3f. Dispatcher/entry adapter: their `callDispatcher` + `initialState` vs
      our `.Block [dispatcher]` + `installedSourceState` — reconcile the
      entry convention and prove the one-account initial states equal (both
      literally construct `EvmYul.SharedState .Yul`).
- Statement review checkpoint BEFORE grinding 3c (oracle if re-enabled, else
  adversarial self-review + counterexample hunt on quantifier boundaries).
- Gate: `#print axioms` = standard three; zero per-shape wrapper families;
  audit entry.

### Phase 4 — State & observation plumbing (~1–2 weeks)
- Public initial conditions: constructor from (tx, storage) to
  `baseSource`/`gasfulInitial` discharging `OpenStateRel` from public data
  (code = bytes, pc = 0, empty stack, encoded world, gas = g); reconciliation
  lemmas so the crown never mentions installed-state builders.
- Observation extraction: from `RunRefinesOpenTotal` + `FinalStateObs`,
  derive Verity's surface: success flag; one-word return decode; event-series
  decode (define the encoding relation between their `List (List Nat)` events
  and EvmYul log records — topics/data layout per their scalar-event
  wrappers); `observableSlots` storage projection (their `projectStorage` vs
  our OpenWorld account storage).
- Theorem-truth check: revert outputs (their pre-encoded revert strings) vs
  our `ExceptionRel` + output pinning.

### Phase 5 — Composition + crown (~days once 3–4 land)
- Chain: their generic supported-fragment theorem → (3f entry adapter) →
  (3) bridge → our `compile_correct` → (4) observation extraction.
- Define `VerityOutcome`; state `verity_compile_correct` in the thin spec
  module `VerityCorrectness.lean`; prove by composing internal endpoints.
- Completion Gate (skill): axioms audit; no compiler-generated evidence in
  public hypotheses (AST gate + headroom cert live INSIDE `compileVerity?`;
  dispatch guards + tx normalization are source-facing premises); fragment
  says "fragment" in names/API; remaining assumptions stated plainly.

### Phase 6 — Widening (post-crown, ordered by value)
1. Creation/constructor composition via `compile_correct_creation` (their
   constructor proofs are per-contract today — interim per-contract creation
   crowns acceptable, named as such).
2. Route B: generic AST-agreement theorem replacing the runtime equality gate.
3. Envelope theorem: their codegen provably in-envelope on the fragment
   (removes the emission gate).
4. Fragment widening in lockstep with their Layer-2 growth (fallback/receive,
   typed errors, non-empty loop bodies, linked libraries via our
   linker-symbol path).
5. Gas observability: keep `gas()` excluded unless their source semantics
   models it (never patch with replay oracles).

## Standing rules for the campaign
- Single-pin invariant: both packages move EVMYulLean/mathlib pins together,
  or not at all.
- Commit verified checkpoints per phase gate; PROGRESS_LOG.md entries with
  tags; no doc sprawl beyond this file + the log.
- The main-repo Solidus spine is not modified except: the structured entry
  (Phase 2) and any bridge-required lemma additions — all additive; the
  existing public crowns' statements are frozen.
