# Non-CALL Proof-Hardening Roadmap

Created: 2026-05-29

This roadmap is intentionally separate from `ROADMAP.md` so the CALL/open
external-world refactor can proceed in parallel.  It covers only the non-CALL
gaps requested in this order:

1. Quarantine/delete legacy gas-aware theorem routes.
2. Derive trace-local non-gas `EVM.X` checks.
3. Derive clean fallthrough finalization.
4. Remove or shrink the source-fuel/`.OutOfFuel` boundary.

Out of scope for this roadmap: ordinary `CALL`, CALL-family external-world
semantics, CREATE/CREATE2, and the separate `RETURNDATACOPY` accepted-fragment
restriction unless explicitly re-prioritized.

## Coordination Rules

- [x] Do not edit `EvmCompiler/Yul/RecursiveBridgeSupport.lean` or
  `EvmCompiler/Yul/Reference.lean` while the CALL agent owns that refactor,
  unless both agents explicitly coordinate.
- [x] Prefer new helper lemmas in the smallest target-owned file possible.
  For this roadmap, the expected low-conflict files are
  `EvmCompiler/Assembly/GasAware.lean`,
  `EvmCompiler/Yul/NoCallRuntime.lean`, and
  `EvmCompiler/LayerAudit.lean`.
- [x] Before each implementation phase, run a public-root grep and record the
  current preferred theorem:
  `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM`.
- [x] After each phase, run:
  `lake env lean EvmCompiler/Assembly/GasAware.lean`,
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`, and
  `lake env lean EvmCompiler/LayerAudit.lean`, narrowing only if unrelated
  CALL edits block an import.  Final checkpoint used
  `lake env lean EvmCompiler/Assembly/GasAware.lean`,
  `lake build EvmCompiler.Yul.NoCallRuntime`, and
  `lake env lean EvmCompiler/LayerAudit.lean`.
- [x] After each phase, run a scoped proof-escape scan over touched Lean files:
  `rg -n "\\b(sorry|admit|axiom|unsafe)\\b" <touched-files>`.
- [x] Commit each verified checkpoint separately, staging only files touched by
  this roadmap.

## Current Preferred Boundary

The preferred public alias now points at the actual-trace no-CALL,
no-`RETURNDATACOPY`, sufficient-gas, step-trace theorem:

`compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_stepTrace_actualTraceFacts_noReturnDataCopy_X`

Current remaining non-CALL public premises after this checkpoint:

- `hActualXTraceFacts`:
  `RecursiveBridgeActualXTraceFacts cfg program asm target shared store initial
  referenceResult`, an actual-trace package keyed by the checked source run,
  semantic outcome relation, lowered target outcome relation, and concrete
  `BlockTraceResult`.  After the latest checkpoint this package carries the
  actual core target trace plus the final fallthrough-PC fact only.  The theorem
  derives trace-local instruction-input readiness from the core trace, derives
  final return-buffer cleanliness from
  `RecursiveBridgeInitialCodeImageRel.returnBuffersClean` plus no-CALL target
  trace preservation, derives final installed-code preservation from the
  no-CALL trace, and derives decode-none-at-fallthrough from the bytecode
  length theorem.
- `hExprResultContracts`: source expression-result contracts.  The old broad
  `RecursiveBridgeExprNoOutOfFuelContracts` public premise is no longer on the
  preferred alias.

This deliberately demotes the older global target-side predicates.  The old
`XBlockInstrCoreInputResources` and `XBlockTraceFinalizationReady` routes remain
as compatibility/internal lemmas, but `LayerAudit.ImportedYulBoundary` no longer
points at them.

## Phase 1: Quarantine Legacy Gas-Aware Routes

Goal: make it hard to accidentally use older theorem routes that still accept
`hTargetGasForX`, `XResultPreconditionAssumptions`, or broad replay/precondition
certificates.

- [x] Inventory all remaining stale gas-aware route names:
  `rg -n "hTargetGasForX|XResultPreconditionAssumptions|XResultRunnerCompleteness|XBlockReplayReady" EvmCompiler/Yul/NoCallRuntime.lean EvmCompiler/LayerAudit.lean`.
- [x] Classify each hit as one of:
  preferred public route, legacy compatibility theorem, lower assembly helper,
  or dead code.
- [x] Confirm `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM`
  and `recursiveBridgeTopToGasAwareEVMNoOutOfGas` do not expose the legacy
  precondition route.
- [x] Add an audit-facing negative grep note or small Lean tripwire so future
  public aliases cannot quietly revert to a theorem containing
  `XResultPreconditionAssumptions`. The checked `LayerAudit` aliases now point
  only at sufficient-gas roots, and the stale-route grep over `LayerAudit` is
  empty.
- [x] Move still-needed compatibility theorems under an explicitly named
  legacy namespace or rename them with a `legacy_` prefix.
- [x] Delete compatibility theorems that have no internal users after the
  preferred step-trace root is checked.
- [x] Re-run `LayerAudit` and the scoped stale-route grep.
- [x] Exit criterion: the public audit surface contains no legacy gas
  precondition route, and any remaining route is either private/internal or
  visibly marked legacy.

## Phase 2: Derive Trace-Local Non-Gas `EVM.X` Checks

Goal: replace the public `hTargetTraceInputsReady` premise with checked
evidence for the actual compiled target trace, or with a clearly fundamental
resource premise if total EVM stack growth is genuinely unbounded.  Current
checkpoint: the public root no longer asks for trace-local instruction inputs;
it derives them from `CoreBlockTraceResultFor` carried by
`RecursiveBridgeActualXTraceFacts`.

- [x] Freeze the exact target predicates to discharge:
  `Assembly.GasAware.XStepTrace.InstrCoreBlockTraceInputsReadyFor` for
  trace-local instruction inputs, and
  `Assembly.GasAware.XStepTrace.CoreBlockTraceResultFor` for the remaining
  actual core target trace boundary.
- [x] Split its obligations into four buckets:
  stack underflow, exact stack-overflow inequality, jump target validity, and
  static-mode write exclusion.
- [x] Reuse already-checked assembler facts for generated jump safety:
  `labelPc` emits `JUMPDEST`, and `Bytecode.JumpdestCorrect` implies
  `validJumps` membership.
- [x] Prove block-local control-instruction input readiness for `.label`,
  `.push`, `.jump`, and `.jumpi` from `emitInstr?` plus the concrete
  `Target.runListResult`.
- [x] Prove primitive stack-underflow readiness for trace-local inputs from
  the actual core target trace.  The deeper source-facing task is now to derive
  `CoreBlockTraceResultFor` itself, not to expose the older
  `XBlockInstrCoreInputResources` fields.
- [x] Prove or expose the exact stack-overflow inequality:
  `state.stack.length - δ(op) + α(op) <= 1024`.
- [x] Important decision point: if recursive function calls can create hidden
  return frames that make total EVM stack depth a real resource limit, expose a
  narrow public resource premise such as `TargetTraceStackResourceBound`
  instead of smuggling it through `traceInputsReady`.  This checkpoint exposes
  the narrow package as the actual-trace `RecursiveBridgeActualXTraceFacts`
  boundary, after proving the older global `XBlockInstrCoreInputResources`
  shape would imply false arbitrary-state push stack room obligations.
- [x] Prove static-mode write exclusion for trace-local inputs from the actual
  core target trace.  The deeper source-facing task is now to derive
  `CoreBlockTraceResultFor` itself, likely using checked source-static facts
  plus a resource invariant.
- [x] Package the per-block facts into a whole-trace theorem by induction over
  `Assembly.Preservation.BlockTraceResult`.
- [x] Add a no-CALL public wrapper that requests
  `InstrCoreBlockTraceInputsReadyFor` only for the actual preservation trace
  and removes `hTargetTraceInputsReady`/`XBlockInstrCoreInputResources` from the
  preferred public theorem.
- [x] Exit criterion: `recursiveBridgeTopToGasAwareEVM` no longer takes a
  public `hTargetTraceInputsReady`-style predicate.  Any remaining stack-depth,
  primitive-underflow, jump, or static-mode premise is represented by the
  actual-trace `CoreBlockTraceResultFor` boundary inside
  `RecursiveBridgeActualXTraceFacts`, not a global target replay/resource
  predicate.

## Phase 3: Derive Clean Fallthrough Finalization

Goal: replace the public `hTargetFallthrough` premise with a checked theorem
about the actual final gasless target trace.

- [x] First repair the shape if needed: the current premise quantifies over all
  running `BlockTraceResult`s from the entry state, which includes fuel-zero
  `done` traces.  The preferred theorem should only require or construct
  fallthrough cleanliness for the actual target trace produced by the source
  preservation theorem.  The preferred root now derives
  `XTraceFinalizationReadyFor hTrace` from the actual core trace, the actual
  fallthrough-PC fact inside `RecursiveBridgeActualXTraceFacts`, and checked
  no-CALL return-buffer preservation from the clean entry relation.
- [ ] Prove a trace-final-state lemma distinguishing genuine completion
  fallthrough from ordinary target fuel exhaustion.
- [x] Prove that a no-CALL running target trace preserves the installed code
  image, and that final `pc.toNat = codeByteLength target.code` implies
  `decode code pc = none` for the encoded target bytecode.
- [x] Prove the final stack bound needed by `XFallthroughStopCleanReady`, or
  reuse the Phase 2 stack-resource theorem.
- [x] Prove the return-data/H_return cleanliness equation required by
  `XFallthroughStopCleanReady`; if this depends on terminal semantics, split
  regular fallthrough from `RETURN`/`REVERT`/`SELFDESTRUCT` halted cases.  The
  checked route now requires clean entry return buffers in
  `RecursiveBridgeInitialCodeImageRel`, proves primitive/target/run-list
  preservation for running no-CALL target traces, and derives the final
  cleanliness equation from the actual trace rather than exposing it in
  `RecursiveBridgeActualXTraceFacts`.
- [x] Route the public sufficient-gas theorem through an actual-trace
  finalization package and remove the raw `hTargetFallthrough` callback and
  global `XBlockTraceFinalizationReady` premise from the preferred public alias.
- [ ] Exit criterion: the preferred public theorem does not take a
  fallthrough-cleanliness callback, and running final states are finalized by
  checked code-image/trace facts.  Current checkpoint removes the callback,
  global-finalization shapes, and direct observation-ready predicate from
  `LayerAudit`, and now derives return-buffer cleanliness internally.  The
  remaining finalization payload is the actual final fallthrough-PC fact.

## Phase 4: Remove Or Shrink Source-Fuel `.OutOfFuel` Boundary

Goal: eliminate `RecursiveBridgeExprNoOutOfFuelContracts cfg program` from the
preferred public root, or replace it with a smaller actual-run/resource premise
whose meaning is transparent to users.

- [x] Avoid implementation in
  `RecursiveBridgeSupport.lean` and `Reference.lean` settle, because this phase
  is likely to touch source-recursive proof code.  This checkpoint shrinks the
  public boundary entirely from `NoCallRuntime.lean`.
- [x] Inventory every use of `RecursiveBridgeExprNoOutOfFuelContracts` in the
  preferred no-CALL public spine.
- [x] Separate two concerns:
  source fuel sufficiency, and the imported evaluator's successful
  `.OutOfFuel` marker.
- [x] Check whether the existing `hSourceFuelRun : ∃ sourceFuel,
  RecursiveBridgeSourceRun ...` plus a non-`.OutOfFuel` result can construct
  the needed expression contract for the actual run.
- [ ] If yes, prove an actual-run-scoped constructor and route the public root
  through it.  Current checkpoint instead routes through the narrower
  `RecursiveBridgeExprResultContracts` premise plus `RecursiveBridgeSourceRun`.
- [ ] If no, define a narrow source-facing premise such as
  `SufficientSourceFuelForRun program shared store referenceResult` and prove
  it implies the old expression no-successful-out-of-fuel package.
- [ ] Avoid proving semantic correctness only for a convenient fuel.  The final
  statement should still say: if the source run with enough fuel produces the
  reference result, then the compiled EVM run agrees.
- [x] Exit criterion: the public root no longer asks users for a broad
  program-wide expression contract.  Any remaining source-fuel premise is
  explicitly about sufficient source fuel or the actual imported run.

## Final Gate

- [x] Preferred public theorem surface grep contains no:
  `hTargetGasForX`, `XResultPreconditionAssumptions`,
  `hTargetTraceInputsReady`, `hTargetFallthrough`, or broad
  `RecursiveBridgeExprNoOutOfFuelContracts`.
- [x] `LayerAudit` aliases point only to the final non-CALL root.
- [x] Touched Lean files pass focused checks and scoped proof-escape scans.
- [x] The remaining public assumptions are classified as fundamental source
  acceptedness, source run/input, initial state/code relation, explicit
  resource bounds, or no-CALL/no-`RETURNDATACOPY` fragment restrictions.
- [ ] Fully derive `RecursiveBridgeActualXTraceFacts` from source-facing
  stack/static/finalization invariants, or replace it with a narrower
  source-facing resource/call-depth premise if recursive internal calls make
  total EVM stack depth a true accepted-fragment bound.  Remaining payload:
  actual `CoreBlockTraceResultFor` plus actual `XTraceFallthroughPcFor`;
  trace-local instruction-input readiness, final stack bound,
  return-buffer cleanliness, installed-code preservation, and final
  decode-none observation are now derived internally.
