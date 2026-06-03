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
  unless both agents explicitly coordinate.  One minimal coordinated
  compatibility edit was made in `RecursiveBridgeSupport.lean` to unfold
  `.Ok` state projections at an existing CALL proof rewrite; it changes no CALL
  theorem statement or semantics and was needed to unblock the no-CALL rebuild.
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
no-`RETURNDATACOPY`, sufficient-gas, step-trace theorem with a combined
executable source-recurrence and inferred assembly-bound stack gate:

`compile_whole_program_result_sound_of_recursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_canonicalEntry_sourceStaticFeatureResourceBytecodeChecked_canonicalObservation_codeImage_existsSourceRun_exprResultContracts_sufficientGas_stepTrace_executableAssemblyInferredBoundStackSafeCompile_initialPerm_noReturnDataCopy_X`

Current remaining non-CALL public premises after this checkpoint:

- `hInitialPerm`: `initial.executionEnv.perm = true`, the ordinary non-static
  entry-state condition.  Under no-CALL/no-CREATE target execution, checked
  permission-preservation lemmas keep this true for every running target block,
  so primitive static-mode compatibility is now derived internally for the
  preferred public alias.
- `hCheckedCompileTarget` now uses
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`.
  That gate first runs the executable source recurrence checker
  `recursiveBridgeExecutableStackCheck?`, then runs executable word-PC
  assembly stack-bound inference and rechecks the inferred table into an
  `AssemblyBounds.ProgramBoundCheckResult`.  The public theorem no longer
  takes a source-run frame-resource witness, target replay equality, or
  per-block target headroom witness.  Instead, the executable checks derive
  both the source-side stack-resource evidence and
  `state.stack.length + 17 <= 1024` for every state in the actual gasless
  target block trace.  The accepted fragment is therefore conservative:
  recursive internal-call cycles are rejected unless they fit one of the
  checker-derived bounded-recursion patterns: `SelfGuardedOnce`,
  `MutualGuardedOnce`, or the generic `GuardedZeroCalls` one-step finite
  function set.
- `hSourceFuelRun`: there exists enough source fuel for the actual Yul
  reference run.  This is source-facing execution evidence, not a
  compiler-generated target-resource witness.
- `hExprResultContracts`: source expression-result contracts.  The old broad
  `RecursiveBridgeExprNoOutOfFuelContracts` public premise is no longer on the
  preferred alias.

This deliberately demotes the older global target-side predicates.  The old
`XBlockInstrCoreInputResources` and `XBlockTraceFinalizationReady` routes remain
as compatibility/internal lemmas, but `LayerAudit.ImportedYulBoundary` no longer
points at them.  New target-local bridge: if an actual `CoreBlockTraceResultFor`
is available, checked lemmas now derive `InstrCoreBlockTraceResidualReadyFor`
from it, so exact control-room, primitive-overflow, and primitive-static facts
do not need to be supplied separately.

## Phase 1: Quarantine Legacy Gas-Aware Routes

Goal: make it hard to accidentally use older theorem routes that still accept
`hTargetGasForX`, `XResultPreconditionAssumptions`, or broad replay/precondition
packages.

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
it derives them from the actual trace's residual/headroom-static package via
`CoreBlockTraceResultFor`.

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
  successful gasless no-CALL primitive execution.  The deeper source-facing
  task is now to derive the actual headroom/static trace invariant, not to
  expose the older `XBlockInstrCoreInputResources` fields.  Lower-level
  checkpoint:
  successful gasless execution of any no-CALL primitive step now directly
  implies its `XCoreStackAndJumpInputsReady` fact, including terminal
  `RETURN`/`REVERT`/`SELFDESTRUCT` cases, so this part no longer has to be
  supplied by a core-trace package.
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
  headroom/static residual package.  The deeper source-facing task is now to
  derive that package from checked source-static facts plus a resource
  invariant.
- [x] Package the per-block facts into a whole-trace theorem by induction over
  `Assembly.Preservation.BlockTraceResult`.
- [x] Add a no-CALL public wrapper that requests
  `InstrCoreBlockTraceInputsReadyFor` only for the actual preservation trace
  and removes `hTargetTraceInputsReady`/`XBlockInstrCoreInputResources` from the
  preferred public theorem.
- [x] Exit criterion: `recursiveBridgeTopToGasAwareEVM` no longer takes a
  public `hTargetTraceInputsReady`-style predicate.  Any remaining stack-depth,
  primitive-underflow, jump, or static-mode premise is represented by the
  actual-trace `RecursiveBridgeActualXTraceHeadroomStaticFacts` boundary, not a
  global target replay/resource predicate.  The exact residual predicate is
  mechanically derivable from either this headroom/static package or from an
  actual `CoreBlockTraceResultFor`.

## Phase 3: Derive Clean Fallthrough Finalization

Goal: replace the public `hTargetFallthrough` premise with a checked theorem
about the actual final gasless target trace.

- [x] First repair the shape if needed: the current premise quantifies over all
  running `BlockTraceResult`s from the entry state, which includes fuel-zero
  `done` traces.  The preferred theorem should only require or construct
  fallthrough cleanliness for the actual target trace produced by the source
  preservation theorem.  The preferred root now derives
  `XTraceFinalizationReadyFor hTrace` from the actual core trace, the checked
  preservation-produced end-PC fact, and checked no-CALL return-buffer
  preservation from the clean entry relation.
- [x] Prove a trace-final-state lemma distinguishing genuine completion
  fallthrough from ordinary target fuel exhaustion.  The current route
  recomputes the target run from the accepted source run with
  `TargetOutcomeEndPc`, then converts that checked whole-program end-PC fact
  into `XTraceFallthroughPcFor` for the actual block trace.
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
- [x] Exit criterion: the preferred public theorem does not take a
  fallthrough-cleanliness callback, and running final states are finalized by
  checked code-image/trace facts.  Current checkpoint removes the callback,
  global-finalization shapes, and direct observation-ready predicate from
  `LayerAudit`, and now derives final fallthrough PC, return-buffer
  cleanliness, installed-code preservation, and decode-none observation
  internally.

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
- [x] `LayerAudit` aliases point only to the final non-CALL root.  The public
  aliases now use the combined executable source-recurrence plus inferred
  assembly-bound checked compiler boundary:
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`.
  Current local verification: `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`
  and `lake env lean EvmCompiler/LayerAudit.lean` pass.
- [x] Touched Lean files pass focused checks and scoped proof-escape scans.
- [x] The remaining public assumptions are classified as fundamental source
  acceptedness, source run/input, initial state/code relation, explicit
  resource bounds, or no-CALL/no-`RETURNDATACOPY` fragment restrictions.
- [x] Hide `RecursiveBridgeActualSourceRunFrameStackHeadroom` behind checked
  compiler acceptance.  The old proof-carrying
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticStackSafeNoReturnDataCopy?`
  route has been removed from `NoCallRuntime`; the preferred public root now
  requires
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`,
  which combines the executable source recurrence checker with the inferred
  assembly stack-bound checker.  Preferred-gate projections now expose the
  executable source-side `StackResourceSafe` theorem as well as the checked
  assembly-derived concrete EVM stack-headroom bound.  The target inequality is checked from
  `Frame.StateRel`; the public root no longer asks for an `EVM.X` headroom
  package or a direct `RecursiveBridgeActualEVMStackHeadroomBound`.
  Primitive static-mode compatibility is now derived internally from
  `hInitialPerm` plus checked no-CALL/no-CREATE target permission preservation;
  trace-local instruction-input readiness, exact residual inputs, final stack
  bound, return-buffer cleanliness, installed-code preservation, and final
  decode-none observation are also derived internally.
- [x] Replace the proof-carrying stack-resource evidence with an executable
  or separately checkable static analysis when we want the compiler artifact
  itself to compute boundedness instead of carrying a semantic Lean proof at
  the public no-CALL boundary.
  Current checkpoint: the acyclic and ranked executable gates compute checked
  stack-resource check results in `Type`, and successful checked compilation now projects
  them to semantic `StackResourceSafe` evidence over the lowered function
  program.  A first narrow recursive source-side sidecar,
  `CallDepth.Ranked.SelfGuardedOnce.checkResult?`, recognizes
  `f(counter) { if counter { f(0) } }` with literal roots, finite-unrolls the
  possible recursive edge into ranks zero/one, rechecks the ranked depth/budget
  result, and packages it into the same executable stack-resource
  check-result family in `NoCallRuntime`.  The checker now also derives the
  selected function, its guarded body facts, its unique internal self-call,
  root-call facts, and the rank-1-to-rank-0 recursive resource-context step
  from the checked shape, rather than accepting those facts as caller-supplied
  evidence.  A second narrow source-side checker,
  `CallDepth.Ranked.MutualGuardedOnce.checkResult?`, accepts exactly two
  functions that guard on their own counter and call the other function with
  literal zero, deriving the checked mutual rank graph
  `left(1) -> right(0)` and `right(1) -> left(0)`.  A generic checker,
  `CallDepth.Ranked.GuardedZeroCalls.checkResult?`, accepts any finite
  set of one-step guarded functions `if counter { callee(0) }` whose callees
  stay in the checked function set; this admits larger bounded cycles such as
  guarded three-function rings without proof-carrying evidence. The default
  executable source-side stack check now tries these paths after the
  conservative inferred rank-zero checker fails, so the source recurrence gate
  can accept these bounded cycles.  The preferred public no-CALL gate now also
  requires this executable source-side stack check result, together with the
  inferred assembly-bound check result.  Its checked branch audit theorem,
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceRecurrenceAcceptedShape`,
  proves successful preferred compilation used either the inferred ranked
  checker, the `SelfGuardedOnce` fallback, the `MutualGuardedOnce` fallback, or
  the `GuardedZeroCalls` fallback.  In the narrow fallback cases the recursive
  graph is empty or exactly the checked finite self/mutual rank graph; in the
  generic fallback, checker success exposes that all roots have rank at most
  one and every generated body edge goes from rank one to rank zero.  The
  default branch equations also prove that the source recurrence checker
  returns `none` when all executable branches fail. A new trace-context bridge
  converts per-block
  source/direct-resource contexts plus structured frame relations into the old
  actual source-run headroom package.  The target-headroom-to-source-resource
  adapter route has been deleted: target EVM stack headroom proves concrete
  target safety, but it does not manufacture source/direct call-stack context.
  The honest source-frame route now goes through
  `RecursiveBridgeActualSourceRunActiveResourcePoints.toFrameStackHeadroom`;
  the remaining preservation-side task is to produce those active resource
  annotations for the actual source/direct run.  The assembly-side target-safety
  route now has a checked first version in
  `Structured.StackResource.AssemblyBounds`: a word-PC keyed bound
  table, executable per-instruction/whole-program checks, successor-PC
  soundness for running assembly steps, and a `programBoundOk?` theorem that
  derives source-run headroom points.  `NoCallRuntime` now has the bridge hook
  `RecursiveBridgeActualSourceRunEVMStackHeadroomPoints.of_assemblyBoundCheck`
  and executable compile-gate helpers projecting the check result to EVM
  headroom points and frame resource points.  It also has a checked sidecar
  compiler boundary,
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticAssemblyBoundStackSafeNoReturnDataCopy?`,
  whose success yields the base compile result, emitted assembly compilation,
  the checker-produced check result, check/table identity, actual
  source-run EVM headroom points, and the concrete
  `RecursiveBridgeActualEVMStackHeadroomBound`.
  There is also an inferred-bound boundary,
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticAssemblyInferredBoundStackSafeNoReturnDataCopy?`,
  which runs a monotone assembly-bound inference pass, rechecks the inferred
  table into a checked bound result, derives the canonical empty-entry initial point,
  and projects checked success to concrete EVM stack headroom without requiring
  a supplied sidecar table.  This inference is intentionally conservative: it
  accepts zero-net stack cycles in the executable examples and rejects positive
  stack-growth cycles.  The current preferred public gate wraps this assembly
  inference with the executable source recurrence checker:
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`.
  The remaining gap is acceptance power, not public soundness: path-sensitive
  and ranking analysis can accept source/data-guarded recursion patterns that
  need more than the current uniform assembly-PC stack bound.
  Inspection note: the existing structured preservation interface returns only
  `ARunResult` plus a final `WholeProgramOutcomeRel`; it does not expose the
  per-block `Frame.StateRel` annotations that are produced internally while the
  proof steps through code.  A more computational checker will need either an
  annotated preservation theorem or a source-only stack/call-depth invariant
  threaded through that theorem.
  Static-call entry coverage remains a separate possible strengthening:
  without `hInitialPerm`, static compatibility still has to come from
  source/static semantics or an explicit source-facing restriction.  Guardrail
  kept checked: successful gasless execution is not enough to derive
  static-mode readiness; `SSTORE` can succeed in the gasless target model while
  `InstrPrimitiveStaticInputsReady` is false in a static state.  Likewise,
  successful gasless target execution is not enough to derive stack headroom:
  `PUSH32` can succeed from a full 1024-word stack in the gasless target model
  even though the `EVM.X` headroom inequalities are false.
