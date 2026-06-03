# Roadmap

## Active CALL Finish Checklist

Last updated: 2026-06-03 03:29 CEST.

### Architecture Lock: CALL Frontiers

The CALL proof should not be advanced by shape-specific CALL lemmas or by
reintroducing a concrete external world. The intended proof spine is a mutual
source-fuel induction with exactly these recursive hypotheses:

- `CALLOpenSeqPathRecursiveAt`: ordinary statement sequences with one selected
  finite external-response trace.
- `CALLOpenSeqKontPathRecursiveAt`: the same selected finite trace, but with
  typed `regular`/`break`/`continue`/`leave` continuation layouts for generated
  control constructs.
- `CALLOpenLoopContinuationPathRecursiveAt`: the direct generated
  `runForLoop` continuation used after a regular post step. This is an internal
  induction member, not a public assumption.

Expression preservation is recursive on expression structure and may consume
`CALLOpenSeqPathRecursiveAt` only for internal user-call bodies. This is what
handles nested `CALL`s in arguments, conditions, and compound expressions.

A checked `For` head must be proved from these ingredients, not from a fallback:

- condition expression: expression-level open preservation at the actual
  condition fuel;
- body: `CALLOpenSeqKontPathRecursiveAt` under
  `SourceModeKontLayouts.block layout outcomeLayout`;
- post-final path: `CALLOpenSeqPathRecursiveAt` under `ctx.withoutLoopControl`
  and the enclosing outcome layout;
- post-loop path: `CALLOpenSeqPathRecursiveAt` under `ctx.withoutLoopControl`
  and regular layout `layout`;
- generated recursive loop continuation:
  `CALLOpenLoopContinuationPathRecursiveAt`;
- syntactic tail: `CALLOpenSeqPathRecursiveAt` at the enclosing tail fuel.

Execution order:

1. [x] Make the combined one-head dispatcher consume the checked generated-`For`
   helper directly and remove the live `For => hOther` branch.
2. [x] Add the loop-continuation frontier constructor so `hLoopRec` is produced by
   the same source-fuel induction package rather than assumed at public
   boundaries.
3. [x] Replace the remaining closed `CALLSeqLoweringFrontierAt`/`CALLSeqKontFrontierAt`
   all-bounds route with the open finite-path sequence/kont/loop package.
4. [ ] Wire the CALL-capable frontier into the preferred public compiler theorem.
   The top CALL assumption package now exposes
   `RecursiveBridgeCALLTopAssumptions.callOpenSeqPathKontPathLoweringFrontiersUpTo_canonical`;
   the source-to-compiler-open dispatcher boundary is now exposed by
   `RecursiveBridgeCALLTopAssumptions.sourceOpenDispatcherBlockResult_canonical`.
   The target-side open primitive/instruction/list/program boundary is now started in
   `OpenAssembly`: primitive CALL extraction resolves one selected open event,
   and `Target.openStepInstr` resumes CALL-family instructions with the PC
   increment required by the closed EVM CALL-family step; `Target` and
   `Compiled` open result runners now mirror the closed running/halted control
   flow. Non-CALL target instruction lists now have an empty-trace compatibility
   theorem against the closed runner. Emitted primitive CALL blocks and compiled
   current primitive CALL steps now expose the selected open event, and the
   compiled open fuel runner has the checked CALL-then-tail continuation lemma
   needed for later instructions and later CALLs. `Compiled.OpenTraceResult`
   now packages multi-step open compiled-assembly traces with constructors for
   CALL, no-CALL running, and no-CALL halted current blocks, plus a resolver back
   to `Compiled.openRunNResult`; the no-CALL constructors can now derive their
   emitted-code no-CALL fact directly from the current assembly instruction's
   `Instr.usesCallCreate = false`. `OpenBlockTraceResult` now mirrors the closed
   emitted-block replay proof object while replacing each emitted target block
   run with an open trace resolution, and it resolves back to
   `Compiled.openRunNResult`. The assembly layer now also has an honest
   source-open runner: `Source.OpenTraceResult.to_openBlockTrace` proves that
   an assembled source-open assembly trace replays through emitted target blocks
   as `OpenBlockTraceResult`, so the lower boundary no longer has to pretend
   CALL passed through the closed assembly source interpreter.
   `Source.OpenTraceResult.of_resolves`,
   `compile_openRunN_result_openBlockTrace_sound`, and
   `compile_openRunN_result_compiled_sound` now give the direct open analogue
   of the closed assembly compile theorem from the real `Assembly.compile?`
   success fact. `Yul.OpenLowering` now pins the next adjacent proof boundary:
   `FunctionsBlockToAssemblySourceOpenSoundAt` is the compiler-open
   function-block to assembly source-open theorem we still have to prove, while
   its checked `.to_compiled` wrapper shows that theorem immediately composes
   through the existing assembly compile proof. Closed no-CALL assembly source
   runs now also embed into this open target tower with the empty trace through
   `Source.openRunNResult_resolves_closed_of_no_callCreate` and the direct
   no-CALL compile wrappers. The remaining work is proving the open compiler
   preservation theorem for traces that may contain CALL, then composing it into
   the whole-program imported-Yul-to-open-EVM theorem.
5. [ ] Delete private direct-CALL or compatibility scaffolding that is no longer
   reached from that spine.

Definition of done: the preferred checked compiler theorem admits accepted Yul
programs containing ordinary `CALL`, proves that imported-Yul execution and
compiled EVM execution expose the same external call requests, and relates
continuations for every shared abstract response. The proof must not model a
concrete callee, chain world, precompile dispatcher, child-code branch, or
callee semantics. Requested gas may stay opaque, but it must be threaded
consistently as a call operand. The response may carry arbitrary
caller-account/storage mutation; both sides require only the same response and
the shared-state relation demanded by the open boundary.

Current rule: keep the existing no-CALL theorem as a proved fallback while CALL
is in flight, but do not finish by adding compatibility wrappers, direct
let/assign CALL scaffolding, or a concrete external-world model.

- [x] Replace the concrete external-world route with the open finite
  request/response model: equal call requests, one selected finite trace, and
  universally shared abstract responses.
- [x] Prove the expression-level CALL route, including nested calls inside
  arguments and expression forms.
- [x] Prove structural one-head frontier cases for blocks, conditionals,
  switches, abrupt control, uninitialized declarations, rejected no-lowering
  heads, expression statements, and terminal primitives.
- [x] Prove discarded internal procedure calls through the open frontier,
  including low-fuel edges and recursive selected-callee callbacks.
- [x] Prove productive zero-target and multi-target assignment internal calls,
  fold them into the generic single-expression one-head frontier, and delete
  the stale assignment productive dispatcher.
- [x] Prove productive initialized `let` internal-call routing, fold the
  declaration-form user-call branches into the generic single-expression
  one-head frontier, and delete the stale declaration productive dispatcher.
- [x] Finish low-fuel internal-call edge classification for zero-target and
  multi-target assignment/declaration heads, especially the source-fuel-four
  boundary. Source-fuel-one is now checked through the generic `cons_one`
  route; source-fuel-two/three are checked after deriving the source
  assignment/declaration domain checks; assignment source-fuel-four is now
  checked by the selected low-fuel internal-call boundary; declaration
  source-fuel-four is checked by the two-layout let-head/tail boundary.
- [x] Audit and eliminate the remaining live one-head `hOther` fallback from
  the canonical CALL route. Every syntactic branch used by the canonical
  frontier is now proved covered, impossible, or rejected by the checked
  lowerer. An older private structural dispatcher with an `hOther` parameter
  still exists as stale scaffolding, but the canonical program-CALL frontier no
  longer depends on it.
- [x] Apply the exhaustive one-head frontier to the finite-path sequence
  induction (`CALLOpenSeqPathLoweringFrontierAt`) and its typed-continuation
  sibling. The strict mutual package
  `callOpenSeqPathKontPathLoweringFrontiersUpTo_canonical_of_programCALL`
  proves ordinary and typed frontiers together by source-fuel induction, using
  only strictly smaller counterpart frontiers.
- [x] Replace the remaining checked recursive/top-assumption consumers with the
  exhaustive CALL-capable frontier. The top CALL package now derives the checked
  `ProgramCALLBridgeContext` from compilation and exposes ordinary/typed
  canonical open frontiers without a public callee oracle.
- [ ] Wire the preferred public Yul preservation theorem to the CALL-capable
  frontier, while leaving the no-CALL theorem only as a fallback/special case.
  The source-to-compiler-open dispatcher-block result is now wired. The
  target-side primitive/instruction/list/program CALL adapter is Lean-checked
  in `OpenAssembly`, including empty-trace compatibility for no-CALL target
  instruction lists, emitted/current primitive CALL bridge lemmas, and
  CALL-through-tail fuel composition. The new `OpenBlockTraceResult` wrapper is
  the intended target-side proof object for emitted-block-aware open compiled
  assembly runs, with current-instruction no-CALL wrappers removing the
  emitted-code classifier side condition for ordinary steps. The assembly
  source-open runner, `Source.OpenTraceResult.to_openBlockTrace`, and the direct
  `Assembly.compile?` wrappers are now Lean-checked, giving the adjacent
  assembly source-to-emitted-block open preservation layer. `Yul.OpenLowering`
  now names the exact remaining compiler-open/function-block to assembly
  source-open theorem and proves its composition into the compiled open runner.
  Closed no-CALL assembly source runs now resolve through the open target tower
  on the empty trace, so the old no-CALL preservation route can be reused for
  non-CALL branches inside the future open proof. The remaining public gap is
  proving the CALL-capable compiler-open/function-block theorem, then composing
  the public imported-Yul dispatcher result through it.
- [ ] Audit the public theorem boundary: no concrete world/precompile/callee
  model, no direct CALL scaffolding, no generated compiler evidence assumed
  without a checked constructor, no public call oracle, and no hidden no-CALL
  premise on the preferred route.
- [ ] Extend the same architecture from ordinary `CALL` to the CALL family when
  ordinary `CALL` is finished: `CALLCODE`, `DELEGATECALL`, `STATICCALL`,
  `CREATE`, and `CREATE2`, with a request-boundary audit for each.
- [ ] Run the verification gate: focused Lean check for
  `EvmCompiler/Yul/RecursiveBridgeSupport.lean`, relevant `lake build`, layer
  audit/tripwire checks, proof-escape scans, and public-spine grep for stale
  no-CALL assumptions or wrappers.

## CALL Detailed Status Notes

The following notes preserve the running proof status behind the checklist
above.

Finite-trace correction:

- [x] Reject and remove the false global "every larger target cutoff works"
  scaffold. `CompilerOpen` cutoff fuel is executable: after an arbitrary
  response, an over-fueled target can expose a later request after finite-fuel
  imported Yul has exhausted.
- [x] Add `OpenEvent`, `OpenTrace`, `OpenResultResolves`, and
  `OpenResultPathRel`, recording equal request sites and the same concrete
  black-box response along one finite interaction path.
- [x] Add trace response certificates and the generic projection from a local
  tree-shaped `OpenResultRel` proof to one concrete admitted
  `OpenResultPathRel`.
- [x] Add the checked hidden-context finite-path sequence target and
  `CALLOpenSeqPathLoweringFrontierAt`. For each concrete admitted trace and
  requested target cutoff floor, the target constructs one adequate exact
  cutoff at or above that floor; it does not claim every larger cutoff works.
  The direct zero/one source-fuel base cases are verified.
- [x] Add successful-path target cutoff extension for `CompilerOpen`: once one
  concrete finite response path resolves successfully, any larger cutoff
  follows that same selected path to the same result. This covers blocks,
  scoped blocks, user-function bodies, loops, conditionals, switches, and
  internal user calls without making a whole-tree monotonicity claim.
- [x] Add canonical finite-path re-pairing from two same-trace resolutions,
  raw-expression selected-path cutoff padding, and the local adapter from a
  tree-shaped raw-expression proof to the requested-floor finite-path
  interface.
- [x] Normalize source and compiled declaration/assignment expression heads
  through `runLetSource`/`runAssignSource` and the terminal-aware `runRaw`
  bind boundary, so the path-native successor proof can split and rebuild one
  selected trace without ad hoc unfolding. Add the corresponding selected-path
  resolver rebuild helpers for compiled `pre ++ head ++ tail` blocks.
- [ ] Make expression-prefix, generated-argument, selected-callee body, and
  sequence-tail composition path-native. Construct the exact target cutoff
  from the selected finite trace rather than asking one cutoff to cover the
  whole response tree.
  The declaration- and assignment-expression successors are checked: each
  splits the selected source trace at the raw-expression bind, recursively
  chooses the tail cutoff from the actual filled state, pads the completed raw
  target prefix to that cutoff, and rebuilds the full compiled path. Assignment
  additionally derives its destination-preservation invariant from arbitrary
  prefix write-disjointness. Recursive expressions, including nested internal
  user calls, are checked. Direct internal-call post-return replay is checked
  for discard/existing-assignment targets and fresh declaration targets. The
  generic direct emitted-block wrapper and concrete `ExprStmtCall`,
  multi-`Assign`, and multi-`Let` source-form wrappers are checked. The
  checked compiler-output lifts for those three direct forms are checked.
  Selected-callee callback synthesis is checked as well: internal procedures
  recursively enter the selected compiled body and nested calls in actual
  arguments use the same callback. The path-native one-head dispatcher now has
  frontier-shaped selected-path wrappers for rejected no-lowering heads,
  uninitialized declarations, abrupt `break`/`continue`/`leave`, and
  expression-level initialized single declarations, single assignments, and
  conditionals/switches. The checked conditional and switch expression wrappers
  now carry recursive body selected-result relatability explicitly; switch also
  transports selected case/default source-name reservation via
  `SourceNamesReserved.switch_selected`, so recursive selected bodies can enter
  the same finite-path callback without weakening the fresh-name invariant. A
  structural one-head dispatcher now packages the verified block, conditional,
  switch, and abrupt-control heads while explicitly delegating the remaining
  declaration/assignment/expression/loop families to the next dispatcher layer.
  A single-expression-head dispatcher now also packages all uninitialized
  declarations plus `let x := expr` and `x := expr` through expression-level
  open preservation, so calls nested inside those expressions use the
  recursive expression route.  Initialized empty-target or multi-target
  declarations/assignments whose value is a literal, variable, or primitive
  call are now also discharged as checked no-lowering heads; the remaining
  initialized declaration/assignment fallback is the real zero-target or
  multi-target internal-user-call branch.  Productive zero-target and
  multi-target assignment internal calls are now checked and folded into the
  combined dispatcher for the recursive high-fuel case; the remaining
  assignment work is the low-fuel edge classification. Productive initialized
  `let` internal calls now have the same checked open selected-path
  wrapper/dispatcher treatment and are folded into the combined dispatcher;
  their remaining work is the matching low-fuel edge classification.
  Source-fuel-one zero-target and multi-target assignment/declaration user-call
  heads are now classified with the checked generic `cons_one` branch. A
  theorem-boundary attempt to classify source-fuel-two/three by pure
  `execSeq = OutOfFuel` equality was rejected: after declaration/assignment
  prechecks, those branches need selected-path handling through the argument
  and call binds, so they remain real low-fuel proof obligations.
  Expression statements and loops remain delegated to their specialized
  frontier layers.
  Internal procedure-call propagation is split by statement shape:
  single-result initialized declarations/assignments use the expression route,
  discarded procedure calls use the statement route below, and multi-target
  `let`/`assign` internal calls are covered by the newer checked typed-
  continuation sequence frontier rather than by the old direct open
  let/assign-CALL wrappers.
  The structural and single-expression dispatchers are now folded behind one
  combined one-head dispatcher, leaving only the genuinely unfinished
  non-single-expression statement families delegated. Discarded literal and
  variable expression statements are also discharged in the frontier as checked
  no-lowering heads, and primitive expression statements that cannot lower as
  zero-result statements are classified there too. Discarded internal
  procedure calls are now routed through the open frontier for every source
  fuel: tiny fuels use the checked out-of-fuel branches, fuel four uses the
  exact direct-call boundary, and larger fuels use the recursive program-call
  wrapper so nested calls inside arguments share the same selected-callee
  callback. The now-unused direct open let/assign internal-call program
  wrappers were deleted; future wiring should keep using expression-level
  preservation for single-result heads and the checked frontier shape for
  multi-target procedure statements. A follow-up exact-name audit also removed
  the now-unused lower-level checked open `let`/`assign` internal-call wrappers;
  the semantic target relations remain because discarded calls and future
  multi-target statement routes still need them. Low-fuel open `for` heads are
  now discharged in the CALL finite-path frontier by unfolding the open
  interpreter's `execSeq`/`exec`/`loop` fuel-two and fuel-three out-of-fuel
  cases; productive loop execution remains the real loop proof obligation.
  Actually lowering zero-output primitive expression statements are now routed
  through the checked open frontier as well: the raw `lower0?` theorem handles
  nested argument calls through expression-level recursion, and the checked
  wrapper resumes the statement tail through the sequence callback. The
  remaining expression-statement work is terminal primitive statements. The
  terminal route now has the source normalizer, argument-terminal done-relation
  adapter, singleton `terminalArgs` resolver, and generated-argument-prefix
  target compositor checked. The source side now also has a normal form that
  rewrites terminal expression-statement execution into an `evalArgs` bind
  followed by the terminal primitive, and the source finite-path combinator is
  checked: argument-side halt/revert paths stop before the terminal statement,
  while regular argument completion enters a source-facing terminal contract and
  the emitted target tail is skipped. The checked lowerer-driven wrapper is now
  checked as well: it reconstructs the generated `lowerBound1?` variable-list
  evidence from compiler output, sends nested argument calls through
  expression-level recursion, and then calls the terminal finite-path
  combinator. The combined one-head open dispatcher now has a terminal
  primitive branch ahead of the zero-output primitive branch, parameterized by
  the source-facing terminal contract. Terminal primitives are now also proved
  to be outside the open CALL boundary, to produce a terminal/error result
  rather than falling through into the syntactic tail, and to force an empty
  terminal suffix trace after regular argument completion. That empty-trace
  fact is now constructed inside the terminal finite-path combinator, so the
  source-facing terminal contract no longer has to prove it. The next terminal
  step is partly checked too: the selected terminal suffix exposes its exact
  terminal error result, relatability forces either `stop` or the terminal
  arity invariant, and the structured terminal primitive step is constructed
  directly from the post-argument open suffix. The canonical post-argument
  terminal observation adapter is now checked too: already-evaluated terminal
  arguments are replayed as literal Yul arguments, and STOP/RETURN/REVERT/
  SELFDESTRUCT are case-split to prove the replayed closed run has the exact
  same halt/revert result as the selected open suffix. The canonical structured
  source-facing terminal-open contract is now checked and threaded into a
  canonical combined one-head frontier wrapper, so callers on that route no
  longer provide a bespoke `hTerminalOpen` parameter. The remaining terminal
  work is to make this canonical route the one used by the higher recursive/
  public CALL frontier rather than leaving the older generic wrapper as the
  only reusable dispatcher.
  Direct discarded-CALL source-fuel two and
  three branches are checked as impossible source out-of-fuel paths; source-fuel
  four is not syntactic out-of-fuel because simple arguments may evaluate first,
  so that branch must consume the scoped/exact-state expression-result-ok
  invariant before proving callee-body exhaustion. Switch now has verified open
  source normalization, target-after-raw continuation, compiled-path resolver
  primitives, path-native block-head/sequence wrappers over the raw scrutinee
  boundary, a recursive source switch theorem, and the checked compiler-output
  switch wrapper over compiler-produced empty/nonempty-default lowerings, the
  specialized source-fuel-3 switch frontier, the checked all-fuel switch
  dispatcher, and the program-context switch wrapper. The discarded direct
  internal-CALL source-fuel-four low-fuel/result-ok boundary is checked through
  the source wrapper, checked compiler-output lift, and program-context wrapper:
  after simple arguments finish, the one remaining user-call tick is proved to
  be an unrelatable `OutOfFuel`/missing-function error path. Conditionals are
  already on the expression-level open dispatcher, and loops now have the first
  source-side open normalization lemma for the condition/body/post/recur bind
  shape plus target-side normalizers exposing the compiler-generated empty-init
  `for true` block as an open `runForLoop` bind directly from the checked
  `GeneratedForCompiled` evidence package. The exhaustive successor dispatcher
  remains: port full path-native structural propagation through loop
  conditions/bodies/post blocks, assemble every statement head, and replace the
  stale public spine. The checked finite-path compiler-output wrapper for
  generated `for` heads is now verified; it reconstructs
  `GeneratedForCompiled` from lowering, delegates the actual semantic loop-head
  relation to a path-native head theorem, and composes regular loop completion
  with the syntactic tail. Productive loop heads now also have the normalized
  `SourceOpenLoopHeadPathSoundWhenAtExactHiddenCtx` boundary: the `.For` head
  proof is derived from a proof over `runLoopSource`, and the checked
  generated-`for` wrapper consumes that normalized contract at the exact
  `loopFuel + 4` sequence-fuel shape. `runLoopSource` itself is now rewritten
  through condition `evalValues`, so nested CALLs in loop conditions can use the
  expression-level open proof. The target-side open false-condition subpath is
  checked through the generated loop statement: selected raw condition prefixes
  are inverted, selected zero values drive the generated `iszero` guard, the
  guard exits the generated body by `break`, and the generated `for true`
  statement falls through regularly over the same trace. The source-facing
  selected false branch is now checked too: a zero-valued condition
  `evalValues` trace is paired with the compiled raw prelude via the
  expression-level open theorem, local-domain exactness is recovered from the
  open condition-domain invariant, and the resulting generated block produces
  the loop-head `OpenResultPathRel`. The condition terminal branch is also now
  checked for the normalized loop boundary: a selected condition `evalValues`
  error is paired with a raw generated-prelude `stopped` target, the stopped
  mode is proved to be a target halt, and the generated `for true` block
  propagates that halt without entering the guard or body. The first nonzero
  target-side guard prefix is checked as well: a selected raw condition path
  yielding a nonzero singleton now drives generated `iszero` to false over the
  same trace and reconstructs a regular `pre ++ if iszero(cond) { break }`
  compiler block for the later body/post branch proofs. The first nonzero
  body branch target path is checked too: that selected guard prefix now
  composes with a selected lowered-body `.brk` path, pads the body cutoff from
  the actual existential guard cutoff, and turns generated loop-body `break`
  into regular `for true` statement completion over the concatenated trace.
  That path is also lifted through the singleton `generatedForLowerBlock`
  wrapper, so the next source-facing theorem can target the actual compiler
  output block rather than a bare target statement. The body-break branch now
  also has path-native source/target components in the final compositional
  shape: the target side is factored over an already-selected generated guard
  prefix plus selected lowered-body path, and the source side normalizes
  nonzero condition `evalValues` plus body `Break` into a `runLoopSource`
  path over `trace ++ bodyTrace`. Those components are now paired in the
  source-facing selected body-`break` branch for `generatedForLowerBlock`,
  producing the regular loop-head relation over the concatenated trace. The
  selected body-terminal branch is checked too: a nonzero condition followed
  by a selected body error now normalizes the source loop to that same
  terminal error and propagates the corresponding generated target halt
  through `generatedForLowerBlock` over `trace ++ bodyTrace`. The selected
  body-`leave` branch is now checked as well: nonzero condition plus selected
  body `Leave` becomes the same source checkpoint and target leave through the
  generated block over the concatenated trace. The selected body-regular/
  post-terminal branch is now checked too: regular body completion is promoted
  through scoped exactness, the selected post error is related to a target halt,
  and the generated block propagates that halt over
  `(trace ++ bodyTrace) ++ postTrace`. The body-regular/post-regular recursive
  branch now has its source normalizer, target generated-loop core/statement/
  singleton-block wrappers, and source-facing pairing checked. The pairing
  composes condition, generated guard, body, post, and recursive raw
  `runForLoop` paths over the selected finite trace; target no-`break`/
  no-`continue` is derived from explicit source no-loop-control facts that the
  accepted/scoped caller must discharge. The body-regular/post-`leave` branch
  is checked end to end for the selected open path: source normalization,
  generated target statement/block wrappers, and the source-facing pairing all
  pass over `(trace ++ bodyTrace) ++ postTrace`. The body-`continue`/
  post-`leave` sibling is also checked through the same source normalizer,
  target statement/block wrapper, and source-facing selected-path pairing. The
  body-`continue`/post-terminal branch is now checked end to end as well:
  source normalization, generated target statement/block wrappers, and the
  source-facing selected-path pairing all pass over
  `(trace ++ bodyTrace) ++ postTrace`.
  The body-`continue`/post-regular recursive branch is now checked end to end:
  source normalization, target `runForLoop`/statement/
  `generatedForLowerBlock` wrappers, and the source-facing selected-path
  pairing compose condition, guard, body, post, and recursive loop traces.
  The source side now also has a reusable continuation-unzip layer for the
  normalized open loop: `runLoopSource` splits through the condition
  `evalValues` prefix and singleton invariant, `runLoopSourceAfterHead` splits
  nonzero paths through the selected body trace, `runLoopSourceAfterBody`
  splits regular/continue paths through the selected post trace, and
  `runLoopSourceAfterPost` extracts the recursive loop prefix for regular
  post completion. Pure zero/body-break/body-leave/out-of-fuel and
  post-leave/out-of-fuel branches have checked trace-empty inversions, so the
  remaining generated-loop constructor can dispatch from the actual selected
  source trace without re-expanding the whole interpreter. The condition side
  now has the raw-prelude shape inversion needed by that dispatcher: successful
  singleton condition paths are proved to end in a normal `.Ok` source state,
  source/result out-of-fuel eliminators are explicit under the standard
  allowed-result relatability premise, and the generated-loop condition split
  now immediately discharges condition-error and zero-condition paths before
  handing nonzero paths to the body/post dispatcher. The nonzero body split
  dispatcher is checked: body terminal, `break`, and `leave` paths now finish
  immediately, body `OutOfFuel` is eliminated by allowed-result relatability,
  and regular/`continue` body paths expose selected post continuations. The
  regular-body and continue-body post split dispatchers are checked too:
  post terminal/`leave`/regular-recursive cases dispatch through the selected
  branch lemmas, post `OutOfFuel` is eliminated, and post `break`/`continue`
  are explicit impossible selected paths. These are now composed into a full
  condition/body/post selected-source dispatcher for generated loops; the
  remaining step is to derive the exact-domain and post-control impossibility
  inputs from the checked loop-domain/scoping facts and expose the result as
  `SourceOpenLoopHeadPathSoundWhenAtExactHiddenCtx`. The full
  `sourceOpenLoopHeadPath_generatedForLowerBlock` route was explored under a
  generated open-loop contract bundle, but that route is not present in the
  current checked file as an open sequence wrapper. Loop heads therefore remain
  on the residual one-head fallback until the open-loop helper is rebuilt
  honestly from the available recursive sequence/kont frontiers. The body/post
  selected block contract fields now require explicit
  `SourceResultRelatable` premises, so they line up with the recursive open
  sequence theorem boundary instead of demanding exact selected-result proofs
  for unrelatable imported errors. The path-native open-kont boundary is now
  checked too: `SourceOpenResultSeqKontDoneRel`,
  `SourceOpenResultSeqKontPathSoundWhenAtExactHiddenCtx`,
  `CheckedOpenSeqKontPathLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx`,
  `CALLOpenSeqKontPathRecursiveAt`, the matching frontier, and the
  frontiers-to-recursive adapter are available for generated-control internal
  mode paths.
  Current audit: productive `For` heads are not yet wired into the canonical
  one-head open CALL frontier. The attempted exact branch referenced a missing
  open-loop helper and has been backed out; fuel-4 loop out-of-fuel remains a
  known boundary to re-express when the productive loop helper is rebuilt.
  The generated loop's internal body `layout` callbacks are now retargeted to
  the open-kont done relation, with selected regular/`break`/`continue` body
  results converted back to ordinary layout relations only at branch use sites.
  The body callbacks now also require the post-guard source-scope and handler
  invariants, derived in the selected branch lemmas from the generated guard
  prefix via the compiler-open context-extension invariant.  A selected open
  block adapter for typed continuations is checked: recursive `execSeq` body
  paths can be transported through imported Yul `.Block` store cleanup without
  changing the selected target path.  Selected-result support is now explicit
  in the generated body contract split: `bodyLayout` is consumed only for
  mode-supported regular/`break`/`continue` results, while `bodyOutcome` owns
  terminal and `leave` exits.  The recursive `bodyLayout` and `bodyOutcome`
  field constructors are checked for successor block fuel: they call the
  typed-kont and ordinary recursive frontiers on the underlying body `execSeq`,
  thread `restrictSourceResultTo storeIn` through the selected-result
  predicate, and lift the path back through imported Yul `.Block` cleanup.
  `bodyOutcome` now carries explicit ordinary outcome-layout support, so body
  `leave` support is transported from the enclosing allowed-result support
  instead of being implicit in the generated loop contract.  Post callbacks now
  carry the same explicit ordinary outcome-layout support, and the generic
  recursive post-path constructor is checked for either the loop-internal
  layout or the outer outcome layout.  The full generated-loop path contract
  can now be built from recursive body/post callbacks plus the residual bundle
  of domain facts, impossible post/recursive loop-control facts, and the raw
  recursive `runForLoop` callback.  The residual bundle now has checked
  constructors that project the body/post exact-domain fields from state-valued
  open done-invariants and, more concretely, from CALL-safe/scoped body/post
  blocks.  The same open checkpoint invariant discharges post and recursive
  no-`break`/no-`continue` selected paths from scoping, using empty-layout
  containment because checkpoint legality is independent of store-domain
  exactness.  The remaining hard piece is constructing the raw recursive
  `runForLoop` path callback from recursive loop preservation; the older closed
  branch contracts still feed the
  closed/hidden-scope route and should not be treated as CALL-spine coverage.
  The source singleton `execSeq` normalization for a `.For` head is checked,
  so the recursive sequence proof can now be aligned with the raw loop
  callback by spending one extra source tick.  The next exact-domain theorem
  must be stated only for reachable regular-entry recursive loop states; the
  tempting arbitrary-state `mkOk` exact-domain route is false.
  The path-native dispatcher now also has
  frontier-shaped wrappers for uninitialized declarations and rejected
  no-lowering heads, plus `break`/`continue`/`leave` abrupt heads, so those
  closed-spine cases can be ported without new semantic assumptions.
- [ ] Replace the six stale closed-shell singleton dispatch branches with the
  path-native open sequence frontier and delete the temporary tree frontier.
- [ ] Carry ordinary `CALL` through the preferred public checked compiler/EVM
  theorem spine, then extend the same abstract-response trace boundary across
  `CALLCODE`, `DELEGATECALL`, `STATICCALL`, `CREATE`, and `CREATE2`.

Checked base we can rely on:

- [x] Generated-variable open stack/final-prelude adapters.
- [x] Empty open argument-prelude case.
- [x] Single-word expression-head adapter from `YulOpen.evalValues` to
  `YulOpen.eval`.
- [x] Normalized productive-loop source boundary from `.For` to
  `runLoopSource`, including the condition `evalValues` equation and the
  checked generated-`for` wrapper at the exact productive fuel shape.
- [x] Target-side selected-trace false-condition generated-loop path from raw
  condition zero through generated guard `break` to regular generated
  `for true` statement completion.
- [x] Source-facing selected-trace false-condition normalized-loop branch from
  condition `evalValues` zero to the generated lower block path relation.
- [x] Source-facing selected-trace condition-terminal normalized-loop branch
  from condition `evalValues` error to generated lower block halt propagation.
- [x] Target-side selected-trace nonzero-condition generated-guard prefix from
  raw condition value to regular guard fallthrough.
- [x] Target-side selected-trace nonzero-condition/body-`break` generated-loop
  path from raw condition value plus lowered-body `break` to regular generated
  `for true` statement completion.
- [x] Block-level wrapper for that selected nonzero/body-`break` path over
  `generatedForLowerBlock`.
- [x] Factor target body-`break` over the actual selected guard prefix and
  selected body path, and add the matching source `runLoopSource` selected-path
  body-`break` normalizer.
- [x] Source-facing selected-trace nonzero-condition/body-`break` normalized
  loop branch from condition `evalValues` and body `Break` to generated block
  regular completion.
- [x] Source-facing selected-trace nonzero-condition/body-regular/post-terminal
  normalized loop branch from condition `evalValues`, regular body completion,
  and terminal post result to generated block halt propagation.
- [x] Source normalizer, target `runForLoop`/statement/
  `generatedForLowerBlock` wrappers, and source-facing selected-path pairing
  for the nonzero/body-regular/post-regular recursive branch.
- [x] Source normalizer, target statement/`generatedForLowerBlock` wrappers,
  and source-facing selected-path pairing for the nonzero/body-regular/
  post-`leave` branch.
- [x] Source normalizer, target statement/`generatedForLowerBlock` wrappers,
  and source-facing selected-path pairing for the nonzero/body-`continue`/
  post-`leave` branch.
- [x] Source normalizer, target statement/`generatedForLowerBlock` wrappers,
  and source-facing selected-path pairing for the nonzero/body-`continue`/
  post-terminal branch.
- [x] Source normalizer, target `runForLoop`/statement/
  `generatedForLowerBlock` wrappers, and source-facing selected-path pairing
  for the nonzero/body-`continue`/post-regular branch.
- [x] Reusable source-side normalized-loop continuation unzippers for
  condition `evalValues`, singleton condition values, nonzero body prefixes,
  body regular/continue post prefixes, post-regular recursive-loop prefixes,
  and pure zero/body/post stopping branches.
- [x] Raw-expression path shape inversion for condition success: a selected
  singleton source condition value related by the raw generated prelude ends in
  a normal `.Ok shared store` source state.
- [x] Generated-loop condition split dispatcher: condition-error and
  zero-condition paths are completed through the selected terminal/false branch
  lemmas at the statement-level generated `for` shell, while nonzero paths
  return the normalized condition trace, suffix, domain fact, and continuation
  proof for body/post dispatch.
- [x] Generated-loop nonzero body split dispatcher: body terminal/error,
  `break`, and `leave` paths are completed through checked generated-loop
  branch wrappers, body `OutOfFuel` is eliminated by selected-result
  relatability, and only body-regular/body-continue post suffixes remain as
  callbacks.
- [x] Generated-loop post and condition/body/post split dispatchers:
  body-regular and body-continue post suffixes now close post
  terminal/error, `leave`, `OutOfFuel`, impossible `break`/`continue`, and
  post-regular recursive-loop paths, and the condition splitter now composes
  those callbacks into one selected-source generated-loop dispatcher.
- [ ] Rebuild an internal generated open-loop contract bundle naming the body,
  post, recursive-loop, and no-break/no-continue selected-path callbacks that
  the generated-loop dispatcher consumes, with explicit selected-result
  relatability premises on body/post exact-result callbacks.
- [x] Path-native open typed-continuation boundary for generated-control
  recursion: checked definitions for kont done relations, kont path soundness,
  checked kont lowering, recursive kont callbacks, kont frontiers, and the
  frontiers-to-recursive adapter.
- [x] Retarget generated-loop internal body `layout` callbacks from the public
  open sequence done relation to the open-kont done relation, then convert the
  selected regular/`break`/`continue` branches back to ordinary layout outcome
  relations at their exact use sites.
- [x] Add the recursive generated-loop `bodyLayout` constructor for successor
  body-block fuel from `CALLOpenSeqKontPathRecursiveAt`, including the
  `restrictSourceResultTo` selected-result bridge through imported Yul
  `.Block` cleanup.
- [x] Add the recursive generated-loop `bodyOutcome` constructor for successor
  body-block fuel from `CALLOpenSeqPathRecursiveAt`, including the ordinary
  block-cleanup adapter and explicit outcome-layout support for terminal/
  `leave` body exits.
- [x] Add the generic recursive generated-loop post-path constructor for
  successor post-block fuel from `CALLOpenSeqPathRecursiveAt`, parameterized by
  the selected post outcome layout, with explicit support for post terminal/
  `leave` exits and the imported Yul `.Block` cleanup bridge.
- [ ] Remove or replace the residual generated-loop open contract bundle after
  the checked constructor derives exact-domain, no-break/no-continue, and
  raw-recursive-loop obligations from CALL-safe/scoped loop facts plus
  recursive seq/kont frontiers.
- [ ] Wire productive `.For` heads into the open finite-path dispatcher. The
  full-fuel-4 condition out-of-fuel edge is now handled in the checked fuel
  frontier, so this item is down to the successor recursive loop case.
- [ ] Build the successor/all-bounds finite-path frontier from the canonical
  one-head loop-aware dispatcher. First remove the remaining live `hOther`
  fallback by covering or rejecting every residual statement-head case, then
  apply the existing finite-path sequence induction while threading both
  `CALLOpenSeqPathRecursiveAt` and `CALLOpenSeqKontPathRecursiveAt` from
  smaller frontier bounds.
- [x] Source-side singleton, append-singleton, reverse-cons, and `consResult`
  open-bind equations for scheduled `YulOpen.evalArgs`.
- [x] Target-side open append equations for generated preludes, including
  `preHead ++ [let tmp := lowerHead]` and
  `preTail ++ (preHead ++ [let tmp := lowerHead])` followed by final generated
  variable replay.
- [x] Generic `OpenResultRel` tail/head/final bind composition plus the
  concrete scheduled reverse-cons wrapper.
- [x] Done-branch final replay adapter from hidden temp insertion plus checked
  final `evalSeq`.
- [x] General `SourceArgPreludeOpen.run` open append equation, so the
  generated-cons target split no longer assumes the tail prelude is generated.
- [x] Arbitrary open `SourceWritesDisjoint` invariant for source preludes,
  including internal source-call statements; the generated-cons target split no
  longer assumes the head prelude is generated either.
- [x] Tail `toStackSeq?` witness construction for recursive generated-cons
  packaging, so the lowerBound component wrapper no longer requires the caller
  to guess the tail stack sequence.
- [x] Checked `lowerBound1?` cons decomposition, so future recursive
  generated-argument constructors can recover tail lowering, head lowering, and
  hidden-temp freshness from the compiler output instead of assuming them.
- [x] Full `lowerBound1?` cons-result wrapper for the open generated-argument
  constructor, so callers can consume compiler output plus final `toStackSeq?`
  instead of exposing tail/head/fresh compiler components.
- [x] Compiler-output nil wrapper for the open generated-argument constructor,
  so the recursive argument proof has checked base and cons constructors over
  actual `lowerBound1?`/`toStackSeq?` output.
- [x] CALL-family source head single-value invariant from checked
  `lowerBound1?`/`toStackSeq?` arity, so generated argument cons callers can
  derive `hHeadSingle` for primitive CALL heads without a concrete-world or
  store-domain premise.
- [x] Primitive CALL `lower1?` decomposition plus direct
  `sourceHeadSingle` wrapper, so generated argument cons callers with only the
  checked head-lowering equation can recover the CALL argument lowering
  internally.
- [x] CALL-specialized generated-cons wrapper over compiler `lowerBound1?`
  output, so the recursive argument proof can consume a primitive CALL head
  without separately threading `hHeadSingle`.
- [x] Canonical response relation for the expression-head
  `evalValues`-to-`eval` adapter, so generated-cons constructors no longer
  expose a separate `hHeadEvalResponse` plumbing premise.
- [x] Canonical response relation for the primitive-CALL argument prelude,
  so CALL expression wrappers no longer expose a separate `hPreludeResponse`
  plumbing premise.
- [x] CALL-head generated-cons wrapper that derives the head expression proof
  from the head CALL's own open argument-prelude proof, primitive response
  relation, and checked `Expr.lower1?` decomposition.
- [x] Canonical response relation for safe non-CALL primitive argument
  preludes, so the safe primitive expression wrapper no longer exposes a
  separate `hPreludeResponse` plumbing premise.
- [x] Safe primitive generated-cons wrapper that derives the head expression
  proof and source single-result invariant from the head primitive's own open
  argument-prelude proof, checked lowering, no-error invariant, and primitive
  stack-soundness theorem.
- [x] CALL-safe primitive generated-cons dispatcher that consumes
  `Safe.CallSafe.primitive` and internally splits primitive heads into the
  already-safe route or the ordinary-`CALL` route.
- [x] Canonical `beforeCallSafePrimitive` response relation plus generated-cons
  wrapper, so recursive primitive-head callers can provide one head-argument
  prelude proof and let the checked `Safe.CallSafe.primitive` split choose the
  safe or ordinary-`CALL` continuation relation.
- [x] Primitive-head `Safe.CallSafe.expr` generated-cons wrapper, so recursive
  argument-list induction can consume the actual head safety fact and extract
  both primitive-family safety and argument-list safety internally.
- [x] Primitive-head `Safe.CallSafe.exprs` generated-cons wrapper, so recursive
  argument-list induction can pass the cons-list safety fact directly and let
  the wrapper split head and tail safety.
- [x] Generic `Safe.CallSafe.exprs` generated-cons wrapper, so recursive
  argument-list induction can pass list safety directly while the head proof is
  supplied by the expression-level open preservation route.
- [x] Expression-level `Safe.CallSafe.primitive` dispatcher over the canonical
  `beforeCallSafePrimitive` argument-prelude relation, so safe primitive heads
  and ordinary `CALL` heads share one primitive-expression wrapper once the
  recursive argument-prelude proof is supplied.
- [x] Expression-level `Safe.CallSafe.expr` primitive wrapper over checked
  `Expr.lower1?` output, so recursive expression preservation can consume the
  actual expression safety/lowering facts and recover the primitive op,
  argument lowering, stack sequence, and one-result cast internally.
- [x] Open literal expression-prelude preservation plus a checked `lower1?`
  wrapper, giving the recursive expression route a direct non-CALL base case.
- [x] Open scoped-variable expression-prelude preservation plus a checked
  `lower1?` wrapper, with the variable-presence/store-domain premise kept
  explicit instead of folded into `SourceStateRel`.
- [x] Checked expression-level `Safe.CallSafe.expr` dispatcher over
  `Expr.lower1?`, so literals, scoped variables, and primitive heads all enter
  the open expression-prelude proof through one interface. Internal user calls
  now enter the same recursive expression route, including nested calls in
  arguments and compound expressions.
- [x] Checked expression-level single-result invariant dispatcher over
  `Expr.lower1?`, so generated argument cons can derive the head one-value fact
  through the same literal/variable/primitive/user-call case split as expression
  preservation.
- [x] Checked expression-level done invariant combining exact source
  store-domain preservation with the single-result fact, so open let/assign
  sequence constructors can consume one expression-head completed-branch
  theorem instead of separately rebuilding domain and result-count facts.
- [x] Path-native direct internal-user-call restored-result replay for discarded
  results and existing assignment targets, including terminal halt/revert
  propagation, exact visible source-domain preservation, and selected-trace
  lifting.
- [x] Path-native direct internal-user-call restored-result replay for fresh
  multi-result declarations, extending the visible source layout only after a
  regular return while terminal exits bypass publication.
- [x] Regular-argument direct internal-user-call semantic heads for
  discard/existing-assignment and fresh-declaration targets, composing lowered
  target argument replay, recursively selected callee-body execution, return
  arity, caller restoration, and pure target publication.
- [x] Generic path-native direct internal-user-call emitted-block join: terminal
  argument exits pad only the selected generated prefix and skip the call;
  regular argument exits append one recursively selected singleton-call path
  and rebuild `preArgs ++ [call]`.
- [x] Concrete direct internal-user-call statement wrappers for discarded
  `ExprStmtCall`, existing-target multi-`Assign`, and fresh multi-`Let`.
  Multi-`Let` initializes target return slots as hidden compiler state, retains
  the old source-visible layout during argument/callee execution, and publishes
  the extended layout only after successful return.
- [x] Safe one-output primitive singleton/domain invariants no longer consume
  primitive no-error evidence. If the source primitive errors, the singleton
  postcondition is vacuous; the remaining no-error boundary is confined to the
  strict primitive expression-preservation relation.
- [x] Allowed-aware expression-prelude sequence relation plus strict-to-sequence
  adapter, so expression preservation can be weakened at sequence frontiers
  without baking source primitive errors into the strict expression relation.
- [x] Open let/assign expression-prelude sequence constructors now consume the
  allowed-aware expression relation directly. The relation only admits source
  expression errors against target expression errors, avoiding an unsound
  source-error/target-success continuation.
- [x] Checked generated-argument cons wrapper using the expression-level
  dispatchers, so `Safe.CallSafe.exprs (head :: tail)`, source scoping,
  checked `lowerBound1?`, final `toStackSeq?`, freshness, and recursive
  head/tail premises feed one `SourceArgStackPreludeOpenSoundAtExactTarget`
  cons step.
- [x] Target-fuel-parametric expression-level dispatcher, so sequence-frontier
  proofs can request expression preservation at their exact `pre.length +
  tailFuel.succ` fuel instead of the older fixed `pre.length + 2` fuel.
- [x] Open let/assign sequence-head constructors now derive expression
  preservation and done-domain/singleton invariants from checked
  `Safe.CallSafe.expr` lowering, instead of taking separate `hExpr` and
  `hExprDone` premises.
- [x] Removed the now-stale primitive-specific open let/assign sequence
  scaffolds; the live sequence-head route is the generic expression-level
  `Safe.CallSafe.expr` wrapper.
- [x] Non-user-call checked statement decomposition for `let/assign x := expr`,
  separating expression-lowered heads from the internal-user-call
  statement-lowering branch.
- [x] No-internal-user-call generated-prelude bridge for expressions, so
  checked non-user-call let/assign heads can recover `GeneratedPrelude pre`
  from `Expr.lower1?` instead of assuming it.
- [x] Checked no-internal-user-call let/assign sequence-frontier constructors,
  so expression-lowered heads can derive the generic `Safe.CallSafe.expr`
  sequence proof from checked compiler output, generated-prelude recovery, and
  the recursive argument-prelude premise at the exact tail fuel.
- [x] Live safe non-CALL primitive expression and sequence-frontier routes no
  longer take primitive no-error as a premise. Checked argument evaluation now
  carries arity plus positive-fuel as a done invariant, and
  `SourcePrimitiveCallNoErrorAt.of_safe_one_output_positive_fuel` constructs
  the `.Ok`/actual-args no-error fact only at the primitive done branch.
- [x] Checked internal user-call expression lowering decomposition:
  `lower1?_user_call_some_components` exposes the unsupported-object-builtin
  rejection, the direct-argument fast path versus generated argument prelude,
  the generated `let tmp := 0; call [tmp] f ...` shape, final temp variable,
  and fresh state. `CallSafe`/lexical user-call projection lemmas now expose
  argument safety, argument scope, and builtin support explicitly. The
  `directCallArgsSafe?` path is now proved to be exactly the nil-argument case.
- [x] Existing internal user-call expression success bridges now consume
  `lower1?_user_call_some_components` instead of re-unfolding
  `Expr.lower1?`/`Expr.lower?`, so the closed/direct and generated argument
  cases share the same checked compiler decomposition that the open branch will
  use.
- [x] Current `YulOpen` internal user-call boundary is explicit:
  `yulOpen_evalValues_user_call_succ_eq_bind_args` and
  `yulOpen_execCall_user_succ_eq_bind_args` show that user-call arguments are
  evaluated with open external-CALL suspension, and completed arguments enter
  `OpenExternal.YulOpen.call` so CALL-family primitives inside user function
  bodies stay visible.
- [x] Added the target open-body internal call semantics:
  `OpenExternal.YulOpen.call` mirrors imported `Yul.call` but runs the selected
  function body through `YulOpen.exec`, so CALL-family primitives inside the
  callee body can suspend. The live `YulOpen.evalValues` and `YulOpen.execCall`
  user-call branches now route through this open-body function.
- [x] Made the executing-contract override authoritative for open internal
  function resolution. Reentrant abstract responses may mutate caller account
  state, but they cannot replace the fixed code image of an already-executing
  frame. `OpenExternal.YulOpen.callFrame` names the explicit immutable-frame
  boundary. A no-override call consults mutable `accountMap` only once to load
  an entry frame, then executes the selected body under that fixed code image.
- [x] Removed mutable account lookup from the selected-callee proof stack:
  override-specific source decomposition, CALL-safe/scoped restoration, and raw
  hidden-slot replay wrappers now consume the fixed executing contract image
  directly. Rewrote open caller-local/domain/out-of-fuel invariants for the
  corrected override split and deleted the unused open-to-closed argument
  adapter instead of preserving it as a compatibility route.
- [x] Factored the open internal-call function selector as
  `OpenExternal.YulOpen.callFunction?` and checked
  `call_succ_eq_bind_body_of_find_function`, exposing the successful branch as
  exactly open callee-body execution followed by imported call restoration.
- [x] Deleted the stale open-vs-imported closed-agreement compatibility layer
  after frame snapshotting made its claim intentionally false. Removed the
  auxiliary strict Yul-to-EVM argument adapter family that consumed it; the
  CALL-capable route stays open through nested responses instead of collapsing
  back to Nethermind's mutable account-reload behavior.
- [x] Added the open internal-user-call one-result invariant:
  `yulOpenEvalValues_user_call_doneInvariant_single_of_exprOk` proves from
  `UserCallArity.ExprOk` that every completed open user-call expression result
  is a singleton, following any suspended callee-body CALL responses rather
  than appealing to closed `Yul.call`.
- [x] Added contract-specialized expression-frontier wrappers for open
  let/assign heads and generated argument cons:
  `sourceOpenResultSeqSoundAtExactHiddenCtx_cons_let_callSafe_expr_prelude_of_lower1?_cases_userArity`,
  `sourceOpenResultSeqSoundAtExactHiddenCtx_cons_assign_callSafe_expr_prelude_of_lower1?_cases_userArity`,
  and
  `sourceArgStackPreludeOpenSoundAtExactTarget_cons_generated_of_lowerBound1?_callSafe_exprs_expr_cases_userArity`.
  These construct the internal user-call singleton branch from
  `UserCallArity.ExprOk` in concrete-contract contexts instead of asking the
  caller for an ad hoc `hUserSingle` premise.
- [x] Added raw let/assign sequence-frontier constructors over
  `SourceExprSeqPreludeOpen`. These target the arbitrary-prefix equations
  directly, so internal user-call expression preludes can propagate suspended
  or nonregular target prefix results instead of passing through the strict
  `SourceExprPreludeOpen.run` invalidation adapter. The assignment wrapper now
  derives its prefix-containment invariant from `SourceWritesDisjoint`, so this
  path is ready to consume checked expression-lowering write-disjointness.
- [x] Factored the older generated-prelude let/assign sequence constructors
  through `SourceExprSeqPreludeOpen`; the duplicated bind proof is gone, and
  existing checked no-user expression frontiers now pass through the same raw
  sequence boundary that internal user-call expression preludes need.
- [x] Added checked raw-head let/assign constructors for non-top-level-user-call
  expressions. These remove the `ExprNoUserCalls`/generated-prelude gate from
  checked statement decomposition, exposing the real continuation-aware
  expression-head proof obligation needed for nested internal user calls.
- [x] Added raw append laws for `SourceExprSeqPreludeOpen.runLetTarget` and
  `runAssignTarget`. These let the expression-recursive route peel arbitrary
  generated/internal-user-call target prefixes while preserving suspended and
  nonregular prefix outcomes.
- [x] Added checked target decompositions for internal user-call expression
  lowering, exposing the actual `lower1?` shape as `preArgs` followed by
  `let tmp := 0; call [tmp] f lowerArgs` through the raw
  `SourceExprSeqPreludeOpen` target append laws.
- [x] Added source-side `SourceExprSeqPreludeOpen.runLetSource` and
  `runAssignSource` equations for internal user-call expressions, exposing
  open argument evaluation followed by open internal function-call execution
  before the outer let/assign tail continuation.
- [x] Added exact target suffix equations for internal user-call expression
  heads: `runLetTarget_user_call_suffix_eq` and
  `runAssignTarget_user_call_suffix_eq` expose the hidden temporary
  initializer, the open target `Stmt.call`, regular continuation through the
  temporary read, and nonregular call propagation without closing the callee
  body.
- [x] Added checked `Expr.lower1?` target wrappers for internal user-call
  expression heads: `runLetTarget_user_call_lower1?_eq_open_call` and
  `runAssignTarget_user_call_lower1?_eq_open_call` combine the compiler-output
  decomposition with the suffix equations, so let/assign frontiers can expose
  `preArgs`, hidden temp insertion, the open target `Stmt.call`, regular temp
  replay, and nonregular propagation from the actual checked lowering result.
- [x] Added raw argument-prelude soundness wrapper
  `sourceArgRawPreludeOpenSoundAtExactTarget_of_stack_varMap_toStackSeq`,
  which peels the stack-order generated argument proof down to
  `SourceArgRawPreludeOpenDoneRel` so target internal `Stmt.call` can consume
  the checked `Functions.Source.ArgList.eval` state/value relation directly.
- [x] Added target-side internal-call decomposition
  `compilerOpen_stmt_run_call_succ_eq_bind_body_of_find_function`, exposing
  the open `Stmt.call` execution as argument evaluation, resolved open callee
  body execution, return assignment, or terminal propagation.
- [x] Added closed-to-open variable argument-list bridge
  `compilerOpen_functionsArgList_eval_var_map_of_source`, so the raw
  generated-argument relation can feed its checked closed `ArgList.eval` fact
  into the open target internal-call statement.
- [x] Added hidden-result-temp argument bridge
  `compilerOpen_functionsArgList_eval_insert_of_user_call_args`, so direct
  empty argument calls and generated variable-only argument calls can evaluate
  lowered arguments after the target inserts the fresh return slot.
- [x] Added done-branch handoff
  `sourceArgCallPreludeOpenDoneRel_targetArgEval_insert`, combining the
  post-reversal source/target argument relation with the hidden-temp argument
  bridge and preserving `SourceStateRel` after target return-slot insertion.
- [x] Added generic open-bind handoff
  `sourceArgCallPreludeOpenResultRel_bind_targetArgEval_insert`, allowing the
  post-reversal open argument-prelude relation to compose through target
  lowered-argument evaluation after hidden return-slot insertion.
- [x] Added raw-to-bound wrapper
  `sourceArgRawPreludeOpenResultRel_bind_reverse_targetArgEval_insert`, so
  internal user-call expression callers can consume the raw generated-argument
  relation and get reversal plus hidden-temp target argument evaluation in one
  checked step.
- [x] Added expression-level target decomposition for internal user-call
  lowering: `sourceExprPreludeOpen_append_eq`,
  `sourceExprPreludeOpen_user_call_suffix_eq`, and
  `sourceExprPreludeOpen_user_call_lower1?_eq_open_call` expose the checked
  `Expr.lower1?` result as `preArgs`, hidden temp initialization, open
  `Stmt.call`, and regular temp read without going through let/assign
  statement frontiers.
- [x] Added resolved-callee target bind shape
  `sourceExprPreludeOpen_user_call_lower1?_eq_open_call_body_of_find_function`,
  which unfolds the checked expression-level target `Stmt.call` through open
  lowered-argument evaluation, open `FunDef.runBody`, return assignment, and
  regular temp read.
- [x] Added source-side open bind equations
  `yulOpen_toOpenResult_evalValues_user_call_succ_eq_bind_args` and
  `yulOpen_toOpenResult_call_succ_eq_bind_body_of_find_function`, exposing
  imported-Yul internal user calls as open argument evaluation followed by
  open callee-body execution after function lookup.
- [x] Added open-bind normalization utilities `openResult_bind_ok_eq` and
  `yulOpen_toOpenResult_reverseResult_eq_bind`, needed to line up the source
  reversed-argument result with the target raw argument-prelude relation.
- [x] Added `SourceArgCallPreludeOpenDoneRel` plus
  `sourceArgCallPreludeOpenDoneRel_of_raw_reverse`, naming the post-reversal
  argument-prelude done relation consumed by internal user-call bodies.
- [x] Added `sourceArgCallPreludeOpenResultRel_of_raw_reverse` and
  `_reverseResult`, converting raw open argument-prelude `OpenResultRel`
  evidence through source `reverseResult` while keeping the target raw
  argument prelude unchanged.
- [x] Added source/target callee-body bind equations:
  `yulOpen_toOpenResult_exec_block_succ_eq_bind_execSeq` and
  `compilerOpen_funDef_runBody_succ_eq_bind_body_of_insertMany`, exposing the
  open body execution underneath internal user calls on both sides.
- [x] Added callee-entry/body-return bricks:
  `sourceStateExactRel_initcall_of_lowerFun_insertMany` packages the exact
  source/target callee body-start relation from the caller argument relation,
  lowered parameter insertion, and AST/lowered function metadata.
- [x] Added callee-body completed-branch adapters:
  `sourceOpenResultSeqDoneRel_lookupMany_eq_map_lookup!` transports return
  value lookup equality out of an open body sequence done relation, while
  `compilerOpen_funDef_runBody_succ_returned_of_body_done` and
  `compilerOpen_funDef_runBody_succ_halted_of_body_done` expose the target
  `FunDef.runBody` returned and halted branches after completed open body
  execution.
- [x] Added the source restriction return-list bridge used by
  `YulOpen.exec (.Block ...)`: `lookupBang_restrictStoreTo_eq_of_scope_some`,
  its list forms, `sourceOpenResultSeqDoneRel_lookupMany_eq_map_lookup_restrictStoreTo`,
  and `compilerOpen_funDef_runBody_succ_returned_of_body_done_rel` now prove
  the target returned values are exactly the values read by the source open
  block after callee-frame restriction.
- [x] Added the generalized caller-restore state relation:
  `SourceStateRel.callRestore` proves that internal user-call restoration keeps
  the source-visible caller locals related while adopting the callee body's
  related shared state before any caller-specific continuation.
- [x] Added the pre-replay completed-body internal-user-call bridge:
  `sourceOpenResultSeqDoneRel_reviveJump_stateRel_of_regular_leave` extracts
  the revived callee state relation from a completed open body;
  `compilerOpenUserCallBodyResult`, `SourceUserCallResultDoneRel`, and the
  completed return/terminal adapters keep successful values and terminal exits
  distinct before caller-specific replay.
- [x] Added the suspension-preserving open internal-user-call result bridge:
  `SourceUserCallBodyDoneRel`, `sourceUserCallResultOpenResultRel_bind_body`,
  and `sourceUserCallResultOpenResultRel_succ_of_find_function_body` compose
  recursively related open callee bodies into selected `YulOpen.call` and
  target `FunDef.runBody` executions, preserving every suspended external
  request and related abstract response while keeping terminal exits available
  for statement-level propagation.
- [x] Added the checked recursive-body relation constructor:
  `OpenResultDoneInvariant.strengthen_rel`,
  `sourceUserCallBodyDoneRel_of_seq_checkpoint_contains`, and
  `sourceUserCallBodyOpenResultRel_of_seq_checkpoint_contains` strengthen
  ordinary recursive open-sequence preservation with an explicit source-side
  function-body invariant. The source checkpoint predicate rules out leaked
  `break`/`continue`, and visible-store containment plus `SourceStateRel`
  constructs the compiler return lookup without a target-side oracle.
- [x] Removed the temporary returned-singleton hidden-slot replay recursion
  scaffold instead of retaining compatibility wrappers. The live bridge no
  longer forces terminal callee exits through an expression-value read.

Remaining work:

1. [ ] Close the recursive generated-argument theorem.
   - [x] Prove the immediate generated-variable replay lemma from the
     `lowerBound1?` cons shape: after the tail variables are evaluated, the
     head prelude runs, and the fresh hidden temp is inserted, final
     `toStackSeq?` evaluation replays the tail variables and appends the head
     value in the exact stack order.
   - [x] Derive the replay lemma from the existing closed invariants:
     generated-variable shape, temp freshness, disjoint generated writes,
     local-domain preservation, `SourceVarsAgree`, tail replay after head
     insertion, and final value-order agreement.
   - [x] Instantiate the checked final replay done adapter with that generated
     `evalSeq` fact, rather than taking final replay as an external proof.
   - [x] Prove the recursive source-side `YulOpen.evalArgs (head :: tail).reverse`
     tail/head split: tail calls suspend first, completed tails continue into
     the head, and completed heads continue into final generated-variable
     replay.
   - [x] Prove all three branches of that split: done, suspended tail, and
     suspended head. The done branch should mirror the closed
     `evalArgs_reverse_cons_ok_split_lt` fuel split and recover the bounded
     head-fuel fact needed by recursive expression preservation.
   - [x] Compose the source split with the checked target-side
     `preTail ++ preHead ++ [let tmp := lowerHead]` open equations through
     `OpenResultRel`, preserving the response relation at every bind boundary.
   - [x] Port the proof route of
     `sourceArgListPreludeRegularAt_cons_of_tail_head` to the open theorem,
     replacing closed `Exists`/`ok` splits with open bind composition.
   - [x] Package the cons induction step for `Expr.List.lowerBound1?`,
     `Expr.List.toStackSeq?`, `Safe.CallSafe.exprs`, scoping, arity, and
     freshness into `SourceArgStackPreludeOpenSoundAtExactTarget`.
   - [x] Package the expression-head done invariant needed by open sequence
     heads: exact source store-domain preservation plus one-result completion.
  - [x] Shrink the primitive no-error boundary to
     `SourcePrimitiveCallNoErrorAt`, indexed only by source fuel, Yul
     primitive, and checked `BasicOp` arity. The older open-argument-run
     no-error predicates were removed rather than kept as compatibility
     wrappers.
  - [x] Transport the safe non-CALL primitive no-error fact without a premise:
     argument completion supplies checked arity plus `0 < sourceFuel`, the
     argument-prelude done relation supplies the `.Ok` source state, and
     `SourcePrimitiveCallNoErrorAt.of_safe_one_output_positive_fuel` closes the
     primitive error branch from existing `PrimSemantics.primCall_*_ok` lemmas.
     The stale hNoError-taking safe-primitive expression wrappers were removed.
  - [ ] Continue transporting the remaining strict-preservation facts consumed
     by safe non-CALL primitive heads through the recursive frontier:
     primitive stack soundness/result relatability, state relation, storage
     equality, result equality, and local preservation. These now sit in the
     primitive stack-soundness and recursive frontier packages, not in a raw
     primitive no-error assumption.
  - [x] Factor the current open internal-user-call semantics boundary into
     checked equations, so the next user-call expression wrapper can use the
     open argument route and then enter the live open-body call semantics.
  - [x] Add a real `YulOpen.call` open-body semantic target for internal
     user-function calls, and migrate the live `YulOpen.evalValues` /
     `YulOpen.execCall` user-call branches from closed `Yul.call` to this
     open-body function.
  - [x] Prove the full `execSeq`/`exec`/`loop`/`call` done-branch agreement
     with imported closed Yul, extending the already-checked argument and
     primitive/user-call helper agreement lemmas.
  - [x] Add local-domain preservation for live open internal user calls:
     completed or resumed callee bodies restore the caller varstore via the
     imported call-return state operation, while external suspensions recurse
     through the open result.
   - [x] Run
     `lake env lean EvmCompiler/Yul/RecursiveBridgeSupport.lean` and record
     the checked theorem names in `PROGRESS_LOG.md`.

2. [ ] Move CALL support to expression-level open preservation.
   - [x] Identify the canonical recursive expression theorem that replaces the
     direct let-CALL/assign-CALL route.
   - [x] Make primitive expression preservation depend on the recursive open
     argument-prelude theorem for every primitive head, including ordinary
     `CALL`.
   - [x] Prove safe non-CALL primitive preservation through the same route,
     with primitive-error exclusion kept explicit.
   - [x] Prove ordinary `CALL` primitive preservation through the same route,
     so the enclosing abstract CALL request appears only after all argument
     expressions have completed.
   - [x] Factor the compiler side of internal user-call expression lowering,
     including the direct-argument fast path and generated-argument prelude, so
     the open user-call expression branch can consume checked components
     instead of re-opening `Expr.lower1?`.
   - [x] Refactor the existing internal user-call expression success bridges to
     use that checked decomposition, reducing the next open theorem to a
     semantic argument-prelude/function-body problem rather than compiler
     case analysis.
   - [x] Add the generic open pair-state bind layer plus concrete
     checkpoint/store adapters for safe primitives, malformed non-suspending
     ordinary `CALL`, exposed ordinary-`CALL` responses, and restored caller
     locals after internal user calls. The open response adapter quantifies
     over every shared abstract response and does not inspect a concrete
     external world.
   - [x] Prove the recursive open expression-local invariant:
     `yulOpenEvalValues_evalArgs_toOpenResult_doneInvariant_checkpointStoreContains_of_callSafe_primitiveFamilies`
     threads checkpoint legality and visible-local containment through
     literals, variables, nested argument lists, safe primitives, ordinary
     external `CALL`, and internal user calls. Named `evalValues`, scalar
     `eval`, and reversed-argument corollaries now expose this layer to
     statement proofs.
   - [x] Add the state-valued open done-invariant layer and first statement
     bricks: block scope restoration, let/assign expression binds,
     break/continue/leave markers, and sequence head/tail composition now
     preserve checkpoint legality and protected visible locals across every
     exposed response.
   - [x] Add open call-statement and branch bricks: `ExprStmtCall`,
     `execPrimCall`, and `execCall` reuse the recursive argument invariant,
     assign returned values after completion, and keep exposed ordinary
     `CALL` requests open; `if` and `switch` compose scalar evaluation into
     recursively supplied blocks.
   - [x] Prove the exact open out-of-fuel expression invariant: nested
     arguments, arbitrary exposed ordinary-`CALL` responses, malformed
     non-suspending fallback, and internal caller restoration all keep
     `.OutOfFuel` sticky. This is the honest exceptional branch needed before
     scoped block recursion.
   - [x] Lift the exact sticky `.OutOfFuel` invariant through open statements
     and sequences, including statement-form CALL, blocks, conditionals,
     selected switch bodies, and loop exceptional flow.
   - [x] Add ordinary scoped-recursion bridge facts: construct the combined
     invariant for real `.Ok` stores, lift strict top-level admission into
     enclosing contexts, split strict successful states into `.Ok` versus
     sticky `.OutOfFuel`, convert the sticky proof back into the normal
     invariant, and run continuations through that honest split.
   - [x] Add ordinary open `if` and `switch` combinators: scrutinees run under
     strict admission, chosen blocks recurse from their actual `.Ok` scope
     store or the verified sticky `.OutOfFuel` path, and no checkpoint input
     is fabricated.
   - [x] Add the ordinary open loop post-block combinator: scoped post
     `.OutOfFuel` and `leave` return outward, scoped post `break`/`continue`
     are impossible, and only a real `.Ok` post state recurs into the next
     iteration.
   - [x] Add the ordinary open loop body combinator: body `.OutOfFuel` and
     `leave` return outward, body `break` is consumed through revival, and body
     `continue` or normal completion enters the checked post-block
     continuation.
   - [x] Compose the ordinary open loop condition: zero returns the strict
     condition state outward, `.OutOfFuel` follows the sticky body theorem,
     and a real `.Ok` condition state enters the verified body/post/recursion
     continuation.
   - [x] Assemble the ordinary CALL-safe scoped `exec`/`execSeq` induction:
     declarations, assignments, statement-form calls, blocks, conditionals,
     selected switch bodies, loops, control markers, and sequence tails now
     preserve checkpoint admission and visible-local containment across every
     exposed ordinary-`CALL` response.
   - [x] Recurse through compound expression contexts, including cases like
     `add(call(...), x)`, so nested CALLs are handled by expression structure
     rather than by direct statement-shape lemmas.
   - [x] Adapt internal user-call expression preservation when arguments may
     suspend.
   - [x] Connect completed internal-user-call argument states to the recursive
     function-body bridge at the sequence frontier.
   - [x] Correct the selected-callee target-proof-fuel boundary in recursive
     expression preservation: thread an explicit minimum residual target fuel
     through generated argument prefixes, and request selected-callee callbacks
     only above that floor instead of at impossible clocks such as zero.
   - [x] Reject and remove the attempted uniform at-or-above target-proof-fuel
     contract after theorem-truth audit: extra executable target cutoff can
     expose a later CALL after finite-fuel Yul has exhausted on the same
     response path.
   - [x] Add finite open interaction traces and pathwise result preservation:
     each event records the equal external request site and one shared
     arbitrary black-box response, without pretending executable proof fuel is
     a semantic monotone.
   - [x] Lift recursive open sequence preservation through the actual scoped
     `.Block` executed by an internal Yul call: source local-store restriction
     is threaded through a bind pullback, target execution remains unchanged,
     and every exposed external response keeps the same relation.
   - [ ] Replace the scalar-floor sequence target with a pathwise finite-trace
     target: quantify over every concrete arbitrary response trace and
     construct exact target cutoff adequacy for that trace from compiler
     output and source-fuel/resource premises.
     The primitive expression-statement compiler decomposition now has the
     finite-path raw-head adapter
     `checkedOpenSeqPathLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_exprStmt_prim_rawHead`,
     matching the existing `let`/`assign` adapters. The target-side raw
     normalizer/resolver
     `compilerOpen_block_runOpen_exprStmt_expr_prelude_resolves` is also
     checked. The source side now has the exact primitive expression-statement
     normalization layer:
     `yulOpen_toOpenResult_execSeq_exprStmt_prim_eq_bind_evalValues` and
     `yulOpen_toOpenResult_execSeq_exprStmt_prim_eq_runExprStmtPrimSource`.
     The source-side finite-path semantic combinator
     `sourceOpenResultSeqPathSoundWhenAtExactHiddenCtx_cons_exprStmt_prim_expr_prelude_raw`
     is now checked over that normalized runner. The checked wrapper now has
     the needed `lower0?` primitive decomposition and domain-only imported
     source invariant:
     `lower0?_primitive_call_some_components` and
     `lower0?_yulOpenEvalValues_callSafe_prim_doneInvariant_domain_of_lower0?_actual_fuel`.
     `lower0?_callSafe_primitive_safe_of_lower0?` also records the semantic
     boundary that ordinary external `CALL` cannot be the primitive head of a
     successful zero-result expression-statement lowering; zero-output safe
     primitives still need the raw path theorem to split successful primitive
     execution from nonrelatable static/resource errors. The selected
     successful primitive half of that split is now available as
     `sourceExprRawPreludeOpenPathRel_prim_regular_safe_ok_of_arg_terminal`,
     which deliberately assumes only that the concrete selected primitive path
     resolved successfully, not that the primitive is globally no-error. The
     full zero-output primitive compositor
     `sourceExprRawPreludeOpenPathSoundWhen_prim_safe_zero_of_arg_terminal_canonical`
     now packages the selected primitive-success path together with rejection
     of selected primitive-error paths through the caller's relatability
     filter. The raw compiler-derived path theorem
     `lower0?_sourceExprRawPreludeOpenPathSoundWhen_callSafe_prim_of_lower0?_actual_fuel_recursive`
     and checked wrapper
     `checkedOpenSeqPathLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_exprStmt_prim_of_programCALL_recursive`
     are now checked and folded into the exact exhaustive expression-statement
     frontier; the old zero-output expression-statement dispatcher has been
     deleted. Terminal primitive statements are covered by the same exact
     expression-statement frontier.
   - [x] Construct the selected-callee open body invariant from CALL-safe body
     scoping and initialized local-store exactness: after every shared external
     response, completed source bodies must satisfy function checkpoint
     admission and retain the visible return/parameter store domain.
   - [x] Feed the selected-callee source invariant into the ordinary recursive
     body relation: strengthening follows every existing suspension and enriches
     only completed body branches before caller restoration/replay.
   - [x] Specialize resolved internal-call restoration to a checked CALL-safe
     selected function: callers now provide the ordinary recursive open body
     theorem and receive the restored `YulOpen.call` relation directly.
   - [x] Replay a successful restored internal-call expression through its
     generated hidden result slot: the returned singleton is assigned into the
     existing compiler-only temp, read back as the source expression value,
     and hidden again from the visible source layout.
   - [x] Preserve restored internal-call completion at the raw hidden-slot
     statement boundary: successful singleton returns populate the generated
     temp while keeping it hidden from the visible source layout, and callee
     halt/revert results remain terminal target outcomes for enclosing
     generated preludes to propagate.
   - [x] Replay restored internal-call completion into the terminal-aware raw
     expression endpoint: successful hidden-slot assignments read back the
     singleton value, while callee halt/revert outcomes remain stopped target
     preludes with their terminal state intact.
   - [x] Lift terminal-aware hidden-slot replay across the full open restored
     internal-call trace: arbitrary suspended external requests remain visible,
     and only completed callee branches enter the raw expression endpoint.
   - [x] Decompose the generated internal-call suffix through the terminal-aware
     raw endpoint: hidden-slot initialization, lowered-argument evaluation,
     selected open body execution, and hidden-slot replay retain stopped
     terminal outcomes under the actual suffix scope.
   - [x] Extend the terminal-aware suffix equation across the complete lowered
     internal-call expression: generated argument preludes run first, any
     suspended nested request remains visible, stopped prefixes remain stopped,
     and only regular prefixes enter the selected callee body.
   - [x] Add the terminal-aware generated argument-prefix relation: regular
     completion retains the existing lowered-argument replay contract, while
     nested `YulHalt` and `Revert` outcomes retain the target statement stop
     needed by the enclosing raw expression.
   - [x] Lift strict raw argument-prefix proofs into the terminal-aware relation
     and compose terminal-aware prefixes with raw expression continuations:
     regular prefixes continue, terminal prefixes stop, and suspended requests
     remain visible through the outer bind.
   - [x] Name strict and terminal-aware raw generated-argument soundness at the
     exact target block boundary, and lift any checked strict raw proof into
     the terminal-aware interface without changing its observable call trace.
   - [x] Add the terminal-aware raw empty-argument constructor: empty imported
     evaluation and empty generated target prefixes finish regularly with
     empty lowered replay and no hidden external interaction.
   - [x] Hide the terminal-aware raw empty-argument constructor behind the
     checked compiler-output interface, so nil and cons recursion both consume
     successful whole-list `lowerBound1?` results.
   - [x] Factor one generated argument head on the target through the raw
     expression runner: successful singleton values populate the fresh
     temporary, while stopped nested-call preludes skip that binding unchanged.
   - [x] Extract the closed variable-only replay core for one generated
     argument head: after the head runs, inserting its fresh temporary makes
     `.var tmp :: lowerTail` replay the new value followed by the retained tail.
   - [x] Preserve generated-tail variable agreement across the terminal-aware
     raw head runner: only successful value completions need replay evidence;
     stopped nested-call outcomes bypass replay and remain intact.
   - [x] Factor imported reverse-cons argument evaluation through raw
     `evalValues` for the head before its singleton projection, so nested calls
     remain visible at the recursive expression boundary in source order.
   - [x] Compose one terminal-aware raw generated argument head after a regular
     tail prefix: successful heads insert the fresh temporary and replay the
     complete lowered list, while stopped heads propagate their terminal result
     without entering generated replay.
   - [x] Factor the terminal-aware raw argument-tail binder: regular tails
     enter the remaining generated prefix, while halt/revert tails skip it and
     propagate unchanged across arbitrary suspended requests.
   - [x] Compose terminal-aware raw reverse-cons argument lowering: imported
     Yul evaluates the recursive tail and raw head in semantic order, while the
     target executes the matching tail prefix and generated head temporary.
   - [x] Derive raw reverse-cons freshness and write-disjointness obligations
     from checked lowering components, so recursive callers do not provide
     generated-variable bookkeeping as semantic assumptions.
   - [x] Hide terminal-aware raw reverse-cons lowering decomposition behind a
     compiler-output wrapper: recursive callers now provide the successful
     whole-list `lowerBound1?` result while tail/head lowering and fresh-temp
     components are recovered internally.
   - [x] Parameterize the terminal-aware raw generated-head chain by remaining
     target fuel, so recursively proved tails can reserve fuel for outer
     generated heads instead of relying on the non-compositional minimal
     `preHead.length + 2` case.
   - [x] Package terminal-aware raw checked argument lowering as structural
     syntax recursion: nil and cons consume whole-list `lowerBound1?` results,
     recursive tails reserve the generated outer-head cost, and recursive
     heads delegate to raw expression preservation.
   - [x] Add the terminal-aware raw primitive-expression binder: argument-side
     halt/revert outcomes become stopped raw expressions, regular completion
     enters an explicit primitive continuation, and suspended argument calls
     retain the full post-primitive response relation.
   - [x] Add the strict-value-to-raw-expression lift: already-proved regular
     expression continuations map into `RawTarget.values` without inventing a
     stopped branch, keeping terminal propagation confined to honest raw
     boundaries.
   - [x] Recover compiler stack-sequence replay from regular terminal-aware raw
     generated arguments: the proof reverses the recorded source-order closed
     variable replay and derives the compiler-open stack evaluator result.
   - [x] Add the regular terminal-aware raw primitive reuse adapter: generated
     stack-sequence replay reconstructs the strict primitive input, existing
     strict primitive continuations run unchanged, and successful values lift
     back into the terminal-aware raw expression relation.
   - [x] Construct regular raw primitive input arity from the checked
     `toStackSeq?` witness and lowered `ArgList.eval` replay, then specialize
     strict continuation reuse to safe non-CALL primitives and CALL-family
     primitives. The CALL-family adapter retains the universal shared-response
     preservation premise through the raw-value wrapper.
   - [x] Name the canonical terminal-aware raw primitive argument-response
     adapter and add the CALL-safe raw primitive dispatcher. Recursive callers
     now provide one generated argument proof; regular completion chooses the
     safe primitive or ordinary open-`CALL` strict continuation internally,
     while stopped prefixes bypass the primitive.
   - [x] Add terminal-aware raw literal and scoped-variable leaves plus their
     checked `lower1?` wrappers. Empty generated prefixes return honest raw
     values directly; variable lookup keeps the visible-store containment
     premise explicit.
   - [x] Hide CALL-safe raw primitive decomposition behind checked `lower1?`
     output and add the whole terminal-aware raw expression dispatcher.
     Literals, variables, and primitive calls are now internal branches;
     selected internal user calls remain the single explicit expression
     callback to connect to recursive body preservation.
   - [x] Scope the structural raw argument dispatcher callback to head
     subterms of the current argument list before assembling the final
     recursive expression constructor. The live theorem now threads
     `head ∈ args` through cons recursion, so its callback cannot ask an
     induction hypothesis to prove arbitrary expressions.
   - [x] Thread each checked head `lower1?` equation into the structural raw
     argument singleton callback. Recursive one-result proofs can now be
     derived from actual compiler output instead of a lowering-independent
     expression oracle.
   - [x] Scope each raw argument singleton callback to the related regular tail
     state already produced by recursive prefix preservation. Head one-result
     facts no longer need to hold for arbitrary unrelated source states.
   - [x] Construct checked raw argument-head singleton invariants from
     whole-list CALL safety, lexical scope, user-call arity, head membership,
     checked lowering, and the actual related regular tail state.
   - [x] Hide raw structural argument-head singleton plumbing behind a checked
     compiler-output wrapper. Recursive callers now supply only whole-list
     facts, head expression preservation, and continuation-response adapters.
   - [x] Reuse the checked hidden-result-slot freshness theorem at the
     terminal-aware raw boundary: regular prefixes replay the reversed lowered
     arguments unchanged after insertion of the fresh compiler-only slot.
   - [x] Compose regular terminal-aware argument completion with an open
     restored internal-call relation: the callee consumes the replayed stack
     order, arbitrary external suspensions remain visible, and hidden-slot
     replay preserves terminal stops.
   - [x] Instantiate the regular raw composition with the checked selected
     CALL-safe/scoped function-body bridge: completed argument prefixes now
     enter the actual recursively related callee body before restoration and
     hidden-slot replay.
   - [x] Name the canonical selected-callee caller-restoration, hidden-slot
     replay, and composed selected-body response transformers, and specialize
     the raw selected-body bridge so recursive callers provide one body
     relation without ad hoc adapters.
   - [x] Specialize the terminal-aware argument binder to imported
     `YulOpen.evalValues` user-call semantics: reversed raw argument evaluation,
     restored stack order, open callee entry, stopped prefixes, and suspended
     requests now share one checked source-side equation.
   - [x] Name and expose the compact target-side internal-call continuation:
     regular generated argument completion enters lowered argument replay,
     selected body execution, and hidden-slot replay; stopped prefixes remain
     stopped without duplicating the bind tree in recursive callbacks.
   - [x] Add the whole lowered internal-call raw expression wrapper: checked
     expression lowering, terminal-aware recursive argument preservation, and
     the regular selected-callee continuation now compose without direct
     declaration-CALL or assignment-CALL statement shapes.
   - [x] Name the canonical terminal-aware raw internal-user-call
     argument-response relation and add its whole-expression wrapper.
     Suspended argument requests now resume into the full selected-callee
     continuation without an ad hoc response adapter premise.
   - [x] Construct the checked internal-user-call direct argument fast path
     from `directCallArgsSafe?`, `toLocals1?`, and explicit positive source
     and target fuel; dispatch direct versus generated arguments without
     exposing empty-list replay plumbing.
   - [x] Feed the checked direct/generated argument split into the canonical
     raw internal-user-call expression wrapper. Callers now provide only
     positive source fuel, generated-prefix preservation when selected, and
     the regular selected-callee continuation.
   - [x] Expose the raw reversed-argument scheduler as residual base fuel plus
     fixed list overhead, and recover a residual base from any sufficient-fuel
     inequality. This is the checked algebra needed before widening recursive
     nested-expression adequacy.
   - [x] Widen all-residual-base raw argument preservation to arbitrary source
     fuel above the fixed reversed-list traversal overhead. Nested-head
     adequacy remains an explicit recursive obligation.
   - [x] Define syntax-aware raw expression residual reserves and split an
     adequate call reserve into the exact reversed-argument scheduler base plus
     a reserve proof for every selected nested argument head. No fuel
     monotonicity assumption is used.
   - [x] Factor generic open-call response-relation bind comaps and rewrite raw
     primitive, user-call argument, caller-restoration, and hidden-slot replay
     adapters as thin specializations instead of bespoke continuation records.
   - [x] Define canonical generated-argument tail and head response pullbacks
     and prove reverse-cons terminal-aware raw composition without caller
     supplied response-conversion premises.
   - [x] Lift canonical generated-argument response composition through
     compiler-derived freshness, generated-variable disjointness, and hidden
     temporary safety bookkeeping.
   - [x] Hide generated reverse-cons `lowerBound1?` decomposition behind a
     checked canonical wrapper, so recursive callers consume the whole-list
     lowering result and the induced tail/head relations only.
   - [x] Recurse structurally over generated argument lists with canonical
     pulled-back response relations. Nested heads are proved at the expression
     interface under the exact continuation that remains around each head.
   - [x] Add the checked canonical generated-argument facade: whole-list CALL
     safety, lexical scope, and user-call arity now construct selected-head
     singleton invariants internally.
   - [x] Carry syntax-reserve adequacy through canonical generated-argument
     recursion and expose `sourceExprRawPreludeBaseReserve head ≤ residualBase`
     at every nested expression callback.
   - [x] Thread reserved-layout coverage into each canonical generated
     argument head callback from the checked tail lowering, and expose both
     whole-list and selected-head reserve adequacy from the CALL reserve split.
   - [x] Define actual-prestate raw response admissibility generically over
     suspended result carriers and preserve it through bind pullbacks.
     Canonical generated-argument recursion now constructs and passes this
     semantic boundary to every nested expression callback.
   - [x] Add the reserve-aware raw expression dispatcher for literals,
     variables, and primitive heads. Primitive CALL arguments now recurse
     through the canonical generated-argument facade at the exact scheduler
     fuel, and safe primitive no-error evidence is constructed from checked
     one-output lowering plus positive fuel.
   - [x] Add the reserve-aware internal-user-call expression wrapper.
     Generated prefixes recursively preserve nested argument CALLs before
     entering the selected-callee continuation; the checked direct empty-arg
     path remains compiler-constructed.
   - [x] Assemble well-founded raw expression recursion over syntax size.
     Literals, variables, primitive CALLs, nested compound-expression CALLs,
     and internal-user-call argument prefixes now share one expression proof;
     the sequence layer supplies only the named selected-callee regular
     continuation.
   - [x] Introduce the terminal-aware raw generated-expression runner and
     relation: regular preludes return the existing strict value payload,
     stopped preludes retain their full target outcome/context, append
     propagation is explicit, and generic let/assign consumers continue only
     from successful singleton values.
   - [x] Feed terminal-aware raw generated expressions into generic
     declaration and assignment sequence consumers: successful singleton
     values enter the tail, while preserved halt/revert outcomes close the
     enclosing sequence without direct let-CALL or assign-CALL cases.
   - [x] Build the user-call singleton/done-invariant part from checked
     user-call arity and the live open `YulOpen.call` result.
   - [x] Close the arbitrary-actual-fuel generated-argument frontier:
     unreachable heads retain their unexecuted compiler suffix, the two
     residual boundary clocks are rejected through the relatable-result
     filter, and productive heads reconstruct the private scheduler only
     after its exact residual base is available.
   - [x] Prove the expression-level low-clock semantic leaves: every call
     expression at one total tick exhausts before argument completion, and
     internal user-call expressions at totals two and three reduce to explicit
     nonrelatable frontend/resource errors before a productive callee body.
   - [x] Relate or rule out expression error and out-of-fuel branches using
     existing acceptedness/resource premises.
   - [ ] Delete direct let-CALL and assign-CALL scaffolding as soon as the
     expression theorem subsumes it; do not leave compatibility aliases.
   - [ ] Run the focused Lean check and log the exact removed theorem names.

3. [ ] Thread expression preservation through open sequence frontiers.
   - [x] Update no-internal-user-call expression `let` and assignment sequence
     constructors to derive expression evidence internally from checked
     lowering plus the recursive argument-prelude route.
   - [x] Move path-native `let`, assignment, and `if` expression heads onto
     their actual evaluator clocks, discharge the low-clock leaves explicitly,
     and thread `calleeBodyFuel <= enclosingTailFuel` through recursive
     expressions so selected internal calls can invoke the strong sequence
     callback honestly.
   - [x] Narrow the selected internal-callee continuation from the old broad
     checkpoint scaffold to the admitted concrete body result before invoking
     recursive sequence preservation. Imported success-valued `State.OutOfFuel`
     is isolated behind the explicit source-facing
     `SourceOpenInternalUserCallBodyFuelAdequateAt` resource contract rather
     than reappearing as an all-results callee premise.
   - [ ] Add matching sequence constructors for internal user-call
     declarations and assignments whose arguments may suspend.
   - [ ] Thread open expression preservation through block sequencing without
     falling back to closed source execution after a suspended call.
   - [ ] Update sequence done-relations so they include the strengthened
     storage equality and result equality facts now required by the main spine.
   - [ ] Thread open preservation through `if`, `switch`, loop conditions,
     loop bodies, `break`, `continue`, `leave`, terminal statements, handler
     sequences, and kont/callee-return continuations.
   - [ ] Replace `CALLOpenSeqLoweringFrontierAt` with the finite-trace
     successor frontier and close its pathwise source-fuel step using the
     recursive induction hypothesis.
   - [ ] Prove pathwise successor-fuel and all-bounds wrappers for the open
     sequence frontier without adding all-callees-preserve, replay, monotone
     executable-cutoff, or concrete-world premises.
     A small connective adapter,
     `CALLOpenSeqPathRecursiveAt.of_frontiers_le`, now turns checked
     finite-path frontiers at every smaller bound into the recursive callback
     shape consumed by the expression and internal-procedure wrappers.
   - [ ] Replace closed `CALLSeqKontFrontierAt` dependencies with open
     handler/kont frontiers wherever calls can hide in conditions, user-call
     arguments, generated preludes, or recursive continuations.

4. [ ] Compose the recursive CALL source bridge.
   - [ ] Audit every source bridge assumption and classify it as fundamental
     source acceptedness/resource input, constructed compiler evidence, or
     stale proof scaffold to remove.
   - [ ] Replace the remaining closed `CALLSeqLoweringFrontierAt` dependency
     in the all-bounds bridge with `CALLOpenSeqLoweringFrontierAt`.
   - [ ] Thread the recursive open argument-prelude bundle through the
     accepted recursive source bridge so it is constructed at each source-fuel
     bound instead of assumed.
   - [ ] Prove the all-bounds CALL-admitting recursive source bridge with no
     public all-callees-preserve, replay, direct let/assign CALL, or concrete
     external-world premise.
   - [ ] Preserve the Solidity frontend path and planned Yul-object path while
     deleting only stale proof internals.
   - [ ] Keep `CALLCODE`, `DELEGATECALL`, `STATICCALL`, `CREATE`, `CREATE2`,
     and external account-code inspection rejected by explicit checked feature
     coverage until each has its own open-boundary semantics and proof.

5. [ ] Connect the open CALL boundary to the EVM target.
   - [x] Name the actual-prestate external-response admissibility relation and
     local open-call relation explicitly. Source/compiler and source/EVM
     primitive CALL proofs now expose that non-vacuous boundary directly.
   - [ ] Audit `OpenExternal.OpenCallRel` and request projections for every
     ordinary `CALL` observable: call kind, caller/context address, target/code
     address, value, calldata bytes, static permission, return-copy window, and
     opaque requested-gas operand.
   - [ ] Prove that the source/Yul open primitive request is related to the
     compiler-open primitive request after argument lowering.
   - [ ] Use `OpenPrimitiveCallSound` to relate the source-tower CALL boundary
     to the compiler-open primitive boundary.
   - [ ] Use `OpenPrimitiveEVMCallSound` to relate the compiler-open primitive
     boundary to the EVM stack/CALL boundary.
   - [ ] Keep the response relation universal over all shared responses and
     arbitrary caller-account/storage mutation; no concrete callee, precompile,
     account-map transition, or child-code interpreter may reappear.
   - [ ] Prove response continuations update status-word results, return data,
     memory return-copy regions, storage/account state, terminal results, and
     revert observations consistently across imported Yul, source,
     compiler-open, and EVM layers.

6. [ ] Add ordinary CALL to the public compiler spine.
   - [ ] Update checked feature coverage so ordinary `CALL` is admitted by the
     preferred public theorem while unproved external families remain rejected.
   - [ ] Add the CALL-capable public theorem over finite open CALL interaction
     traces, universally quantified over arbitrary related black-box responses
     on each concrete trace.
   - [ ] Keep the existing no-CALL theorem only as a proved fragment until the
     CALL theorem has passed the same audit gates.
   - [ ] Rename public no-CALL runtime/spine names where they become
     misleading once CALL is admitted; remove old compatibility aliases.
   - [ ] Route `LayerAudit` to the CALL-capable public theorem once the bridge
     is fully checked.
   - [ ] Confirm the public theorem proves storage equality and result equality
     through the strengthened storage/result relation in the main spine.
   - [ ] Confirm the public theorem has no stale compiler-generated evidence,
     replay certificate, all-callees-preserve premise, direct CALL statement
     scaffold, concrete external-world assumption, or hidden checker shortcut.

7. [ ] Remove stale proof internals after CALL wiring.
   - [ ] Delete direct let-CALL and assign-CALL lemmas no longer used by the
     expression-level proof route.
   - [ ] Delete leftover concrete external-world helpers, precompile branches,
     child-code branches, created-account machinery, or world-model transition
     lemmas not used by the open CALL spine.
   - [ ] Remove stale no-CALL-only wrappers once the CALL theorem replaces
     their public role.
   - [ ] Preserve infrastructure used by the Solidity frontend and planned Yul
     object support.
   - [ ] Grep the public theorem spine for stale names and concepts:
     `NoCall`, `World`, `Precompile`, `Child`, `createdAccounts`, `Replay`,
     `Certificate`, `Obligation`, `CallPreserves`, and direct let/assign CALL
     scaffold names.

8. [ ] Run verification, audits, documentation, and commits.
   - [ ] Run focused checks during proof work:
     `lake env lean EvmCompiler/Yul/RecursiveBridgeSupport.lean` and
     `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`.
   - [ ] Run public-spine checks after final wiring:
     `lake env lean EvmCompiler/LayerAudit.lean` and the relevant `lake build`
     targets touched by the CALL route.
   - [ ] Run a scoped placeholder scan over touched proof files for `sorry`,
     `admit`, `axiom`, and unjustified `unsafe`.
   - [ ] Run a public theorem-surface audit for assumptions that could be
     compiler-generated, especially layout records, replay/certificate
     witnesses, callee-preservation obligations, return-layout facts,
     generated label/token uniqueness tables, and proof-carrying emitted-code
     segments.
   - [ ] Update `PROGRESS_LOG.md` at each checked proof checkpoint and keep
     `ROADMAP.md` synchronized with completed checklist items.
   - [ ] Commit coherent verified checkpoints after meaningful proof progress,
     cleanup, or public-spine rewiring.

## Audit Concerns To Fully Discharge

This is the current active goal. These items are not complete until the public
top theorem exports a full-Yul acceptedness surface, internally constructs the
Nethermind-Yul-to-source semantic bridge packages, and derives the gas-aware
`EVM.X` sufficient-gas/precondition evidence instead of taking it as an
external execution certificate.

Last updated: 2026-05-27 22:23 PDT.

Current `GAS` policy: imported Yul may still parse/reference the raw `gas()`
primitive, and the lower EVM/assembly semantics still model the opcode, but the
accepted imported-Yul compiler surface rejects `gas()` the same way it rejects
`pc()`. The public theorem should therefore be read over accepted Yul programs
that do not lower `gas()`; older gas-oracle-parametric proof work is preserved
only on the `codex/gas-oracle-checkpoint` branch.

Current external-call direction: the speculative concrete `World` proof route
has been retired. The new CALL-family route is an open external-call theorem:
prove that imported Yul and compiled EVM reach the same external call site
(same call kind, caller/recipient/code address, value, calldata, static
permission, and local return-copy window), then quantify universally over an
arbitrary shared response. The response may encode an arbitrary opaque
reentrant transformer of caller-visible chain state; the compiler theorem must
not assume anything about that transformer beyond both sides receiving the same
response and the transformer preserving the relevant source/target shared-state
relation.
`EvmCompiler.Yul.OpenExternal` now contains the checked request-extraction
boundary for Yul argument lists and EVM stacks plus `OpenCallRel`, whose
response preservation field is explicitly universal over all shared responses.
The imported Nethermind `accountMap` remains part of the internal local-state
relation for operations such as contract storage and account lookup; the open
external boundary should not expose it as an external-world model.
`createdAccounts` is no longer part of `ChainStateRel` while CREATE/CREATE2
remain outside the live CALL proof.
The current checked hook also proves CALL-family argument/stack agreement over
an arbitrary target stack suffix and derives the needed call-context relation
from the existing compiler/source state relations. The CALL-safe semantic
contract boundary now exposes constructed `OpenPrimitiveCallSound` and
`OpenPrimitiveEVMCallSound` hooks from `SourceStateRel`; these are not new
caller-supplied assumptions.
Gas mechanics are abstracted at the open-call boundary: request equality keeps
the opaque requested-gas operand, but the chain-specific forwarded `Ccallgas`
calculation and `StateRelConfig.callGasRel` proof obligation have been removed.
The open Yul argument-domain contract now has checked constructors for both
the existing no-external-call `Safe.exprs`/`Safe.primitive` family and the
CALL-admitting `Safe.CallSafe.exprs` family: safe primitives cannot suspend as
open CALL-family requests, while ordinary `CALL` suspensions propagate the
local-domain invariant through every possible shared response.
There is now a generic `OpenExternal.OpenResult` carrier/relation and a first
checked stack-argument prelude open-result surface for completed `.done` runs.
`OpenResultRel` chooses admissible responses per suspended source/target call
pair, so nested calls can use the state-dependent reentrant response relation
appropriate to the pre-call states captured by that call.
`EvmCompiler.Yul.CompilerOpen` now gives the compiler side its own source-open
interpreter, mirroring the existing `Locals.Source`/`Functions.Source`
semantics while suspending at CALL-family primitive expressions. The generated
argument-prelude target is named by `SourceArgPreludeOpen.run`, rather than
being represented only by the old closed `EvmYul.Yul.evalArgs` evidence.
Completed open Yul argument evaluation now feeds the generated-prelude proof via
checked open-done-to-closed evaluator agreement lemmas and an adapter from
`YulOpen.evalArgs = .done ...` to `SourceArgPreludeOpenResultRel`. The
`SourceArgPreludeOpen.run` wrapper now has checked structural equations for
regular completion, prelude suspension, and final argument-sequence suspension,
plus a completed-run relation against the actual wrapper rather than only a
hand-built target value. The
remaining CALL-capable step is the true suspending case: prove open Yul
argument evaluation relates to `SourceArgPreludeOpen.run` when it reaches a
CALL-family site, then replace expression-prelude consumers that still expect
the old closed `EvmYul.Yul.evalArgs` result.

Paused checkpoint: before continuing this route, audit the state relation for
contract storage equality. The current open-call work assumes responses
preserve the relevant source/target relation, but the newly discovered concern
is that the public proof may not actually force equality of the contract's
storage state. Resumption should first identify where storage lives in
`SourceStateRel`/`SharedStateRel`/target state relations, strengthen or expose
the needed equality invariant, and only then continue the CALL suspension
bridge.

Architecture checkpoint: the proof tower is being refactored to route
structured control through an explicit typed CFG middle layer before labeled
assembly. `EvmCompiler.TypedCfg` is the new target for this boundary: blocks own
input stack shapes, terminators type-check against target block shapes, and
EVM halts are terminal outcomes rather than continuations. The old
`Structured.TypedContinuations` facade should be retired or bridged through
this IR as the refactor proceeds.

Current cleanup checkpoint: stale proof-facing wrappers that were no longer used
by the main public theorem spine have been removed. `EvmCompiler.LayerAudit`
now intentionally exposes only the current imported-Yul gas-aware top theorem
roots; Solidity frontend and object/Yul-object interfaces remain owned by their
actual modules rather than preserved through audit aliases.

1. [ ] Full Yul accepted language, not a fragment
   - [x] Add a non-rejecting full-Yul safety surface
     `Reference.Safe.Full.*` so code-image, object/data, and external
     call/create primitives are no longer conflated with the narrower
     already-proved local bridge predicate.
   - [x] Add `Reference.FullAccepted` and the checked compatibility theorem
     from old `Reference.Accepted` to the new full acceptedness surface.
   - [x] Split the old safe-fragment meaning into
     `Reference.BridgeCoveredAccepted = FullAccepted + FeatureCoverage`, with
     a checked equivalence to old `Reference.Accepted`. This makes the
     remaining fragment boundary a named semantic-coverage obligation rather
     than part of source acceptedness.
   - [x] Thread the same split into the recursive bridge boundary with
     `RecursiveBridgeFullSourceAccepted`, `RecursiveBridgeFeatureCoverage`,
     and checked conversions to/from old `RecursiveBridgeSourceAccepted`.
     - [x] Audit `RecursiveBridgeFeatureCoverage`: it cannot be constructed
       from `RecursiveBridgeFullSourceAccepted`, because full source validity
       deliberately accepts all primitives and user calls. Successful checked
      compilation constructs only the object-builtin user-call coverage. Local
      code-image coverage is now discharged through the code-image bridge;
      external account-code inspection, create, and external-call coverage
      remain semantic bridge boundaries until their explicit contracts are
      proved.
     - [x] Shrink `RecursiveBridgeCompileResources`: lower-object source
       acceptedness is constructed from `RecursiveBridgeSourceAccepted`, so the
       resource package was reduced to the generated function program's
       source/direct frame bound; the preferred public theorem now constructs
       that bound with `RecursiveBridgeCompileResources.checked?` through
       `compileCheckedAssemblyTargetBytecodeResources?` instead of taking it as
       a separate premise.
    - [x] Add `Reference.Safe.FeatureCoverage.checked?` and the combined
      `compileCheckedAssemblyTargetBytecodeResourcesFeatures?` boundary, so
      the preferred public theorem checks the remaining source feature-family
      exclusions structurally instead of asking callers to prove
      `RecursiveBridgeFeatureCoverage`. Local code-image coverage is now
      discharged by the checked code-image relation; the remaining exclusions
      stay honest unsupported-feature semantic boundaries until their
      source/target contracts are proved.
    - [x] Add checked constructors for the source-static
      `SourceLexical.ProgramScoped`, `ControlFlow.ProgramScoped`, and
      `UserCallArity.ProgramOk` facts, bundle them as
      `RecursiveBridgeSourceStaticFacts`, and route the preferred public
      theorem through
      `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?`.
      This intermediate checkpoint reduced source acceptedness to
      `Reference.FullAccepted`, rather than a caller-provided
      `RecursiveBridgeFullSourceAccepted` package.
    - [x] Extend `RecursiveBridgeSourceStaticFacts` with checked
      `Reference.Safe.NoShadowing.program` construction. This removes the
      caller-supplied `Reference.FullAccepted` premise from the preferred
      gas-aware top theorem: the intermediate public alias now takes
      `Yul.Program.Accepted`, constructs trivial
      `Reference.Safe.Full.program`, and obtains no-shadowing/source-expression
      safety from the checked source-static boundary.
    - [x] Split `Yul.Program.Accepted` at the preferred gas-aware top surface.
      The caller now supplies only `Yul.Program.SourceAccepted`; successful
      checked compilation constructs the lower structured acceptedness needed
      to recover `Yul.Program.Accepted`. This leaves source
      wellformedness/support as the honest source-validity boundary instead of
      asking users for compiler-generated acceptedness evidence.
    - [x] Split `Yul.Program.SourceAccepted` at the preferred gas-aware top
      surface. The caller now supplies `Yul.Program.SourceAcceptedCore`
      (a successful lowering to an `Objects.Program.SourceAccepted`), while
      successful checked compilation constructs `Yul.Program.Supported` via
      `Yul.Program.supported?` as part of the source-static check. Yul `WF`
      is reconstructed from the lowered object's source acceptedness.
    - [x] Remove `Yul.Program.SourceAcceptedCore` from the preferred gas-aware
      top surface. Added computable lower `Functions.Program.SourceAccepted`
      and `Objects.Program.SourceAccepted` checkers with soundness theorems;
      `Yul.Program.sourceAcceptedCore?` now lowers deterministically and checks
      the generated object, so
      `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?`
      constructs the full `Yul.Program.SourceAccepted` boundary.
    - [x] Add preferred gas-aware top wrappers that take full source
      acceptedness plus explicit feature coverage instead of the old bundled
      source-fragment acceptedness predicate.
   - [x] Export checked full-source-surface facts showing code-image and
     external call/create primitives are accepted by `Reference.Safe.Full`,
     while keeping the old rejection facts named as bridge-coverage facts.
   - [x] Refine `Reference.Safe.primitive` so accepted Yul no longer rejects
     local code-image primitives (`CODESIZE`/`CODECOPY`) solely because their
     bridge was previously missing.
   - [x] Add explicit imported-Yul semantics and proof-facing compiler bridge
     facts for local `CODESIZE`/`CODECOPY`: source Yul now reads
     `ExecutionEnv.codeBytes`, object/data `datacopy` lowers to concrete
     `CODECOPY`, and the bridge has reusable wrappers under the explicit
     agreement `source.executionEnv.codeBytes = target.executionEnv.code`.
   - [ ] Add checked semantics and compiler bridge support for
     `EXTCODESIZE`/`EXTCODECOPY`/`EXTCODEHASH`, or state and prove the exact
     external-account/code oracle relation that makes them full semantics
     rather than a fragment exclusion.
   - [x] Add computed solc-Yul object/data image support for `datasize`,
     `dataoffset`, `datacopy`, `loadimmutable`, `setimmutable`, and
     `linkersymbol` in the Solidity frontend path, including nested object/data
     paths, `.metadata` payload ordering, object/data name disambiguation, and
     lowering `datacopy` to concrete `CODECOPY`.
   - [x] Gate checked Solidity-front-end object lowering through
     `Yul.SolcValidation.ProgramOk?` after computed object/data builtin
     resolution and before compiler lowering, and expose that gate as the
     generated backend-check `solc_validation` stage.
   - [x] Add proof-facing checked object-image entrypoints for the computed
     object/data path.  These noncomputable witnesses compile object code only
     after solc-style validation and checked function compilation; executable
     backend-check runners still report the computable `object_image` stage
     plus `solc_validation`.
   - [x] Lift the computed object/data image path through the public checked
     Yul/object theorem by threading code-byte agreement into the public
     initial relation. `RecursiveBridgeInitialCodeImageRel` records that the
     source `ExecutionEnv.codeBytes` image is the assembled target bytecode,
     `LayerAudit` now points at the code-image top theorem, and the structural
     feature checker re-admits local `CODESIZE`/`CODECOPY`.
   - [ ] Add checked semantics and compiler bridge support for
     `CALL`/`CALLCODE`/`DELEGATECALL`/`STATICCALL` and `CREATE`/`CREATE2`, or
     state and prove an explicit external-interaction oracle relation that is
     part of the full source/target semantics rather than a safety rejection.
     - [x] Retire the concrete child/world route with the deleted `World`
       module and the removed closed precompile/child-dispatch support branch.
       The replacement route is the open CALL-family request/response boundary
       in `EvmCompiler.Yul.OpenExternal`, with source/compiler/EVM call-site
       extraction from existing state relations.
     - [x] Add CALL-admitting feature coverage for the next recursive bridge
       surface: `Reference.Safe.FeatureCoverage.externalBoundaryExceptCALL*`
       and `Program.RecursiveBridgeCALLFeatureCoverage` admit ordinary `CALL`
       while still checking out `CALLCODE`, `DELEGATECALL`, `STATICCALL`,
       external account-code inspection, and `CREATE`/`CREATE2`.
     - [ ] Finish the open argument semantics so nested CALL-family expression
       evaluation suspends at the same request/response boundary instead of
       using closed `evalArgs`/`primCall` branches. The open
       `YulOpenResultStateStoreDomainExact` and
       `YulOpenEvalArgsReverseStateDomainExactContract` layer now proves the
       local-domain invariant through nested suspended Yul calls; remaining
       work is to build expression-level constructors for that contract and
       replace the old closed `EvalArgsReverseOkDomainExactContract`
       consumers.
   - [ ] Update the public acceptedness theorem so these operations are either
     supported directly or covered by the explicit full-semantics oracle
     contract.

2. [ ] Internally derive semantic bridge contracts
   - [x] Split primitive assumptions into lower-tower primitive preservation
     (`PrimitiveSound`) and imported-Yul primitive stack agreement
     (`RecursiveBridgePrimitiveStackContracts`) so the remaining bridge
     assumption is visible.
   - [x] Define and export the canonical source-tower primitive semantics
     `Locals.Source.PrimitiveSemantics.structured`, which projects the shared
     EVM primitive/terminal behavior into the stack-free locals source
     interpreter.
   - [x] Provide a canonical `PrimitiveSound` theorem for the concrete
     compiler primitive semantics used by the source tower, specifically
     `Locals.Source.PrimitiveSemantics.structured`.
     - [x] Refine the canonical source primitive evaluator to use a
       source-facing `sourceContinuingStep?`, so backend-only stack shuffles
       (`DUP`/`SWAP`) and still-unmodeled interaction/control primitives are
       rejected explicitly instead of being hidden inside the source boundary.
     - [x] Add reusable checked stack-pop suffix lemmas for arities 1 through
       6; these are the local proof infrastructure needed for the continuing
       primitive preservation fields without unfolding whole EVM traces.
     - [x] Prove safe suffix preservation for every `Assembly.PrimStep`
       admitted by `sourceContinuingStep?`, excluding only backend stack
       shuffles by construction.
     - [x] Prove the canonical continuing-primitive `eval_step` field.
     - [x] Prove the canonical continuing-primitive `eval_step_exists` field.
     - [x] Prove the continuing-primitive output-length field, after making
       canonical source primitive evaluation exact-arity and factoring the
       proof through checked `Assembly.PrimStep` input/output arity lemmas.
   - [ ] Provide a canonical `RecursiveBridgePrimitiveStackContracts`
     constructor for all accepted primitives.
     - [x] Add the reusable binary-one-result bridge shape connecting
       imported Yul source-order arguments to structured source primitive
       stack-order evaluation.
     - [x] Instantiate that bridge for `ADD` under the canonical structured
       primitive semantics.
     - [x] Generalize the Yul side of the binary-one-result bridge through
       `execBinOp`, and instantiate the same canonical bridge for `MUL` and
       `SUB`.
     - [x] Generalize the structured source side for arbitrary `.bin`
       primitives using the checked source-step arity theorem, and instantiate
       the same bridge for `DIV` and `MOD`.
     - [x] Extend the same canonical pure binary bridge to the remaining
       one-result arithmetic/comparison/bitwise primitives:
       `SDIV`/`SMOD`/`EXP`/`SIGNEXTEND` and
       `LT`/`GT`/`SLT`/`SGT`/`EQ`/`AND`/`OR`/`XOR`/`BYTE`/`SHL`/`SHR`/`SAR`.
     - [x] Add the reusable unary-one-result bridge shape and instantiate it
       for the pure comparison/bitwise primitives `ISZERO` and `NOT`.
     - [x] Add the reusable ternary-one-result bridge shape and instantiate it
       for the pure arithmetic primitives `ADDMOD` and `MULMOD`.
     - [x] Add canonical local memory write stack-agreement facts for
       `MSTORE` and `MSTORE8`, using a reusable binary machine-state source
       bridge.
     - [x] Add canonical local memory copy stack-agreement for `MCOPY`, using
       a reusable ternary machine-state source bridge.
     - [x] Add canonical calldata-to-memory stack-agreement for
       `CALLDATACOPY`, using a reusable ternary shared-copy source bridge.
     - [x] Add canonical return-data-to-memory stack-agreement for
       `RETURNDATACOPY`, including its special imported dispatcher equation.
     - [x] Add canonical memory read stack-agreement for `MLOAD`, using a
       reusable unary shared-state-dependent result bridge.
     - [x] Add arity-correct canonical nullary machine-read stack-agreement
       for `RETURNDATASIZE`, `MSIZE`, and `GAS`; this records the imported
       Yul dispatcher's permissive raw nullary behavior explicitly, and `GAS`
       uses the declared `gasValueRel` oracle.
     - [x] Add reusable arity-correct nullary bridge constructors for
       imported `primCall ... []` facts and canonical source
       `executionEnv`/`state` reads, preparing the environment/block read
       families without unfolding the dispatcher per opcode.
     - [x] Instantiate the arity-correct nullary environment-read bridge for
       `ADDRESS`, `ORIGIN`, `CALLER`, `CALLVALUE`, `CALLDATASIZE`, and
       `GASPRICE`.
     - [x] Instantiate the arity-correct nullary block/state read bridge for
       `PREVRANDAO`, `BASEFEE`, `BLOBBASEFEE`, `COINBASE`, `TIMESTAMP`,
       `NUMBER`, `GASLIMIT`, `CHAINID`, and `SELFBALANCE`.
     - [x] Prove imported `evalArgs` length preservation for successful
       argument evaluation, giving the recursive bridge the source-side arity
       evidence needed by arity-aware primitive-stack contracts.
     - [x] Introduce an arity-aware recursive primitive-stack contract package
       and a checked lift from the old strict package, so permissive imported
       nullaries and strict dispatcher primitives can coexist during migration.
     - [x] Add an arity-aware hidden-context primitive-expression bridge that
       derives runtime primitive-call arity from successful imported
       `evalArgs` and checked lowering arity.
     - [x] Add an arity-aware checked `Expr.lower1?` primitive-expression
       wrapper that derives source argument arity from successful
       `lowerBound1?` and `toStackSeq?` evidence.
     - [x] Add arity-aware one-result primitive expression-evaluation
       wrappers, keeping the old strict wrappers as compatibility shims.
     - [x] Add arity-aware primitive and semantic contract packages, with
       checked strict-to-arity compatibility constructors, so the public
       boundary can migrate away from raw-`primCall` strictness.
     - [x] Migrate the recursive one-result expression dispatcher to an
       arity-aware primitive stack premise, with the old dispatcher retained
       as a checked strict-compatibility wrapper.
   - [x] Provide canonical terminal/revert contracts for
     `STOP`/`RETURN`/`REVERT`/`SELFDESTRUCT`.
     - [x] Prove the canonical `STOP` terminal step/existence lemmas for
       `Locals.Source.PrimitiveSemantics.structured`.
     - [x] Prove the canonical `RETURN` terminal step/existence lemmas.
     - [x] Prove the canonical `REVERT` terminal step/existence lemmas.
     - [x] Prove the canonical `SELFDESTRUCT` terminal step/existence lemmas.
     - [x] Bundle the four per-kind lemmas into the canonical
       `PrimitiveSound` terminal-step fields for
       `Locals.Source.PrimitiveSemantics.structured`.
   - [x] Split the expression result-shape premise into constructible
     checkpoint preservation plus the remaining source-fuel boundary.
     - [x] Prove the old `RecursiveBridgeExprResultContracts` package from the
       imported safe-expression checkpoint theorem plus a smaller
       `RecursiveBridgeExprNoOutOfFuelContracts` premise.
     - [x] Audit the remaining premise against the imported evaluator. It is
       not constructible from source acceptedness alone: safe user-function
       expression calls can still expose the imported interpreter's
       success-valued `.OutOfFuel` marker at insufficient source fuel. The
       honest removal path is a sufficient-source-fuel theorem, or a smaller
       actual-run-scoped premise threaded through the recursive expression
       dispatcher.
   - [ ] Route the preferred top theorem through the canonical semantic
     constructors so users do not pass arbitrary semantic-contract packages.
     - [x] Add preferred gas-aware top wrappers specialized to the canonical
       structured primitive semantics, discharging the lower-tower
       `PrimitiveSound` field internally.

3. [ ] Derive gas-aware `EVM.X` sufficient-gas evidence
   - [x] Audit `Assembly.GasAware.XResultPreconditionAssumptions` and split
     fundamental resource assumptions from compiler-derived execution
     evidence. The compiler theorem still derives the concrete
     `BlockTraceResult` internally.
   - [x] Prove the decoded-bytecode path and explicit concrete-gas bridge for
     the no-CALL/no-CREATE fragment from `EncodingCorrect`, `DecodeSafety`,
     code-image preservation, and the finite `XBlockTraceGasBudget`.
   - [x] Strengthen the preferred gas-aware top theorem so it no longer takes
     an external `hTargetGasForX`/`XResultPreconditionAssumptions` certificate:
     the public boundary is now split into gas-budget fit, path-local non-gas
     `EVM.X` checks, and clean fallthrough finalization for running target
     traces.
   - [x] Expose the concrete gas witness in the budgeted public theorem as
     exactly `XBlockTraceGasBudget asm targetFuel initial targetOutcome`
     (specialized to `canonicalEntryState initial` in the preferred wrapper),
     rather than merely existentially producing some gas value.
   - [x] Prove the sufficient-gas strengthening at the assembly bridge:
     `blockTraceResult_runs_at_or_above_computed_gas_of_path_checks_no_call_create_and_budget`
     shows that any UInt256 gas value at least the computed
     `XBlockTraceGasBudget` follows the same checked `EVM.X` path and returns
     an agreeing result.
   - [x] Expose the decoded-path witness directly:
     `blockTraceResult_stepTrace_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget`
     returns an `XStepTrace` for the installed sufficiently-large gas value,
     so the path proof is not merely implicit in the final `EVM.X = .ok`
     equation. The corresponding run theorem now projects through this trace
     witness.
   - [x] Add the non-gas replay adapter:
     `XBlockTraceChecksReadyFor.of_block_replay_nonGas` constructs trace-local
     checks from the older `XBlockReplayNonGasReady` package, and
     `blockTraceResult_runs_at_or_above_computed_gas_of_nonGas_no_call_create_and_budget`
     gives the same sufficient-gas result directly from non-gas replay,
     no-CALL/no-CREATE, and the explicit budget lower bound.
  - [x] Thread the sufficient-gas bridge through the no-CALL public theorem
     spine. `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM`
     now points to the `existsSourceFuel_sufficientGas_stepTrace_..._X`
     theorem, whose conclusion quantifies over every installed UInt256 gas
     value above the computed `XBlockTraceGasBudget` and produces both the
     `XStepTrace` path witness and an agreeing `EVM.X` run.
   - [x] Route the audit-facing no-out-of-gas companion through the same
     trace-local sufficient-gas theorem, so the preferred public no-out root no
     longer points at the older `XResultPreconditionAssumptions` route.
   - [x] Strengthen the preferred no-CALL gas-aware public roots with a checked
     no-`RETURNDATACOPY` wrapper:
     `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticNoReturnDataCopy?`.
     This keeps the public fragment honest while the source/gasless target
     semantics do not yet model the return-data bounds enforced by `EVM.X`.
     The assembly bridge now also has compositional
     `XNonGasChecksPass.intro'` and
     `XNonGasChecksPass.of_no_returnDataCopy_no_create` helpers for the next
     trace-check discharge step.
   - [x] Make that no-`RETURNDATACOPY` wrapper check the emitted target program
     too, not just the source tree. The checked compile theorem now derives
     `targetProgramNoReturnDataCopy target` and
     `XBlockReplayNoReturnDataCopy asm target`, with a suffix-local helper
     producing the exact `instr.op ≠ RETURNDATACOPY` fact needed by the
     gas-aware non-gas checks. `XNonGasChecksPass` also has a writable-state
     constructor for the static-mode subcheck.
   - [x] Split the remaining assembly-level non-gas obligation into a checked
     core predicate plus compiler-derived side conditions:
     `XBlockReplayCoreNonGasReady` combines with
     `XBlockReplayNoReturnDataCopy` and `XBlockReplayNoCallCreate` to build
     `XBlockPathChecksReady`, and the sufficient-gas bridge has a corresponding
     core-based wrapper. The core predicate deliberately does not include
     decoded-bytecode agreement; decode remains proved from
     `EncodingCorrect`/`DecodeSafety` inside
     `XRunListPathReady.of_emitInstr_checks_and_budget`.
   - [x] Hide the remaining source-run stack-headroom premise behind checked
     compiler acceptance.  The old proof-carrying
     `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticStackSafeNoReturnDataCopy?`
     route has been removed from `NoCallRuntime`; the preferred public theorem
     now uses
     `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`,
     which combines the executable source recurrence checker with the inferred
     assembly stack-bound checker.
   - [x] Wire the core predicate through the preferred public no-CALL roots.
     `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM` and its
     no-out companion now point at the strict no-`RETURNDATACOPY` core theorem,
     so checked compiler facts discharge no-CALL/CREATE and no-RDC internally.
   - [x] Make running-target fallthrough finalization concrete and satisfiable.
     `XTraceDoneContinuation.running_of_fallthrough_stop` now uses the one
     fuel step required by `EVM.step`, and the preferred public roots take
     `XFallthroughStopCleanReady` rather than an opaque continuation package.
  - [x] Internalize the remaining path-local non-gas `EVM.X` checks behind a
    checked intermediate target-trace layer. `CoreRunListResult` and
    `CoreBlockTraceResultFor` mirror the gasless target trace while recording
    the core `EVM.X` pre-step checks at each instruction, and the preferred
    public roots now consume that layer rather than exposing raw
    `XBlockTraceCoreChecksReadyFor`.
  - [ ] Derive `CoreBlockTraceResultFor` for compiled no-CALL/no-GAS target
    traces from compiler/source safety facts. These are no longer
    decoded-bytecode, gas-oracle, no-CALL/CREATE, or no-`RETURNDATACOPY` facts:
    they are the real non-gas exceptional checks performed by `EVM.X` before
    `step`, such as jumpdest validity, stack underflow/overflow checks,
    static-mode writes, and create-size limits.
    - [x] Prove the assembler/bytecode side of generated jump safety:
      `labelPc` labels emit concrete `JUMPDEST`s in target code, and
      `Bytecode.JumpdestCorrect` turns those emitted labels into
      `validJumps` membership. The core layer now has checked constructors for
      emitted label/push blocks and generated `push32 label; jump`/`jumpi`
      blocks, with exact stack-overflow premises instead of the too-strong
      "stack <= 16 at every internal instruction" shape.
    - [x] Add the trace builder around the new local shape:
      `InstrCoreBlockReady` discharges non-primitive instructions from control
      stack facts and leaves primitive instructions as explicit
      `XNonGasCoreChecksPass` obligations, while
      `CoreBlockTraceResultFor.of_instr_core_ready` lifts those per-block facts
      over a concrete `BlockTraceResult`.
    - [x] Add the trace-local input wrapper:
      `InstrCoreBlockTraceInputsReadyFor` records exact
      `InstrCoreBlockInputsReady` evidence on the same `BlockTraceResult`
      constructor. For primitives this is the actual `EVM.X` non-gas core
      input package: delta/stack/jump inputs, the precise stack-overflow
      inequality, and static-write exclusion. For control instructions it is
      the control-specific stack precondition. The older `stack <= 16` helper
      is only a sufficient compatibility lemma, not the preferred theorem
      boundary. Keeping this evidence trace-local deliberately avoids
      independent per-trace `Prop` annotations: because `BlockTraceResult` is
      proof-valued, separate annotations can lose the connection to the same
      hidden emitted block data under proof irrelevance. The preferred
      `LayerAudit` gas-aware roots now point at the `traceInputsReady` public
      wrappers, not the older direct `traceInstrCoreReady` wrappers.
    - [x] Make the exact-input boundary interconvert cleanly with the older
      core-ready layer. Checked lemmas
      `instrCoreBlockInputsReady_iff_ready` and
      `instrCoreBlockTraceInputsReadyFor_iff_ready` show that the refactor did
      not weaken the existing core-safe trace story; it only exposes the real
      stack/jump/static inputs before packing them into
      `XNonGasCoreChecksPass`. The block-local
      `XBlockInstrCoreInputsReady` predicate and
      `InstrCoreBlockTraceInputsReadyFor.of_block_instr_inputs_ready` now give
      a reusable hook for a future compiler/source invariant without changing
      the preferred public theorem boundary.
    - [ ] Connect source/frame stack bounds and static-mode source facts to
      `InstrCoreBlockTraceInputsReadyFor` for whole traces. This is now the
      remaining derivation boundary for non-gas core checks. The frame/access
      proofs give active-frame reachability, but structured procedure calls
      materialize hidden return frames under the visible frame, so the total
      EVM stack resource fact must be proved as the exact overflow inequality
      (or exposed as an explicit resource premise) rather than as a blanket
      `stack <= 16` claim. Primitive write/static readiness must likewise come
      from the source/run safety facts on the exact trace constructor, then the
      preferred public root can route through
      `InstrCoreBlockTraceReadyFor.of_inputs_ready`.
   - [ ] Derive the `UInt256` gas-budget fit from checked resource bounds for
     the exact-budget/existence theorem where possible, leaving only an
     explicit code-size/resource bound when needed.

## Final Nethermind Yul Bridge Completion Steps

This is the checklist for the final blocker: construct the recursive
Nethermind-Yul-to-source-tower bridge internally, then thread it through the
dispatcher, assembly, bytecode, and gas-aware theorem surfaces. Mark an item
only when the corresponding Lean theorem exists, is exported through the public
bridge surface when relevant, and the current verification command has passed.

Last updated: 2026-05-26 07:32 PDT. Coarse blockers stay unchecked until every
indented subtask below them is checked. The proof route has pivoted slightly
top-down: finish the accepted-program recursive bridge spine first, then plug
the three user-call statement cases and remaining structured-control /
nonrelatable non-call cases into that accepted successor theorem.

Current assumption-cleanup checkpoint:

- [x] Record the current preferred top-boundary assumptions explicitly:
  - Source validity and source-static checks: the preferred surface uses the
    checked compiler/source boundary
    `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStatic?` to
    construct `Yul.Program.SourceAccepted`, feature coverage, lexical scoping,
    control-flow scoping, user-call arity, no-shadowing, and source-expression
    facts. The checker still rejects the four currently-unproved bridge
    families until their semantics are proved.
  - Lower resource validity: the generated lower function program's
    `SourceDirect.FrameBound.Program` is no longer a preferred public premise.
    `Functions.SourceDirect.FrameBound.program?` checks it over the lowered
    object, and `compileCheckedAssemblyTargetBytecodeResources?` bundles that
    proof with checked compile/bytecode evidence.
  - Shared semantic contracts: `RecursiveBridgeSemanticContracts` names the
    primitive/terminal/revert/outcome agreement between the imported Yul model
    and the compiler source tower.
  - Preferred semantic-boundary surface now splits primitive assumptions into
    lower-tower primitive preservation (`PrimitiveSound`) and imported-Yul
    primitive stack agreement (`RecursiveBridgePrimitiveStackContracts`),
    instead of hiding both in one package.
  - Source run: `RecursiveBridgeSourceRun` is the concrete imported Nethermind
    Yul run plus the explicit exclusion of the historical successful
    `.regular .OutOfFuel` marker.
    `RecursiveBridgeSourceRun.toDispatcherBodyNoOutOfFuel` constructs the
    internal dispatcher-body fuel fact used by the old bridge from that public
    source-run boundary.
  - Target entry/runtime: checked compiler success, checked source
    feature-family exclusions, checked lower frame resources, checked bytecode
    bridge facts, initial shared-state relation, canonical entry PC/empty
    stack, and the exact trace-to-`X` gas precondition callback. The marker-only
    gas oracle, out-of-gas policy, and current-contract projection packages are
    constructed internally by trivial checked constructors.
  - Discharged/generated facts at the top boundary: emitted no-call/create is
    proved from accepted source plus checked compilation; `DecodeSafety` is
    proved from checked assembler layout plus `TargetFitsDecodeWindow`; raw
    `RecursiveBridgeTargetRuntime` is no longer the preferred public input.
  - Remaining preferred inputs after the checked source/static, canonical-entry,
    expression-resource, and gas-boundary checkpoints:
    `RecursiveBridgeSourceRun` is the concrete imported source execution;
    `RecursiveBridgeInitialWorldRel` is the source/target environment
    relation; `RecursiveBridgeTerminalObservationContracts` is the terminal
    and revert observation relation without the recursive proof's initial
    relation/checkpoint filter; `RecursiveBridgeExprNoOutOfFuelContracts` is
    the source-facing expression fuel boundary used to construct the old result
    package internally; and the exact trace-to-`X` gas-precondition callback is
    the target runtime/gas bridge theorem still to be proved below the compiler.
- [x] Classify the remaining `Reference.Safe.primitive` exclusions exactly.
  The public feature package now distinguishes local code-image operations
  (`CODESIZE`/`CODECOPY`), external account-code inspection (`EXTCODESIZE` /
  `EXTCODECOPY` / `EXTCODEHASH`), create (`CREATE`/`CREATE2`), and external
  calls (`CALL`/`CALLCODE`/`DELEGATECALL`/`STATICCALL`) as separate semantic
  boundaries. Object-builtin user-call coverage is no longer public evidence:
  it is constructed from successful checked compilation.
- [x] Check the remaining source feature-family exclusions at the preferred
  top boundary. `Reference.Safe.FeatureCoverage.checked?` structurally rejects
  the four unsupported families in the source program, and
  `compileCheckedAssemblyTargetBytecodeResourcesFeatures?` bundles that source
  check with checked compilation, lower frame resources, and bytecode bridge
  checks. This removes caller-supplied `RecursiveBridgeFeatureCoverage` from
  the preferred theorem without pretending the unsupported families are proved.
- [x] Remove the marker-only gas bookkeeping premises from the preferred
  gas-aware top wrappers. `GasOracleAssumption.trivial`,
  `OutOfGasPolicyAssumption.trivial`, and
  `CurrentContractProjectionAssumption.trivial` now populate the old runtime
  package internally; the remaining target-side runtime premise is now the
  exact trace-to-`X` gas precondition callback.
- [x] Re-express the preferred expression result-shape premise as the narrower
  source-fuel resource boundary. The no-call/gas-aware wrapper spine above
  semantic-core construction now takes `RecursiveBridgeExprNoOutOfFuelContracts`
  directly and constructs `RecursiveBridgeExprResultContracts` internally from
  checked safe-expression checkpoint preservation.
- [x] Construct canonical target entry state in the preferred gas-aware wrapper.
  The default audit alias now takes an initial shared-state relation against an
  arbitrary EVM state and runs the target from `canonicalEntryState initial`,
  so `pc = pcAfter []` and `stack = []` are compiler-entry construction facts
  rather than public assumptions.
- [x] Re-express the initial Yul/EVM world agreement as the named semantic
  boundary `RecursiveBridgeInitialWorldRel`.
  This is not compiler-constructible for an arbitrary `StateRelConfig`: account
  maps, code images, gas erasure, and total-gas agreement are deliberately
  supplied by the source/target environment relation.
- [x] Split the structured terminal/revert contract into constructed terminal
  primitive execution plus the remaining observation boundary. The preferred
  structured-primitive gas-aware wrappers now take
  `RecursiveBridgeTerminalObservationContracts`; the old
  `RecursiveBridgeTerminalContracts` is constructed internally for structured
  primitives by `RecursiveBridgeTerminalContracts.structured_of_observation`
  using the checked imported-terminal relatability theorem. The terminal and
  revert state relations remain a real semantic boundary, not compiler-created
  evidence.
- [x] Add the target-side no-call/create runtime constructor
  `RecursiveBridgeTargetRuntime.withNoCallCreate`.
- [x] Add the local primitive guardrail
  `Reference.Safe.lowered_basicOp_not_callCreate`: any accepted Yul primitive
  that lowers through `Prim.toBasicOp?` produces a structured/assembly
  primitive whose `isCallCreate` flag is false.
- [x] Add assembly-level compositional lemmas for `Program.usesCallCreate`
  over append, so the emitted-program no-call proof can be built layer by
  layer.
- [x] Add Structured syntax-level `usesCallCreate` predicates and checked
  generated-code no-call lemmas for stack shuffles and switch-test dispatch.
  Focused verification:
  `/tmp/evm_structured_compiler_nocall_generated_only_check2.log`.
- [x] Prove the Structured compiler no-call preservation theorem using a
  structurally recursive proof split over statement lists, case lists, and
  optional defaults. `Structured.CompilerFacts.block_compileFromCtx_noCallCreate`
  and `program_compile_noCallCreate` now cover blocks, statements, switch
  cases/defaults, procedure bodies, generated dispatchers, emitted procedure
  bodies, and whole structured programs. Focused verification:
  `/tmp/evm_layeraudit_nocall_check2.log`.
- [x] Lift the no-call theorem through the Expressions-to-Structured compiler.
  `Expressions.CompilerFacts.Program.compile_noCallCreate` proves that an
  Expressions program whose source syntax contains no call/create primitives
  compiles to assembly with `usesCallCreate = false`, using the Structured
  theorem rather than a target-side assumption. Focused verification:
  `/tmp/evm_expr_nocall_build.log`.
- [x] Lift the no-call theorem through the Locals-to-Expressions compiler.
  - [x] Add Locals `usesCallCreate` predicates plus checked generated-code
    guardrails for DUP/SWAP stack operations, cleanup code, and
    `Expr.compileCode` / `ExprSeq.compileCode`.
  - [x] Add checked no-call helpers for `codeStmt`, `finishTo`,
    `finishToPreserving`, and `finishScoped`, so generated cleanup appended
    around scoped Locals blocks is accounted for compositionally.
  - [x] Prove no-call preservation for `Stmt.compile`, `Block.compileOpen`,
    case/default lowering, procedure lowering, and whole-program
    `toExpressions?`.
- [x] Prove the emitted-program theorem:
  `Reference.Accepted program →
   compileCheckedAssemblyTarget? program = some (asm, target) →
   asm.usesCallCreate = false`, then expose a wrapper that constructs
  `RecursiveBridgeTargetRuntime` from decode/jumpdest/gas/current-contract
  assumptions without a user-supplied external-call agreement.
  - [x] Add checked-compiler no-call boundary theorems through Structured,
    Expressions, and Locals.
  - [x] Add checked-compiler no-call boundary theorems through Functions,
    Objects, and Yul-preservation-with-lowered Functions.
  - [x] Start the Yul accepted-lowering no-call proof in a separate checked
    module: direct expression lowering (`Expr.toLocals?`), expression
    sequences, and stack-order argument sequences now preserve
    `usesCallCreate = false` under `Reference.Safe.expr`.
  - [x] Extend the Yul accepted-lowering no-call proof through generated
    expression preludes (`Expr.lower?`, `lower1?`, `lower0?`, and
    `lowerBound1?`) and statement-level expression calls
    (`ExprStmtCall`, including terminal primitive argument sequences and
    internal user-call argument paths).
  - [x] Prove the Yul lowering fact:
    `Reference.Accepted program → program.toObjects? = some obj →
     obj.toFunctions.usesCallCreate = false`.
    - [x] Lift generated-prelude no-call through statement, block, case,
      function-definition, function-list, and contract lowering.
    - [x] Replace
      `compileChecked?_noCallCreate_of_loweredFunctions` at the public
      theorem boundary with the accepted-program theorem, so no generated
      no-call premise remains.
  - [x] Add the no-call/create target construction that derives
    `asm.usesCallCreate = false` internally from source acceptedness and
    checked compile-target success. The temporary accepted-no-call-create
    public wrapper was later removed once the bundled no-call/create package
    became the spine.
  - [x] Add the bundled public no-call/create top package
    `RecursiveBridgeTopNoCallAssumptions` and theorem
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall`,
    so the preferred exported surface cannot hide a user-supplied arbitrary
    external-call agreement inside `RecursiveBridgeTargetRuntime`.
  - [x] Temporarily export audit projections for the preferred no-call/create
    top package while auditing which facts were source validity, explicit lower
    resource bounds, and checked compiler-derived facts. These projection
    helpers were later removed once the checked bundle became the live public
    spine.
  - [x] Temporarily export audit projections for the then-remaining bytecode
    target boundary while separating the explicit resource/code-size bound from
    the imported jumpdest-scanner boundary. These projection helpers were later
    removed once the bytecode checks moved into the checked compiler package.
  - [x] Replace the public `DecodeSafety` premise with the resource bound
    `Assembly.Bytecode.TargetFitsDecodeWindow`. The actual `DecodeSafety`
    facts are now proved from checked assembler layout plus that byte-length
    bound by `Assembly.Bytecode.compile_decodeSafety`; `JumpdestCorrect`
    remained explicit at that checkpoint because the imported EVMYulLean
    jumpdest scanner is opaque.
  - [x] Add `Assembly.Bytecode.bytecodeBridgeChecked?` and
    `Yul.Program.compileCheckedAssemblyTargetBytecode?`, so the preferred top
    theorem constructs `TargetFitsDecodeWindow` and `JumpdestCorrect` from a
    concrete bytecode check instead of taking them as standalone assumptions.
    The jumpdest fact is checked against the imported scanner output for the
    encoded target bytecode; it is intentionally not hidden in acceptedness or
    claimed as a scanner-internal proof.
  - [x] Add `Functions.SourceDirect.FrameBound.program?`,
    `RecursiveBridgeCompileResources.checked?`, and
    `Yul.Program.compileCheckedAssemblyTargetBytecodeResources?`, so the
    preferred gas-aware top theorem constructs the generated source/direct frame
    bound from the lowered object and a concrete checker rather than exposing
    `RecursiveBridgeCompileResources` as a caller premise.
  - [x] Add `Reference.Safe.FeatureCoverage.checked?`,
    `RecursiveBridgeFeatureCoverage.checked?`, and
    `Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesFeatures?`, so
    the preferred gas-aware top theorem constructs the feature-coverage package
    from a concrete source checker rather than exposing
    `RecursiveBridgeFeatureCoverage` as a caller premise.
- [x] Add the actual result-level gas-aware `EVM.X` top wrapper for the
  preferred no-call/create route.
  - [x] Add `Assembly.GasAware.XResultAgrees` and
    `XResultPreconditionAssumptions`, so halting results are handled without
    narrowing to successful final states. `REVERT` is modeled separately
    because EVMYulLean's revert result carries gas/output but no final state.
  - [x] Add
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_X`,
    which composes the imported-Yul bridge, verified compiler stack, bytecode
    bridge, and explicit result-level sufficient-gas contract into an `EVM.X`
    run theorem.
  - [x] Add the result-level theorem for the no-call/create package. The early
    no-out-of-gas corollary and its `LayerAudit` aliases were later removed
    once the canonical checked no-out route became the preferred public spine.
- [x] Expose the lower compiler-resource boundary through the standard
  source-facing package instead of only through a bespoke recursive-bridge
  resource record.
  - [x] Add `RecursiveBridgeCompileResources.of_sourceCompileAccepted`.
  - [x] Add the temporary projection
    `RecursiveBridgeTopNoCallAssumptions.sourceCompileAccepted`; it was later
    removed with the rest of the non-spine audit projection helpers.
  - [x] Add `RecursiveBridgeTopNoCallSourceCompileAssumptions`, whose public
    resource field is `Yul.Program.SourceCompileAccepted program`, and the
    checked wrapper to the result-level `EVM.X` theorem. The intermediate
    gasless/source-compile public wrapper and aliases were later removed when
    they stopped being part of the preferred surface.
  - [x] Temporarily export source-compile package audit projections for source
    acceptedness, source compile acceptedness, emitted no-call/create, target
    decode-window bound, and target jumpdest correctness. These were audit aids
    for the no-hidden-evidence pass and were later removed after the checked
    package became the public theorem spine.
  - [x] Add a canonical top-level observation relation for the imported
    dispatcher bridge and a checked constructor from
    `RecursiveBridgeSemanticCoreContracts` to
    `RecursiveBridgeSemanticContracts`, so callers of the preferred
    source-compile package no longer need to provide the observation field as
    arbitrary semantic evidence when using the canonical outcome relation.
  - [x] Add the reverse projection
    `RecursiveBridgeSemanticCoreContracts.ofSemanticContracts`, making the
    semantic core/redundant-observation split explicit in both directions.
  - [x] Split the remaining semantic core into named boundary packages:
    `RecursiveBridgePrimitiveArityContracts`,
    `RecursiveBridgeTerminalContracts`, and
    `RecursiveBridgeExprResultContracts`, with a checked constructor
    `RecursiveBridgeSemanticCoreContracts.ofBoundaries`. This makes clear which
    fields are shared primitive semantics, terminal/revert semantics, and
    imported-Yul expression result-shape/resource behavior.
  - [x] Add preferred gas-aware wrappers that take those three boundary
    packages directly:
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalBoundaries_X`
    and the matching no-out-of-gas corollary. `LayerAudit`'s preferred
    gas-aware aliases now route through this split-boundary surface rather than
    through the opaque semantic-core bundle.
  - [x] Shrink the expression result-shape package to the actual remaining
    resource premise. The no-call/gas-aware wrapper spine above semantic-core
    construction now takes `RecursiveBridgeExprNoOutOfFuelContracts` directly;
    checkpoint preservation for safe expressions constructs
    `RecursiveBridgeExprResultContracts` internally, leaving only the
    successful `.OutOfFuel` source-fuel boundary.
  - [x] Add the result-level canonical `EVM.X` wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X`,
    and route the preferred `LayerAudit` gas-aware aliases through it. The
    public spine now constructs the canonical dispatcher outcome relation from
    the semantic core instead of accepting an arbitrary `outcomeRel`/observation
    pair at the preferred top boundary.
  - [x] Add the matching canonical no-out-of-gas corollary
    `compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_X`,
    so both public gas-aware result theorems have a canonical-observation
    surface.
- [x] Promote the actual result-level `EVM.X` theorem as the preferred public
  gas-aware alias.
  - [x] `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM` and
    `recursiveBridgeTopNoCallToGasAwareEVM` now point at the source-compile
    no-call/create canonical-observation result-level `EVM.X` theorem. This
    has since been strengthened to expose the sufficient-gas `XStepTrace`
    witness at the preferred public alias.
  - [x] The older gasless result bridge remains as an internal spine theorem,
    but is no longer exported as an alternate `LayerAudit` route.
- [x] Run final proof-hygiene audit for the current public theorem surface.
  - [x] No declaration-level `axiom`, `admit`, `sorry`, `sorryAx`, `unsafe`,
    or `partial` was found in `EvmCompiler` Lean modules.
  - [x] Preferred public theorem axiom audit reports no `sorryAx`, only
    standard Lean axioms.
  - [x] Full `lake build EvmCompiler` passes after the latest boundary checks.

Immediate recursive-bridge execution checklist:

Successor theorem readiness gate:

- [x] Preserve the patched `evmyul` loop post-success semantics in a proper
  dependency branch/revision and update the manifest so the final theorem is
  reproducible from a clean checkout. The local package currently carries the
  semantics fix needed for Solidity-compatible post `leave` behavior. The
  exact build-checked patch is preserved locally as `evmyul` commit `5d7511d`
  on branch `codex/solidity-loop-post-success-defeq`, and the root
  `lakefile.lean`/`lake-manifest.json` now point at that revision. Verified the
  branch is fetchable from `https://github.com/danrobinson/EVMYulLean.git`:
  `git ls-remote` reports
  `5d7511d768bd35622a9f151324650f57707684f2`.
- [x] Add/export/audit the accepted-program recursive bridge boundary
  `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames`, with zero
  and monotonicity lemmas, bundling program-level `toObjects?`, safety,
  control-flow scoping, no-shadowing, user-call arity, and checkpoint contracts.
- [x] Thread the accepted-program recursive bridge boundary through the
  dispatcher and whole-program bytecode/gas-aware theorem route, so the final
  all-bounds recursive proof can feed the public theorem without exposing the
  older unrestricted program-recursive premise.
- [x] Add/export/audit accepted-context projection helpers for dispatcher facts
  and selected callee bodies, including
  `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.block_of_function_lookup`,
  so recursive user-call cases can re-enter the bridge at callee bodies through
  one compositional theorem.
- [x] Add/export/audit accepted-program callee-body soundness and function-body
  reconstruction adapters for successful returns and terminal errors, so
  user-call reconstruction can consume the accepted recursive bridge directly.
- [x] Add/export/audit accepted-program terminal user-call reconstruction, so
  callee-error branches no longer depend on the old unrestricted
  program-recursive bridge.
- [x] Add/export/audit accepted-program successful no-target user-call
  reconstruction, deriving the callee-body checkpoint contract from
  `ProgramBridgeContext`.
- [x] Add/export/audit accepted-program successful returned-assignment and
  generated-temporary `let` user-call reconstruction, using the accepted
  recursive bridge for selected callee bodies.
- [x] Discharge the successful callee-body store-presence callback from safe,
  scoped imported body execution.
  - [x] State the helper at the actual entry shape used by `initcall`: the
    callee body starts from an `Ok` state whose varstore contains exactly the
    initialized return and parameter names.
  - [x] Add the source-store lookup bridge needed for the compositional route:
    if the source-side function body result still contains the return names,
    `SourceStateRel` alone recovers the exact Nethermind `lookup!` return list.
  - [x] Add/export the small source variable-presence API
    (`SourceVarsContains`) needed to prove return-name retention in the
    stack-free function-body interpreter before relating it back to imported
    Yul stores.
  - [x] Prove/export that source expression evaluation, expression sequences,
    and function-call argument-list evaluation preserve `SourceVarsContains`.
  - [x] Prove/export that source-side parameter insertion, return
    initialization, and assignment preserve `SourceVarsContains`.
  - [x] Prove/export the source-result variable-presence theorem
    compositionally over the stack-free source `runScoped` interpreter, avoiding
    the too-broad imported `OutOfFuel` block-entry theorem shape.
  - [x] Specialize that theorem to function bodies and expose source-side
    return-name lookup adapters for recursive and program-recursive callee-body
    runs.
  - [x] Replace the remaining `hBodyContains`/successor-boundary
    `hBodyDomain` premises in the scoped successful user-call wrappers with the
    source-side callee-body helper.
- [x] Build combined actual-run wrappers for expression-statement,
  returned-value assignment, and generated-temporary `let` user calls, so each
  wrapper internally dispatches between successful callee return and terminal
  callee halt.
  - [x] Add/export success-side singleton-block decomposition lemmas after
    successful argument evaluation for expression-statement, returned-value
    assignment, and generated-temporary `let` user calls.
  - [x] Add/export the expression-statement actual-run prelude theorem that
    dispatches between successful callee return and terminal callee halt after
    successful argument evaluation.
  - [x] Add/export the checked expression-statement actual-run wrapper on top
    of that prelude theorem.
  - [x] Add/export the returned-value assignment actual-run prelude theorem and
    checked wrapper on top of the assignment singleton-block success/error
    decompositions.
  - [x] Add/export the generated-temporary `let` actual-run prelude theorem and
    checked wrapper, including the hidden `initNames` scope boundary.
  - [x] Remove the bespoke local `.ok Checkpoint` and `.ok OutOfFuel`
    exclusion premises from the actual-run wrapper family: `.ok OutOfFuel` is
    rejected by `SourceResultRelatable`, and singleton user-call checkpoints
    are ruled out by checked execution-shape lemmas after successful argument
    evaluation.
- [x] Prove the three user-call statement cases for
  `recursiveSourceBridgeWhenUpToAt_succ`.
  - [x] Add/export an arity-aware generated-argument terminal interface:
    `sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded_safe_ok_covers_regularAt`
    plus expression-statement, returned-assignment, and generated-temporary
    `let` accepted successor wrappers whose terminal callbacks consume
    `Safe.expr` and `UserCallArity.ExprOk`.
  - [x] Add/export the primitive-expression terminal connector
    `sourceExprPreludeTerminalAt_prim_of_args_terminal`, so generated argument
    recursion can compose argument-terminal evidence without unfolding opcode
    semantics at each expression site.
  - [x] Discharge or bundle the one-result safe/basic primitive-call
    post-argument error nonrelatability fact consumed by the expression
    terminal dispatcher via
    `safeBasicOneOutputPrimCall_error_not_relatable`.
  - [x] Add/export the single-expression terminal dispatcher that handles
    literals/variables, primitive calls, and direct/generated user calls from
    `Safe.expr`, `UserCallArity.ExprOk`, fresh coverage, and `Expr.lower1?`.
    - [x] Add/export the primitive-call branch,
      `sourceExprPreludeTerminalAt_prim_of_lower1?_bounded_safe_ok_covers_regularAt`,
      using generated argument terminal evidence plus
      `safeBasicOneOutputPrimCall_error_not_relatable`.
    - [x] Add/export the recursive fuel-induction wrapper
      `sourceExprPreludeTerminalAt_of_lower1?_program_accepted_recursive`,
      eliminating the nested expression-terminal callback from the dispatcher.
- [x] Assemble the generic sequence/block successor case around those statement
  cases.
  - [x] Add/export the expression-statement user-call adapter
    `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminal`,
    replacing caller-supplied nested expression-terminal evidence with the
    recursive expression dispatcher.
  - [x] Add/export the returned-assignment and generated-`let` user-call
    adapters,
    `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminal`
    and
    `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_succ_of_recursiveExprTerminal`.
  - [x] Bundle/export the source-facing argument-prelude invariant as
    `SourceArgListPreludeRegularAllAt`, plus `argRegularAllAt` wrappers for
    the expression-statement, returned-assignment, generated-`let`, and
    single-expression terminal paths, so successor assembly has one coherent
    argument-boundary premise.
  - [x] Remove the proof-hostile nonempty direct-argument fast path for
    user-call arguments; direct lowering is now empty-only, and all nonempty
    user-call arguments go through the generated `lowerBound1?` prelude.
  - [x] Add/export
    `sourceArgListPreludeRegularAllAt_of_lowerBound1?_exprEvalSound_covers`,
    constructing the argument-prelude invariant without a caller-supplied
    direct-argument regularity oracle.
  - [x] Prove the regular single-expression prelude dispatcher for
    `Expr.lower1?`, so the generated argument-list constructor can be
    instantiated inside the successor theorem rather than supplied as a
    callback.
    - [x] Add/export the source-visible expression scoping facade
      `SourceExprScoped`/`SourceExprsScoped` and direct regular-success
      `ExprEvalPreludeSound` facts for literals and scoped variables.
    - [x] Add/export
      `sourceArgListPreludeRegularAt_of_lowerBound1?_exprEvalSound_scoped_covers`,
      the scoped generated-argument induction theorem that threads lexical
      expression facts through `Expr.List.lowerBound1?`.
    - [x] Decide and implement the regular argument-prelude boundary as
      scoped-expression aware; the old unscoped `SourceStateRel`-only shape is
      too weak for arbitrary variable reads.
      - [x] Add/export `SourceArgListPreludeRegularAllScopedAt` and
        `sourceArgListPreludeRegularAllScopedAt_of_lowerBound1?_exprEvalSound_scoped_covers`,
        so generated argument regularity requires source-visible lexical
        expression scoping rather than pretending `Safe.exprs` is enough.
    - [x] Prove the primitive-call regular expression branch from generated
      argument preludes and `PrimitiveStackSoundAt`.
      - [x] Add/export the source-order-to-stack-order generated-variable
        adapter
        `sourceArgStackPreludeRegular_of_argListRegularAt_varMap_toStackSeq`,
        plus the reusable `ArgList` append/reverse and `toSeq?` replay
        lemmas it depends on.
      - [x] Add/export the success-side primitive singleton-output family
        theorem `safeBasicOneOutputPrimCall_ok_single`, then use it to remove
        the `hPrimSingle` premise from
        `lower1?_prim_exprEvalPreludeSound_of_lowerBound1?_regularAt`.
      - [x] Add/export the hidden-context `At` primitive regular bridge
        (`sourceArgStackPreludeRegularAt_of_argListRegularAt_varMap_toStackSeq`
        and
        `lower1?_prim_exprEvalPreludeSound_of_lowerBound1?_regularAt_noScope`),
        so generated head expressions after tail temporaries no longer require
        the false `ctx.scope = layout` premise.
    - [x] Prove the one-result user-call regular expression branch from the
      accepted recursive callee bridge and generated/direct argument preludes.
      - [x] Add/export the imported success splitter
        `eval_user_call_ok_split`, decomposing `eval` success into argument
        evaluation, user-call execution, and the observed head return value.
      - [x] Add/export `SourceStateRel.of_hidden_multifill`, projecting the
        relation for compiler-only call targets back to the visible source
        layout after `multifill`.
      - [x] Add/export the generated-argument success theorem
        `sourceExprEvalPreludeSound_user_call_generated_ok_of_program_accepted_recursive`
        at the explicit `Ok` imported-state/resource boundary.
      - [x] Add the direct-empty-argument sibling or derive it as the `preArgs = []`
        specialization.
      - [x] Name/export the resource-aware regular expression boundary
        `ExprEvalPreludeSoundOk`.
      - [x] Add/export the dispatcher-shaped user-call theorem
        `lower1?_user_call_exprEvalPreludeSoundOk_of_argRegularAllScopedAt`
        at the explicit `Ok` result boundary.
      - [x] Add/export the named resource/control side condition
        `ExprEvalResultOkAt` and the lift
        `ExprEvalPreludeSoundOk.toSound`.
      - [x] Add/export the regular user-call branch
        `lower1?_user_call_exprEvalPreludeSound_of_argRegularAllScopedAt`,
        with the ordinary-`Ok` result condition explicit.
    - [x] Add/export the full regular expression dispatcher
      `lower1?_exprEvalPreludeSound_of_argRegularAllScopedAt` for literals,
      scoped variables, primitive calls, and user calls.
    - [x] Add/export the checked regular expression dispatcher
      `lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt`, consuming
      `SourceArgListPreludeRegularAllCheckedAt` and working under hidden
      compiler contexts.
    - [x] Derive the bundled regular argument-prelude invariant used by the
      successor theorem from the recursive expression dispatcher and the
      source/resource facts at the actual call site, rather than taking
      `SourceArgListPreludeRegularAllAt` as public evidence.
      - [x] Add/export bounded generated-argument regularity helpers:
        `sourceArgListPreludeRegularAt_cons_of_tail_head_bounded`,
        `sourceArgListPreludeRegularAt_of_lowerBound1?_exprEvalSound_scoped_covers_bounded`,
        and
        `sourceArgListPreludeRegularAllScopedAt_of_lowerBound1?_exprEvalSound_scoped_covers_bounded`.
      - [x] Add/export the checked argument-prelude bundle
        `SourceArgListPreludeRegularAllCheckedAt`, which carries lexical
        scoping plus `UserCallArity.ExprsOk` instead of treating nested
        user-call arity as hidden proof evidence.
      - [x] Add/export the source-visible lexical scoping predicate
        `SourceLexical.*`, attach it to `ProgramBridgeContext`, and expose the
        user-call argument projections needed by the checked wrapper family.
      - [x] Add checked expression-dispatcher/argument-bundle constructors
        that consume `SourceArgListPreludeRegularAllCheckedAt` and discharge
        the bounded expression callback by fuel induction.
      - [x] Reroute the successor-facing user-call wrappers from
        `SourceArgListPreludeRegularAllAt` to the checked bundle, deriving the
        actual call-site facts from `Safe`, `SourceExprScoped`, and
        `UserCallArity`.
        - [x] Export checked terminal-expression theorem surfaces for
          expression-statement, returned-assignment, and generated-temporary
          `let` user-call wrappers.
        - [x] Export checked recursive-expression dispatcher surfaces for all
          three user-call statement shapes.
        - [x] Export checked bundled-argument wrapper surfaces for all three
          user-call statement shapes.
        - [x] Add/export source-lexical wrapper surfaces so each checked
          user-call case derives `SourceExprsScoped` from the source statement
          scoping predicate instead of receiving it manually.
  - [x] Add/export the reserved accepted-head sequence dispatcher
    `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_frontier_of_programAccepted_reserved_supported`,
    covering simple heads, blocks, declarations, user calls, non-terminal
    primitives, `if`, `switch`, `for`, and no-lowering heads through one
    compositional case split.
  - [x] Add/export the list-level reserved sequence frontier
    `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_of_programAccepted_frontier_reserved_supported`
    by combining the accepted-head dispatcher with the fuel/list induction
    spine.
  - [x] Discharge the remaining terminal-primitive sequence-head callback used
    by the reserved sequence dispatcher by reducing it to the same
    source-facing terminal semantic contract already exposed by the statement
    frontier.
  - [x] Add/export the list-level terminal-dispatched reserved sequence
    frontier
    `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_of_programAccepted_frontier_terminal_reserved_supported`.
  - [x] Add/export/audit the singleton-block-to-statement adapter
    `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_singleton_block`,
    so exact statement frontiers can reuse the compositional sequence/block
    frontier.
  - [x] Add/export/audit the reserved successor assembly wrapper
    `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.succ_of_sequence_frontier_terminal_supported`,
    reducing the successor boundary to the hidden-mode-block frontier and the
    generated argument-prelude bundle at `bound.succ`.
  - [x] Add/export/audit the reserved generated-argument successor constructor
    `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.args_succ`,
    so the successor theorem no longer needs an external argument-prelude
    bundle.
  - [x] Add/export/audit the successor wrapper
    `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.succ_of_sequence_frontier_terminal_args_supported`,
    leaving hidden-mode-block soundness as the only remaining successor
    frontier.
- [x] Replace or repair the overgeneral hidden-mode-block frontier.
    `HiddenBlockModeSound.brk`/`.cont` currently ask for target `brk`/`cont`
    behavior under an arbitrary `Functions.Source.Ctx`, but the Functions
    semantics requires installed break/continue cleanup targets. The proof
    should either make the mode contract handler-aware or avoid a public
    arbitrary-block mode field and derive only the generated loop body/post
    mode facts where handlers are known to be installed.
    - [x] Add the corrected handler-aware mode contract or generated-loop-only
      frontier statement.
    - [x] Prove generated loop body mode soundness from the reserved
      hidden-sequence/block frontier under `withLoopControl`.
    - [x] Prove generated loop post mode soundness from the reserved
      hidden-sequence/block frontier under `withoutLoopControl`.
    - [x] Rewire the `for` frontier and recursive successor to use the
      corrected handler-aware mode frontier, so `hiddenModeBlock` is no longer
      an impossible arbitrary-context premise.
    - [x] Discharge the remaining handler-aware `hiddenModeBlock` premise from
      a compositional exact-fuel frontier, or replace it with a narrower
      generated-loop mode theorem if the generic block result theorem is the
      wrong abstraction.
      - [x] Confirm architecture with Aristotle: ordinary hidden block
        soundness cannot imply hidden mode soundness because break/continue
        containment goes in the opposite direction; use a dedicated
        hidden-mode sequence frontier.
      - [x] Add the mode-facing hidden-context `break`/`continue` head lemmas
        where handler scopes may contain the visible layout.
      - [x] Add the named `SourceResultHiddenModeSupported` contract for
        mode-facing sequence/block frontiers.
      - [x] Add helper constructors from handler availability to hidden-mode
        break/continue support.
      - [x] Add transport of hidden-mode support across handler-preserving
        regular generated preludes.
      - [x] Generalize the hidden-mode sequence frontier to carry explicit
        mode continuation layouts: regular/current, break, continue, and
        leave. This is needed because declaration heads can extend the regular
        layout while break/continue still target the enclosing loop layout.
        - [x] Add the `SourceModeKontLayouts` /
          `SourceResultModeKontSupported` facade.
        - [x] Add handler-preserving transport for
          `SourceResultModeKontSupported`.
        - [x] Add `SourceModeKontLayouts.block` and correct regular hidden-mode
          support to be independent of final `outcomeLayout`.
        - [x] Add regular/break/continue/leave constructors for
          `SourceResultModeKontSupported`.
        - [x] Add adapters between block-shaped hidden-mode support and the
          four-continuation facade.
        - [x] Add typed-continuation outcome relations
          `SourceOkKontOutcomeRel` and `SourceResultKontOutcomeRel`.
        - [x] Add the typed-continuation open-sequence soundness target
          `SourceResultSeqKontSoundWhenAtExactHiddenCtx`.
        - [x] Add the checked lowering facade
          `CheckedSeqKontSoundWhenFreshNamesAtCompileFuelHiddenCtx`.
        - [x] Add the uniform-layout adapter from existing
          `SourceResultOutcomeRel` proofs into the typed-continuation relation.
        - [x] Add the scoped-block bridge from the typed-continuation open
          sequence relation to block-shaped continuation outcomes.
        - [x] Add the checked adapter from block-shaped continuation outcomes
          to the existing handler-aware `HiddenBlockModeSound` interface.
        - [x] Add the typed-continuation nil/open-sequence base case and
          checked lowering wrapper.
        - [x] Add the typed-continuation cons/open-sequence composition
          theorem for regular and nonregular heads.
        - [x] Add direct typed-continuation nonregular head bridges for
          `break`, `continue`, and `leave`.
        - [x] Add the checked lowering wrapper for the typed-continuation cons
          theorem.
        - [x] Add the typed-continuation checked `break :: rest` constructor.
        - [x] Add the typed-continuation checked `continue :: rest`
          constructor.
        - [x] Add the typed-continuation checked `leave :: rest` constructor.
        - [x] Add typed-continuation low-fuel/out-of-fuel checked sequence
          helpers.
        - [x] Add fuel-dispatched typed-continuation checked constructors for
          `break`, `continue`, and `leave`.
        - [x] Add the successor wrapper whose public premise is the
          typed-continuation sequence frontier, internally deriving the
          handler-aware `hiddenModeBlock` field through the block-shaped
          continuation adapter.
        - [x] Generalize the typed `break`/`continue`/`leave` head bridges to
          arbitrary declared continuation layouts, separating handler
          availability from the static proof that the continuation layout is
          still present in the current source layout.
        - [x] Add checked typed-continuation constructors for generic
          `break :: rest`, `continue :: rest`, and `leave :: rest`, so abrupt
          heads can be used after declaration heads have extended the current
          layout.
        - [x] Add fuel-dispatched generic typed-continuation constructors for
          those abrupt heads for use in the sequence-fuel induction.
        - [x] Add the `SourceModeKontLayouts.ControlWithin` invariant, naming
          the static fact that declared break/continue continuation layouts
          remain present as the current layout grows.
        - [x] Add the generic typed-continuation hidden-sequence fuel induction
          from a one-head frontier, carrying both dynamic mode support and the
          static control-continuation shape invariant.
        - [x] Add typed-continuation one-head frontiers for `break`,
          `continue`, and `leave`.
        - [x] Add typed-continuation one-head frontiers for regular assignment
          heads `x := literal` and `x := y`.
        - [x] Add the typed-continuation one-head frontier for declaration
          head `let x`, including current-layout growth and monotone
          `ControlWithin` transport.
        - [x] Add typed-continuation one-head frontiers for initialized
          declaration heads `let x := literal` and `let x := y`, including
          current-layout growth and preservation of enclosing break/continue
          continuation shapes.
        - [x] Add the typed-continuation dispatcher for the accepted simple
          source-visible head slice: `break`, `continue`, `leave`,
          one-target literal/variable assignment, and one-name literal/variable
          declarations.
        - [x] Add the typed-continuation no-lowering contradiction helper for
          accepted dispatcher branches that are intentionally rejected by the
          backend lowerer.
        - [x] Add a non-checkpoint projection from old single-layout outcome
          proofs to arbitrary typed-continuation outcomes, so regular/terminal
          head frontiers can stay continuation-polymorphic.
        - [x] Add sequence-level checked adapters from old same-layout
          hidden-context sequence proofs to typed-continuation sequence proofs
          when the admitted source run cannot produce checkpoints.
        - [x] Add the typed-continuation terminal primitive head frontier,
          reducing terminal heads to the same-layout terminal proof plus a
          no-checkpoint source-run fact.
        - [x] Add a typed-continuation scoped-block nonregular-head adapter,
          so block exits can reuse one continuation-polymorphic proof path.
        - [x] Add a successor handoff wrapper that accepts the induction-shaped
          typed sequence theorem with `ControlWithin`, instantiating the
          invariant internally for block-shaped continuations.
        - [x] Prove the continuation-layout sequence frontier constructors
          and use them to discharge handler-aware `hiddenModeBlock`.
          - [x] Add the arbitrary-continuation block head frontier, using the
            typed scoped-block/nonregular adapter and same-layout regular block
            path.
            - [x] Add the generic scoped-block bridge from hidden open
              sequences to arbitrary declared continuation layouts, with
              `ControlWithin` handling break/continue cleanup.
            - [x] Add the regular block-head adapter from block-shaped typed
              scoped-block soundness to ordinary regular hidden statement
              soundness.
            - [x] Add the checked block-head frontier with a fuel-parametric
              recursive body callback. Check:
              `/tmp/evm_kont_block_frontier_check3.log`.
            - [x] Tighten the block-head frontier so the body callback is
              explicitly smaller-fuel (`sourceFuelBody ≤ tailFuel`), making it
              dischargeable from the strong recursive sequence induction.
              Check: `/tmp/evm_kont_block_frontier_bounded_body_check1.log`.
            - [x] Add the dispatcher-ready accepted block wrapper that derives
              body/tail facts from the source head and feeds both through the
              strong recursive sequence callback. Check:
              `/tmp/evm_kont_block_recursive_wrapper_check2.log`.
            - [x] Add the accepted simple-or-block typed dispatcher slice,
              reusing the simple-head dispatcher and the strong-recursive block
              wrapper. Check: `/tmp/evm_kont_simple_block_slice_check1.log`.
          - [x] Add arbitrary-continuation `if`, `switch`, and `for` head
            frontiers, with generated loop handlers preserving the declared
            break/continue shapes.
            - [x] Add typed-continuation `if` support lemmas for the
              nonregular true-branch statement bridge and singleton generated
              condition-prelude sequence. Checks:
              `/tmp/evm_kont_if_nonregular_helper_check1.log`,
              `/tmp/evm_kont_single_if_check1.log`.
            - [x] Add the generic `withRegular` continuation-layout helper
              and nonregular relation conversion needed to compose structured
              singleton proofs into sequence frontiers without conflating
              fallthrough with abrupt continuations. Check:
              `/tmp/evm_kont_withregular_check1.log`.
            - [x] Add typed helper lemmas for regular scoped-block extraction,
              `if` condition-terminal heads, typed nonregular mode
              discrimination, and checked open-sequence-to-scoped-block
              closure. These are the reusable atoms for the accepted `if`,
              `switch`, and `for` frontiers. Checks:
              `/tmp/evm_kont_block_regular_exact_check2.log`,
              `/tmp/evm_kont_if_condition_terminal_check3.log`,
              `/tmp/evm_kont_mode_lemmas_check3.log`,
              `/tmp/evm_kont_checked_block_adapter_check2.log`.
            - [x] Add the dispatcher-ready accepted `if :: rest`
              typed-continuation frontier, using the singleton typed `if`
              bridge plus a source-domain lemma for regular fallthrough.
              Check: `/tmp/evm_kont_if_frontier_check2.log`.
            - [x] Add the dispatcher-ready accepted `switch :: rest`
              typed-continuation frontier, using the singleton typed `switch`
              bridge, selected-body recursive block closure, and a
              source-domain lemma for regular fallthrough. Check:
              `/tmp/evm_kont_switch_frontier_check3.log`.
            - [x] Add whole-loop no-raw-`break`/`continue` semantic
              eliminators for accepted `for` statements. Check:
              `/tmp/evm_for_no_raw_break_continue_check2.log`.
            - [x] Add typed mode-support adapters that collapse a nonregular
              whole-loop result to the old leave-layout compatibility shape
              once raw `break`/`continue` are ruled out. Check:
              `/tmp/evm_kont_leave_layout_support_adapter_check2.log`.
            - [x] Add the generated-loop typed branch-contract facade
              `GeneratedForLoopKontBranchContracts` plus the conversion from
              old branch bundles using the no-raw-loop-control theorem. Check:
              `/tmp/evm_kont_for_branch_contract_facade_check2.log`.
            - [x] Add the leave-supported typed generated-`for` head bridge
              `sourceResultSeqKontSoundWhenAtExactHiddenCtx_cons_for_head_of_branch_contracts_leave_supported`,
              reusing the old branch dispatcher but returning typed
              nonregular head evidence. Check:
              `/tmp/evm_kont_for_head_leave_supported_check1.log`.
            - [x] Weaken the old generated-loop dispatcher so leave-layout
              compatibility is required only for concrete `Leave`
              checkpoints, then derive that branch-locally from
              `SourceResultModeKontSupported` in the typed head bridge. Check:
              `/tmp/evm_kont_for_head_branch_local_support_check1.log`.
            - [x] Add the checked typed generated-`for :: rest` sequence
              wrapper
              `checkedSeqKontSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_branch_contracts_reserved_supported`,
              threading branch contracts through the compiler/freshness
              plumbing. Check:
              `/tmp/evm_kont_for_branch_contract_seq_wrapper_check2.log`.
            - [x] Weaken the generated-loop post-regular branch-contract
              derivation to use actual-run nonregular compatibility rather
              than global `SourceResultOutcomeLayoutSupported`, so accepted
              typed continuation support can discharge only the concrete loop
              result. Check: `/tmp/evm_typed_branch_core_check1.log`.
            - [x] Add the accepted reserved recursive-bridge constructor for
              typed generated-loop branch contracts,
              `generatedForLoopKontBranchContracts_of_programAccepted_hiddenMode_reservedBridge`,
              plus the typed-to-leave-layout projection adapter needed by the
              existing head dispatcher. Check:
              `/tmp/evm_typed_branch_core_check1.log`.
            - [x] Add the accepted typed generated-`for :: rest` sequence
              wrapper by integrating the accepted typed branch-contract
              constructor through the generated-head theorem without exposing
              branch bundles at the public boundary. Check:
              `/tmp/evm_kont_for_programaccepted_seq_direct_check4.log`.
          - [x] Add arbitrary-continuation primitive and user-call head
            frontiers using the no-checkpoint projection for regular/terminal
            source runs.
            - [x] Add same-compiler state weakening plus
              `SourceResultOutcomeRel.to_kont_of_supported_within`, so
              same-layout outcome proofs can be projected to typed
              continuations when `ControlWithin` supplies break/continue
              containment. Check:
              `/tmp/evm_kont_outcome_within_projection_check3.log`.
            - [x] Add sequence-level and checked-lowering adapters from
              same-layout hidden-context proofs to typed continuations under
              `ControlWithin`. Check:
              `/tmp/evm_kont_same_layout_within_seq_check1.log`.
            - [x] Add head-level nonregular projection from same-layout
              hidden-head proofs to typed-continuation hidden-head proofs under
              `ControlWithin`. Check:
              `/tmp/evm_kont_nonregular_head_projection_check1.log`.
            - [x] Add the typed-continuation expression user-call head theorem
              by projecting the existing same-layout user-call head proof and
              deriving the non-checkpoint/support facts internally. Check:
              `/tmp/evm_kont_expr_user_head_tight_check3.log`.
            - [x] Add the typed-continuation expression-statement user-call
              sequence frontier. Check:
              `/tmp/evm_kont_expr_user_seq_frontier_check1.log`.
            - [x] Add typed-continuation head bridges for assignment and
              generated-temporary `let` user calls. Check:
              `/tmp/evm_kont_assign_let_user_heads_check2.log`.
            - [x] Add the typed-continuation assignment user-call sequence
              frontier. Check:
              `/tmp/evm_kont_assign_user_seq_frontier_check1.log`.
            - [x] Add the typed-continuation generated-`let` user-call
              sequence frontier. Check:
              `/tmp/evm_kont_let_user_seq_frontier_check1.log`.
            - [x] Add typed-continuation primitive sequence frontiers for
              expression statements, assignments, and generated `let` heads,
              including low-fuel assignment/declaration helpers and
              declaration-layout `ControlWithin` growth. Checks:
              `/tmp/evm_kont_expr_prim_frontier_check3.log`,
              `/tmp/evm_kont_assign_prim_frontier_check1.log`,
              `/tmp/evm_kont_let_prim_frontier_check1.log`.
          - [x] Add the accepted-head typed dispatcher over all source heads,
            routing rejected lowerer shapes through the typed no-lowering
            helper. Check:
            `/tmp/evm_typed_all_head_dispatcher_check3.log`.
          - [x] Instantiate the typed hidden-sequence fuel induction with the
            accepted-head dispatcher.
            - [x] Add the strong-fuel typed sequence induction whose head
              frontier receives a recursive callback for any smaller
              source-fuel sequence. Check:
              `/tmp/evm_kont_sequence_strong_induction_check4.log`.
            - [x] Add the exact-bound wrapper over the strong-fuel typed
              sequence induction, matching the successor theorem's expected
              frontier shape. Check:
              `/tmp/evm_kont_sequence_strong_exact_wrapper_check1.log`.
          - [x] Feed that induction-shaped sequence theorem into
            `succ_of_sequence_kont_frontier_within_terminal_args_supported`
            through
            `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.succ_of_typed_sequence_frontier_terminal_args_supported`.
            Check: `/tmp/evm_typed_sequence_successor_check2.log`.
- [x] Export and audit `recursiveSourceBridgeWhenUpToAt_succ`, then derive the
  all-bounds theorem by induction over the recursive-call/source-fuel bound.
  - [x] Add/export/audit the exact-fuel frontier interface
    `ProgramAcceptedRecursiveSourceBridgeAtExactFuelCompatNames` and the checked
    bridge extender
    `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.succ_of_atExactFuel`,
    so the successor proof only needs the new fuel frontier and reuses the
    previous bound for all smaller source fuels.
  - [x] Add/export/audit the exact-fuel projection
    `ProgramAcceptedRecursiveSourceBridgeAtExactFuelCompatNames.of_whenUpTo`,
    so already-proved bounded bridges can be consumed by exact-fuel helper
    constructors without reopening their fields.
  - [x] Prove the exact-fuel frontier constructor for accepted statements and
    blocks from the existing per-construct checked wrappers.
    - [x] Tighten `SourceLexical` so declaration and assignment source scoping
      carries the left-hand-side facts the checked lowering theorems need:
      declaration/assignment target `Nodup`, declaration freshness, and
      assignment target membership.
    - [x] Add/export source-scoped checked wrappers for existing declaration,
      literal/variable assignment, and assignment/let user-call successor
      cases, so the frontier constructor can consume the accepted source
      lexical predicate directly instead of asking for separate hygiene
      witnesses.
    - [x] Add/export/audit the accepted-recursive bracketed-block wrapper
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_of_programAcceptedBody`,
      so `.Block body` can consume the recursive hidden-block bridge without
      exposing the one-more-body-lowering fuel detail at the exact frontier.
    - [x] Add/export/audit the exact-frontier bracketed-block constructor
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_block_of_programAcceptedBody_frontier`,
      including the fuel-1 out-of-fuel branch and the higher-fuel delegation to
      the accepted recursive hidden-block wrapper.
    - [x] Add/export/audit exact-frontier user-call constructors for the three
      source statement shapes:
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_user_call_of_program_accepted_recursive_actual_or_arg_terminal_frontier`,
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_user_call_of_program_accepted_recursive_actual_or_arg_terminal_frontier`,
      and
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_user_call_of_program_accepted_recursive_actual_or_arg_terminal_frontier`.
    - [x] Add/export/audit primitive argument-boundary split lemmas for
      expression statements, returned-value assignments, and generated
      temporaries:
      `exec_block_expr_prim_call_evalArgs_split_of_relatable`,
      `exec_block_assign_prim_call_evalArgs_split_of_relatable`, and
      `exec_block_let_prim_call_evalArgs_split_of_relatable`.
    - [x] Add/export/audit the primitive argument-terminal checked wrappers
      for the three statement shapes:
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_of_arg_terminal`,
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_prim_of_arg_terminal`,
      and
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_prim_of_arg_terminal`.
    - [x] Add/export/audit actual-or-argument-terminal primitive statement
      wrappers that combine the existing regular-success primitive wrappers
      with the new argument-terminal wrappers and the primitive
      error/nonrelatability facts.
      - [x] Add/export/audit the zero-output safe/basic primitive-call
        nonrelatability fact
        `safeBasicZeroOutputPrimCall_error_not_relatable`, including the
        reusable zero-result machine/state/copy wrapper lemmas and the
        static-mode `sstore`/`tstore` branches.
      - [x] Add/export/audit the primitive expression-statement adapters
        `evalValues_prim_call_ok_of_evalArgs_ok_primCall_ok` and
        `exec_block_expr_prim_call_error_of_evalArgs_ok_primCall_error`, so
        actual primitive calls can split cleanly between successful primitive
        execution and nonrelatable primitive errors after argument evaluation.
      - [x] Add/export/audit the assignment and generated-`let` primitive
        post-argument error splitters
        `exec_block_assign_prim_call_error_of_evalArgs_ok_primCall_error`
        and
        `exec_block_let_prim_call_error_of_evalArgs_ok_primCall_error`.
      - [x] Add/export/audit the expression-statement actual-or-argument
        terminal primitive wrapper
        `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal`.
      - [x] Add/export/audit the returned-assignment actual-or-argument
        terminal primitive wrapper.
      - [x] Add/export/audit the generated-`let` actual-or-argument terminal
        primitive wrapper.
    - [x] Add the generic checked frontier wrappers for structured control
      (`if`, `switch`, and `for`) from source-scoped conditions, selected
      body/case/post recursive bridge calls, and generated expression prelude
      soundness.
      - [x] Add/export source-lexical projections for `if`, `switch`, and
        `for`, including selected `switch` case/default scoping via
        Nethermind's `selectSwitchCase`.
      - [x] Prove the checked `if` frontier wrapper.
        - [x] Add/export exact-domain lifting for single-value condition
          preludes (`ExprEvalPreludeSound.run_exact_*`).
        - [x] Add/export the exact hidden-head bridge for a generated-prelude
          `if` whose condition evaluates to false, preserving the visible
          layout and skipping the body.
        - [x] Add/export the exact hidden-head bridge for a generated-prelude
          `if` whose condition evaluates to true and whose body falls through
          regularly, with the body proof parametric in the post-prelude hidden
          compiler context.
        - [x] Add/export the hidden nonregular-head interface and sequence
          combinator, plus the generated-prelude `if` true/nonregular-body
          bridge that skips enclosing sequence tails.
        - [x] Add/export the regular-body exact adapter
          `sourceRegularBlockRunAtExact_of_resultBlockSound_ok_domain`, so the
          checked `if` wrapper can recover exact post-body state from a
          same-layout block result theorem instead of inlining scoped block
          cleanup.
        - [x] Add/export the existential-fuel true/regular hidden-head bridge
          `sourceRegularStmtRunHiddenExact_if_true_regular_exists_of_eval_domain`,
          so recursive body block soundness can supply its target fuel locally.
        - [x] Add/export
          `sourceRegularStmtRunHiddenExact_if_true_regular_of_blockSound_ok_domain`,
          connecting same-layout recursive body block soundness directly to the
          generated-prelude `if` true/regular hidden-head interface.
        - [x] Add/export
          `sourceResultSeqSoundWhenAtExactHiddenCtx_single_if_of_eval_domain`,
          the compositional singleton generated-prelude `if` sequence bridge
          that handles condition errors, false conditions, and true body
          outcomes through one source-facing theorem, now passing the derived
          post-prelude scope containment fact to the body proof.
        - [x] Add/export the hidden-scope block boundary
          `sourceResultBlockSoundWhenAtExactHiddenScope_of_hiddenCtx_compat`,
          so generated control preludes can run bodies under contexts that
          retain compiler-only locals while preserving the source-visible
          layout through a current-scope containment premise.
        - [x] Add/export the checked compile-fuel hidden-scope block facade
          `checkedBlockLoweringSoundWhenFreshNamesAtCompileFuelHiddenScope_of_hiddenCtx_compat`
          so generated control wrappers can consume body lowering evidence as
          one checked contract.
        - [x] Make hidden-context block closures filter-aware, deriving inner
          relatability/layout compatibility through block cleanup instead of
          requiring arbitrary inner `allowed` filters.
        - [x] Add handler-compatibility transport across regular generated
          preludes via `SourceResultOutcomeLayoutCompatible.of_handler_eq`.
        - [x] Add/export the generic checked `if` frontier wrapper
          `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_of_condition_body`,
          decomposing the real compiler output and consuming checked condition
          and hidden-scope body contracts.
        - [x] Add/export/audit the exact-fuel accepted `if` frontier
          constructor
          `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_of_programAcceptedCondition_frontier`,
          including low-fuel out-of-fuel branches and productive-fuel
          delegation to the accepted condition/body wrapper.
      - [x] Prove the checked `switch` frontier wrapper.
        - [x] Add/export freshness-bearing selected-body lowering witnesses
          `SwitchSelectedLoweringWithCover` for empty-default and
          nonempty-default switch lowering, so selected case/default bodies can
          re-enter checked block proofs without a hand-supplied freshness
          oracle.
        - [x] Add/export
          `sourceResultSeqSoundWhenAtExactHiddenCtx_single_switch_of_eval_domain`,
          the compositional singleton generated-prelude `switch` bridge,
          covering scrutinee terminal errors, no-default/no-match empty-default
          behavior, and selected case/default body outcomes.
        - [x] Add/export the generic checked `switch` frontier wrapper
          `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_switch_of_scrutinee_body`,
          decomposing the real compiler output and consuming selected bodies
          through the hidden-scope checked block contract.
        - [x] Add/export/audit the exact-fuel accepted `switch` frontier
          constructor
          `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_switch_of_programAcceptedScrutinee_frontier`,
          including low-fuel out-of-fuel branches and productive-fuel
          delegation to the accepted scrutinee/selected-body wrapper.
      - [x] Prove the checked `for` frontier wrapper.
        - [x] Add/export generic singleton hidden-head adapters, including a
          branchable regular-or-nonregular bridge, so the generated `for`
          frontier can close singleton sequences after source-branch analysis
          without redoing empty-tail/layout bookkeeping in every branch.
        - [x] Add/export the allowed-aware singleton hidden-head adapter, so
          generated-control terminal branches can use the actual filtered
          sequence result to derive source-result relatability.
        - [x] Add/export the imported singleton `execSeq` adapter plus the
          source-facing result-equality and `allowed` projections for singleton
          sequences, so loop recursion can reuse the public `allowed` filter
          without open-coding nil-tail fuel cases.
        - [x] Align the imported Yul loop post-success semantics with Solidity
          and the source tower: post `OutOfFuel`/`leave` now propagates instead
          of re-entering the loop, and the imported reduction, checkpoint, and
          store-domain support lemmas have been repaired against that behavior.
        - [x] Add the source-facing loop bridge for the compiler's lowering
          strategy: imported Yul `for cond post body` must match a target
          infinite `for true post (guard; body)` where the generated guard
          evaluates `cond` and `break`s when it is zero.
          - [x] Export the target-generated `iszero` guard condition lemma
            from the primitive stack-soundness contract, rather than treating
            generated `iszero` as an ad hoc special case.
          - [x] Prove/export the condition-zero generated guard/prelude helper:
            after the condition prelude materializes `0`, the inserted
            `if iszero(cond) { break }` exits the loop before the lowered body
            runs.
          - [x] Lift the condition-zero guard helper through the outer target
            `for true` statement and the imported source `loop` false branch.
          - [x] Prove/export the target-side `for true` false-condition
            statement run: generated guard `break` becomes regular loop exit.
          - [x] Connect that target-side false-condition run to the imported
            Nethermind source `loop` false branch and singleton sequence/block
            regular-head relation.
          - [x] Lift the regular false-branch head relation through the
            singleton sequence/block result relation inside the final checked
            `for` wrapper.
        - [x] Thread generated condition-prelude terminal/regular evidence
          through the guard body without exposing hidden temporaries above the
          loop boundary.
          - [x] Prove/export the condition-prelude terminal branch:
            if imported condition evaluation halts/reverts before producing a
            value, the generated target `for true` body prelude halts/reverts
            with the same observable outcome before the inserted guard runs.
          - [x] Prove/export the generated nonzero guard-skip prefix:
            target-generated `iszero(cond)` evaluates false for nonzero
            imported condition values, and the inserted guard falls through
            regularly without running the lowered body yet.
          - [x] Lift the nonzero guard-skip prefix through the ordinary
            `ExprEvalPreludeSound` / exact-domain interface, so checked `for`
            wrappers consume imported condition evaluation rather than raw
            generated-prelude runs.
          - [x] Add/export/audit
            `sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_imported_loop_branches`,
            the source-facing generated-loop dispatcher that case-splits the
            imported loop run, rules out post `break`/`continue` through a
            caller-supplied scoped-post contract, and delegates each reachable
            body/post/recursive branch to compositional callbacks.
          - [x] Add/export/audit the scoped-post checkpoint extractors
            `post_break_false_of_checkpointAllowed_false_false_true` and
            `post_continue_false_of_checkpointAllowed_false_false_true`, so the
            checked `for` wrapper can discharge the dispatcher's illegal
            post-control callbacks from `SourceResultCheckpointAllowed` rather
            than by open-coding checkpoint cases.
          - [x] Add/export/audit the checked compiler-decomposition wrapper
            `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_singleton_hiddenCtx`,
            so the successor proof can consume one source-facing singleton
            generated-loop bridge without exposing `Stmt.toFunctionsListFuel?`
            components or outer block-cleanup fuel arithmetic.
          - [x] Add/export/audit
            `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_imported_loop_branches`,
            bundling generated `for` compiler pieces in `GeneratedForCompiled`,
            installing the imported-loop dispatcher under the checked wrapper,
            and discharging the condition terminal/false branches from the
            condition prelude plus generated `iszero` primitive contract.
          - [x] Add/export/audit `GeneratedForLoopBranchContracts` and
            `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_branch_contracts`,
            replacing the loose body/post callback list with one generated-loop
            branch-contract package plus the separate scoped-post
            `break`/`continue` impossibility facts.
          - [x] Split the generated-loop branch package into
            `GeneratedForLoopNonrecursiveBranchContracts` plus a named
            `GeneratedForLoopPostRegularBranchContract`, and export the
            checked combiner so the recursive post-regular continuation is the
            only remaining branch-specific loop obligation.
          - [x] Add/export/audit
            `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_postRegular`,
            deriving all non-recursive body/post loop branches directly from
            hidden-scope checked block contracts and leaving only the
            post-regular recursive continuation as an explicit callback.
          - [x] Construct `GeneratedForLoopPostRegularBranchContract` from the
            bounded recursive IH at the smaller source fuel, including the
            body-regular/post-regular and body-continue/post-regular regular
            and nonregular recursive-loop outcomes.
            - [x] Thread the concrete `Stmt.toFunctionsList?` proof through
              `GeneratedForCompiled` as `stmtLower`, so loop callbacks can
              re-enter the accepted recursive bridge using the exact emitted
              statement rather than reconstructing lowering evidence.
            - [x] Add/export/audit
              `generatedForLoopPostRegularBranchContract_of_hiddenScope_blockSound_and_loop`,
              reducing the post-regular branch to two source-result-shaped
              loop callbacks: regular `.ok (.Ok ...)` recursive iterations and
              nonregular checkpoint/terminal iterations, plus exact-domain
              preservation for successful loop results.
            - [x] Add/export/audit
              `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_checked_loop`,
              deriving the post-regular branch contract from hidden-scope
              body/post contracts plus a smaller checked loop theorem.
            - [x] Derive the regular `.ok (.Ok ...)` loop callback from the
              accepted smaller-fuel recursive bridge.
            - [x] Derive the nonregular checkpoint/terminal loop callback from
              the accepted smaller-fuel recursive bridge.
            - [x] Derive exact-domain preservation for successful recursive
              loop results from the source acceptedness/domain-preservation
              facts already carried by the successor frontier.
              - [x] Add/export/audit the generic all-fuel theorem
                `exec_for_ok_domain_exact_of_all_fuel_parts`, specialized to
                successful `Ok` loop entries/results rather than the false
                arbitrary-state store-containment boundary.
              - [x] Bundle the semantic condition/body/post premises as
                `ForOkDomainExactContracts` and route
                `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_programAcceptedLoop`
                through `ForOkDomainExactContracts.exec_for_ok`, so the old
                opaque `hLoopDomainOk` premise is no longer public.
              - [x] Construct `ForOkDomainExactContracts` at the exact-fuel
                successor site from `Safe`, scoped post facts, condition
                result/domain facts, and recursive hidden-scope body/post
                block-domain facts.
                - [x] Add/export/audit source-domain contract facades
                  (`ExprOkDomainExactContract`,
                  `BlockDomainExactContract`, and
                  `ForOkDomainExactContracts.of_contracts`) plus the block
                  boundary exact-domain lemmas that turn `execSeq`
                  store-containment into successful block exact-domain
                  preservation.
                - [x] Add/export/audit
                  `ForOkDomainExactContracts.of_execSeq_contains`, reducing
                  body/post domain contract construction to all-fuel
                  source-side `execSeq` store-containment plus the condition
                  exact-`Ok` contract and scoped-post checkpoint
                  impossibility.
                - [x] Add/export/audit
                  `eval_ok_or_outOfFuel_domain_exact_of_safe_primitiveFamilies`,
                  separating the safe-expression condition invariant from the
                  resource assumption: successful safe condition evaluation
                  from an exact `Ok` store is either explicit `OutOfFuel` or
                  an ordinary `Ok` state with exact store domain, with
                  checkpoints ruled out by the primitive checkpoint contract.
                - [x] Replace the loop-domain condition premise with the
                  `Ok`-or-`OutOfFuel` safe-expression invariant so the
                  successor frontier does not need the too-strong all-fuel
                  `ExprEvalResultOkAt`/`ExprOkDomainExactContract` assumption.
                  - [x] Add the narrow absorbing-resource lemma needed by that
                    replacement: if a `for` condition evaluates successfully
                    to `State.OutOfFuel`, the surrounding imported loop cannot
                    produce a final ordinary `.Ok` result. This should stay
                    specialized to the condition/loop proof boundary, not a
                    broad arbitrary-state block store-containment theorem.
                - [x] Add/export/audit the narrow `.Ok`-entry source-domain
                  constructor route:
                  `eval_ok_or_outOfFuel_domain_contains_of_safe_primitiveFamilies`,
                  `SourceResultStoreContains.loop_succ_succ_of_ok_or_outOfFuel_parts`,
                  `SourceResultStoreContains.execSeq_ok_of_safe_primitiveFamilies`,
                  and
                  `ForOkDomainExactContracts.of_safe_scoped_primitiveFamilies`.
                  The checked program-accepted `for` wrapper now constructs its
                  own loop-domain contract from `Safe` and scoped post-control
                  facts instead of receiving it as public evidence.
          - [x] Instantiate
            `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_postRegular`
            inside the exact-fuel successor frontier for source `.For`.
            - [x] Add/export/audit
              `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition`,
              so the source `.For` frontier consumes the recursive
              expression/argument dispatcher for the generated condition
              prelude instead of carrying condition terminal/sound evidence by
              hand.
            - [x] Add/export/audit the generic coercions
              `SourceResultBlockSoundWhenAtExact.to_hiddenScope` and
              `CheckedBlockLoweringSoundWhenFreshNamesAtExact.to_hiddenScope`,
              allowing exact-scope recursive block proofs to feed
              hidden-scope APIs when no generated temporaries have extended the
              target context.
            - [x] Add the accepted-recursive `hiddenBlock` bridge field and
              use it in
              `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition`,
              deriving generated body/post hidden-scope block contracts from
              the recursive bridge instead of receiving them as public
              callbacks.
            - [x] Add the accepted-recursive checked argument-prelude `args`
              bridge field plus the zero-fuel base bundle, and use it in the
              checked source `.For` wrapper so generated condition arguments no
              longer appear as a public call-site premise.
            - [x] Rewire the successor-facing expression-statement,
              assignment, and `let` user-call source-scoped wrappers to derive
              checked argument-prelude evidence from the accepted recursive
              bridge instead of exposing an `hArgs` premise at the successor
              call site.
            - [x] Generalize/export the checked argument-prelude constructor
              to the successor frontier as
              `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.args_succ`,
              so the accepted bridge's `args` field is generated from the
              previous recursive bridge plus explicit primitive/resource facts.
            - [x] Add/export/audit the accepted-recursive source-facing `if`
              wrapper
              `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_of_programAcceptedCondition`,
              deriving condition preludes and hidden-scope body evidence from
              the accepted recursive bridge rather than exposing callbacks at
              the successor call site.
            - [x] Add/export/audit the accepted-recursive source-facing
              `switch` wrapper
              `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_switch_of_programAcceptedScrutinee`,
              strengthening the generic switch frontier to pass selected-body
              evidence so case/default body acceptedness is derived locally.
            - [x] Add/export/audit the exact-fuel accepted `for` frontier
              constructor
              `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition_frontier`,
              including fuels 1-4 out-of-fuel branches and productive-fuel
              delegation to the accepted loop wrapper.
        - [x] Delegate body and post executions through hidden-scope checked
          block contracts, handling regular/continue/post recursion,
          break-as-loop-exit, leave/halt pass-through, terminal errors, and
          source-fuel decrease.
          - [x] Add/export general hidden-scope block mode extractors
            (`ok_regular_exact`, `ok_break`, `ok_continue`, `ok_leave`,
            `error_halt`) so generated-loop branch callbacks can consume
            checked block soundness compositionally instead of unpacking block
            result relations in every branch.
          - [x] Add/export body-break and body-leave generated-loop wrappers
            that consume hidden-scope checked block soundness directly via the
            mode extractors.
          - [x] Add/export the body-halt generated-loop wrapper that consumes
            hidden-scope checked block soundness directly, carrying the
            existential terminal outcome through the generated guard/body run
            instead of assuming halt-kind uniqueness.
          - [x] Prove/export the nonzero guard-plus-body-break composition:
            after the generated guard falls through, a hidden-scope body
            `break` makes the whole generated loop body break without exposing
            generated temporaries.
          - [x] Lift generated body `break` through the outer target
            `for true` statement: the generated loop exits regularly and the
            compiler state is restricted back to the loop layout.
          - [x] Connect the generated body-break target run to the imported
            Nethermind source `loop` nonzero/body-break branch as a regular
            hidden-head theorem, with body exact-domain preservation explicit.
          - [x] Prove/export the nonzero body-`leave` pass-through family:
            guard-plus-body composition, outer generated `for true` statement
            propagation, and source-facing nonregular hidden-head theorem.
          - [x] Prove/export the nonzero body-halt/error pass-through family:
            guard-plus-body composition, outer generated `for true` statement
            propagation, and source-facing nonregular hidden-head theorem
            preserving the terminal `SourceResultOutcomeRel`.
          - [x] Prove/export the nonzero guard-plus-body-`continue`
            composition, so post-running branches can reuse the generated
            guard/body prefix without exposing hidden temporaries.
          - [x] Prove/export the body-`continue` plus post-halt/error branch:
            shared-fuel target `for true` behavior via `Nat.max`, and the
            source-facing nonregular hidden-head theorem preserving terminal
            `SourceResultOutcomeRel`.
          - [x] Add/export the body-continue plus post-halt block-soundness
            wrapper, consuming hidden-scope checked body/post contracts and
            carrying the existential terminal post outcome directly.
          - [x] Add/export the body-continue plus post-`leave`
            block-soundness wrapper, consuming hidden-scope checked body/post
            contracts and preserving the Yul `leave` checkpoint as source
            `Outcome.leave`.
          - [x] Prove/export the nonzero guard-plus-body-regular composition,
            witnessing the outer block cleanup state after the hidden generated
            guard/body scope cleanup.
          - [x] Prove/export the body-regular plus post-halt/error branch:
            shared-fuel target `for true` behavior via `Nat.max`, and the
            source-facing nonregular hidden-head theorem preserving terminal
            `SourceResultOutcomeRel`.
          - [x] Add/export the body-regular plus post-halt block-soundness
            wrapper, consuming hidden-scope checked body/post contracts and
            carrying the existential terminal post outcome directly.
          - [x] Add/export the body-regular plus post-`leave`
            block-soundness wrapper, consuming hidden-scope checked body/post
            contracts and preserving the Yul `leave` checkpoint as source
            `Outcome.leave`.
          - [x] Prove/export the body-regular plus post-regular recursive
            branch, using a smaller-fuel generated-loop statement theorem for
            the recursive loop step.
          - [x] Add/export the body-regular plus post-regular block-soundness
            wrapper, consuming hidden-scope checked body/post contracts and
            leaving only recursive loop continuation plus exact-domain facts
            explicit.
          - [x] Prove/export the body-continue plus post-regular recursive
            branch, using the same smaller-fuel generated-loop statement
            theorem after reviving the source continue checkpoint.
          - [x] Add/export the body-continue plus post-regular block-soundness
            wrapper, consuming hidden-scope checked body/post contracts and
            leaving only the recursive loop continuation plus exact-domain
            facts explicit.
          - [x] Add/export the body-regular plus post-regular nonregular
            recursive-loop sibling, so a later iteration that leaves/halts is
            preserved instead of forcing the recursive continuation to be
            regular.
          - [x] Add/export the body-continue plus post-regular nonregular
            recursive-loop sibling, matching the same later-iteration
            abrupt/terminal behavior after `continue` revives into `post`.
    - [x] Add/export/audit the accepted exact-fuel statement frontier
      `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_programAccepted_frontier`,
      discharging primitive expression/assignment/generated-`let` statement
      families from the shared primitive/result contracts and leaving only
      terminal primitive expression statements as an explicit terminal
      observation contract.
    - [x] Add/export/audit the exact-frontier package handoff
      `ProgramAcceptedRecursiveSourceBridgeAtExactFuelCompatNames.of_frontier_fields`
      and
      `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.succ_of_frontier_fields`,
      so statement and argument frontiers are bundled once and the remaining
      successor boundary is ordinary block plus hidden-block list evidence.
    - [x] Add/export/audit the hidden-context sequence handoff
      `checkedBlockLoweringSoundWhenFreshNamesAtExact_of_hiddenCtxSeq_frontier`,
      `checkedBlockLoweringSoundWhenFreshNamesAtCompileFuelHiddenScope_of_hiddenCtxSeq_frontier`,
      and
      `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames.succ_of_hiddenCtxSeq_frontier`,
      reducing both block fields to one accepted open-sequence frontier at the
      previous source-fuel bound.
    - [x] Prove the accepted hidden-context open-sequence frontier for
      `CheckedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx`; this is
      now the only remaining constructor needed before instantiating the
      accepted recursive successor theorem.
      - [x] Add/export/audit the empty hidden-context sequence case
        `sourceResultSeqSoundWhenAtExactHiddenCtx_nil_of_compat` and
        `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_nil_of_compat`,
        including the fuel-zero out-of-fuel branch and arbitrary compile-fuel
        lowering boundary.
      - [x] Add/export/audit the general hidden-context out-of-fuel wrappers
        `sourceResultSeqSoundWhenAtExactHiddenCtx_of_execSeq_outOfFuel` and
        `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_of_execSeq_outOfFuel`,
        so the sequence frontier's source-fuel-zero branch is one reusable
        contradiction from the relatability filter.
      - [x] Add/export/audit
        `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_zero`,
        the source-fuel-zero base case for arbitrary statement lists and
        compile fuel.
      - [x] Add/export/audit
        `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_one`,
        the source-fuel-one base case for arbitrary nonempty statement lists.
      - [x] Prove the nonempty hidden-context sequence case by composing the
        accepted head statement frontier with the tail sequence frontier.
        - [x] Add/export/audit the generic current-head composition lemmas
          `sourceResultSeqSoundWhenAtExactHiddenCtx_cons_current_regular_or_nonregular_hidden`
          and
          `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_current_regular_or_nonregular`,
          so nonempty sequence proof work is reduced to accepted head-branch
          construction plus tail fresh-coverage.
        - [x] Add/export/audit the reservation-aware hidden-sequence block
          handoff and accepted recursive bridge spine
          (`ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved`),
          making the future-source-name invariant explicit instead of relying
          on arbitrary `reserved` prefixes.
        - [x] Build the accepted head-branch constructor for each supported
          head family and feed it through the checked cons facade.
          - [x] Add/export/audit direct hidden-context abrupt head lemmas for
            `break`, `continue`, and `leave`, plus checked `head :: tail`
            sequence wrappers using the generic cons facade.
          - [x] Add/export/audit direct hidden-context regular head lemmas and
            checked sequence wrappers for simple local heads:
            `x := literal`, `x := y`, `let x`, `let x := literal`, and
            `let x := y`.
          - [x] Add/export/audit fuel-dispatched hidden-sequence constructors
            for abrupt heads and simple local heads, including source-fuel-two
            out-of-fuel declaration branches and the source-name reservation
            projection API needed by `let` tails.
          - [x] Add/export/audit the reservation-aware accepted simple-head
            dispatcher slice `SimpleHiddenSeqHead` /
            `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_simple_head_reserved`.
          - [x] Fold structured heads, primitive generated-prelude heads, and
            user-call heads into the accepted hidden-sequence dispatcher.
            - [x] Add/export/audit the hidden-context primitive argument
              adapter
              `sourceArgStackPreludeRegularAt_of_checkedAt_lowerBound1?_toStackSeq`
              and missing zero-output primitive prelude lemma
              `lower0?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegularAt`,
              eliminating the false `ctx.scope = layout` requirement for
              primitive generated-prelude sequence heads.
            - [x] Add/export/audit the zero-output primitive
              expression-statement hidden head slice:
              `sourceResultSeqSoundWhenAtExactHiddenCtx_cons_expr_prim_of_lower_preludeRegularAt_general_of_eval_domain`,
              `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_prim_of_preludeRegularAt_success`,
              and
              `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_prim_of_checkedArgs_success`.
            - [x] Add the corresponding hidden-context checked-argument
              slices for assignment and declaration primitive heads.
              - [x] Add/export/audit the assignment primitive slice:
                `sourceResultSeqSoundWhenAtExactHiddenCtx_cons_assign_prim_of_lower_preludeRegularAt_general_of_eval_domain`,
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_assign_prim_of_preludeRegularAt_success`,
                and
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_assign_prim_of_checkedArgs_success`.
              - [x] Add/export/audit the declaration primitive slice:
                `sourceResultSeqSoundWhenAtExactHiddenCtx_cons_let_prim_of_lower_preludeRegularAt_general_of_eval_domain`,
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_prim_of_preludeRegularAt_success`,
                and
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_prim_of_checkedArgs_success`.
            - [x] Add terminal/error primitive head dispatch so primitive
              generated-prelude heads are not limited to successful primitive
              evaluation.
              - [x] Move/export/audit the generic hidden-context terminal
                prelude suffix theorem
                `sourceResultSeqSoundWhenAtExactHiddenCtx_arg_terminal_prelude_suffix`.
              - [x] Add/export/audit hidden-context argument-terminal
                wrappers for primitive expression, assignment, and declaration
                heads:
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_prim_of_arg_terminal`,
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_assign_prim_of_arg_terminal`,
                and
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_prim_of_arg_terminal`.
              - [x] Add/export/audit checked-argument adapters for the same
                three terminal primitive hidden-head wrappers, so the accepted
                recursive bridge supplies generated argument-terminal evidence
                directly:
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_expr_prim_of_programAccepted_arg_terminal`,
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_assign_prim_of_programAccepted_arg_terminal`,
                and
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_let_prim_of_programAccepted_arg_terminal`.
            - [x] Fold structured-control and user-call heads through the
              reserved hidden-sequence frontier.
              - [x] Add/export/audit the scope- and handler-transfer-aware
                hidden-head `if` lemmas:
                `sourceNonregularStmtRunHiddenExact_if_condition_terminal`,
                `sourceRegularStmtRunHiddenExact_if_true_regular_exists_of_eval_domain_scope`,
                and
                `sourceNonregularStmtRunHiddenExact_if_true_exists_of_eval_domain_scope`.
              - [x] Add/export/audit the reservation-aware hidden-sequence
                `if :: tail` fold
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_if_of_programAcceptedCondition_reserved`,
                deriving condition terminal/regular evidence and body
                hidden-scope evidence from the accepted recursive bridge.
              - [x] Add/export/audit reusable hidden-head `switch` branch
                lemmas for scrutinee terminal errors and regular no-match
                fallthrough:
                `sourceNonregularStmtRunHiddenExact_switch_scrutinee_terminal`
                and
                `sourceRegularStmtRunHiddenExact_switch_no_match_of_eval_domain`.
              - [x] Add/export/audit reusable hidden-head `switch` branch
                lemmas for selected case/default bodies:
                `sourceRegularStmtRunHiddenExact_switch_selected_regular_exists_of_eval_domain_scope`
                and
                `sourceNonregularStmtRunHiddenExact_switch_selected_exists_of_eval_domain_scope`.
              - [x] Add/export/audit the reservation-aware hidden-sequence
                `switch :: tail` fold
                `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_switch_of_programAcceptedScrutinee_reserved`,
                routing scrutinee terminal errors, no-match fallthrough, and
                selected case/default body outcomes through the generic cons
                facade.
              - [x] Add/export/audit hidden-scope generated-`for`
                condition-terminal and false-condition branch lemmas, where
                the target loop break/continue handlers use the full hidden
                `ctx.scope` and the proof projects back to the visible
                `layout`:
                `sourceForGeneratedFalseStmtRun_of_eval_domain_zero_hidden_scope`,
                `sourceRegularStmtRunHiddenExact_for_generated_false_of_eval_domain_zero_hidden_scope`,
                and
                `sourceNonregularStmtRunHiddenExact_for_generated_condition_terminal_hidden_scope`.
              - [x] Introduce the loop-body hidden-handler contract needed for
                nonzero `for` branches. The old generic block compatibility
                predicate assumes checkpoint handler layouts are visible
                source layouts; hidden sequence contexts instead install
                target break/continue handlers at full `ctx.scope`, while the
                source relation must remain projected to `layout`.
                - [x] Prove/export the body-`break` hidden-scope branch shape
                  directly:
                  `sourceForGeneratedBodyBreakStmtRun_of_eval_domain_nonzero_hidden_scope`
                  and
                  `sourceRegularStmtRunHiddenExact_for_generated_body_break_of_eval_domain_nonzero_hidden_scope`.
                - [x] Prove/export the body-`leave` hidden-scope branch shape
                  directly:
                  `sourceForGeneratedBodyLeaveStmtRun_of_eval_domain_nonzero_hidden_scope`
                  and
                  `sourceNonregularStmtRunHiddenExact_for_generated_body_leave_of_eval_domain_nonzero_hidden_scope`.
                - [x] Prove/export the body halt/error hidden-scope branch
                  shape directly:
                  `sourceForGeneratedBodyHaltStmtRun_of_eval_domain_nonzero_hidden_scope`
                  and
                  `sourceNonregularStmtRunHiddenExact_for_generated_body_halt_of_eval_domain_nonzero_hidden_scope`.
                - [x] Prove/export the body-`continue` plus post halt/error
                  hidden-scope branch shape directly:
                  `sourceForGeneratedBodyContinuePostHaltStmtRun_of_eval_domain_nonzero_hidden_scope`
                  and
                  `sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_halt_of_eval_domain_nonzero_hidden_scope`.
                - [x] Prove/export the body-`continue` plus post-`leave`
                  hidden-scope branch shape directly:
                  `sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_leave_of_blockSound_hidden_scope`.
                - [x] Prove/export the body-regular plus post halt/error
                  hidden-scope branch shape directly:
                  `sourceForGeneratedBodyRegularPostHaltStmtRun_of_eval_domain_nonzero_hidden_scope`
                  and
                  `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_of_eval_domain_nonzero_hidden_scope`.
                - [x] Prove/export the body-regular plus post-`leave`
                  hidden-scope branch shape directly:
                  `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_leave_of_blockSound_hidden_scope`.
                - [x] Prove/export the body-regular plus post-regular
                  recursive hidden-scope branch shape directly:
                  `sourceRegularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero_hidden_scope`.
                - [x] Prove/export the body-regular plus post-regular
                  nonregular recursive hidden-scope branch shape directly:
                  `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero_hidden_scope`.
                - [x] Prove/export the body-continue plus post-regular
                  recursive hidden-scope branch shape directly:
                  `sourceRegularStmtRunHiddenExact_for_generated_body_continue_post_regular_of_eval_domain_nonzero_hidden_scope`.
                - [x] Prove/export the body-continue plus post-regular
                  nonregular recursive hidden-scope branch shape directly:
                  `sourceNonregularStmtRunHiddenExact_for_generated_body_continue_post_regular_of_eval_domain_nonzero_hidden_scope`.
                - [x] Add/export/audit the hidden-context singleton generated
                  `for` sequence bridge
                  `sourceResultSeqSoundWhenAtExactHiddenCtx_single_for_of_branch_contracts`,
                  so condition terminal/false branches and the bundled
                  generated-loop branch contracts feed the sequence-level
                  theorem without an exact-scope premise.
                - [x] Add/export/audit the checked hidden-context
                  `for :: tail` lowering-plumbing fold
                  `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_generated_head_reserved`,
                  so the remaining semantic obligation is a generated-loop
                  head proof over decomposed compiler pieces rather than
                  repeated `Stmt.List`/fresh-state mechanics.
                - [x] Split and prove the generated-loop post-regular
                  semantic head obligation for hidden `for :: tail`: regular
                  recursive loop results must produce a regular head without
                  requiring outer `SourceResultOutcomeLayoutCompatible`, while
                  nonregular recursive loop results use the outer allowed
                  final sequence result/compatibility.
                  - [x] Add/export/audit the regular-only generated-loop
                    post-regular contract and hidden-loop/mode-facing wrappers:
                    `GeneratedForLoopPostRegularOkBranchContract`,
                    `generatedForLoopPostRegularOkBranchContract_of_hiddenCtx_callbacks_and_loop`,
                    `generatedForLoopPostRegularOkBranchContract_of_hiddenCtx_callbacks_and_hidden_loop`,
                    and
                    `generatedForLoopPostRegularOkBranchContract_of_hiddenCtx_modeSound_and_hidden_loop`.
                  - [x] Add/export/audit nonregular-head `for :: tail`
                    sequence adapters
                    `allowed_of_execSeq_cons_error_succ`,
                    `allowed_of_execSeq_cons_checkpoint_succ`, and
                    `allowed_of_execSeq_cons_outOfFuel_succ`, so abrupt/error
                    head results use final sequence allowedness without
                    routing through singleton `[for]` facts.
                  - [x] Prove the generated `for` head semantic dispatcher for
                    hidden `for :: tail`, using the regular-only contract for
                    recursive loop `Ok` states and the existing outer
                    allowed/compatibility contract only for nonregular
                    recursive loop states:
                    `sourceResultSeqSoundWhenAtExactHiddenCtx_cons_for_head_of_imported_loop_branches`.
                  - [x] Add/export/audit the accepted-program generated-loop
                    branch packages
                    `generatedForLoopBranchContracts_of_programAccepted_hiddenMode`
                    and
                    `generatedForLoopPostRegularOkBranchContract_of_programAccepted_hiddenMode`,
                    deriving body/post/recursive-loop evidence from the
                    accepted recursive `hiddenBlock`/`hiddenModeBlock`
                    interface instead of caller-supplied generated witnesses.
                  - [x] Add/export/audit the accepted-program hidden-context
                    checked sequence fold
                    `checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_for_of_programAcceptedLoop_reserved`,
                    so generated `for :: tail` heads now consume only source
                    acceptedness, primitive/result families, and the tail
                    frontier.
              - [x] Add the remaining hidden-sequence head folds for bracketed
                blocks and user-function-call heads: bracketed block heads,
                expression-statement user calls, returned-assignment user
                calls, and generated-temporary `let` user calls.
              - [x] Add/export/audit the scope-aware hidden-context cons
                interface, so regular head-to-tail composition proves the
                post-head source-visible layout is contained in the actual
                emitted head block `outEnv` before invoking the recursive tail
                frontier.
              - [x] Convert the major accepted structured/user-call head folds
                to the scoped-tail interface: bracketed blocks, expression and
                assignment user calls, generated-temporary `let` user calls,
                `if`, `switch`, and generated `for`.
              - [x] Add/export/audit syntactic target-scope helpers for
                declaration prefixes (`initNames`) so visible-layout-extending
                heads can prove their post-head continuation shape
                compositionally.
              - [x] Convert the remaining simple hidden-sequence head folds
                (`break`, `continue`, `leave`, assignments, and simple
                declarations) to the scoped-tail interface.
              - [x] Assemble the recursive list-level `hSeq` frontier consumed
                by
                `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.succ_of_hiddenCtxSeq_frontier_fields`.
                - [x] Make the hidden-sequence tail interface carry the
                  compositional outcome-layout/handler compatibility needed
                  after layout-extending heads, instead of trying to derive a
                  larger-layout tail proof from the caller's initial
                  `hCompat`.
                  - [x] Add build-checked supported-layout base cases and the
                    source/checked supported cons facades.
                  - [x] Add build-checked supported-tail declaration wrappers
                    for `let`, `let := literal`, and `let := variable`,
                    including their fuel-dispatched forms.
                  - [x] Add build-checked supported-tail assignment wrappers
                    for `x := literal` and `x := variable`, including their
                    fuel-dispatched forms.
                  - [x] Add build-checked source-level supported adapters for
                    abrupt `break`/`continue`/`leave` checkpoint heads.
                  - [x] Thread the supported tail interface through the
                    checked abrupt wrappers and accepted simple-head
                    dispatcher.
                  - [x] Add build-checked supported block-frontier wrappers
                    and a reserved supported successor handoff, so the
                    eventual recursive `hSeq` theorem can feed the public
                    exact block/successor spine.
                  - [x] Add the build-checked supported-tail wrapper for a
                    bracketed block head.
                  - [x] Add the build-checked supported-tail wrapper for an
                    expression-statement user-call head.
                  - [x] Add the build-checked supported-tail wrapper for a
                    returned-assignment user-call head.
                  - [x] Add the build-checked supported-tail wrapper for a
                    generated-temporary `let` user-call head.
                  - [x] Add the build-checked supported-tail wrapper for an
                    `if` head.
                  - [x] Add the build-checked supported-tail wrapper for a
                    `switch` head.
                  - [x] Add the build-checked supported-tail plumbing wrapper
                    for a generated `for` head.
                  - [x] Generalize the generated-`for` imported-loop source
                    head theorem to consume supported outcome-layout
                    compatibility.
                  - [x] Generalize the generated-`for` branch-contract source
                    wrapper and add the build-checked supported-tail
                    branch-contract sequence wrapper.
                  - [x] Generalize the generated-`for` post-regular
                    recursive-loop contract chain from exact to supported
                    outcome-layout compatibility, with exact singleton loop
                    callbacks derived locally.
                  - [x] Add the build-checked supported-tail accepted-program
                    `for` wrapper.
                  - [x] Thread the supported tail interface through the
                    recursive list frontier.
                    - [x] Add the hidden-context terminal primitive
                      argument/sequence helper
                      `sourceResultSeqSoundWhenAtExactHiddenCtx_cons_terminalStackPrelude_of_preludeRegularAt_general`,
                      so terminal heads can short-circuit emitted tails without
                      `ctx.scope = layout`.
                    - [x] Add the checked terminal primitive hidden-head
                      wrapper on top of that source helper.
                    - [x] Add the checked terminal primitive
                      argument-terminal hidden-head wrapper, so terminal
                      primitive heads cover both successful argument
                      evaluation and argument-halting branches.
                    - [x] Add build-checked accepted-program adapters for
                      terminal primitive hidden-sequence heads, so generated
                      argument regular/terminal evidence comes from the
                      recursive bridge instead of raw call-site witnesses.
                    - [x] Add build-checked open-sequence primitive
                      argument-boundary split lemmas for expression-statement,
                      returned-assignment, and generated-`let` heads.
                    - [x] Add build-checked open-sequence primitive
                      post-argument error lemmas for expression-statement,
                      returned-assignment, and generated-`let` heads.
                    - [x] Add the build-checked source-facing supported-tail
                      adapter for arbitrary uninitialized declaration heads
                      (`let x, y`), deriving freshness and `Nodup` from source
                      lexical scoping.
                    - [x] Add the build-checked lexical scoping bridge from
                      source-order declaration tails to compiled stack-order
                      declaration tails for arbitrary `let x, y` heads.
                    - [x] Add build-checked nonregular primitive
                      argument-terminal head lemmas for expression-statement,
                      returned-assignment, and generated-`let` heads, so the
                      final dispatcher can use the generic supported cons
                      facade for argument-halting primitive branches.
                    - [x] Add build-checked supported-tail actual-run
                      primitive head wrappers for expression-statement,
                      returned-assignment, and generated-`let`, combining
                      primitive success, safe primitive post-argument error
                      contradiction, and argument-terminal branches behind one
                      compositional interface.
                    - [x] Add build-checked accepted-program adapters for
                      those actual-run primitive head wrappers, deriving
                      regular and terminal generated-argument evidence from
                      the accepted recursive bridge.
                    - [x] Add build-checked low-fuel open-sequence lemmas for
                      primitive assignment heads, so the final dispatcher can
                      close the fuel-two/fuel-three out-of-fuel branches
                      before the productive primitive wrapper applies.
                    - [x] Add build-checked low-fuel open-sequence lemmas for
                      primitive generated-`let` heads, so declaration
                      out-of-fuel edges match the assignment frontier.
                    - [x] Add the build-checked fuel-dispatched
                      accepted-program primitive assignment wrapper, packaging
                      low-fuel and productive branches behind one
                      dispatcher-facing theorem.
                    - [x] Add the build-checked fuel-dispatched
                      accepted-program primitive generated-`let` wrapper,
                      packaging low-fuel declaration checks, source-name
                      reservation, and productive primitive branches behind one
                      dispatcher-facing theorem.
                    - [x] Add the build-checked fuel-dispatched
                      accepted-program primitive expression-statement wrapper,
                      so all non-terminal primitive sequence heads have the
                      same one-call dispatcher interface.
                    - [x] Add build-checked general hidden-head regular
                      support for arbitrary uninitialized declaration lists
                      (`let x, y`), so the recursive dispatcher is not limited
                      to singleton declarations.
                    - [x] Add the build-checked supported-tail hidden-sequence
                      wrapper for arbitrary uninitialized declaration heads,
                      with the tail stated at the target stack-order layout.
                    - [x] Add build-checked contract-name reservation and
                      freshness support for selected callee bodies, so
                      function-body recursive calls can use the reserved
                      bridge rather than the older non-reserved bridge.
                    - [x] Add build-checked reserved callee-body block and
                      `FunDef.runBody` return/halt bridges for concrete
                      selected user-call runs.
                    - [x] Move the accepted no-target and terminal user-call
                      reconstruction theorems onto the reserved recursive
                      bridge, with legacy non-reserved callers explicitly
                      adapting through the checked `of_unreserved` embedding.
                    - [x] Move the expression-statement user-call hidden-head
                      theorem onto the reserved recursive bridge, with legacy
                      sequence wrappers adapting through `of_unreserved`.
                    - [x] Move the assignment user-call success reconstruction
                      and hidden-head theorem onto the reserved recursive
                      bridge, with legacy callers adapting through
                      `of_unreserved`.
                    - [x] Move the generated-temporary `let` user-call
                      success reconstruction and hidden-head theorem onto the
                      reserved recursive bridge, with legacy callers adapting
                      through `of_unreserved`.
                    - [x] Add the reserved recursive capability facade and
                      split terminal argument prelude construction through an
                      explicit expression-terminal capability instead of the
                      whole recursive bridge.
                    - [x] Move expression user-call terminal wrappers onto the
                      reserved recursive bridge and add
                      `SourceNamesReserved` subset/monotonicity/weakening
                      lemmas for the generalized list induction.
                    - [x] Move the checked single-expression terminal
                      dispatcher family onto the reserved recursive bridge,
                      with old callers adapting through `of_unreserved`.
                    - [x] Add the reserved-facing checked argument terminal
                      wrapper, so terminal primitive/user-call sequence heads
                      can consume the reserved recursive bridge directly.
                    - [x] Add the reserved-bridge sibling for
                      expression-statement user-call sequence heads, leaving
                      the legacy old-bridge theorem as an explicit
                      compatibility alias.
                    - [x] Add the reserved-bridge siblings for returned
                      assignment and generated-`let` user-call sequence heads,
                      leaving both legacy old-bridge theorem names as explicit
                      compatibility aliases.
                    - [x] Assemble the recursive statement-list dispatcher
                      over empty, simple, structured, user-call, primitive
                      success/error, terminal primitive, and low-fuel `for`
                      cases. Check:
                      `/tmp/evm_typed_all_head_dispatcher_check3.log`.
  - [x] Instantiate the successor handoff with that frontier constructor to
    obtain the exported accepted successor theorem
    `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.succ_of_typed_sequence_frontier_terminal_args_supported`.
    Check: `/tmp/evm_typed_sequence_successor_check2.log`.
  - [x] Induct over fuel to construct the all-bounds accepted recursive bridge
    without a caller-supplied bridge premise:
    `programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved_allBounds`.
  - [x] Add the reservation-aware dispatcher consumer
    `checkedRecursiveDispatcherRunBridge_of_programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved_actual`,
    instantiating source-name reservation at the concrete dispatcher names.
  - [x] Add the reservation-aware whole-program bytecode/gas-aware theorem
    `compile_whole_program_result_sound_of_programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved_compileAccepted`.
  - [x] Add the no-recursive-premise whole-program theorem
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_compileAccepted`,
    constructing the accepted recursive bridge internally at `sourceFuel`.
  - [x] Add the public bridge-facts wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_bridgeFacts_compileAccepted`,
    discharging the `safe` and `noShadowing` fields of
    `ProgramBridgeContext` from `Reference.Accepted`.
  - [x] Add the initial-layout wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_initialLayout_compileAccepted`,
    discharging the definitional
    `Functions.Source.Ctx.initial.scope = layout` premise by specializing the
    public theorem to the actual empty initial source layout.
  - [x] Add the source-state initial-relation wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_sourceStateRel_initialLayout_compileAccepted`,
    specializing the lower compiler state relation to
    `SourceStateRel cfg []` and deriving its installed-contract initial
    relation from the bridge's source initial relation.
  - [x] Add the object-compile-accepted wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_objectCompileAccepted`,
    constructing the source-accepted field of `SourceCompileAccepted` from
    `Reference.Accepted` and leaving only object-level compile acceptance as a
    lower-tower resource/acceptedness premise.
  - [x] Add the checked-root wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_compileCheckedRoot`,
    extracting the compiler-generated lowered `Functions.Program` and
    `program.toObjects?` root witness from `compileChecked? program = some asm`.
  - [x] Add `CheckpointExpressionSound.of_primitive_families` and the
    primitive-checkpoint top wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_primitiveCheckpoint`,
    discharging checkpoint expression soundness from the primitive-family
    checkpoint lemmas.
  - [x] Add the canonical initial-source-state wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_initialShared`,
    replacing explicit `sourceInitial`/source-initial-equality inputs with the
    fundamental `SharedStateRel` premise between the installed Yul shared state
    and `initial.toSharedState`.
  - [x] Add the public source-facing acceptedness/resource package
    `RecursiveBridgeAccepted` and the top wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_bridgeAccepted`,
    bundling reference acceptedness, lexical/control scoping, user-call arity,
    and lower object compile acceptance into one explicit boundary contract.
  - [x] Re-run `lake build EvmCompiler.LayerAudit` after theorem-boundary
    cleanup. Check: `/tmp/evm_post_cleanup_layeraudit_check1.log`.
  - [x] Verify the new public wrapper names report no `sorryAx`. Check:
    `/tmp/evm_new_public_axioms_check1.log`.
  - [x] Verify the initial-shared wrapper reports no `sorryAx`. Check:
    `/tmp/evm_initial_shared_axioms_check1.log`.
  - [x] Re-run `lake build EvmCompiler.LayerAudit` after the initial-shared
    wrapper. Check: `/tmp/evm_initial_shared_layeraudit_check1.log`.
  - [x] Verify the bridge-accepted wrapper reports no `sorryAx`; rerun the
    layer audit. Checks:
    `/tmp/evm_bridge_accepted_axioms_check1.log`,
    `/tmp/evm_bridge_accepted_layeraudit_check1.log`.
  - [x] Replace the public dispatcher-body no-out-of-fuel premise with the
    source-facing run-result premise
    `referenceResult ≠ .regular .OutOfFuel`, via
    `DispatcherBodyNoOutOfFuel.of_runResult_not_outOfFuel` and
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_referenceNoOutOfFuel`.
    Checks: `/tmp/evm_reference_noout_wrapper_check1.log`,
    `/tmp/evm_reference_noout_axioms_check1.log`,
    `/tmp/evm_reference_noout_layeraudit_check1.log`.
  - [x] Bundle the remaining source-facing primitive/terminal/expression-result
    and dispatcher-observation assumptions into
    `RecursiveBridgeSemanticContracts`, and expose the concise public wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_semanticContracts`.
    Checks: `/tmp/evm_semantic_contracts_wrapper_check1.log`,
    `/tmp/evm_semantic_contracts_layeraudit_check1.log`.
  - [x] Split the public acceptedness boundary into
    `RecursiveBridgeSourceAccepted` and `RecursiveBridgeCompileResources`, so
    source-language validity and lower stack/frame resource bounds are no
    longer conflated inside one acceptedness package. Public wrapper:
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_splitAccepted`.
    Checks: `/tmp/evm_split_accepted_wrapper_check1.log`,
    `/tmp/evm_split_accepted_layeraudit_check1.log`.
  - [x] Combine Yul checked compilation and assembly resolution into one public
    compiler-success boundary,
    `compileCheckedAssemblyTarget? program = some (asm, target)`, with wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_compiledTarget`.
    Checks: `/tmp/evm_compiled_target_wrapper_check2.log`,
    `/tmp/evm_compiled_target_layeraudit_check2.log`.
  - [x] Bundle target-side gas/external runtime assumptions with canonical
    entry PC and empty-stack requirements as `RecursiveBridgeTargetRuntime`,
    exposed by
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_targetRuntime`.
    Checks: `/tmp/evm_target_runtime_wrapper_check1.log`,
    `/tmp/evm_target_runtime_layeraudit_check1.log`.
  - [x] Bundle the imported Nethermind Yul run result with the sufficient-fuel
    exclusion of the historical successful `.regular .OutOfFuel` marker as
    `RecursiveBridgeSourceRun`, exposed by
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_sourceRun`.
    Checks: `/tmp/evm_source_run_wrapper_check1.log`,
    `/tmp/evm_source_run_layeraudit_check1.log`.
  - [x] Add the final public assumption package
    `RecursiveBridgeTopAssumptions` and bundled theorem
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top`,
    whose fields are source acceptedness, lower compiler resources,
    semantic contracts, initial shared-state relation, source run/resource
    condition, checked compile-and-assemble success, and target runtime/entry
    assumptions. The later preferred no-call/create surface makes the target
    assumptions more explicit and derives the external-call absence fact from
    accepted checked compilation. Checks: `/tmp/evm_top_assumptions_wrapper_check1.log`,
    `/tmp/evm_top_assumptions_layeraudit_check1.log`.
  - [x] Expose the final recursive bridge surface through
    `EvmCompiler.LayerAudit.ImportedYulBoundary`, including
    `recursiveBridgeTopAssumptions`, source/resource/semantic/run/runtime
    assumption packages, checked compile-and-assemble boundary, and the
    remaining current boundary packages. The current default
    `recursiveBridgeTopToGasAwareEVM` alias is the stricter source-compile
    no-call/create sufficient-gas `XStepTrace`/`EVM.X` theorem; alternate
    runtime-bundled and gasless compatibility exports have been removed.
    Checks:
    `/tmp/evm_layeraudit_top_alias_check2.log`,
    `/tmp/evm_top_after_layeraudit_alias_axioms_check1.log`.
- [x] Add/export the program-scoped scoped-primitive-family dispatcher and
  whole-program theorem surfaces, so the final program-recursive bridge feeds
  the bytecode/gas-aware path without a caller-supplied checkpoint-freedom
  premise.

- [x] Align imported `contract.functions.lookup` with the compiled
  `Functions.Source.FunList.find?` callee entry.
- [x] Lift that lookup alignment through the actual `Program.toObjects?`
  root-object lowering.
- [x] Decompose successful imported `EvmYul.Yul.call` user calls into selected
  callee body execution, caller-state restoration, and returned values.
- [x] Decompose successful imported `EvmYul.Yul.execCall` user calls into
  selected callee body execution and final caller-target `multifill`.
- [x] Prove lowering-fuel stability for Yul blocks, so a function body lowered
  with whole-function-list fuel can be reused at the canonical
  `Stmt.List.toBlock?` fuel expected by the recursive block theorem.
- [x] Strengthen the compiled-callee lookup theorem to expose canonical
  `Stmt.List.toBlock?` body-lowering evidence for the selected Nethermind
  function body.
- [x] Relate compiler tower return-variable extraction to imported Yul
  body-state `lookup!` under the recursive body outcome relation.
- [x] Relate imported callee `initcall` state to the compiler tower's
  stack-free `Functions.Source` call-frame initial state, including the
  exact-domain variant required by the recursive body theorem.
- [x] Derive selected-callee param/return no-duplicate and disjointness facts
  from imported contract lookup plus `Safe.NoShadowing.program`.
- [x] Finish the checked source singleton-call block reconstruction helper that
  rebuilds a `Functions.Source.Block.runOpen` singleton call from decomposed
  argument evaluation, selected callee body execution, returned-value lookup,
  and caller-target assignment.
- [x] Build regular user-call continuations for expression statements,
  returned-value assignments, and generated-temporary `let` bindings by
  applying the recursive induction hypothesis to the selected callee body.
- [x] Build terminal user-call continuations for the same call shapes by
  applying the recursive induction hypothesis to callee halts.
- [x] Plug the regular and terminal user-call continuations into the
  `recursiveSourceBridgeWhenUpToAt_succ` user-call cases.
  - [x] Add/export a program-scoped names-aware recursive bridge and
    dispatcher/whole-program theorem route, so the final proof can fix
    `codeOverride` to the executed Yul contract when proving user-function
    calls.
  - [x] Add/export program-scoped callee-body adapters and the
    expression-statement terminal user-call checked wrapper.
  - [x] Add/export program-scoped returned-value assignment and
    generated-temporary `let` terminal checked wrappers.
  - [x] Add/export program-scoped successful user-call source reconstruction
    helpers and checked wrappers for expression-statement, returned-value
    assignment, and generated-temporary `let` call shapes.
  - [x] Add/export source-call reconstruction helpers that consume the bounded
    recursive IH directly for successful no-target user calls and terminal
    user-call callee errors.
  - [x] Add/export the returned-value assignment and generated-temporary `let`
    recursive-IH source-call helpers.
  - [x] Thread the recursive-IH source-call helpers through the checked
    statement wrappers used by the successor constructor.
    - [x] Expression-statement user-call checked wrapper threaded to the
      bounded recursive IH.
    - [x] Returned-value assignment user-call checked wrapper threaded to the
      bounded recursive IH.
    - [x] Generated-temporary `let` user-call checked wrapper threaded to the
      bounded recursive IH.
    - [x] Terminal user-call checked wrappers threaded to the bounded recursive
      IH.
  - [x] Port the successor-facing checked user-call wrappers to the
    accepted-program recursive bridge boundary.
    - [x] Expression-statement actual-or-argument-terminal successor wrappers
      consume `ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames`.
    - [x] Returned-value assignment actual-or-argument-terminal successor
      wrappers consume the accepted recursive bridge.
    - [x] Generated-temporary `let` actual-or-argument-terminal successor
      wrappers consume the accepted recursive bridge.
    - [x] Nested one-result user-call expression terminal preludes for both
      generated-argument and direct-argument lowerings consume the accepted
      recursive bridge.
  - [x] Add/export imported terminal expression-statement user-call
    decomposition from successful argument evaluation to selected callee body
    error.
  - [x] Add/export imported terminal returned-value assignment user-call
    decomposition from successful argument evaluation to the inner `execCall`
    error.
  - [x] Add/export imported generated-temporary `let` user-call
    decompositions from successful argument evaluation to the inner `execCall`
    result/error.
  - [x] Add/export fuel-explicit block-level terminal returned-value
    assignment and generated-temporary `let` user-call decompositions to
    selected callee body errors.
  - [x] Add/export fuel-parametric terminal prelude wrappers for
    returned-value assignment and generated-temporary `let` user calls, so the
    recursive successor can keep imported block fuel separate from argument
    evaluation fuel.
  - [x] Add/export successor-facing terminal returned-call wrappers for
    assignment and generated-temporary `let` that derive selected callee body
    errors from the actual imported caller run plus the successful
    argument-evaluation branch.
  - [x] Restore the focused `EvmCompiler.Yul.RecursiveBridgeSupport` build
    after the newest body-checkpoint/body-domain helper edits.
  - [x] Add/export a source-acceptedness helper deriving successful callee-body
    checkpoint admissibility from `Safe.program`, `ControlFlow.ProgramScoped`,
    function lookup, and the primitive checkpoint contract.
  - [x] Export/audit the checkpoint-only scoped successful-call wrappers for
    expression-statement, returned-value assignment, and generated-temporary
    `let` user calls if they remain useful as an intermediate theorem surface.
  - [x] Add/export imported argument-evaluation splitters for
    expression-statement, returned-value assignment, and generated-temporary
    `let` user-call heads, separating successful argument evaluation from
    argument-side terminal/revert errors.
  - [x] Add/export the source-side terminal argument-prelude interface and
    generic user-call composition theorem, so argument-side halts/reverts
    short-circuit before the generated final call.
  - [x] Add/export the combined generic user-call prelude theorem that consumes
    the imported argument splitters, dispatching to either the regular
    generated call or the terminal argument-prelude short-circuit branch.
  - [x] Add/export the expression-statement user-call combined prelude theorem,
    consuming the imported argument split and terminal argument-prelude
    interface before the final generated call.
  - [x] Add/export the returned-value assignment user-call combined prelude
    theorem, consuming the imported argument split and terminal
    argument-prelude interface before the final generated call.
  - [x] Add/export the generated-temporary `let` user-call combined prelude
    theorem, consuming the imported argument split and terminal
    argument-prelude interface after generated result-slot initialization and
    before the final generated call.
  - [x] Add/export the expression-statement checked user-call wrapper that
    consumes generated/direct regular argument-prelude evidence plus terminal
    argument-prelude evidence, deriving the imported argument split internally.
  - [x] Add/export the returned-value assignment checked user-call wrapper that
    consumes generated/direct regular argument-prelude evidence plus terminal
    argument-prelude evidence, deriving the imported argument split internally.
  - [x] Add/export the generated-temporary `let` checked user-call wrapper that
    consumes generated/direct regular argument-prelude evidence plus terminal
    argument-prelude evidence, deriving the imported argument split internally.
  - [x] Add/export the successor-facing generated-temporary `let` adapter for
    the combined regular-or-argument-terminal checked wrapper.
  - [ ] Prove/instantiate the terminal argument-prelude interface for
    `Expr.List.lowerBound1?` argument preludes, using the recursive IH for
    nested user calls and ruling out nonrelatable direct/pure argument errors.
    - [x] Add/export the compositional induction theorem reducing generated
      `Expr.List.lowerBound1?` terminal argument preludes to regular tail
      pre-exact evidence and single-expression terminal evidence.
    - [x] Add/export the bounded compositional induction variant carrying the
      strict head-expression fuel decrease needed by nested recursive user
      calls.
    - [x] Add/export the cover-aware bounded induction variant, so generated
      argument terminal evidence can be constructed from the actual fresh-state
      coverage carried by checked lowering.
    - [ ] Instantiate the regular tail pre-exact evidence from the generated
      argument prelude/domain-preservation route.
      - [x] Add/export the regular pre-exact adapter for
        `Expr.List.lowerBound1?`, consuming generated regular-prelude evidence
        and the existing eval-args exact-domain preservation interface.
      - [x] Add/export state-level exact-domain preservation for safe imported
        `evalValues`, `eval`, and `evalArgs`, including successful user calls
        and safe primitive families.
      - [x] Add/export safe `Expr.List.lowerBound1?` regular pre-exact
        adapters that consume source safety instead of a per-expression
        exact-domain callback.
      - [x] Thread the safe pre-exact adapter into the successor call-site
        construction of generated argument terminal evidence.
        - [x] Add/export the call-site-facing regular-evidence adapter
          `sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded_safe_covers_regularAt`,
          so the safe pre-exact conversion is derived locally from generated
          regular argument-prelude evidence plus single-expression terminal
          evidence.
        - [x] Add/export the scoped `SourceArgListPreludeRegular` sibling
          `sourceArgListPreludeTerminalAt_of_lowerBound1?_bounded_safe_covers_regular`,
          so expression-statement call sites do not need bespoke `.toAt`
          plumbing.
    - [x] Instantiate the single-expression terminal evidence for generated
      `Expr.lower1?` preludes, using the recursive IH for nested user calls and
      existing nonrelatable direct/pure error exclusion.
      - [x] Add/export the single-expression terminal constructor for
        nonrelatable imported eval errors and the direct-safe expression
        instance.
      - [x] Prove the generated user-call `Expr.lower1?` terminal case,
        splitting argument-side terminal errors from nested callee terminal
        errors and using the recursive IH for the latter.
        - [x] Add/export the imported `eval` splitter for user-call
          expressions, separating argument-evaluation errors from nested
          callee-call errors under `SourceResultRelatable`.
        - [x] Add/export the direct imported `EvmYul.Yul.call` error
          decomposer for selected callee body errors, avoiding an `execCall`
          detour at expression level.
        - [x] Add/export generated variable-argument freshness and
          inserted-result-slot preservation lemmas, so the zero-initialized
          call target can be inserted before the final call without changing
          generated argument reads.
        - [x] Compose the argument-evaluation error branch with
          `SourceArgListPreludeTerminalAt`.
        - [x] Compose the nested callee-call error branch with the existing
          program-recursive terminal user-call reconstruction helper.
        - [x] Add/export the direct-argument user-call expression terminal
          theorem, so direct `Expr.lower1?` user-call paths can use the same
          recursive callee-error bridge without generated argument temporaries.
    - [x] Add/export the expression-statement successor-facing wrapper that
      derives generated argument terminal evidence locally from compositional
      regular suffix evidence plus single-expression terminal evidence.
    - [x] Add/export the returned-assignment and generated-temporary `let`
      successor-facing wrappers with the same locally-derived generated
      argument terminal evidence, so all three user-call statement shapes share
      the same compositional proof boundary.
  - [ ] Add/export a source-domain helper deriving successful callee-body
    return/parameter presence from the function `initcall` layout, safe/scoped
    body execution, and the existing primitive/domain-preservation facts.
    - [x] Add/export a `StoreDomainContains` / `StateStoreContains` facade for
      compositional block-cleanup domain preservation.
    - [x] Prove expression and argument-list domain preservation for safe
      imported Yul expressions using the existing safe primitive-store and
      user-call store-restoration facts.
    - [x] Add/export contains-based return lookup adapters for source stores,
      related source states, regular scoped function bodies, and `leave` scoped
      function bodies.
    - [x] Add/export exact-domain preservation for imported `State.insert`,
      `State.multifill`, and successful user `execCall` assignment into already
      declared targets.
    - [x] Add/export source-variable presence adapters for regular generated
      preludes plus argument evaluation, and the converse
      `checkAssignment`/exact-domain target-declared fact needed by assignment
      user-call successor cases.
    - [x] Add/export the combined assignment-target presence helper that
      consumes imported `checkAssignment`, the exact initial relation, the
      regular generated prelude run, and source argument evaluation.
    - [x] Add/export the source-side `initNames` presence helpers showing that
      generated hidden `let` target slots are present immediately after the
      zero-initializer prefix, including the actual-run-result form.
    - [x] Add/export the direct-argument continuation of that helper through
      source `ArgList.eval`, covering the no-generated-prelude branch for
      generated-temporary `let` user calls.
    - [x] Thread hidden-target presence through the exact generated-temporary
      `let` actual-run prelude theorem, and discharge both direct/no-prelude
      and generated-prelude target-presence branches locally.
    - [x] Prove/export that `Expr.lower1?` and `Expr.List.lowerBound1?`
      generate contains-preserving preludes, then remove that
      generated-prelude evidence from the generated-temporary `let`
      actual/successor wrapper boundary.
    - [x] Add/export statement- and singleton-block-level lemmas exposing
      imported `checkAssignment = .ok ()` for successful or source-relatable
      returned-value user-call executions after successful argument evaluation.
    - [x] Add/export evalArgs/store-containment assignment-target adapters and
      move the actual returned-value assignment user-call wrappers from an
      arbitrary target-presence callback to a source-facing `Safe.exprs args`
      premise, deriving argument-store containment internally.
    - [x] Add/export a function-body soundness wrapper that extracts the exact
      Nethermind return list from `StateStoreContains`, not full exact-domain
      equality.
    - [x] Move successful recursive user-call reconstruction and the
      program-scoped successful checked wrappers onto `StateStoreContains`, with
      older exact-domain callers coercing exactness to contains.
    - [ ] Prove statement/list domain preservation for `Ok` statement-entry
      states through block cleanup, `let`, assignment, expression statements,
      `if`, `switch`, `for`, and structured checkpoints.
      - [x] Add/export the loop/checkpoint substrate needed when Nethermind
        loop recursion re-enters through a checkpoint after post/body control.
      - [x] Add/export generic store-contains execution helper lemmas for
        nil/cons `execSeq`, block cleanup, `let`, assignment, `if`, and
        `switch`.
      - [ ] State the main theorem over the actual `execSeq` continuation
        boundary: statements start from `Ok` states, while `OutOfFuel` and
        checkpoints are terminal/special loop cases rather than generic block
        entries.
      - [ ] Include the block-entry store-scope premise needed for block
        cleanup; the too-broad theorem over arbitrary `OutOfFuel` states is
        intentionally rejected.
    - [ ] Specialize the statement/list theorem to selected safe/scoped
      function bodies starting from `StateStoreDomainExact.initcall_of_length`
      and expose the resulting `StateStoreContains` postcondition.
    - [ ] Export/audit the successful callee-body contains helper and
      confirm axiom prints show only standard Lean axioms.
  - [x] Audit and retire the older program-scoped successful user-call
    store-domain route from the successor path.
    - [x] Remove `hBodyAllowed` from the scoped successful wrappers by deriving
      checkpoint admissibility from source acceptedness.
    - [x] Keep the older `*_bodySound_success` wrappers as backend evidence,
      but route the actual and successor checked wrappers through the
      source-side `*_source_ok` callee-body helpers instead of through public
      `StateStoreContains` / `hBodyDomain` callbacks.
    - [x] Export the `*_source_ok` callee-body helper surface through
      `LayerAudit`.
  - [x] Add/export a combined expression-statement user-call checked wrapper
    that cases on the actual imported singleton-block result and dispatches
    internally to the regular-return wrapper or terminal-callee wrapper,
    ruling out unrelated nonrelatable errors through the `allowed` filter.
  - [x] Add/export the same combined actual-run wrapper for returned-value
    assignment user calls.
  - [x] Add/export the same combined actual-run wrapper for generated-temporary
    `let` user calls.
  - [x] Remove local checkpoint/out-of-fuel exclusion callbacks from the
    combined actual-run wrappers.
  - [ ] Prove the successor statement cases for the three user-call AST shapes,
    using the combined wrappers plus `UserCallArity.StmtOk`, safe/scoped facts,
    argument-prelude soundness, lookup alignment, and source-fuel decrease.
    - [x] Add/export successor-fuel adapters for expression-statement,
      returned-value assignment, and generated-temporary `let` user calls,
      deriving the smaller recursive callee/body fuel bound internally from
      the caller-side singleton-block fuel inequality.
    - [x] Add/export exact-fuel frontier adapters for all three user-call
      statement shapes, including the low-fuel out-of-fuel branches and
      source-scoped productive delegation.
    - [x] Add/export source-facing safe-statement projections for the three
      user-call AST shapes, deriving `Safe.exprs args` and unsupported-name
      rejection from `Safe.stmt` instead of carrying bespoke premises.
    - [x] Tighten the successor-facing user-call wrappers so they consume
      `Safe.stmt` for their exact AST shape, deriving unsupported-name
      rejection and assignment argument safety internally.
    - [x] Add/export `SourceArgListPreludeRegularAllAt` and the three
      user-call successor adapters that consume it, replacing duplicated
      direct/generated argument-premise signatures with one bundled invariant.
    - [x] Add/export regular-success `evalArgs` splitters for append-singleton
      and source-order cons forms, so the generated argument-list regular
      theorem can recurse over argument evaluation without unfolding the Yul
      interpreter at every call site.
    - [x] Add/export the one-value `ExprEvalPreludeSound` boundary for
      argument-list evaluation, keeping it distinct from multi-value
      `ExprValuePreludeSound`.
    - [x] Add/export the source-facing no-overwrite facade
      (`SourceWritesDisjoint` / `SourceVarsAgree`) for generated preludes, so
      the remaining regular generated-argument proof can reason about hidden
      temporary value preservation without a broad public oracle.
    - [x] Prove/export the lowering-specific no-overwrite theorem for
      `Expr.lower1?` / `Expr.List.lowerBound1?` generated preludes from
      freshness.
    - [x] Instantiate regular generated argument-list evidence from the
      lowering-specific no-overwrite theorem.
      - [x] Add/export the write-disjoint regular-run and variable-map replay
        helpers, plus the compositional cons constructor for generated
        argument-list regularity.
      - [x] Prove/export the full `Expr.List.lowerBound1?` induction theorem
        from the cons constructor and single-expression regular evidence.
      - [x] Add/export a bundled `SourceArgListPreludeRegularAllAt`
        constructor that keeps direct-argument evidence local while deriving
        generated-argument regularity from the induction theorem.
  - [ ] Verify the successor block/sequence case can consume those statement
    cases for user-call heads without adding a separate public call/body
    obligation.
    - [x] Add/export the generic `Functions.Source.Block.runOpen`
      append-nonregular theorem, so terminal user-call prefixes can be
      composed with an enclosing lowered tail without executing that tail.
    - [x] Add/export exact-domain adapters for `SourceArgListPreludeRegular`
      and `SourceArgListPreludeRegularAt`, so successful user-call heads can
      feed exact-domain tail proofs once the call-result domain lemma is
      supplied.
  - [x] Export the successor-facing user-call theorem surface through
    `LayerAudit`, run focused support/audit builds, and confirm axiom prints
    show only the standard Lean axioms.
  - [x] Confirm by public-signature grep that the user-call successor path no
    longer exposes callee-body callbacks, replay/call obligations, body-domain
    obligations, or generated compiler evidence as premises.
- [x] Historical duplicate successor/all-bounds/dispatcher/gas-aware checklist
  superseded by the checked top-of-file bridge checklist above. The actual
  public theorem is
  the current source-compile no-call/create sufficient-gas `XStepTrace`/`EVM.X`
  root exported through
  `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM`;
  its preferred source-compile no-call/create assumption package no longer
  exposes recursive bridge evidence, replay or call obligations, generated
  layout evidence, dispatcher certificates, or a caller-supplied external-call
  agreement as public inputs.

1. [x] Stabilize the names-aware bridge-support substrate.
   - [x] Restore the focused bridge-support build after the names-aware
     result-sequence helper ordering repair.
   - [x] Add names-aware fresh/source-name coverage facts for initial compiler
     freshness, contract-name reservations, and dispatcher source names.
   - [x] Add names-aware exact wrappers for empty blocks, empty block
     statements, and abrupt `break` / `continue` / `leave` leaves.
   - [x] Add names-aware exact wrappers for uninitialized `let`, singleton
     `let`, literal/variable initialized `let`, literal/variable assignment,
     and the false empty-`if` checkpoint.
   - [x] Complete the names-aware sequence/block helper layer: nil, regular
     head/tail sequencing, bracketed block closure, abrupt short-circuiting,
     source-name freshness, and compatible-layout result projection.
2. [x] Stabilize primitive and terminal statement wrappers.
   - [x] Add names-aware exact wrappers for terminal hidden-prelude calls,
     covering the `return` / `revert` / `selfdestruct` terminal-prelude path.
   - [x] Prove and export the names-aware wrapper for plain no-argument
     `stop()`.
   - [x] Prove the names-aware successful nonterminal primitive expression/call
     statement wrapper over the hidden regular-sequence bridge.
   - [x] Prove the names-aware primitive call statement wrappers for the
     state-changing zero-result primitive families accepted by the bridge.
3. [x] Add public self-bound wrappers around the still-assumed recursive bridge.
   - [x] Add self-bound dispatcher and whole-program wrappers, so callers no
     longer pass the actual source-fuel bound separately from the recursive
     bridge evidence.
4. [ ] Finish user-function call wrappers and discharge their callee behavior
   through the recursive induction hypothesis.
   - [x] Source-tower regular sequence substrate for no-return-value
     user-function call expression statements.
   - [x] Checked lowerer wrapper for successful no-return-value user-function
     call expression statements.
   - [x] Source-tower regular sequence substrate for returned-value assignment
     from a user-function call.
   - [x] Lowerer-decomposition lemma for returned-value assignment from a
     user-function call.
   - [x] Checked lowerer wrapper for returned-value assignment from a
     user-function call.
   - [x] Lowerer-decomposition lemma for `let` / generated-temporary bindings
     initialized by a user-function call.
   - [x] Checked wrapper for `let` / generated-temporary bindings initialized
     by a user-function call.
   - [x] Compositional source-result bridge for a hidden argument prelude
     followed by a terminal user-function call, so the recursive IH can supply
     callee halts without a separate public call oracle.
   - [x] Checked lowerer wrapper for expression-statement user-function calls
     whose callee terminates.
   - [x] Checked lowerer wrapper for returned-value assignment from a
     user-function call whose callee terminates.
   - [x] Checked lowerer wrapper for `let` / generated-temporary
     user-function calls whose callee terminates.
   - [x] Function-table lookup alignment from Nethermind
     `contract.functions.lookup` through `Contract.functionEntries` and
     `FunctionList.toFunDefs?` to the compiled `Functions.Source.FunList.find?`
     callee body-lowering evidence.
   - [x] Program-level lookup alignment from the actual `Program.toObjects?`
     lowering to the compiled `functionProgram.functions` lookup, reusing the
     checked function-table alignment internally.
   - [x] Imported user-call body decomposition under `some contract`, exposing
     the selected Nethermind function, callee body `exec`, restored caller
     state, and return-value list from a successful `EvmYul.Yul.call`.
   - [x] Imported `execCall` decomposition for successful user calls, exposing
     the same callee body `exec` plus the final `multifill` assignment to
     caller targets.
   - [x] Regular callee behavior discharged through the recursive induction
     hypothesis rather than a public call continuation.
   - [x] No-target expression-statement user calls have an exported checked
     body-soundness wrapper, so this shape no longer takes a bespoke `hCall`
     continuation.
   - [x] Returned-value substrate exposes the exact Nethermind `lookup!`
     return list from recursive body soundness and peels successful assignment
     user-call execution to its underlying `execCall` at the matching fuel.
   - [x] Returned-value assignment user calls now have the exported
     source-level body-soundness continuation theorem, including the
     `assignMany`/`multifill` state relation.
   - [x] Returned-value assignment user calls use the same body-soundness
     continuation style.
   - [x] `let` / generated-temporary user calls use the same body-soundness
     continuation style.
   - [x] Terminal callee behavior discharged through the recursive induction
     hypothesis rather than a public call oracle.
5. [x] Close or explicitly reject any remaining terminal variants not already
   covered by `stop()` or the hidden-prelude `return` / `revert` /
   `selfdestruct` wrappers.
6. [x] State and prove the recursive constructor theorem
   `recursiveSourceBridgeWhenUpToAt_succ`, taking the bridge up to `k` and
   producing the bridge up to `k + 1`.
   - [x] Prove the recursive nil and block-sequence cases from the names-aware
     helper layer.
   - [x] Prove the recursive ordinary statement cases: `let`, assignment,
     expression/call statements, bracketed blocks, and generated temporary
     bindings.
   - [x] Prove the recursive structured-control cases: `if`, `switch`, and
     `for`, including `break`, `continue`, `leave`, regular fallthrough, and
     terminal pass-through.
   - [x] Prove the recursive terminal cases for EVM-level halts: `stop`,
     `return`, `revert`, `selfdestruct`, and the argument-prelude variants.
   - [x] Prove the recursive user-function/call cases, with imported-Yul
     argument evaluation order, source-name freshness, returned-value
     assignment, and terminal callee behavior handled through the induction
     hypothesis.
7. [x] Close the recursive proof bookkeeping.
   - [x] Ensure every recursive use of a subprogram proof is justified by a
     source-fuel decrease.
   - [x] Close the bookkeeping lemmas for fuel inequalities,
     `ctx.scope = layout`, source-name freshness, layout compatibility, code
     override, result relatability, and filtered successful imported runs.
   - [x] Confirm no public callee, statement, callback, replay, layout,
     generated-label, or generated-evidence oracle remains.
8. [x] Prove the all-bounds constructor, e.g.
   `recursiveSourceBridgeWhenUpToAt_all`, producing the recursive bridge for
   any source-fuel bound.
9. [x] Lift the constructed recursive bridge into the dispatcher packages:
   `RecursiveDispatcherBridgeUpTo`, `CheckedRecursiveDispatcherSound`, and the
   checked compile-accepted dispatcher wrapper.
10. [x] Thread the checked dispatcher bridge through assembly, bytecode, and the
    gas-aware EVM theorem.
11. [x] Replace public Yul-to-EVM theorem premises so the top theorem no longer
    accepts `hRecursive`, `RecursiveDispatcherBridgeUpTo`,
    `CheckedRecursiveDispatcherSound`, replay evidence, generated layout
    evidence, or equivalent compiler-generated artifacts as inputs.
12. [x] Run the completion gate: full `lake build EvmCompiler`, targeted
    no-`sorry`/`admit`/new-`axiom` scan, public-signature grep for certificate
    leaks, `LayerAudit` update, and `PROGRESS_LOG.md` audit entry. Full build
    check: `/tmp/evm_full_build_20260524_1627.log`.

## Public Spine

Nethermind Yul reference semantics -> source-complete Yul bridge -> objects/data -> functions -> locals/scopes -> expressions/literals -> structured control -> labeled assembly -> resolved EVM assembly -> encoded bytecode -> gas-aware EVMYulLean `X`

## Completion Target

- [x] Name the exact Nethermind Yul reference semantics used as the source run boundary, currently `EvmYul.Yul.exec` / `EvmYul.Yul.eval` / `EvmYul.Yul.call` / `EvmYul.Yul.primCall` over `EvmYul.Yul.State`.
- [x] Prove a checked theorem from that reference semantics to the compiler source semantics; elaboration through lowering alone is not sufficient. The current public bridge is the checked recursive theorem family culminating in `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top`.
- [ ] Make `Accepted` source-complete for the requested source language. It may reject malformed or semantically invalid programs, but not proof-inconvenient constructs.
- [x] Keep `GAS` and higher-layer `PC` behavior behind explicit oracle/agreement assumptions where source abstractions do not have concrete target byte offsets or exact gas accounting.
- [x] Expose a top theorem whose premises make the gas oracle, external call/create agreement, jumpdest scanner boundary, and possible out-of-gas behavior legible.
- [ ] Replace the source bridge and external call/create agreement assumptions with checked per-construct proofs.
  - [x] Remove the artificial lowerer gap for external call/create primitives:
    `Prim.toBasicOp?` now maps `CREATE`, `CALL`, `CALLCODE`,
    `DELEGATECALL`, `CREATE2`, and `STATICCALL` to the corresponding
    structured/basic EVM opcodes. The accepted bridge still rejects them until
    the open external-call/create and static-mode result contracts are proved.
  - [x] Admit `LOG0` through `LOG4` in `Reference.Safe.primitive` with checked primitive
    contracts for varstore preservation, non-`Ok` state preservation, and
    non-checkpoint/nonrelatable error behavior.
  - [x] Add a checked exact-boundary theorem for `Reference.Safe.primitive`:
    the only remaining excluded primitive families are code-image operations
    (`CODESIZE`, `CODECOPY`, `EXTCODESIZE`, `EXTCODECOPY`, `EXTCODEHASH`) and
    external call/create operations (`CREATE`, `CALL`, `CALLCODE`,
    `DELEGATECALL`, `CREATE2`, `STATICCALL`).
  - [x] Add checked constructors discharging the target-side
    `ExternalInteractionAssumption` when emitted assembly has
    `usesCallCreate = false`, and export the corresponding top-runtime helper
    through `LayerAudit`.
  - [x] Add a checked imported-semantics classification of the remaining
    source primitive boundary: code-image ops plus `CREATE`/`CREATE2` are
    imported-Yul semantics gaps, while `CALL`, `CALLCODE`, `DELEGATECALL`, and
    `STATICCALL` are external-call boundary ops.
- [x] Ensure the public Yul theorem computes its intermediate lowering/checked structured compiler evidence internally via `Yul.Program.compileChecked?`.

## Current Stack

- [x] Import Nethermind EVM/Yul semantics as the shared execution substrate.
- [x] Define labeled assembly over EVM state, with labels replacing concrete PCs and gas omitted from the source semantics.
- [x] Assemble labeled assembly to resolved EVM code and prove whole-program preservation, including the bytecode/gas-aware bridge assumptions.
- [x] Define structured control over the same EVM state and primitive semantics, then compile it to labeled assembly with a composed top theorem.
- [x] Support terminal EVM outcomes across existing layers: `STOP`, `RETURN`, `REVERT`, and `SELFDESTRUCT`.
- [x] Define arity-indexed closed expressions/literals over structured primitives and prove lowering into structured control.
- [x] Structured procedure control has an independent interpreter, checked acceptance/compiler bounds, generated label/token uniqueness checks, and public `Structured.Preservation.compile_preserves` with no public replay/layout/call-preservation certificate.

## Explicit Boundaries

- Gas is not modeled in source layers; the EVM bridge carries explicit sufficient-gas/no-out-of-gas assumptions.
- Program counters and raw jumps are target-level concerns; source layers use labels and structured control. If a higher source layer exposes `PC`, it must be modeled through an explicit PC oracle/agreement premise, not by silently reading a target byte offset.
- `Structured` is still an abstract stack machine, so stack values, stack effects, and stack-shape continuations are legitimate source/proof concepts there. The abstraction introduced at this layer is over raw jumps/labels/PC control transfer, not over the EVM stack itself.
- Procedure return destinations in `Structured` are ghost source state and concrete hidden target stack tokens. The checked relation is `Structured.Preservation.Frame.StateRel`; successful `compileChecked?` now checks the generated dispatch-token and label uniqueness facts used by `Structured.Preservation.compile_preserves`. This is acceptable only as a structured-layer implementation boundary: return-token/frame conventions must not be part of `Locals.Source`, `Functions.Source`, object, or Yul source semantics.
- Structured control labels are tracked through the typed-continuation facade: every generated branch target has a declared symbolic stack shape, every control transfer carries a conformance obligation, `leave` targets the procedure epilogue statically, and dynamic procedure returns use generated symbolic return continuations until the final token/offset encoding proof. This is a lower-boundary proof interface, not a requirement that higher layers expose stack-shaped control.
- `SourceAccepted` names source-side wellformedness/scoping for Expressions, Locals, Functions, Objects, and Yul separately from older `Accepted` predicates that still include lower compiler acceptance. Higher bridge statements should move toward `SourceAccepted` plus explicit compiler-success/lower-accepted premises, rather than hiding lower artifacts inside source acceptance.
- External-facing EVM effects are not all the same boundary: logs, storage, memory, code reads, and terminal selfdestruct already pass through higher layers. The current preferred top theorem uses the no-call/create route: accepted source programs compile to assembly with `usesCallCreate = false`, and `ExternalInteractionAssumption.noCallCreate` discharges the target external-call agreement without a caller-supplied call/create contract. The separate `CallCreateAgreementWithGasAwareRunner` branch remains available only for a future source semantics that admits call/create.
- The bytecode theorem still isolates the EVMYulLean jumpdest scanner behind the `JumpdestCorrect` assumption boundary.

## Layer Sequence

1. [x] Expressions/literals
   - Literals and primitive calls over the existing EVM primitive semantics.
   - Arity/result behavior is explicit from day one, including multi-result expression forms when needed.
   - No identifiers, locals, user functions, or object pseudo-builtins in this layer.
   - Source-facing compile boundary now has `Expressions.Program.compileChecked?` and `compile_preserves_of_compileChecked`, so the public audit spine uses a computed structured-compiler result instead of exposing raw structured compile evidence.
   - Adjacent theorem `Expressions.Program.run_toStructured` lowers expression-aware control into structured control; public theorem `Expressions.Program.compile_preserves` connects expression-aware source runs to the existing EVM bridge.

2. [x] Local variables and scopes
   - Yul-style `let`, assignment, identifier reads, and lexical block scopes.
   - Source environment and target stack layout are related by an explicit environment/stack relation.
   - Current status: syntax, executable direct semantics, `Program.eval_of_run`, lowering, WF transport, expression correctness, cleanup/layout helpers, generic scoped preservation, and composed EVM bridge theorem are checked.
   - Abstraction repair in progress: `Locals.SourceSemantics` introduces a stack-free named-store source interpreter so future higher layers do not depend on layout depths or stack cleanup as part of their source meaning. `Locals.Program.SourceAccepted` now uses `Source.Program.SourceWF`, which separates pure lexical scoping/no-shadowing (`Locals.Lexical`) from source ownership. Raw lower `.code` is lexically scoped if it mentions no names, but rejected by `SourceOwned` and invalid in the stack-free source interpreter; `Source.PrimitiveSemantics` no longer contains a `lowerCode` hook. Scoped block cleanup is now exposed as source-level facts `Block.runScoped_regular_eq_restrict` and `Block.runScoped_regular_drops_not_mem`, and successful regular source statement/open-block runs expose their syntactic `Scope.outEnv` via `Stmt.run_regular_scope` and `Block.runOpen_regular_scope`. `Locals.SourceLowering` now owns checked relation lemmas from that source interface to the existing stack-shaped backend: context handlers to cleanup depths and retained handler scopes, source store to stack layout, expression results as target stack temporaries, source-owned expression execution, source-environment access bounds, scoped-to-source-owned/accessibility conversion, scoped statement bridge wrappers for expression statements, `let`, assignment, and terminal arguments, exact source-run-driven wrappers for ordinary expression/`let`/assignment/break/continue/terminal statement heads, an atomic statement dispatcher, exact source-run-driven open-block head/tail composition including an atomic-head wrapper, scoped-block closure from open-block bridge evidence, source-run-driven block/`if`/`switch` statement wrappers, generic one-result `let` and assignment replay, `break`/`continue` cleanup replay, terminal-with-arguments replay, local insertion, suffix-scope cleanup, and outcome modes. It now also exposes `HandlerScopesEq`, `RunResultRelAt`, `ScopedOutcomeRelAt`, `StmtRunBridgeAt`, and `BlockOpenRunBridgeAt`; the new open-block bridge separates handler-entry context from current lexical context, so structural block proofs can keep abrupt exits tied to source handlers while regular tails extend local scope. The handler-aware bridge now has checked base statement wrappers, exact source-run atomic dispatch, open-block cons drivers, source-run-driven `block`/`if`/`switch` wrappers, and handler-preservation propagation for regular atomic heads, giving the recursive locals theorem a source-run-driven path that does not collapse abrupt exits back to existential target layouts.
   - Structural source-run checkpoint: `Locals.SourceLowering.Structural` defines an explicit locals-source structural subset (`expr`, `let`, assignment, scoped block, `if`, `switch`, `for`, `break`, `continue`, terminal statements), proves it implies source scoping/access bounds, proves regular structural statement and open-block runs preserve installed handler scopes, and proves a recursive source-run-driven `BlockOpenRunBridgeAt`/`StmtRunBridgeAt` theorem that now includes `for`. The loop proof uses a bounded-fuel bridge interface for init/post/body blocks, so nested loop recursion is discharged by Lean's termination checker instead of an opaque arbitrary-fuel callback. Separate checked `runForLoopBridgeAt_of_source_run` and `forStmtRunBridgeAt_of_source_run` wrappers remain available for direct use. Procedure calls, nonempty procedure lists, and procedure-delimited `leave` are intentionally not Locals-source features; they belong to the Functions layer. `Locals.Source.Program.CompileAccepted` is now the source-facing compiler gate: it bundles stack-free `SourceAccepted` with structural/access-bound lowerability, and `SourceWF` separately derives the `Scope.*.Scoped` predicates without claiming that lexical source wellformedness alone proves DUP/SWAP access bounds.
   - Direct compile boundary now has `Locals.Program.compileChecked?` and `compile_preserves_checked`, so the public direct Locals theorem computes expression/structured compiler success instead of exposing raw lowering evidence.
   - Source-owned boundary: `Locals.Source.Program.SourceOwned` intentionally rejects lower-only stack/procedure constructs such as `.call`, `.assignTop`, `.exprs`, `.code`, and nonempty `procs`; those are backend features unless/until an explicit abstract procedure-call interface is added.
   - Public theorem status: `Locals.Program.compile_preserves` composes a direct Locals source run through Expressions/Structured to labeled assembly without taking intermediate lowering evidence as an input.
   - Adjacent theorem lowers scoped statements/expressions into the expressions/structured-control layer.

3. [x] Functions
   - Function declarations, calls, parameters, return variables, multi-return behavior, and `leave`.
   - Current status: syntax, structural WF, scopedness/closedness checks for accepted programs, explicit `Accepted`, independent direct call-frame semantics over function syntax, parameter binding, return initialization, procedure-delimited `leave`, assignment back to caller targets, lower WF transport from source `Program.WF`, and adjacent preservation into the Locals procedure layer are checked.
   - Abstraction repair in progress: `Functions.SourceSemantics` adds a stack-free function source interpreter over named stores, source argument values, fresh function-local environments, return variables, and Yul-like `leave`; stack frames, hidden return tokens, layout depths, cleanup code, and caller-stack reconstruction remain in the direct backend/lowering proof. Function-call target lists are now Yul-like: duplicate targets are invalid in `Source.Stmt.run`, and `Scope.Stmt.Scoped` requires `targets.Nodup`. `Scope.ExprScoped` also rejects raw lower `.code` expressions, so function-source acceptedness cannot smuggle arbitrary structured/stack code through the expression surface. Source-level arity/validity facts `ArgList.eval_length`, `Store.insertMany_length`, `Store.lookupMany_length`, `Store.assignMany_length`, `Store.assignMany_append`, `Store.assignMany_preserves_contains_of_not_mem`, `Store.assignMany_snoc_of_run`, `FunDef.runBody_args_length`, `FunDef.runBody_returned_length`, `Stmt.call_regular_targets_nodup`, `Stmt.call_regular_args_length`, `Stmt.call_regular_targets_length`, bundled `Stmt.call_regular_arities`, `Stmt.call_halt_targets_nodup`, and `Stmt.call_halt_args_length` are checked, and scoped block cleanup is exposed as `Block.runScoped_regular_eq_restrict` and `Block.runScoped_regular_drops_not_mem`, so future proofs can reason about parameters/returns/scopes without target-stack exposure. `Functions.SourceLowering` now owns the first checked source-to-source bridge facts from that clean function semantics into `Locals.Source` for source-owned non-call statements: expression statements, `let`, assignment, break/continue/leave, terminal statements, block statements whose bodies stay in the same source-owned subset, `if` statements whose taken branch is such a block, `switch` statements whose cases/default are such blocks, and `for` loops whose init/post/body blocks stay in the subset. `Functions.SourceLowering.SourceToLocals` now has both the theorem-backed `AtomicSourceOwned` checkpoint and a recursive `SourceOwned` grammar for the whole no-call/no-return-stack subset; `atomic_runOpen_toLocals_of_run`, `atomicList_runOpen_toLocals_of_run`, `atomicBlock_runScoped_toLocals_of_run`, `blockStmt_toLocals_of_run`, `ifStmt_toLocals_of_run`, `switchStmt_toLocals_of_run`, `runForLoop_toLocals_of_run`, and `forStmt_toLocals_of_run` lift the current checkpoint to open/scoped `Locals.Source` block execution and structured statement execution over the real compiler output. Returned-value assignment now uses lower-only `Locals.Stmt.assignTopWithOffset` / `Functions.Direct.assignTopWithOffset`, so multi-return calls assign through the remaining returned-value prefix instead of accidentally treating another returned value as a local. `Functions.SourceDirect` now defines the source-to-direct procedure-backend relation: source scopes are related by name membership/length rather than stack order, break/continue handlers additionally carry retained cleanup-suffix scope evidence via `CleanupScopeRel`, and source `leave` is related to a procedure epilogue cleanup-to-depth-0 with `retc` preserved; `ArgList.eval_argExprs`, `Expr.lit_bridge`, `Expr.var_bridge`, `ReturnValuesRel.pushReturns`, `ReturnedStackRel`, `Cleanup.runCleanupToPreserving_exists`, `Stmt.let_lit_bridge`, `Stmt.let_var_bridge`, `Stmt.assign_lit_bridge`, `Stmt.assign_var_bridge`, `Stmt.brk_bridge`, `Stmt.cont_bridge`, and `Stmt.leave_bridge` are checked operational bridges over that relation. `Functions.SourceDirect.StmtOutcomeRel` now packages regular/break/continue/halt outcomes and treats `leave` via returned values instead of a live local-stack relation; the existing expression/let/assignment/break/continue/leave/call/terminal bridge pieces have wrappers into that relation, and all leaf/call component cases now also expose `StmtRunResultRel` wrappers for recursive block proof use. Call lowering now uses `Lower.argExprs` plus one offset-aware `Locals.Stmt.exprs`/`Direct.evalArgs` evaluation, so later argument expressions read through the correct local-stack offset after earlier argument values have been pushed; `ArgList.eval_argExprs` proves the compiler prelude has the same stack-free source values as source argument evaluation whenever source `evalOne` succeeds. Terminal statement cases now share the explicit `PrimitiveSound.terminal_step` / `terminal_step_exists` contract, with `Stmt.terminal_stmtOutcome_bridge` and `terminalArgs_stmtOutcome_bridge` joining the same leave-aware outcome relation. `StmtRunResultRel` distinguishes regular follow-on state from early exits; `BlockOpenResultRel` now does the same for open blocks, so regular block fallthrough carries the actual returned target layout while early exits retain a flexible handler/terminal layout. Checked nil, regular-head/tail, nonregular-head, statement-result-driven regular/nonregular cons wrappers, a generic existential statement-result cons driver, exact `CleanupLayoutRel`, and regular/nonregular scoped-block statement wrappers give the recursive theorem a compositional block boundary. `RecursiveCallbacksUpTo.all_upTo`, `RecursiveCallbacks.constructed`, `runState_toDirect_exists`, and `run_toDirect_exists` now discharge recursive loops and function calls by source fuel induction, so the public source/direct theorem no longer takes a callee-or-callback oracle. Nonempty-return `leave` is packaged through the returned-stack relation without exposing the concrete return-token stack to higher source interpreters.
   - Source-facing compile boundary: `Functions.Source.Program.runState_toDirect_exists_of_compileAccepted`, `run_toDirect_exists_of_compileAccepted`, `compileChecked?`, and `compile_preserves_checked_of_compileAccepted` now mirror Locals, so public function preservation consumes `Functions.Source.Program.CompileAccepted` rather than raw scopedness and frame-bound premises. The older raw theorem remains only a lower proof helper.
   - Direct compile boundary now has `Functions.Program.compileChecked?` and `compile_preserves_checked`, so the public direct Functions theorem computes Locals/Expressions/Structured compiler success instead of exposing raw lowering evidence.
   - Public theorem status: `Functions.Program.compile_preserves` composes a direct Functions source run through Locals/Expressions/Structured to labeled assembly without taking intermediate lowering evidence as an input.
   - Adjacent theorem lowers function bodies/calls into the locals/scopes layer.

4. [x] Objects
   - Yul objects, code sections, data sections, and object-level namespace behavior.
   - Pseudo-builtins such as `datasize`, `dataoffset`, and `datacopy` are proved or named as explicit assumptions.
   - Current status: object/data syntax, recursive object WF, direct root-object interpreter over `Object.mk`, checked `run_toFunctions`/`eval_toFunctions` connection to the call-capable Functions layer, explicit acceptance, and composed accepted-object-to-EVM bridge theorems are checked.
   - Abstraction repair in progress: `Objects.SourceSemantics` is now the source-facing transparent object adapter over `Functions.Source`, so root-object execution no longer has to inherit the direct function stack-frame interpreter at the semantic boundary.
   - Source-facing compile boundary: `Objects.Source.Program.compileChecked?` and `compile_preserves_checked_of_compileAccepted` now mirror the lower layers, so public object preservation consumes `Objects.Source.Program.CompileAccepted` rather than raw function-frame bounds. The older raw-frame-bound theorem remains only a lower proof helper.
   - Direct compile boundary now has `Objects.Program.compileChecked?` and `compile_preserves_checked`, so the public direct Objects theorem computes Functions/Locals/Expressions/Structured compiler success instead of exposing raw lowering evidence.
   - Accepted boundary: data sections and nested objects are carried and checked structurally but are not yet addressable from code; object pseudo-builtins are rejected by the Yul accepted-fragment predicate.
   - Beyond accepted subset: model and lower `datasize`, `dataoffset`, and `datacopy`.
   - Adjacent theorem lowers object structure into the function layer plus bytecode/data boundary.

5. [ ] Remaining Yul surface
   - Parser-facing AST alignment and any remaining Yul constructs.
   - Unsupported or implementation-defined features are rejected by acceptance or carried as explicit assumptions.
   - Current status: `EvmCompiler.Yul` imports Nethermind `EvmYul.Yul.Ast`, defines an explicit `Program.Supported` accepted-fragment predicate, lowers accepted contracts to the object layer, and exposes composed compiler-facing bridge theorems. `Yul.Program.run` is now the independent imported Nethermind-Yul `callDispatcher` source interpreter; the old lowering-defined execution is quarantined as `Yul.Lowered.run`.
   - Solidity front-half checkpoint: `scripts/solidity_to_yul_lean.py` invokes `solc --standard-json`, imports solc's Yul JSON AST structurally, emits bridge JSON or typed `EvmCompiler.Solidity.Frontend.Program`, accepts normalized bridge JSON back via `--input-format bridge-json`, documents that bridge contract with `scripts/bridge-json-v3.schema.json`, can persist creation/runtime bridge files with `--bridge-json-dir`, and provides conversions into the current `EvmCompiler.Yul.Program` backend entrypoint plus an object-preserving `EvmCompiler.Objects.Program` path. `EvmCompiler.Solidity.BridgeJson` decodes the normalized bridge JSON inside Lean, so the executable bytecode/artifact paths now keep solc-facing AST normalization in Python, write a temporary normalized-JSON sidecar, and hand Lean only that sidecar path before backend compilation; constructor-style `lean-ir` emission remains available for inspection. Generated Lean modules now expose both the checked backend handoff artifacts (`Yul.Program.compileChecked?`, `Assembly.compile?`, and encoded bytecode) and executable unchecked backend artifacts (`Program.compileUnchecked?` / `Program.bytecodeUnchecked?`) for the typed front-end path. The script also has `--format bytecode`, which asks Lean to compute `Program.bytecodeImageUnchecked?`: a code image with object/data pseudo-builtins resolved from this backend's emitted byte lengths and with child-object/data payload bytes appended. Runtime objects and creation objects can now emit bytecode hex from Solidity/Yul AST input without solc byte offsets. The typed front-end IR preserves data sections structurally as `DataSection` records with optional names and byte payloads instead of anonymous hex strings, records solc's mixed child-object/data payload order with `ObjectItemRef`, computes named local data-section `datasize` from those typed bytes, computes local named `dataoffset` from the emitted code image base and ordered payload stream, resolves child object `datasize`/`dataoffset` from recursively emitted child images, lowers `datacopy` to backend `codecopy`, and handles immutable placeholders in the executable image path by marker-computing Lean byte offsets for `loadimmutable` sites and expanding creation `setimmutable` patches to `mstore`. The executable smoke surface now includes dynamic calldata bytes/strings, `uint256[]` ABI round trips, environmental primitive reads, Solidity loops through solc's helper Yul, and memory struct allocation/field access through solc's memory helpers. The object-preserving path carries typed data sections and nested objects into the backend object layer, while still lowering each object's code through the existing Yul bridge. The checked object/data path now gates through solc-style validation, checked function compilation, computed payload layout, immutable patching, target bytecode encoding, and the public code-image bridge relation.
   - Abstraction repair in progress: `Yul.SourceLowered.runState` is the compiler-facing lowering path into the repaired source tower (`Objects.Source` -> `Functions.Source` -> `Locals.Source`) so the imported-Yul bridge has a clean target that does not expose stack layouts or function return-frame conventions.
   - Target reference version: Lake pins `EvmYulLean` to the corrected fork branch `codex/solidity-switch-semantics` at `2cf8181c562abca3e35c600c9514e35c46260d46`, which includes selected-branch switch semantics, omitted-default-as-empty-block notation, and halting `SELFDESTRUCT` behavior.
   - Recursive theorem target: `SourceBridgeFacts.CheckedBlockLoweringSound` names the fuel-induction goal from checked Yul block lowering to `SourceResultBlockSound`; `SourceBridgeFacts.CheckedStmtBlockLoweringSound` names the single-statement version keyed to the actual `Stmt.toFunctionsList?` head/dispatcher lowerer; `SourceBridgeFacts.FreshCoversLayout` plus the fresh-aware `CheckedBlockLoweringSoundFresh` / `CheckedStmtBlockLoweringSoundFresh` variants capture the invariant that compiler-generated temporaries are fresh for the current source layout; `SourceBridgeFacts.CheckedDispatcherLoweringSound` is the root-dispatcher companion shaped around the exact `Stmt.toFunctionsList?` body equation produced by `Program.toObjects?`; and `Yul.Program.DispatcherSourceSound` bundles the dispatcher body soundness and result projection for the public source/assembly/bytecode wrappers. `checkedStmtBlockLoweringSound_stop_call` consumes real lowerer output for the no-temporary terminal target, and `checkedStmtBlockLoweringSoundFresh_selfdestruct_lit_call`, `checkedStmtBlockLoweringSoundFresh_return_lit_lit_call`, and `checkedStmtBlockLoweringSoundFresh_revert_lit_lit_call` consume real lowerer output plus the fresh-state/layout invariant for generated terminal preludes. `checkedDispatcherLoweringSound_of_stmtBlockLoweringSound` and `checkedDispatcherLoweringSound_of_stmtBlockLoweringSoundFresh` lift the single-statement theorem to the dispatcher theorem; `checkedDispatcherLoweringSound_selfdestruct_lit_call`, `checkedDispatcherLoweringSound_return_lit_lit_call`, and `checkedDispatcherLoweringSound_revert_lit_lit_call` package the generated-prelude literal terminal cases at the dispatcher boundary from only the dispatcher-shape equation, initial-scope equation, and terminal/revert contracts. The matching checked-spine assembly wrappers `compile_preserves_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted`, `compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted`, and `compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted` now route through those checked dispatcher constructors and generic result adapters instead of the older generated-prelude decomposition proof; the checked-spine bytecode/gas-aware wrappers `compile_whole_program_result_sound_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted`, `compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted`, and `compile_whole_program_result_sound_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted` compose the same checked assembly facts through the bytecode theorem. `LayerAudit` points the default assembly and bytecode aliases for those cases at the checked-spine wrappers while keeping older raw/compositional routes under explicit names. `Yul.Program.dispatcherSourceSound_of_checked_dispatcher_lowering` recovers the actual compiled dispatcher body from `toObjects?`, and `sourceBridge_of_checked_dispatcher_lowering_sound` plus the matching assembly/bytecode wrappers consume the checked dispatcher-lowering theorem target directly. `Reference.Imported.exists_exec_dispatcher_of_runResult_succ_ok`, `Yul.Program.DispatcherRunResultSound`, and `Yul.Program.DispatcherObservationSound` lift that boundary to the real imported `Reference.runResult`, with source-bridge/assembly/bytecode wrappers starting from a successful imported run plus ordinary/terminal/revert observation contracts instead of a raw dispatcher-body `exec` or prebuilt result adapter. This is the intended boundary for the full imported-Yul recursive proof: callers should not pass independent body/result callbacks once the checked constructor exists.
   - Imported-Yul argument order is now separated from lower stack-order primitive evaluation by `ExprArgStackPreludeSound`, `PrimitiveStackSoundAt`, and `exprValuePreludeSound_prim_of_arg_stack_prelude`: generated preludes can be proved once in the source tower, while per-primitive lemmas state only the named source-order-to-stack-order semantic contract. Zero-result state-changing primitives now have reusable binary/ternary contract constructors and concrete wrappers for `mstore`, `mstore8`, `mcopy`, `calldatacopy`, and `returndatacopy`, so higher bridge proofs do not expose the relation plumbing for those families. Terminal prelude composition now has the same source-facing shape via `generatedPrelude_runOpen_append_exists`, `sourceResultBlockRunBridge_terminalStackPrelude_of_exec`, `sourceResultBlockRunBridge_terminalStackPrelude_of_arg_sound`, and the public `SourceResultBlockSound` lift `sourceResultBlockSound_terminalStackPrelude_of_arg_sound`; `sourceResultBlockSound_selfdestruct_lit_prelude_call_compositional`, `sourceResultBlockSound_return_lit_lit_prelude_call_compositional`, and `sourceResultBlockSound_revert_lit_lit_prelude_call_compositional` are the first concrete terminal-prelude theorems routed through that wrapper. The clean `return(offset, size)`, `revert(offset, size)`, and `selfdestruct(recipient)` paths now also reach compositional dispatcher `SourceBridge`, assembly compile-preserves, and bytecode/gas-aware wrapper theorems.
   - Accepted compiler-facing subset currently includes literals, variables, primitive calls that map to the verified structured primitive surface including `gas`, blocks, lets, switches, optimizer-style `for`, break/continue/leave, user-function declarations, statement-level user calls, and one-result user-call expressions lowered through fresh temporaries.
   - Accepted imported-reference bridge subset is still narrower at the proof boundary: it rejects external account-code inspection and external-call/create primitives in `Reference.Safe` until the corresponding state/result relations are proved against the imported reference semantics. Local code-image primitives (`CODESIZE`/`CODECOPY`) are admitted through the explicit `codeBytes` relation. `RETURN`, `REVERT`, and `SELFDESTRUCT` are accepted at the safe-boundary; concrete dispatcher terminal coverage now reaches the gas-aware bytecode theorem for `stop()`, zero/literal `return`/`revert`, writable `selfdestruct(0)`, and the generated-prelude literal-argument terminal variants, with auto wrappers deriving generated temporary names, fresh-name distinctness, and literal argument lowerer evidence from compiler output.
   - Rejected by accepted lowering for now: external call/create builtins, unresolved object pseudo-builtins outside the computed object/data frontend path, and any construct that fails lower-layer WF or bounded inline expansion.
   - Public theorem status: `Yul.Program.compile_preserves_checked` still records the quarantined compiler-facing `Yul.Lowered.run` path, while `Yul.Program.compile_source_preserves_checked_of_compileAccepted`, `Yul.Program.compile_preserves_of_reference_source_runs_compileAccepted`, and `Yul.Program.compile_whole_program_result_sound_of_reference_source_runs_compileAccepted` are the active source-facing route through `Yul.SourceLowered.run`. `Reference.SourceBridge` / `Reference.LoweredBridge` remain legacy compatibility surfaces and are not the intended public imported-source spine.

## Source-Complete Repair Plan

1. [ ] Lower primitive boundary
   - [x] Add explicit gas oracle/agreement interface above assembly and admit `GAS` through the lower primitive/Yul path.
   - [ ] Add explicit PC oracle interface if a higher source layer exposes EVM `PC`.
   - [x] Add the locals-lowering primitive contract and source-owned expression result-length/accessibility substrate (`PrimitiveSound`, `Expr.Accessible`, `ExprSeq.Accessible`, `StackPrefixRel`) needed to prove generic expression-prefix lowering without exposing stack slots in source semantics.
   - [x] Extend that primitive contract to terminal halts via `PrimitiveSound.terminal_step` / `terminal_step_exists`, so source `prim.terminal` facts can be connected to `Structured.Terminal.step` inside the function source/direct proof instead of becoming public assumptions.
   - Add checked structured-source support for the call/create family or an explicit semantic-family bridge to the imported gas-aware EVM operation semantics.
   - [x] Add terminal-with-arguments plumbing so `return`, `revert`, and `selfdestruct` evaluate arguments and then halt with the matching EVM/Yul behavior.

2. [ ] Functions
   - [x] Replace bounded inlining-as-source-semantics with independent direct function-call semantics over `Functions.Program`.
   - [x] Implement `leave` as a real function-scope control effect and prove it lowers to the chosen function exit representation.
   - [x] Support nested one-result user-call expressions by hoisting them into fresh temporaries and statement-level calls with Yul argument evaluation order.
   - [x] Prove the returned-value assignment bridge shape: duplicate-free source `assignMany` can be replayed in reverse order, and `Functions.SourceDirect.Assignment.assignReturnedTops_source_order` consumes the backend's returned-value stack prefix while concluding the original source named store.
   - [x] Tighten function scoping so parameter/return signatures are source-level `Nodup`, and expose checked helpers that turn source target membership plus frame accessibility into assignment-target stack indices.
   - [x] Package call-frame entry/exit facts: source parameter binding relates to the direct callee entry stack, direct return-variable initialization reaches the body context, regular return epilogues push/clean return values, and returned stacks pop/attach to the caller frame.
   - [x] Package caller-side call completion: returned callees pop/attach the hidden frame and assign returned values back to source targets, while terminal callees preserve only the terminal shared-state observation.
   - [x] Add a compositional open-block result relation and nil/cons wrappers so the recursive statement theorem can compose regular tails and nonregular early exits without fused per-construct proofs.
   - [x] Add `StmtRunResultRel`, separating regular follow-on state/layout from early-exit outcomes, and route regular tail composition plus nonregular block short-circuiting through it.
   - [x] Lift existing non-call leaf statement bridges (`expr`, `let`, assignment, `break`, `continue`, `leave`, terminals) into `StmtRunResultRel`.
   - [x] Lift returned and terminal call component bridges into `StmtRunResultRel`; these still carry local body-run premises to be discharged by the recursive induction, not exposed publicly.
   - [x] Lift returned and terminal call component bridges into `StmtRunBridge`, keeping calls on the same recursive statement boundary as leaves, structured control, and loops.
   - [x] Add a generic existential block-cons driver over `StmtRunResultRel`, so the recursive block induction can consume one head/tail interface.
   - [x] Tighten `BlockOpenResultRel` so regular fallthrough carries the concrete returned target layout, and add exact cleanup-layout regular/nonregular scoped-block wrappers.
   - [x] Add the one-result condition bridge plus `if` statement-result wrappers for false conditions, regular true bodies, and nonregular true bodies.
   - [x] Add the scrutinee pop bridge, source/direct switch-selection equality, and `switch` statement-result wrappers for no selected body, regular selected bodies, and nonregular selected bodies.
   - [x] Add the first loop bridge substrate: source-store restriction over same-scope layouts, false-condition `runForLoop`, and regular `for` completion through exact target cleanup.
   - [x] Add true-condition loop body-exit wrappers for body `break`, `leave`, and terminal `halt`.
   - [x] Tighten full-`for` pass-through to `leave`/terminal `halt`; loop-level `break` and `continue` remain consumed or invalid at the source/direct statement boundary.
   - [x] Add generic post-step loop wrappers: body regular/continue followed by post `leave`/halt, and body regular/continue followed by regular post plus recursive loop replay.
   - [x] Add the initializer early-exit `for` wrapper for init-block `leave`/terminal `halt`, using the same nonregular block-result relation as statement-list short-circuiting.
   - [x] Add a function source/direct-owned classifier that admits calls and nonempty-return `leave` while still rejecting raw lower `.code` expressions, and prove ordinary source scopedness implies it.
   - [x] Package statement and open-block preservation as `StmtRunBridge` / `BlockOpenRunBridge`, with nil and cons drivers that expose the regular tail relation only when the head statement falls through.
   - [x] Lift the existing leaf statement result facts (`expr`, `let`, assignment, `break`, `continue`, `leave`, and terminal statements) into `StmtRunBridge` constructors.
   - [x] Lift the existing structured statement result facts (`if`, `switch`, and full `for` completion/pass-through cases) into `StmtRunBridge` constructors.
   - [x] Tighten function source scoping so `let` names are fresh in the visible source scope, matching the no-shadowing Yul bridge boundary and the direct layout invariant.
   - [x] Add scoped ordinary-statement bridge constructors: expression, `let`, and assignment cases now consume source scoping directly, with assignment target slots derived from `CtxRel` instead of supplied as ad hoc witnesses.
   - [x] Derive lower expression accessibility from source scoping plus a syntactic access-width bound, so ordinary scoped statement bridges no longer take raw `Accessible` proof witnesses.
   - [x] Extend that scoped/access-width interface to terminal-argument statements, false `if`, and no-match `switch`, so these bridge constructors no longer take raw lower expression ownership/accessibility witnesses.
   - [x] Add continuation-style scoped true-`if` and selected-`switch` bridge constructors: condition/scrutinee target execution is derived before invoking the body bridge, so recursive branch proofs receive related source/direct states instead of threading target replay facts.
   - [x] Add a scoped/access-width false-loop-condition wrapper, deriving the direct loop guard execution internally for the recursive loop base case.
   - [x] Factor loop guard replay as `runForLoop_condition_bridge_from_scoped` and use it for true-condition body `break`/`leave`/terminal halt wrappers, so those loop exits now take body bridge continuations over related states instead of target guard witnesses.
   - [x] Add scoped-condition continuation wrappers for the recursive loop post-step cases, covering body regular/continue followed by post `leave`/halt and body regular/continue followed by regular post plus recursive loop replay.
   - [x] Add a block-statement bridge eliminator over `BlockOpenRunBridge`, so recursive statement preservation can consume an open-block bridge and handle regular scoped cleanup/nonregular short-circuiting internally.
   - [x] Bundle regular block cleanup layout into `BlockOpenRunBridgeWithLayout`, so callers consume one open-block preservation interface instead of a separate target-layout witness.
   - [x] Add `StmtRunBridgeWithLayout` and a bundled block-cons driver, so regular head/tail layout cleanup composes structurally via `CleanupLayoutRel.trans`.
   - [x] Lift ordinary leaf statements and call component bridges into `StmtRunBridgeWithLayout`, keeping regular layout preservation and nonregular impossibility inside the source/direct proof boundary.
   - [x] Lift block, `if`, `switch`, and full-`for` statement bridge endpoints into `StmtRunBridgeWithLayout`, so structured-control heads share the same cleanup/layout interface as ordinary leaves.
   - [x] Add source-run-driven `StmtRunBridgeWithLayout` entry lemmas for ordinary heads (`expr`, `let`, assignment, `break`, `continue`, `leave`, and terminal statements), so block induction can consume source execution facts without replaying source evaluator cases at every call site.
   - [x] Add source-run-driven `StmtRunBridgeWithLayout` entry lemmas for `if` and `switch` heads. These destruct the independent source run for the condition/scrutinee once, then invoke branch/body bridge continuations over the related post-expression states.
   - [x] Add exact-source block/`if`/`switch` bridge variants that pass the concrete source open-block run into the body continuation, so recursive preservation can invoke the induction hypothesis on actual source evidence instead of a total body oracle.
   - [x] Add source-run-driven `StmtRunBridgeWithLayout` entry lemmas for block and `for` heads. The `for` wrapper consumes a bundled initializer bridge, a loop-preservation continuation, and discharges source-invalid initializer/loop `break`/`continue` cases inside the proof.
   - [x] Add an exact-source `for` wrapper whose loop-preservation continuation receives the concrete source `runForLoop` fact after a regular initializer, matching the source-evidence boundary used by block/`if`/`switch`.
   - [x] Add an exact-source `runForLoop` wrapper whose body, post, and recursive-loop continuations consume the actual source run fragments for that iteration, eliminating the loop-step replay oracle at this proof boundary.
   - [x] Derive function-call argument preludes from source call scoping plus a syntactic access-width bound, replacing the raw lower `ExprSeq.Accessible` witness at this call-proof boundary.
   - [x] Add a source-run-driven `StmtRunBridgeWithLayout` entry lemma for function-call heads, leaving only returned/terminal callee preservation as local continuations for the recursive induction.
   - [x] Add source open-block cons decomposition, so recursive block preservation can recover the head statement run and regular-tail source run without repeatedly unfolding `Source.Block.runOpen`.
   - [x] Add exact-source eliminators for statement/open-block bridge packages and a source-run-aware open-block cons driver, so block recursion can pass exact source tail runs into the recursive hypothesis.
   - [x] Add a source-run-driven open-block recursion driver over a statement callback, so the final recursive theorem can be organized as one statement preservation callback plus structural block traversal.
   - [x] Add source-shaped selected-switch projections for scopedness and frame bounds, so recursive statement preservation can recover selected branch invariants from source `Switch.select` evidence instead of target-layout witnesses.
   - [x] Add regular-head source context transport facts for `leaveScope?`, scope `Nodup`, return-scope containment, and return variables in scope, so recursive block tails can re-establish source invariants without exposing target frame details.
   - [x] Bundle statement and block source proof obligations as `SourceInvariant.Stmt` / `SourceInvariant.Block`, with checked head and regular-tail projections for recursive block preservation.
   - [x] Add a source-invariant statement dispatcher, covering all function-source statement constructors from exact source runs and source-shaped invariants while keeping nested blocks, loop recursion, and callee bodies as explicit recursive hooks.
   - [x] Add a source-invariant open-block driver that recurses through exact source runs and uses the regular head run to transport `SourceInvariant.Block` to the tail.
   - [x] Compose the invariant open-block driver with the source-invariant statement dispatcher, so block preservation now exposes recursive block, loop, and callee-body hooks rather than a per-statement callback.
   - [x] Close that source-invariant block dispatcher through scoped block execution with `BlockScopedOutcomeRel`: regular fallthrough is related at the scoped block input layout, while nonregular exits keep their explicit handler/terminal layout instead of smuggling in an invalid block-input layout assumption.
   - [x] Add safe scoped-outcome extractors and current-scope `break`/`continue` bridges, preparing the loop-body specialization where handler scopes are exactly the loop layout rather than arbitrary outer continuations.
   - [x] Add regular open-block source transport for leave-scope, return-scope, and return variables in scope, so loop initializer proofs can produce post/body source invariants without reaching into target layouts.
   - [x] Add source-invariant projections for `for` post/body after a regular initializer, eliminating another manual reconstruction point in the upcoming loop theorem.
   - [x] Add `LoopStmtRunResultRel` / `LoopStmtRunBridgeWithLayout`, a current-loop statement preservation package that pins `break`/`continue` to the loop layout while converting back to the ordinary statement bridge for non-loop consumers.
   - [x] Add `LoopBlockOpenResultRel` / `LoopBlockOpenRunBridgeWithLayout`, the current-loop open-block package needed for structural body induction.
   - [x] Add a source-invariant current-loop statement dispatcher, so loop-body statement preservation consumes source invariants plus handler-depth facts and keeps cleanup/layout evidence in the function lowering proof.
   - [x] Add regular-head source transport for `breakScope?` and `continueScope?`, then compose the current-loop dispatcher into the loop-body open/scoped block theorem.
   - [x] Use the loop-body open/scoped dispatcher to discharge the body hook in the exact-source `runForLoop` theorem, then continue the source/direct function recursion.
   - [x] Use ordinary block dispatch to discharge the post hook in the exact-source `runForLoop` theorem.
   - [x] Thread the body/post-dispatched loop theorem into a `for` statement bridge boundary that preserves the regular-initializer proof supplying post/body source invariants.
   - [x] Add upgraded statement/open-block/scoped-block dispatcher wrappers that route `for` through the body/post-dispatched loop theorem without circular definition ordering.
- [x] Add a fuel-induction loop theorem and route the `for` statement bridge through it, so self-recursive loop replay is discharged where the post/body source invariants are in scope.
- [x] Add no-thin-loop statement/open-block/scoped-block dispatcher wrappers whose recursion boundary is an invariant-carrying `for` statement bridge rather than a raw `runForLoop` callback.
- [x] Add current-loop no-thin-loop statement/open-block/scoped-block dispatcher wrappers, preserving loop-specific `break`/`continue` handling while routing nested `for` through an invariant-carrying statement bridge.
- [x] Add callback-driven loop/`for` theorem variants after the block callback wrappers, so body, post, self-recursive loop, and full `for` preservation can use the invariant-carrying `for` callback instead of the old thin nested-loop hook.
- [x] Add callback-dispatcher statement/open-block/scoped-block replacements that construct concrete `for` preservation through the callback loop theorem family while keeping nested `for` recursion as the invariant-carrying statement callback.
- [x] Add callee-body source-invariant recovery from function lookup and whole-program invariants, then package ordinary block, current-loop block, invariant-carrying `for`, and callee-body preservation as `RecursiveCallbacks`.
- [x] Add fuel-bounded recursive callback interfaces (`RecursiveCallbacksUpTo`) with zero-fuel base, monotonicity, unbounded/bounded adapters, and bounded ordinary open/scoped block structural preservation.
- [x] Thread fuel bounds through the ordinary statement dispatcher and ordinary open/scoped block dispatcher wrappers.
- [x] Thread fuel bounds through the active-loop structural induction, active-loop statement dispatcher, and active-loop open/scoped block dispatcher wrappers.
- [x] Thread fuel bounds through the callback-driven `for` bridge family and callee-body callback path.
- [x] Construct `RecursiveCallbacks` by source-fuel/evaluation induction, then remove recursive callback evidence from the active public function source/direct theorem path.
- [x] Use the recursive callback facade in the source/direct function induction so `for` and function calls no longer depend on older loop/callee callback boundaries.
   - [x] Derive returned-value stack evidence from source `lookupMany` plus explicit accessibility, and add function-body returned/terminal call bridges over `BlockOpenRunBridgeWithLayout`; returned and halted callee preservation can now be driven by the recursive body bridge instead of a public stack/return-token oracle.
   - [x] Add call-prelude adapters `FunDef.returned_runBody_from_body_bridge_with_layout` and `halted_runBody_from_body_bridge_with_layout`, which decompose source `runBody`, prepare the direct call frame, and invoke a recursive `BlockOpenRunBridgeWithLayout` continuation to produce the direct returned/terminal callee run.
   - [x] Add function-list lookup facts for scoped/source-owned callees and `ReturnValuesRel.accessible_of_ctxRel`, so recursive call preservation can recover callee body invariants and return-variable access from whole-program/context facts rather than raw witnesses.
   - [x] Add `FrameBound`, a source-scope-shaped compiler resource predicate for function lowering, plus checked projections for call argument access, call return assignment bounds, callee lookup, and `leave` return-value accessibility. This packages EVM stack-width obligations without exposing target stack slots or layouts to higher source interpreters.
   - [x] Add `ReturnValuesRel.lookupMany_exists_of_accessible`, `exists_of_stateRel_accessible`, and `Stmt.leave_stmtRunBridge_from_source_run_frameBound`, so the recursive `leave` case derives return-value stack evidence from `StateRel` plus source-shaped `FrameBound` instead of taking a raw `ReturnValuesRel` witness.
   - [x] Add regular-tail invariant transport: `SameScope` now preserves `Nodup`, `CtxRel` derives target-layout `Nodup` from source scope `Nodup`, `SourceScope` proves scoped `outEnv` preserves freshness and existing-name membership, and `FrameBound.StmtList` has head/tail projections. This prepares the recursive block theorem to recover tail invariants from source scopedness/resource facts.
   - [x] Add `ReturnValuesRel.safe_of_ctxRel`, bundling target-layout freshness plus return-variable accessibility from source scope freshness, return-name membership, and a source-shaped width bound.
   - [x] Replace the internal `hRegularSafe` callback in returned function-body bridges with checked source-shaped regular-exit facts: `SourceRun.block_runOpen_regular_scope`, strengthened `FrameBound.FunDef`, and `FrameBound.funDef_regular_return_safe`.
   - [x] Add program-lookup wrappers for returned/halted callee body bridges, deriving per-callee scopedness and `FrameBound.FunDef` from whole-function-list facts instead of requiring per-call callee invariants.
   - [x] Add a program-level source-run-driven function-call wrapper, deriving returned/halted callee preservation from whole-program scopedness, whole-program frame bounds, and a recursive body bridge instead of a per-call callee oracle.
   - [x] Discharge the remaining recursive source-to-direct call theorem by induction on source fuel/evaluation, using the returned/terminal call parts and `PrimitiveSound` rather than a public callee oracle.
   - Support source-complete multi-return call behavior against the Nethermind interpreter bridge.

3. [ ] Objects/data
   - [x] Define backend object layout/image helpers for executable code, child-object payloads, and data sections (`EvmCompiler.Objects.Layout`).
   - [x] Add checked typed-Yul front-end rewrites showing `datasize` and `dataoffset` become Yul literals, and `datacopy` becomes the Yul/EVM `codecopy` primitive after argument resolution.
   - [x] Prove typed front-end data-section payload, named-size, and named-offset entries agree with the backend object-layout helpers after `DataSection.toObjects`.
   - [x] Expose checked typed-front-end compilation entrypoints after object-builtin resolution with object layout and local data-base context; these route to the checked `Objects.Source.Program.compileChecked?` path rather than the executable unchecked bytecode lane.
   - [ ] Lower and prove `datasize`, `dataoffset`, and `datacopy` against that layout in the checked Yul/object path.
   - State any external object/account assumptions separately from compiler correctness.

4. [ ] Nethermind Yul bridge
   - [x] Define the theorem-boundary state relation between `EvmYul.Yul.State` and the compiler's EVM state, parameterized by the Yul/EVM global-state relation.
   - [x] Make the local-variable bridge strict: accepted no-shadowing exposes freshness/nodup facts, and checked zero-initializer/insert-pair lemmas extend the imported Yul varstore and compiler stack without relying on missing-variable defaults.
   - [x] Add a temporary-stack expression bridge relation so evaluated expression results can sit above the strict local-variable stack suffix.
   - [x] Prove the first variable-expression bridge: imported `.Var` evaluation and compiler local-variable `DUPn` code push the same temporary under exact varstore/stack relation, no-shadowing/nodup, and the real `DUP1..DUP16` stack-depth bound.
   - [x] Prove first statement-level bridges for `let`: single declarations with literal or variable initializers, plus multi-name zero-initializer declarations, connecting imported Yul store insertion to Functions direct execution and exact compiler stack-layout extension.
   - [x] Prove first statement-level bridges for assignment: single-target literal and variable assignments derive imported `checkAssignment` from the strict store-domain relation, execute the compiler-side `SWAPn; POP` update, preserve the exact local stack relation, and have compositional prefix forms for open statement sequences.
   - [x] Add the first checked bracketed-scope statement bridge: imported `Block []` and compiler `Stmt.block []` agree through scoped cleanup, with a compositional regular-prefix fact for statement-sequence induction.
   - [x] Prove the generic scoped-block closure substrate: imported block-end `restrictStoreTo` preserves the exact live-layout relation after target cleanup, packaged as `regular_block_scope_close_bridge` for the eventual recursive block bridge.
   - [x] Generalize block-end `restrictStoreTo` preservation to outcome/result relations, so nonregular checkpoints and terminal/error-shaped block results can be closed without re-proving varstore restriction per construct; the reusable relation theorem needs only live-layout containment in the block-entry scope, with exact-domain wrappers where useful.
   - [x] Add handler-layout-aware source-tower closure lemmas for `SourceResultSeqRunAt`: checkpoint and terminal/error block exits now close through imported `restrictStoreTo` while preserving the handler outcome layout, so recursive scoped-block proofs do not collapse abrupt exits back to the block-entry layout.
   - [x] Add generic source-result sequence wrappers for bracketed block heads, composing regular open-body evidence through scoped cleanup and nonregular open-body evidence through the handler-layout-aware checkpoint/error closures.
   - [x] Add source-domain variants for nonregular block-head wrappers, deriving the required imported-store containment from `StoreDomainExact layout store` plus handler-scope subset instead of forcing callers to rebuild raw lookup predicates.
	   - [x] Introduce the run-filtered open-sequence proof target `SourceResultSeqSoundWhenAt`, plus exact-run projection and nil base case, so the eventual recursive theorem has a list-level induction boundary rather than only scoped-block soundness.
	   - [x] Add the fixed-target-fuel companion `SourceResultSeqSoundWhenAtFuel` with projection to the public existential target, so regular-head composition can share the same target subfuel across head and tail instead of rebuilding replay witnesses.
	   - [x] Add source-owned fixed-fuel nil and regular-statement-head constructors (`SourceRegularStmtSoundAt` plus `sourceResultSeqSoundWhenAtFuel_cons_regular_stmt`) so recursive open-sequence proofs compose through ordinary heads before projecting to existential target fuel.
	   - [x] Add exact-domain source-state bridge facts (`SourceStateExactRel`, exact fixed-fuel open-sequence nil/regular-head constructors, and `sourceRegularStmtSoundAtExact_assign_lit_single`) so assignment/declaration-style Yul checks can be proved from a real varstore-domain invariant rather than the weaker live-name relation.
	   - [x] Mirror the exact-domain sequence boundary at checked lowering (`CheckedSeqLoweringSoundWhenFreshAtCompileFuelExact`, exact nil/regular-head cons, and checked assignment literal/variable singleton soundness), so real lowerer output can feed domain-aware regular statement heads.
	   - [x] Add exact-domain source and checked singleton soundness for `let x`, `let x := literal`, and `let x := y`; checked declaration cases carry the explicit premise that the declared source name is already in the lowerer's `Fresh.State.used`, matching the contract-wide source-name coverage needed to keep generated temporaries fresh.
	   - [x] Add exact-domain checked sequence-head constructors for assignment literal/variable and let none/literal/variable singleton heads, so recursive open-sequence proofs can consume the common ordinary-head lowerer cases directly.
	   - [x] Add compile-fuel-parametric checked open-sequence lowering (`CheckedSeqLoweringSoundWhenFreshAtCompileFuel`) plus nil and singleton regular-head cons wrappers, so checked list decomposition follows the actual lowerer fuel instead of requiring a separate fuel-invariance theorem for `Stmt.List.toBlock?`.
	   - [x] Add the checked lowering boundary `CheckedSeqLoweringSoundWhenFreshAt` and its nil constructor, so checked Yul statement-list lowering can target the new open-sequence soundness interface directly.
	   - [x] Add source-owned and checked open-sequence constructors for abrupt `break`, `continue`, and `leave` heads, preserving handler-specific outcome layouts while ignoring unreachable tails.
	   - [x] Add the fuel-existential prefix interface for scoped blocks: Functions direct execution now has checked fuel monotonicity plus append-after-regular composition, and the imported-Yul bridge exposes `regularPrefixExists_block_of_open` / `regularSeqRunBridge_cons_of_prefix_exists` so nested bracketed blocks can compose without assuming the tail fuel also replays the whole nested block.
   - [x] Package open sequence bridge evidence with context-layout/suffix facts (`RegularSeqRunBridgeWithLayout`) and prove `regularPrefixExists_block_of_seq_with_layout`, so recursive open-block evidence can close into a reusable scoped-block statement prefix without restating the raw layout premises.
   - [x] Add layout-aware recursive sequence composition (`RegularStmtPrefixBridgeWithLayout`, `regularSeqRunBridgeWithLayout_cons_of_prefix`) and lift the checked `let`/assignment prefix cases plus scoped blocks into that interface.
   - [x] Add concrete layout-aware recursive cons wrappers for the checked regular statement cases: zero-initializer `let`, single literal/variable `let`, single literal/variable assignment, and nested scoped blocks.
   - [x] Add outcome-shaped open-sequence prefix facts for `break`, `continue`, and zero-return `leave`, including existential `SomeOkSeqRunBridge` wrappers for recursive block drivers.
   - [x] Lift `break`, `continue`, and zero-return `leave` prefixes into the result-shaped sequence interface, so abrupt control can coexist with terminal/error-capable recursive tails.
   - [x] Add a result-shaped imported-Yul bridge interface (`CompilerResultOutcomeRel`, `ResultBlockRunBridge`, `ResultSeqRunBridge`) so terminal `YulHalt`/`Revert` results can be related to compiler halt outcomes through explicit `StateRelConfig.terminalRel`/`revertRel` assumptions instead of forcing all source execution through `.ok` states.
   - [x] Add compositional error-prefix sequence bridging (`ErrorStmtPrefixBridge`, `resultSeqRunBridge_cons_of_error_prefix`) so terminal/error-producing statement heads can skip arbitrary tails on both imported and compiled runs.
   - [x] Prove the first concrete terminal statement bridge: imported Yul `stop()` lowers to compiler `terminalArgs .stop []` and feeds the result-shaped/error-prefix sequence bridge under the explicit terminal-state relation.
   - [x] Remove the stale reference-boundary rejection of `REVERT` and `SELFDESTRUCT`, and add checked imported-Yul source reductions for `return(0,0)` and `revert(0,0)` as terminal bridge substrate.
   - [x] Prove concrete `return(0,0)` and `revert(0,0)` target-side terminal bridges and result-shaped sequence-head wrappers, under the explicit terminal/revert state relation hooks.
   - [x] Factor the compiler-side terminal-argument replay into `functions_runOpen_terminalArgs_of_runCode` and `errorPrefix_terminalArgs_of_source_error`, so future terminal primitive bridge cases can reuse one target-side proof instead of unfolding each compiled prefix.
   - [x] Lift the generic terminal-argument replay to exact and existential result-sequence cons wrappers, so terminal primitive heads can be used directly by the recursive imported block/list bridge.
   - [x] Add checked imported-Yul source reductions for `selfdestruct(0)` in both writable mode (`YulHalt` with named source state) and static mode (`StaticModeViolation`), plus compositional result-sequence wrappers for the writable terminal path under explicit target-step and terminal-state relation premises.
   - [x] Fix primitive argument lowering to build EVM stack-order sequences (`[a, b]` lowers to pushes for `b` then `a`) and add checked nonzero literal-pair `return(offset,size)` / `revert(offset,size)` bridge facts so the argument order is observable at the reference boundary.
   - [x] Add result-shaped empty-sequence and existential `stop()` wrappers, giving the recursive statement-list bridge a base case and terminal-head case in the same `SomeResultSeqRunBridge` interface.
   - [x] Add result-shaped bracketed-block base/control wrappers, mirroring the open-sequence interface so empty blocks and `break`/`continue`/zero-return `leave` compose with terminal/error-shaped block results.
   - [x] Add a result-shaped block wrapper theorem from open-sequence evidence under an explicit live-layout containment condition, making imported block-end `restrictStoreTo` reusable for future recursive block drivers without requiring the block-entry scope to contain newly declared locals.
   - [x] Add a nonregular statement-prefix interface and scoped-block wrapper, so block heads that exit by checkpoint or terminal/error result can ignore arbitrary sequence tails compositionally.
   - [x] Add result-to-nonregular conversion lemmas, so recursive bridge proofs can derive nonregular block evidence from result-shaped block bridges plus imported checkpoint/error source shapes.
   - [x] Add compositional regular-prefix sequence bridging for result-shaped tails (`resultSeqRunBridge_cons_of_regular_prefix` and the fuel-existential variant), so ordinary statements and scoped/fuel-existential prefixes can precede tails that finish with `.ok`, terminal `YulHalt`, `Revert`, or imported errors.
   - [x] Add checked result-shaped recursive cons wrappers for the existing regular statement cases: zero-initializer `let`, single literal/variable `let`, single literal/variable assignment, and nested scoped blocks can now precede result-shaped tails without falling back to ok-only recursion.
   - [x] Add compositional target-side prefix/tail replay for zero-initializer lowering, so the future imported-block/list bridge can reuse `initNames` before arbitrary tail blocks instead of relying on fused example proofs.
   - [x] Add layout-carrying recursive wrappers for nonregular `break`, `continue`, zero-return `leave`, terminal/error prefixes, and nonregular bracketed blocks.
   - [x] Start structured-control bridging with a layout-carrying condition-false `if` wrapper parameterized by checked source/target condition evaluation.
   - [x] Add layout-carrying condition-true `if` wrappers for both regular body completion and nonregular body exits.
   - [x] Add checked literal and variable condition bridge lemmas, so control wrappers can consume source expression evaluation and target `runCondition` evidence compositionally.
   - [x] Add checked construct-level `if` wrappers for literal and variable conditions, covering false branches, true branches with regular body completion, and true branches with nonregular body exits.
   - [x] Add checked construct-level literal `switch` wrappers: no selected branch/empty default, selected branch with regular scoped completion, and selected branch with nonregular exits all preserve the layout-carrying result bridge.
   - [x] Add the reusable one-result expression pop bridge and variable `switch` wrappers for the same miss/regular-body/nonregular-body cases, so switch proof coverage now reaches literal and local-variable scrutinees without unfolding stack append proofs at each case.
   - [x] Add `CompilerStateRelWithHiddenLocals` plus checked cleanup back to `CompilerStateRel`, making compiler-only locals from expression preludes explicit instead of pretending they are source varstore entries.
   - [x] Add `CompilerStateRelWithTempsAndHiddenLocals` plus checked one-result pop, so expression results can sit above compiler-only locals and then restore the hidden-local relation.
   - [x] Add hidden-local literal and variable expression bridges; variable reads now account for generated-temp depth shifts through `hiddenLayout ++ sourceLayout`.
   - [x] Add hidden-local condition bridges, including lookup-pinned variable conditions, so literal and variable conditions can be popped while preserving compiler-only locals above the source-local suffix.
   - [x] Add a slot-based variable-condition bridge for full compiler layouts, preparing the bridge for generated temporaries interleaved with source locals rather than only hidden-prefix/source-suffix layouts.
   - [x] Package the full-layout source-variable slot relation with conversions from exact and hidden-prefix relations, so future bridge cases can move off the brittle prefix-only hidden-local invariant.
   - [x] Strengthen the full-layout slot relation with an explicit stack-coverage invariant, so scoped cleanup and block-closure proofs can rely on layout length rather than reconstructing slot availability locally.
   - [x] Add full-layout regular scoped-block closure and recursive block-head composition, so nested bracketed Yul blocks can restrict the imported varstore and clean the target stack back to the outer full-layout relation.
   - [x] Add regular full-layout open-sequence nil/cons constructors, carrying both source-visible and full-layout suffixes for statement-by-statement block-body proofs.
   - [x] Add regular full-layout recursive wrappers for ordinary regular statement heads: `let`, assignment, and nested scoped blocks.
   - [x] Add structural full-layout relation updates for source-visible declarations and compiler-only locals, plus literal/zero-let statement bridge steps over the full-layout slot relation.
   - [x] Add full-layout hidden-prefix/initNames bridging, so generated zero temporaries for call-result allocation can extend arbitrary compiler layouts while preserving the embedded source-variable relation.
   - [x] Move the source-independent visible-slot relation shape below the reference bridge and out of pure locals semantics: `Locals.StackLowering.VisibleLookupSlotRel` owns lookup/layout/stack matching over a generic lookup function, including hidden-prefix extension, source-visible insertion, and assignment-update lemmas, and `Yul.Reference.VisibleVarSlotRel` adapts Nethermind `VarStore.lookup` / `insert`.
   - [x] Add a full-layout variable-declaration bridge for `let x := y`, proving source varstore reads and target `DUPn` agree through the embedded source-variable relation.
   - [x] Add expression-parametric full-layout assignment bridging: any checked one-result RHS bridge can feed `x := <expr>` through a reusable slot-update theorem, with literal and variable assignments now proved as instances.
   - [x] Add the recursive full-layout sequence interface for source variables embedded in arbitrary compiler layouts, plus checked literal/variable assignment cons wrappers using that interface.
   - [x] Add full-layout recursive base and single-declaration wrappers for zero, literal, and variable `let`, so declaration prefixes can compose under arbitrary compiler layouts.
   - [x] Add full-layout recursive multi-name zero-declaration wrappers, so imported `let x, y, ...` with no initializer extends the Yul varstore and compiler stack in one checked batch under arbitrary compiler layouts.
   - [x] Add expression-generic full-layout `if` prefix and recursive wrappers for false conditions, true branches with regular body completion, and true branches with nonregular body exits, so control-flow heads can compose under arbitrary compiler layouts without returning to exact source-stack layout.
   - [x] Add concrete full-layout literal-condition `if` wrappers for false branches and nonregular true branches, reusing a checked `runCondition`/single-temp pop bridge over `CompilerStateRelWithLayoutSlots`.
   - [x] Add concrete full-layout variable-condition `if` wrappers for false branches and nonregular true branches, pinning the imported varstore lookup to the compiler stack slot selected by `VisibleVarSlotRel`.
   - [x] Add regular full-layout `if` sequence wrappers for expression-generic, literal, and variable conditions, covering false branches and true branches whose scoped body completes regularly.
   - [x] Add regular full-layout `switch` sequence wrappers for expression-generic, literal, and variable scrutinees, covering no-selected-branch and selected-branch regular scoped completion.
   - [x] Add result-shaped full-layout `switch` sequence wrappers for no-selected-branch, selected-regular, and selected-nonregular outcomes.
   - [x] Add explicit source-layout embedding and full-layout suffix cleanup for continuation exits, then use it for result-shaped full-layout `break`/`continue` wrappers.
   - [x] Add the zero-return full-layout `leave` wrapper using the same continuation cleanup contract.
   - [x] Add a generic full-layout terminal/revert wrapper for `terminalArgs` prefixes whose imported source execution returns an error.
   - [x] Add concrete full-layout terminal wrappers for `stop`, literal-pair `return`/`revert`, zero-zero `return`/`revert`, and writable `selfdestruct(0)`, all routed through the generic terminal-argument bridge.
   - [x] Add full-layout return-value push substrate: variable reads under existing expression temps, `returnExprs` stack-prefix interpretation, and `pushReturns` preservation with an explicit `ReturnStackRel`.
   - [x] Add checked preserving cleanup under a return-value stack prefix, convert preserved return temps back into named layout slots, and prove the full-layout nonzero-return `leave` sequence wrapper.
   - [x] Add full-layout block closure for nonregular result bodies, including scoped varstore restriction over `CompilerResultOutcomeRelWithLayoutSlots`, so `leave`/halt/checkpoint bodies can lift from open sequences to block-level evidence.
   - [x] Add compiler-lowering-aware full-layout `break`/`continue`/`leave` wrappers, so recursive bridge code can consume actual `Stmt.toFunctionsListFuel?` evidence instead of hand-supplied control prefixes.
   - [x] Add compiler-lowering-aware full-layout ordinary-head wrappers for single zero/literal/variable declarations and literal/variable assignments.
   - [x] Add the same lowering-aware ordinary-head wrappers for regular full-layout open sequences, so normally completing scoped blocks can consume compiler evidence directly.
   - [x] Add compiler-lowering-aware empty scoped-block wrappers for both result-shaped and regular full-layout sequence interfaces.
   - [x] Add generic checked lowering decomposition facts for `block` and `if`, recovering emitted lower blocks/conditions from successful `Stmt.toFunctionsListFuel?` evidence.
   - [x] Add the generic checked lowering decomposition fact for `for`, including the generated body guard emitted by the compiler.
   - [x] Add checked list/block lowering decomposition facts for nil, cons, and block wrapping, so recursive bridge induction can split compiler output into head/tail evidence.
   - [x] Add generic lowering-aware recursive cons drivers for regular heads over full-layout result and regular sequence bridges.
   - [x] Add lowering-aware nil bases and block-lowering lifts for full-layout result and regular sequence bridges.
   - [x] Add the first lowering-aware concrete control wrappers for `if 0`, covering result-shaped and regular full-layout sequence bridges.
   - [x] Add lowering-aware concrete control wrappers for `if x` when the imported store proves `x = 0`, covering result-shaped and regular full-layout sequence bridges.
   - [x] Add lowering-aware concrete control wrappers for taken literal/variable `if` branches, covering regular bodies plus result tails and nonregular bodies with the compiler-derived lower body.
   - [x] Add a hidden-layout regular prefix interface plus false/true regular `if` wrappers, so control-flow prefixes can preserve compiler-only locals instead of forcing them into the source varstore relation.
   - [x] Add the first target-only hidden-local prelude bridge: compiler-side `let tmp := literal` extends the hidden-local prefix and context layout while leaving the imported Yul store relation unchanged.
   - [x] Add target-only hidden zero-initializer prelude bridging for `Stmt.initNames`, matching generated call-result temp allocation without extending the imported Yul varstore.
   - [x] Add the tail-composition bridge for hidden `Stmt.initNames`, so generated temp allocation can prefix arbitrary later lowered call/bind blocks.
   - [x] Add checked switch lowering decomposition facts for empty and nonempty defaults, recovering scrutinee prelude/lower expression, case lowering, optional default lowering, and final emitted statement shape from `Stmt.toFunctionsListFuel?`.
   - [x] Replace the binary primitive hidden-argument proof interface with a slot-addressed invariant: generated temporaries are now tracked by `LayoutSlotValue`, read through declared layout slots and checked `DUP` bounds, and the old top-two bridge is only a compatibility checkpoint.
   - [x] Add a base-stack-preserving expression bridge wrapper with checked literal, variable, `iszero(e)`, and `not(e)` constructors, so hidden compiler slots can be preserved beneath one-result expression temporaries.
   - [x] Add preserving-base hidden binding: when a one-result expression is bound to a compiler-generated local, the new slot and all previously tracked layout slots are preserved under the extended compiler layout.
   - [x] Add a two-argument prelude bridge that evaluates/binds the right argument, then evaluates/binds the left argument, and derives `TwoHiddenArgsBridgeWithLayoutSlotValues` with the imported Yul fuel/order semantics made explicit.
   - [x] Replace the active arity-specific `TwoHiddenArgs*` bridge path for `ADD` with the generic list-shaped `BoundArgsBridgeWithLayoutSlotValues`; the two-argument facts now remain only as compatibility lemmas.
   - [x] Introduce `ArgSlotValues` and `BoundArgsBridgeWithLayoutSlotValues` as the generic source-order argument-slot relation, add the generic nil base, add checked adapters between the generic bridge and the existing two-argument compatibility facts, and route `ADD`'s compiler-output theorem through the generic boundary.
   - [x] Add the generic bound-argument cons component theorem, separating target prelude/slot composition from the imported `evalArgs` append-singleton source-semantics obligation that remains to be discharged.
   - [x] Move compiler-only `Expr.List.lowerBound1?` decomposition and primitive lowering equations down into `Yul.Expr`, leaving `Yul.Reference` with compatibility wrappers rather than owning the compiler facts.
   - [x] Add `Expr.List.BoundLowering` as a checked compiler-side structural certificate generated from `lowerBound1?`, with no external witness requirement; prove it round-trips to the compiler output and records argument-list length / variable-output shape.
   - [x] Add named imported-Yul singleton and pair `evalArgs` source lemmas, and route the unary bridges plus the two-argument compatibility bridge through them instead of re-simplifying `evalArgs` locally.
   - [x] Add `ArgSlotValues.length_eq` and `ArgSlotValues.all_vars` as checked facts needed before the generic `toStackSeq?` target-stack replay theorem.
   - [x] Add scheduled imported `evalArgs` append/snoc and reverse-cons lemmas, then wrap the generic bound-argument cons step as `boundArgsBridgeWithLayoutSlotValues_cons_scheduled` so callers no longer supply raw `hFullEval` source-side evidence.
   - [x] Move pure target-side generated-argument replay below the reference bridge: `Locals.ExprSeq.VarSlotValuesAt` and `Locals.Direct.Expr.ExprSeq.runCode_of_varSlotValuesAt` now own the `ExprSeq.runCode` stack theorem, while `Yul.Reference` only adapts `ArgSlotValues` plus `Expr.List.toSeq?` evidence into that lower relation.
   - [x] Split target-only generated-argument slot replay into `EvmCompiler.Yul.ArgSlots`; `Yul.Reference` now converts its reference-boundary `ArgSlotValues` evidence to lower `ArgSlots.Values` and delegates `toSeq?`/`toStackSeq?` target replay there.
   - [x] Make `Yul.ArgSlots.LayoutSlotValue` the canonical target-side slot-value predicate; `Yul.Reference.LayoutSlotValue` is now only a compatibility alias.
   - [x] Add the `toStackSeq?` wrapper over the lower replay theorem, including source-order reverse/append facts for argument-slot values.
   - [x] Add `boundArgsBridgeWithLayoutSlotValues_runStackSeq`, packaging generated argument prelude execution and `toStackSeq?` target replay behind the generic bound-argument bridge instead of leaving recursive terminal/primitive callers to carry hand-run stack evidence.
   - [x] Add `resultSeqRunBridgeWithLayoutSlots_cons_boundTerminalArgs_of_source_error`, the generated-argument terminal/error sequence constructor that composes the bound-argument prelude, terminal target step, and arbitrary tail through the full-layout result bridge.
   - [x] Add literal terminal inversion/step facts (`evalArgs_lit_lit_reverse_ok_eq`, `terminal_step_return_of_stack`, `terminal_step_revert_of_stack`) and route generated-prelude `return(offset, size)` / `revert(offset, size)` through full-layout recursive sequence wrappers, so those terminal cases no longer depend on direct literal `PUSH` replay at the imported-Yul bridge boundary.
   - [x] Add the matching full-layout recursive sequence wrapper for generated-prelude `selfdestruct(recipient)`, keeping the target SELFDESTRUCT step plus account-effect terminal relation as an explicit callback while discharging imported literal-argument order and generated argument replay generically.
   - [x] Add compiler-output-aware lowerer wrappers for those generated-prelude terminal cases: `resultSeqRunBridgeWithLayoutSlots_cons_return_lit_lit_bound_of_lower`, `..._revert_lit_lit_bound_of_lower`, and `..._selfdestruct_lit_bound_of_lower` consume `Stmt.toFunctionsListFuel?` evidence and recover the emitted prelude/argument sequence through `toFunctionsListFuel?_terminal_components`.
   - [x] Refactor the `ADD` primitive bridge to consume the generic `toStackSeq?` replay wrapper directly instead of the old two-argument compatibility facts.
   - [x] Add the first noncommutative binary primitive on the same path: `sub(left, right)` now uses the generic source-order argument bridge and `toStackSeq?` target replay, giving a checked argument-order regression theorem.
   - [x] Factor the active two-argument primitive bridge through `exprValueBridgeWithLayoutSlots_binary_of_bound_args_target`; compiler-output-aware `ADD`, `MUL`, `SUB`, `DIV`, `SDIV`, `MOD`, `SMOD`, `EXP`, `SIGNEXTEND`, `AND`, `OR`, `XOR`, `BYTE`, `SHL`, `SHR`, and `SAR` lowering now use the shared binary bridge, with the older arity-specific proofs kept only as compatibility checkpoints.
   - [x] Split primitive opcode source/target facts for `iszero`, `not`, `add`, `mul`, `sub`, `div`, `sdiv`, `mod`, `smod`, `addmod`, `mulmod`, `exp`, `signextend`, `lt`, `gt`, `slt`, `sgt`, `eq`, `and`, `or`, `xor`, `byte`, `shl`, `shr`, and `sar` into `EvmCompiler.Yul.PrimSemantics`; `Yul.Reference` now keeps only compatibility wrappers, and the active primitive bridges consume the lower `PrimSemantics` facts directly.
   - [x] Add `DIV` to the same split primitive table and compiler-output-aware bound-argument bridge path, preserving imported Yul division semantics through the target structured `div` opcode.
   - [x] Add `SDIV`, `MOD`, and `SMOD` to the same split primitive table and compiler-output-aware bound-argument bridge path, preserving the imported Yul signed-division and remainder semantics through the matching target structured opcodes.
   - [x] Add `EXP` and `SIGNEXTEND` to the same split primitive table and compiler-output-aware bound-argument bridge path, preserving the imported Yul exponentiation and sign-extension semantics through the matching target structured opcodes.
   - [x] Add the comparison primitive substrate for `LT`, `GT`, `SLT`, `SGT`, and `EQ`, and complete the compiler-output-aware bound-argument bridge for the full comparison family.
   - [x] Add the bitwise/shift primitive substrate for `AND`, `OR`, `XOR`, `BYTE`, `SHL`, `SHR`, and `SAR`, including the imported `SHL`/`SHR` operand order via Nethermind's `flip` semantics, and route them through the same compiler-output-aware bound-argument bridge.
   - [x] Add the ternary pure arithmetic primitive substrate for `ADDMOD` and `MULMOD`, including a reusable list-shaped ternary argument bridge and compiler-output-aware bound-argument lowering wrappers.
   - [x] Extend the nullary environment-read bridge from `ADDRESS` to the equality-shaped execution-environment family: `ORIGIN`, `CALLER`, `CALLVALUE`, `CALLDATASIZE`, `GASPRICE`, `PREVRANDAO`, `BASEFEE`, and `BLOBBASEFEE`. These route through the reusable source/target nullary primitive theorem; `CODESIZE` and `GAS` intentionally remain separate contracts because they depend on code-image size agreement and the gas oracle relation rather than plain execution-environment equality.
   - [x] Extend the nullary state-read bridge to the equality-shaped block/chain state family: `COINBASE`, `TIMESTAMP`, `NUMBER`, `GASLIMIT`, and `CHAINID`, routing them through the reusable source/target state-read theorem.
   - [x] Extend the same nullary state-read bridge to account-map-dependent `SELFBALANCE` by making the required current-account balance preservation contract explicit as `StateRelConfig.selfbalanceRel`.
   - [x] Extend the nullary machine-state bridge to exact machine reads `RETURNDATASIZE` and `MSIZE`, routing through the reusable source/target machine-state theorem.
   - [x] Extend the same nullary machine-state bridge to visible `GAS` by making the required gas-oracle value agreement explicit as `StateRelConfig.gasValueRel`, separate from the broader `gasAvailableRel` resource relation.
   - [x] Add the first one-argument read/state-update primitive bridges, `CALLDATALOAD`, `BLOCKHASH`, `BLOBHASH`, `BALANCE`, `SLOAD`, `TLOAD`, and `MLOAD`, using a compositional hidden-local unary helper plus compiler-output-aware bound-lowering wrappers. Calldata, processed-block/hash, and blob-hash list equality are discharged through the shared-state/execution-environment relations; `BALANCE` uses an explicit `StateRelConfig.balanceRel` account-map value contract plus checked preservation of the accessed-account substate update; `SLOAD` adds an explicit `StateRelConfig.sloadRel` current-contract-storage contract plus checked preservation of the accessed-storage-key substate update; `TLOAD` adds an explicit `StateRelConfig.tloadRel` transient-storage value contract but has trivial state preservation; `MLOAD` uses the existing machine-state relation to prove memory-read equality and active-word update preservation without a new oracle field.
   - [x] Add the first machine-state result/update binary primitive bridge, `KECCAK256`, using the existing memory/active-word machine-state relation to prove hash-result equality and active-word update preservation.
   - [x] Add the first unary zero-result primitive statement bridge, `POP`, using a reusable bound-argument statement-prefix theorem that separates imported Yul's no-op source primitive from the target stack-pop implementation.
   - [x] Start the zero-result primitive statement bridge with `MSTORE` and `MSTORE8`: source and target primitive facts are checked, the shared machine-state relation is preserved after the same write, and a reusable zero-result binary statement-prefix bridge now runs the bound-argument prelude, replays the target expression statement, and returns to the same full compiler layout.
   - [x] Add the first ternary zero-result shared-state primitive statement bridge, `CALLDATACOPY`: source and target primitive facts are checked, calldata/memory/active-word equality preserves the shared-state relation after the same copy, and a reusable ternary statement-prefix bridge now covers bound-argument zero-result calls.
   - [x] Add the first ternary zero-result machine-state primitive statement bridge, `MCOPY`: source and target primitive facts are checked, memory/active-word equality preserves the machine-state relation after the same copy, and the existing ternary statement-prefix bridge covers the bound-argument call.
   - [x] Add the return-data memory-copy primitive statement bridge, `RETURNDATACOPY`: source and target primitive facts are checked, return-data/memory/active-word equality preserves the machine-state relation after the same copy, and the ternary statement-prefix bridge covers the bound-argument call.
   - [x] Tighten imported-Yul `Safe.primitive` so the accepted bridge boundary rejects static-mode-sensitive primitives until the bridge has explicit error/outcome coverage or a writable-context theorem. `SSTORE`, `TSTORE`, and `LOG0`-`LOG4` now have checked coverage at the current boundary.
   - [x] Start discharging the storage-write part of that boundary for `SSTORE`: add imported-Yul writable/static primitive facts, a concrete compiled-stack `SSTORE` step lemma, and explicit `StateRelConfig` storage-write stability hooks for account-map and refund/access substate preservation.
   - [x] Add the checked regular-success statement-prefix bridge for `SSTORE` under an explicit writable-context premise after argument evaluation, by generalizing the reusable binary zero-result primitive theorem so static-mode-sensitive primitives can depend on the post-argument state relation.
   - [x] Mirror the writable/static primitive facts, compiled-stack step lemma, shared-state account-map stability hook, and checked regular-success statement-prefix bridge for `TSTORE`.
   - [x] Add the first log bridge slice for `LOG0`: imported-Yul writable/static primitive facts, concrete compiled-stack step lemma, shared log-effect preservation over `SharedStateRel`, and checked regular-success statement-prefix bridge under the same explicit writable-context premise.
   - [x] Add the `LOG1` bridge slice: imported-Yul writable/static primitive facts, concrete compiled-stack step lemma, and checked regular-success ternary statement-prefix bridge under the explicit writable-context premise.
   - [x] Add the static-mode/error bridge for remaining `LOG2`-`LOG4`, then re-admit them through `Safe.primitive`.
   - [x] Add checked rejection facts for code-image primitives at the current imported-Yul bridge boundary: `CODESIZE`, `CODECOPY`, `EXTCODESIZE`, `EXTCODECOPY`, and `EXTCODEHASH`.
   - [x] Add the checked imported-semantics gap classifier for code-image ops
     and `CREATE`/`CREATE2`, separate from the external-call boundary
     classifier for `CALL`, `CALLCODE`, `DELEGATECALL`, and `STATICCALL`.
   - [ ] Add explicit Yul-level code-image semantics plus a compiler byte-image bridge before re-admitting `CODESIZE`, `CODECOPY`, `EXTCODESIZE`, `EXTCODECOPY`, or `EXTCODEHASH`.
   - [x] Add checked rejection facts for external call/create primitives at the current imported-Yul bridge boundary: `CREATE`, `CREATE2`, `CALL`, `CALLCODE`, `DELEGATECALL`, and `STATICCALL`.
   - [x] Add the target-runtime no-call/create constructor, so programs whose
     emitted assembly syntactically contains no call/create opcodes discharge
     `ExternalInteractionAssumption` without a separate agreement premise.
   - [x] Retire the explicit concrete account-code route for `CALL`.
     The old concrete `World` module and remaining precompile/child-dispatch
     support branch are gone; live `CALL` work now stops at the `OpenExternal`
     request/response boundary with an arbitrary opaque response-state
     transformer, plus
     the pending open argument semantics for nested `CALL`s. `CREATE`,
     `CREATE2`, `CALLCODE`, `DELEGATECALL`, and `STATICCALL` remain future
     external-operation coverage.
   - [ ] Continue the primitive bridge table for remaining state/machine/environment reads and memory/storage/code/external primitives using family-specific semantic relations, rather than treating them all as pure bound-argument stack operators.
   - [x] Change Yul expression lowering for primitive/function/terminal argument lists to bind each argument immediately after its own prelude (`Expr.List.lowerBound1?`), matching imported Yul's right-to-left argument evaluation and avoiding delayed reads across later argument effects.
   - [x] Add checked lowering decomposition for bound binary primitive arguments and a compiler-output-aware `add(left, right)` bridge theorem that composes the generated hidden-argument prelude with generic `toStackSeq?` target replay and the target `ADD` proof.
   - [x] Add generic lowering equations for one-result and zero-result primitive calls over bound arguments, plus a terminal statement decomposition fact for the new bound-argument compiler output.
   - [x] Add a compiler-output-aware `iszero(e)` bridge for the new bound unary-argument lowering path, reusing the existing hidden-temp semantic theorem.
   - [x] Add the matching hidden-temp and compiler-output-aware `not(e)` bridge for the new bound unary-argument lowering path.
   - [x] Factor the unary hidden-temp bridge interface: `exprValueBridgeWithLayoutSlots_unary_hidden_of_target` now separates imported one-argument primitive semantics from the already-typed target expression run, avoiding dependent `BasicOp` arity blowup for future unary primitive cases.
   - [x] Factor switch dispatch into expression-generic scrutinee lemmas parameterized by imported evaluation, compiler `runState`, target pop, and post-pop state relation evidence; richer expression bridges can now feed switch without unfolding switch semantics again.
   - [x] Add checked compiled/source no-default switch miss agreement: if compiled case lowering selects no branch with no default, imported `selectSwitchCase` returns the empty block.
   - [x] Add checked compiled/source no-default switch selected-case agreement: if compiled case lowering selects a case body, imported `selectSwitchCase` selects a source body with a checked lowering to that compiled body.
   - [x] Add checked compiled/source default-aware switch selected-branch agreement: if compiled case/default lowering selects a branch with a compiled default available, imported `selectSwitchCase` selects a source body with a checked lowering to the selected compiled body.
   - [x] Bundle selected switch source/target/lowering evidence as `SwitchSelectedLowering` and add selected-branch regular/nonregular wrappers that consume this single fact instead of separate source-selection and target-selection premises.
   - [x] Bundle no-default switch miss evidence as `SwitchNoMatchLowering` and add no-match empty-default wrappers that consume this single fact.
   - [x] Add result-shaped full-layout no-selected-branch switch wrappers for literal and variable scrutinees, so switch misses no longer need to fall back to exact-layout bridge facts.
   - [x] Add lowering-aware no-default switch-miss wrappers for literal and variable scrutinees, recovering the compiled case table from `Stmt.toFunctionsListFuel?`.
   - [x] Add full-layout selected-switch bundle wrappers for regular and nonregular selected branches, mirroring the exact-layout selected-switch interface over `CompilerStateRelWithLayoutSlots`.
   - [x] Add concrete full-layout selected-switch result wrappers for literal and variable scrutinees, covering regular selected bodies plus arbitrary result tails and nonregular selected bodies.
   - [x] Add lowering-aware no-default selected-switch wrappers for literal scrutinees, recovering the selected compiled branch from the lowered case table.
   - [x] Add lowering-aware no-default selected-switch wrappers for variable scrutinees, including the full-layout slot lookup proof for the scrutinee.
   - [x] Add lowering-aware nonempty-default selected-switch wrappers for literal and variable scrutinees, deriving compiled default selection without a separate target-selection premise.
   - [x] Add generic lowering-aware scoped-block wrappers for regular and nonregular bodies, so arbitrary bracketed blocks can compose from checked `Stmt.toFunctionsListFuel?` evidence rather than only the empty-block special case.
   - [x] Add a checked visible-slot-to-exact-state conversion with explicit `Nodup` and no-extra-stack-suffix premises, keeping the full-layout bridge honest at older exact-layout boundaries.
   - [x] Add the first loop bridge slice: imported false-condition `for` exits regularly while the compiled always-true target loop runs the generated `iszero(cond)` guard and `break`; target guard execution is factored as `functions_for_guard_break_runScoped`, with both result-shaped and regular sequence wrappers.
   - [x] Discharge the generated loop-guard condition premise from target expression evidence: `runCondition_iszero_of_single_zero_temp_layout_slots` turns a checked one-word zero temp into the compiled `iszero` guard branch, with result/regular loop wrappers consuming that `runCode` evidence directly.
   - [x] Add lowering-aware literal-false loop wrappers, so successful `Stmt.toFunctionsListFuel?` evidence for `for 0 { post } { body }` now feeds the checked imported false-condition/compiled-guard bridge directly.
   - [x] Add lowering-aware variable-false loop wrappers, so `for x { post } { body }` is bridged directly when the imported varstore and full-layout slot relation prove `x = 0`.
   - [x] Add a compositional expression-value bridge for lowered one-result expressions, plus generic full-layout assignment prefix/result/regular sequence wrappers that consume expression bridge evidence instead of separate literal/variable statement proofs.
   - [x] Add the first compositional primitive-expression constructor: `iszero(e)` now preserves imported Yul primitive evaluation through the target `BasicOp.iszero` step from a generic bridge for `e`.
   - [x] Add the sibling primitive-expression constructor for `not(e)`, preserving imported Yul `NOT` evaluation through the target `BasicOp.not` step from the same one-argument expression bridge.
   - [x] Add the first argument-order-safe primitive-expression bridge substrate: an evaluated expression can be immediately bound into a compiler-only hidden local, and hoisted `iszero(tmp)` preserves imported Yul evaluation while keeping the generated temp outside the source varstore.
   - [x] Add a two-hidden-argument bridge contract plus the first binary primitive expression theorem: `add(left, right)` preserves imported Yul argument order and target EVM stack order once the checked hidden-argument prelude is established.
   - [x] Add scoped block-run drivers for the imported-Yul bridge: regular open-sequence evidence now closes directly to `Functions.Direct.Block.runScoped` with source `restrictStoreTo` and target cleanup, while nonregular block evidence runs through `runScoped` without taking the regular cleanup branch.
   - [x] Lift those scoped drivers to `Functions.Program.run` at the root function body, giving the future dispatcher/object bridge a checked entry point into the actual compiler-facing function interpreter.
   - [x] Lift the same drivers through the transparent object boundary to `Yul.Lowered.run` when `program.toObjects?` computes the expected root object, matching the legacy backend bridge shape now isolated as `Reference.LoweredBridge.sourceRun`.
   - [x] Compose the regular/nonregular root-block bridge drivers with `Yul.Program.compile_preserves_checked`, producing checked assembly-preservation theorems that derive `Lowered.run` from imported block evidence instead of taking `LoweredBridge.sourceRun`.
   - [x] Add checked imported-dispatcher wrapper lemmas for `callDispatcher`/`runResult`: regular dispatcher body execution, `YulHalt`, and `Revert` cases are now named without repeatedly unfolding the imported interpreter.
	   - [x] Add checked normalization/extraction facts for the dispatcher boundary: installed-contract dispatcher bodies/call frames reduce to the installed contract and empty dispatcher varstore, and `toObjects?` exposes the lowered root body/procedure list.
	   - [x] Add `CheckedRecursiveDispatcherSound`, a source-facing bridge package bundling checked dispatcher lowering with the dispatcher observation contract. Source-bridge, assembly, and gas-aware bytecode wrappers can now consume that single future-recursive-proof artifact instead of exposing separate body-lowering and run-observation callbacks. Constructors now build the package from checked dispatcher lowering, from fresh-aware statement lowering, and from initial-scope fresh-aware statement lowering.
	   - [x] Add direct source-bridge, assembly, and gas-aware bytecode wrappers from the initial-scope fresh-aware statement theorem plus dispatcher observation. These are the generic public wrappers the recursive imported-Yul statement proof should feed, avoiding a public checked-dispatcher-lowering callback.
	   - [x] Add `dispatcherObservationSound_of_handlers`, a named constructor for the observation half of the dispatcher bridge. This keeps regular/halt/revert projection contracts bundled instead of asking public theorem users to construct structure fields manually.
	   - [x] Add the successful-run dispatcher bridge boundary, `CheckedRecursiveDispatcherRunBridge`, plus the gas-aware wrapper `compile_whole_program_result_sound_of_checked_recursive_dispatcher_run_bridge_compileAccepted`. This is the preferred top-level recursive target: it is tied to a successful imported `Reference.runResult` and a concrete dispatcher body run, so it avoids asking the source tower to relate imported `OutOfFuel` results as normal Yul outcomes.
	   - [x] Add the run-filtered source-owned block target `SourceResultBlockSoundWhen`, its run-bridge projection, and the dispatcher package `CheckedRecursiveDispatcherSuccessfulSound`. This gives the future recursive proof a checked source theorem target that only needs to handle the dispatcher body result that projects to the successful imported top-level run.
	   - [x] Add run-filtered checked-lowering targets, `CheckedBlockLoweringSoundWhen`, `CheckedStmtBlockLoweringSoundWhen`, their fresh-aware variants, and `CheckedDispatcherLoweringSoundWhen`, plus constructors from those checked facts to `CheckedRecursiveDispatcherSuccessfulSound`. This is the theorem interface the recursive source-fuel proof should now feed, avoiding raw generated body-sound witnesses at the dispatcher boundary.
	   - [x] Add direct gas-aware bytecode wrappers from `CheckedDispatcherLoweringSoundWhen` and the initial-scope fresh-aware `CheckedStmtBlockLoweringSoundWhenFresh`. These let the eventual recursive source-fuel theorem compose straight to bytecode without callers manually constructing `CheckedRecursiveDispatcherSuccessfulSound`.
	   - [x] Add the run-filtered recursive theorem facade: `SourceBridgeFacts.RecursiveSourceBridgeWhenUpTo` and `Yul.Program.RecursiveDispatcherSuccessfulBridgeUpTo`, with projections from the older all-results recursive package and direct gas-aware wrappers. This is the preferred full-recursive proof target: prove the run-filtered source-fuel package once, under the explicit `SourceResultRelatable` side condition that rules out imported fuel/front-end errors, then compose to bytecode through the successful imported run.
	   - [x] Add the source-owned checked empty-block base case, `sourceResultBlockSoundWhen_nil` / `checkedBlockLoweringSoundWhenFresh_nil`. Fuel exhaustion for fuel 0/1 is discharged by the run filter's `SourceResultRelatable` side condition, so the source tower still does not model imported `OutOfFuel` as a normal Yul outcome.
	   - [x] Add handler-layout-aware source block soundness, `SourceResultBlockSoundWhenAt`, plus checked single-statement abrupt-control base cases for `break`, `continue`, and `leave`. This fixes the theorem-shape leak where abrupt outcomes were forced to use the entry layout instead of the Yul handler scope.
	   - [x] Lift the handler-layout-aware boundary through checked block lowering and the recursive facade: `CheckedBlockLoweringSoundWhenFreshAt`, `RecursiveSourceBridgeWhenUpToAt`, same-layout projections back to existing dispatcher wrappers, and the direct gas-aware bytecode wrapper from the new facade.
	   - [x] Add the projection `checkedRecursiveDispatcherSuccessfulSound_of_checked_recursive_dispatcher_sound`, so the older stronger checked-dispatcher package factors through the new successful-sound boundary before reaching the concrete run bridge.
	   - [x] Add the projection `checkedRecursiveDispatcherRunBridge_of_checked_recursive_dispatcher_sound`, proving the older all-results checked dispatcher package is sufficient to build the successful-run package when the imported top-level run succeeds.
	   - [x] Add the stronger `SourceBridgeFacts.RecursiveSourceBridgeUpTo` / `RecursiveDispatcherBridgeUpTo` facade as a sufficient helper for checked dispatcher lowering. It is intentionally not the preferred public completion target unless the theorem is restricted away from imported out-of-fuel cases; the successful-run bridge above is the end-to-end theorem boundary that matches the current gas/source-fuel assumptions.
	   - [x] Add the first dispatcher-entry composition theorem, `Yul.Program.compile_preserves_of_regular_dispatcher_bridge`, which starts from imported `runResult` for a regular dispatcher run and reaches the assembly run theorem without using `Reference.SourceBridge.sourceRun`.
   - [x] Add the nonregular dispatcher-entry composition theorem and generic dispatcher-result wrapper, so imported terminal/error/checkpoint body results have a named path from `runResult` to the checked assembly theorem without using `Reference.SourceBridge.sourceRun`.
   - [x] Add the first concrete dispatcher terminal theorem, `compile_preserves_of_dispatcher_stop_call_compileAccepted`, so imported `stop()` dispatcher runs compose directly to assembly preservation through `SourceCompileAccepted` without exposing a `Reference.SourceBridge` witness to callers.
   - [x] Add the first concrete gas-aware terminal theorem, `compile_whole_program_result_sound_of_dispatcher_stop_call_compileAccepted`, composing imported `stop()` dispatcher preservation through bytecode/gas-aware runtime assumptions.
   - [x] Add gas-aware bytecode whole-program theorems for the other direct concrete dispatcher terminals: `return(0, 0)`, `revert(0, 0)`, literal `return(offset, size)`, literal `revert(offset, size)`, and writable `selfdestruct(0)`.
   - [x] Add the existential-source-outcome bytecode composition helper plus gas-aware bytecode whole-program theorems for generated-prelude literal terminal dispatchers: prelude `return(offset, size)`, prelude `revert(offset, size)`, and prelude `selfdestruct(recipient)`.
   - [x] Add the corresponding zero-zero terminal dispatcher theorems, `compile_preserves_of_dispatcher_return_zero_zero_call_compileAccepted` and `compile_preserves_of_dispatcher_revert_zero_zero_call_compileAccepted`, packaging the checked imported `return(0, 0)` / `revert(0, 0)` bridge constructors into direct assembly preservation theorems.
   - [x] Add the literal-argument terminal dispatcher theorems, `compile_preserves_of_dispatcher_return_lit_lit_call_compileAccepted` and `compile_preserves_of_dispatcher_revert_lit_lit_call_compileAccepted`, so imported `return(offset, size)` / `revert(offset, size)` dispatcher runs compose directly through the checked source compile boundary.
   - [x] Add the corresponding `selfdestruct(0)` terminal dispatcher theorem, `compile_preserves_of_dispatcher_selfdestruct_zero_call_compileAccepted`, including the explicit writable-execution-environment premise from the imported Yul/EVM semantics.
   - [x] Reroute the concrete `stop`, zero/literal `return`/`revert`, and `selfdestruct(0)` terminal compile-accepted wrappers through explicit imported-run/source-run facts plus `compile_source_preserves_checked_of_compileAccepted`, leaving the older `SourceBridge` constructors as compatibility facts rather than the compile path.
   - [x] Add the prelude terminal dispatcher wrappers, `compile_preserves_of_dispatcher_return_lit_lit_prelude_call_compileAccepted`, `compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_compileAccepted`, and `compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_compileAccepted`. These keep the compiler-side temporary-binding outcome existential and now compose through `SourceLowered.runState` plus source-facing compile preservation instead of the legacy `compile_preserves_of_source_bridge` route.
   - [x] Add the generic bridge-lift theorem `compile_whole_program_result_sound_of_assembly_preservation`, so any checked imported-Yul-to-assembly preservation result can be composed through bytecode/gas-aware correctness under the explicit assembly runtime assumptions without rebuilding a `SourceBridge` witness.
   - [x] Add a layout-carrying result sequence bridge, `ResultSeqRunBridgeWithLayout`, plus nil/conversion/regular-prefix composition lemmas, so recursive imported statement-list proofs can preserve the stack-shape facts needed by scoped block and dispatcher closure. The interface keeps returned context layout separate from outcome-relation layout, because nonregular exits can clean to a continuation while `Block.runOpen` returns the syntactic context.
   - [x] Lift the existing checked regular statement-list cases (`let`, assignment, and nested scoped block) into the layout-carrying result bridge interface.
	   - [x] Start the source-tower version of the recursive imported statement-list bridge: `SourceBridgeFacts.SourceRegularSeqRunBridge` now has stack-free `let x`, `let x := literal`, `let x := y`, `x := literal`, and `x := y` cons theorems over `Functions.Source`, plus the visible-name store-insert/update relations they need. `SourceRegularSeqRunAt` is the target-fuel-parametric interface for future nested block/control composition and now has the same ordinary-head constructors; `SourceRegularSeqRunExact` specializes it where the source and target source interpreters consume fuel alike. `SourceResultSeqRunAt` is now the result-shaped sibling for regular, break, continue, leave, and terminal outcomes at the stack-free source boundary, with regular-to-result, nil, regular-head/result-tail composition, nonregular-head short-circuit composition, source-level `break`/`continue`/`leave` constructors checked against handler-scope cleanup, nested block regular/nonregular cases, false-`if`, true-`if` with regular and nonregular selected-body cases, no-selected-`switch`, selected-`switch` with regular and nonregular selected-body cases, and empty-init `for` cases for direct false conditions, the compiler-shaped `for 1`/`iszero(cond)` false guard, guarded body-break/body-leave/body-halt paths, guarded body-regular/body-continue followed by post halt, guarded body-regular/post-regular and body-continue/post-regular recursive steps, true-condition body `break`/`leave`/halt exits, body `regular`/`continue` followed by post halt, and both statement- and sequence-level body-regular/post-regular and body-continue/post-regular recursive steps. `SourceRegularStmtRunAt` and `SourceNonregularStmtRunAt` now provide a single-statement facade so recursive constructs can be proved at statement granularity before the sequence layer attaches the surrounding tail with its own fuel. Scoped block composition now has `SourceRegularBlockRunAt`, `SourceResultBlockRunAt`, `SourceNonregularBlockRunAt`, `SourceBreakBlockRunAt`, `SourceContinueBlockRunAt`, `SourceLeaveBlockRunAt`, `SourceHaltBlockRunAt`, block-from-open-sequence theorems, and a block-head source-sequence constructor, so bracketed lexical cleanup is handled at the source-tower boundary instead of through backend stack cleanup. `if` now has true/false `SourceRegularSeqRunAt` cons theorems driven by imported condition evaluation, `ExprValueSound`, and the source scoped-block bridge, and `switch` now has selected-branch and no-selected-empty-block source-tower constructors over imported scrutinee evaluation plus source/target branch selection evidence. The source/direct switch-selector equality is named so future proofs can consume existing compiled-branch selection evidence without exposing backend execution. This is the replacement direction for older direct/backend-shaped result bridge facts.
	   - [x] Extend the stack-free expression bridge with a generic primitive-call lifting theorem over `ExprArgListSound` plus a concrete `ADDRESS` expression theorem. Primitive expression preservation can now start at `ExprValueSound`/`ExprArgListSound`, without routing through backend stack/layout bridge facts.
	   - [x] Add `ExprValuePreludeSound` and `exprValuePreludeSound_prim_of_arg_prelude`, the source-tower interface for real Yul primitive-call lowering: imported arguments evaluate directly, compiler-facing source code runs a generated temporary-binding prelude, and the primitive expression then evaluates in the independent source interpreter.
	   - [x] Add `sourceRegularSeqRunAt_cons_let_expr_single`, a source-tower open-sequence constructor for `let x := expr` driven by `ExprValueSound`. The tail is a callback over the actual expression-result state, so no backend stack/layout witness or arbitrary compiler-state equality is exposed.
	   - [x] Add `sourceRegularSeqRunAt_cons_assign_expr_single`, the matching source-tower open-sequence constructor for `x := expr`. This keeps assignment expression preservation stack-free and callback-shaped over the real expression-result compiler state.
	   - [x] Add `SourceRegularSeqRunBridgeHidden`, a source-tower sequence bridge that permits target-only locals in the compiler-facing context while relating imported Yul on the visible source layout. This is the abstraction boundary needed for generated expression preludes without leaking stack/layout facts upward.
	   - [x] Add `GeneratedPrelude` plus `generatedPrelude_runOpen_append_regular_exists`, the compositional fuel helper for compiler-generated let-only expression preludes.
	   - [x] Add `sourceRegularSeqRunBridgeHidden_cons_let_expr_prelude`, connecting imported `let x := expr` with target generated preludes plus the final source-level `let` under the hidden-locals bridge.
	   - [x] Add `Locals.Source.Expr.eval_vars_eq` / `evalOne_vars_eq` and `generatedPrelude_runOpen_regular_preserves_contains`, then use them in `sourceRegularSeqRunBridgeHidden_cons_assign_expr_prelude` so imported `x := expr` also composes through generated expression preludes without exposing lower stack/layout facts.
	   - [x] Add lowering decomposition facts `toFunctionsListFuel?_let_prim_single_components` and `toFunctionsListFuel?_assign_prim_single_components`, splitting primitive-call `let`/assignment compiler output into generated RHS prelude plus the final source-level statement. User-function-call expressions intentionally remain a separate lowering shape.
	   - [x] Add `lower1?_prim_exprValuePreludeSound_of_lowerBound1?`, the source-tower semantic companion for primitive-call expression lowering. It packages the checked `Expr.lower1?` equality together with `ExprValuePreludeSound`, using the existing argument-prelude bridge and primitive semantic contract instead of exposing backend stack/layout facts.
	   - [x] Add lower-driven hidden-prelude source bridge wrappers for imported `let x := prim(...)` and `x := prim(...)`, combining compiler output decomposition with the stack-free primitive expression-prelude theorem.
	   - [x] Add the matching hidden-prelude source bridge for zero-result primitive expression statements, `prim(...)`, including a checked `lower0?` expression-prelude theorem and a `Stmt.toFunctionsListFuel?` decomposition wrapper. This gives regular memory/machine-state statement primitives such as `mstore`, `mstore8`, `mcopy`, `calldatacopy`, and `returndatacopy` the same stack-free imported-Yul sequence interface as primitive `let` and assignment RHSs. The primitive expression-prelude lowerer facts now use the stack-order argument adapter, matching `toStackSeq?`'s deliberate reversal instead of leaking or assuming source-order stack execution.
	   - [x] Add literal argument-lowering decomposition facts for singleton and pair `lowerBound1?` successes, exposing generated temporary shape from compiler output without requiring callers to spell the fresh-name proof route manually.
	   - [x] Add `FreshCoversLayout` transport lemmas for source-layout growth, used-list extension, one fresh allocation, general expression lowering (`Expr.lower?` / `lower1?` / `lower0?`), general bound argument lowering (`Expr.List.lowerBound1?`), and literal singleton/pair `lowerBound1?` successes, so the recursive checked bridge can thread generated-temporary freshness as an invariant instead of rebuilding it in each terminal/prelude proof.
	   - [x] Add generated literal terminal-prelude constructors for bound arguments and stack bounds, plus direct recursive result-sequence wrappers for generated-prelude `return(offset, size)`, `revert(offset, size)`, and `selfdestruct(recipient)`. These remove the semantic argument-prelude callback from that terminal path; remaining premises are the initial source/target relation, context layout, generated-layout `Nodup`, and the explicit terminal/revert relation contracts. The matching lowerer-aware wrappers consume actual `Stmt.toFunctionsListFuel?` output plus exact literal-argument decomposition, so callers no longer pass `BoundArgsBridgeWithLayoutSlotValues` or raw DUP-bound callbacks for these generated terminal cases. The auto dispatcher wrappers additionally derive generated temporary names and fresh-name distinctness internally, removing those compiler-created witnesses from the assembly and bytecode theorem boundary for literal `return`, `revert`, and `selfdestruct` preludes. The short `LayerAudit.ImportedYulBoundary` prelude aliases now point to these auto wrappers by default; older generated-evidence helpers are exposed only under explicit `RawGeneratedEvidence` names.
	   - [x] Add split/composition lemmas from layout-carrying result evidence into regular dispatcher preservation, terminal/error dispatcher preservation, and checkpoint dispatcher preservation.
	   - [x] Reroute the regular/source-block/source-result dispatcher compile-accepted preservation and whole-program gas-aware wrappers through `SourceLowered.runState` plus the source-facing compiler theorem, avoiding the old `Reference.SourceBridge` detour for those public generic paths.
	   - [x] Reroute the raw frame-bound regular/source-block/source-result dispatcher preservation wrappers and their gas-aware whole-program wrappers through `SourceLowered.runState` plus direct source-run preservation, leaving `Reference.SourceBridge` only on the explicitly legacy compatibility theorem path.
   - [x] Compose regular dispatcher-result bridge evidence through the assembly bytecode/gas-aware theorem, matching the EVM-facing theorem layer currently reached by `SourceBridge`.
   - [x] Compose nonregular terminal/error and checkpoint dispatcher-result bridge evidence through the assembly bytecode/gas-aware theorem.
   - [ ] Instantiate and prove that relation for compiled objects/contracts.
   - Prove expression, statement, loop, function-call, object, and primitive-call bridge lemmas from Nethermind Yul semantics into the compiler source semantics.
   - Compose the bridge with the existing lowering tower and gas-aware EVM theorem.
   - Current checked composition points: `Yul.Program.compile_source_preserves_checked_of_compileAccepted`, `Yul.Program.compile_preserves_of_reference_source_runs_compileAccepted`, `Yul.Program.compile_whole_program_result_sound_of_reference_source_runs_compileAccepted`, the dispatcher/root-block bridge theorems, and the legacy backend-only `Yul.Program.compile_whole_program_result_sound_of_lowered_bridge_with_result_rel`.
   - Remaining blocker: the active theorem spine now has a direct imported-run/source-run/bytecode composition target, but the fully general imported-Yul bridge still needs per-construct source-tower proofs from `Yul.Program.run`/`Reference.runResult` into `Yul.SourceLowered.runState` without packaging the run as `Reference.SourceBridge`. The separate `Reference.SourceBridge` and `Reference.LoweredBridge` facts remain legacy compatibility routes.
   - Active external-call checkpoint: the concrete `World` route has been retired in favor of `OpenExternal`, and the leftover closed precompile/child-dispatch support branch has been removed from the recursive bridge support file. The live gap is to route CALL-family primitive preservation through same-site open requests plus universally quantified shared responses that carry arbitrary opaque caller-visible state transformers. Gas mechanics are abstracted at this boundary: request equality keeps the requested-gas operand but does not require a concrete forwarded-gas calculation.
   - Semantic blockers fixed in the target fork: selected-branch switch execution, omitted default notation, and halting `SELFDESTRUCT` behavior. Argument-lowering now binds each argument before later argument effects. Remaining bridge blockers are proof-side: replacing `Reference.SourceBridge.sourceRun` with recursive per-construct source-tower theorems, proving source-to-direct function-call preservation, proving object/data/code-image relations, generalizing primitive bridges beyond the current checked arithmetic/comparison/bitwise-shift/modular-arithmetic/nullary-environment/state/machine-state/first one-argument read/state-update and `KECCAK256` slice (`ADD`/`MUL`/`SUB`/`DIV`/`SDIV`/`MOD`/`SMOD`/`ADDMOD`/`MULMOD`/`EXP`/`SIGNEXTEND`/`LT`/`GT`/`SLT`/`SGT`/`EQ`/`AND`/`OR`/`XOR`/`BYTE`/`SHL`/`SHR`/`SAR`/`KECCAK256`/`ADDRESS`/`ORIGIN`/`CALLER`/`CALLVALUE`/`CALLDATALOAD`/`CALLDATASIZE`/`GASPRICE`/`PREVRANDAO`/`BASEFEE`/`BLOCKHASH`/`BLOBHASH`/`BLOBBASEFEE`/`COINBASE`/`TIMESTAMP`/`NUMBER`/`GASLIMIT`/`CHAINID`/`SELFBALANCE`/`BALANCE`/`MLOAD`/`SLOAD`/`TLOAD`/`RETURNDATASIZE`/`MSIZE`/`GAS`), handling compiler-only temporaries emitted by expression preludes via scoped cleanup or an explicit hidden-local relation, and discharging code-size, remaining account-map-dependent reads, memory-write/storage-write, external-call/create, revert, selfdestruct-result/static-mode, and out-of-gas resource contracts.

## Layer Standard

- [ ] Syntax, independent executable semantics, relational semantics when useful, WF/acceptance, lowering, adjacent preservation theorem, composed public theorem. Transparent adapter boundaries are allowed only when they introduce no new source constructs and are explicitly audited.
  - [x] Assembly through Functions have independent executable semantics over their own syntax and checked adjacent preservation.
  - [x] Objects is an audited transparent root-object adapter with `Object.run` / `Program.run` and checked `run_toFunctions` / `eval_toFunctions`.
  - [x] Yul's public source interpreter is independent: `Yul.Program.run` enters the imported Nethermind interpreter, and `Yul.Reference.runResult` is an alias to that same boundary.
  - [x] Yul's compiler connection has a checked imported-run/source-run/bytecode composition theorem at the accepted boundary. Remaining incompleteness is source-language coverage and semantic-contract discharge, not a missing recursive bridge proof.
- [x] Lower-layer capabilities pass through unless intentionally abstracted or explicitly rejected by the accepted subset.
- [x] Public theorem is same-observation for the accepted source run boundary, not a replay certificate boundary.
- [x] Preferred gas-aware top theorem assumption audit:
  - [x] `Yul.Program.Accepted`, `Yul.Program.SourceAccepted`, and
    `Yul.Program.SourceAcceptedCore` are no longer preferred public premises:
    successful checked compilation constructs supported-syntax evidence and
    checks the lowered object/function source acceptedness, then reconstructs
    Yul `WF` internally.
  - [x] `RecursiveBridgeSourceRun` remains a fundamental input-execution and source-fuel boundary: the compiler cannot prove that an arbitrary imported run with a caller-chosen fuel and result occurred, nor that it avoided the imported successful `.OutOfFuel` marker.
  - [x] `RecursiveBridgeInitialWorldRel` remains a fundamental initial-state boundary: for an arbitrary `StateRelConfig`, source shared state, and EVM state, only the caller can supply the account/code/storage/machine-state relation.
  - [x] `RecursiveBridgeTerminalObservationContracts` remains a semantic observation boundary: it relates imported `YulHalt`/`Revert` results to source-tower halt states under caller-chosen terminal/revert relations, so it is not compiler-generated evidence.
  - [x] The public route takes the narrower source-facing
    `RecursiveBridgeExprNoOutOfFuelContracts` boundary directly. The old
    expression result-shape package is constructed internally from the imported
    safe-expression checkpoint theorem, leaving only the successful
    `.OutOfFuel` resource case pending a sufficient-source-fuel or
    actual-run-scoped theorem.
  - [x] The public route now exposes an explicit trace-local non-gas safety
    premise plus a checked finite gas-budget lower-bound theorem, rather than
    the older trace-to-`X` gas-precondition callback.
- [x] Layer audit gate: build, proof-hole scan, theorem names, remaining assumptions, and progress-log entry.
- [x] Root imports `EvmCompiler.LayerAudit`, a checked theorem-spine tripwire for
  the current public imported-Yul gas-aware theorem roots.
  - [x] `EvmCompiler.LayerAudit` now deliberately names only the two live
    imported-Yul gas-aware top roots. Solidity frontend and object/Yul-object
    public interfaces remain in their own modules, and stale audit/projection
    aliases are not kept alive there.

## Proof Hardening

- [x] Derive sufficient-gas witnesses from finite traces instead of taking them only as assumptions.
- [ ] Derive the remaining trace-local non-gas `EVM.X` safety checks from
  checked source/compiler facts or a checked target-core safety layer.
- [ ] Complete the CALL-family open external semantics spine: requests are
  forwarded-gas-free at the outside-world boundary while preserving the
  requested-gas operand, and the argument-prelude source/compiler,
  EVM-stack, and one-result expression-prelude adapters now reconstruct CALL
  operands from primitive arity and expose the open primitive
  request/response relation. Responses now carry an arbitrary reentrant
  opaque caller-visible state transformer, with preservation quantified over
  every response whose transformer keeps the Yul/compiler/EVM shared-state
  relation; assignment/let
  statement-continuation contracts, checked statement-lowering constructors,
  and CALL-safe argument-bundle adapters expose exact post-response status-word
  writes at the same lowering boundary the closed consumers inspect. The first
  open recursive-consumer frontier now attaches those assignment/let heads to
  the existing closed tail proof as an open head-plus-tail continuation, without
  unfolding closed `primCall`; tail-aware checked assignment/let sequence
  wrappers now compose CALL-safe lowering facts with that frontier, and
  accepted CALL-bridge wrappers derive the checked argument-prelude package
  from `ProgramCALLAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved`.
  The formerly raw nested-CALL argument-domain premise is now named as
  `EvalArgsReverseOkDomainExactContract`, with checked constructors from the
  old no-CALL primitive-family theorem and from a generic per-expression domain
  theorem; the open Yul CALL response continuation now also has checked
  local-frame and `evalValues`-shaped lemmas showing that arbitrary response
  mutations preserve the suspended varstore/domain and resume with exactly the
  response status word. A first checked Yul-side `YulOpenResult`/`YulOpen.eval*`
  skeleton now mirrors imported Yul argument/expression evaluation while
  suspending at CALL-family primitive requests, giving the nested-CALL argument
  proof an honest open source semantics to target; the support bridge now also
  packages primitive CALL suspension/resume for `YulOpen.evalValues` with exact
  status-word and local-domain preservation. The stale closed CALL branch
  that split precompile and
  child-code execution in `RecursiveBridgeSupport` has been deleted so the live
  proof no longer points back at a concrete callee/chain interpreter. The
  open Yul argument-domain layer now follows nested CALL suspensions through
  every response and recovers exact local-domain preservation for completed
  reversed-argument evaluation. The first generic compiler-side
  `OpenResult`/`OpenResultRel` surface now relates imported Yul open argument
  results to generated stack-argument preludes in the completed `.done` case,
  and its call branch now permits call-specific admissible-response predicates
  for nested state-dependent external calls. The checked hidden-context open
  sequence target and `CALLOpenSeqLoweringFrontierAt` now name the exact
  recursive-spine replacement needed for CALL: checked lowering to
  `YulOpen.execSeq`/`CompilerOpen`, with response preservation quantified by
  `OpenResultRel`, rather than the old closed sequence result relation.
  Remaining work is to make generated preludes produce that open result in the
  suspending case, prove the recursive assignment/let CALL consumers against
  `CALLOpenSeqLoweringFrontierAt`, construct expression-level instances of the
  open argument-domain contract, remove the old closed argument-domain premise
  from accepted CALL wrappers, and then compose to the EVM stack boundary.
- [ ] Replace the explicit bytecode jumpdest check with an imported or locally proved emitted-jumpdest theorem if EVMYulLean exposes enough scanner internals.
- [ ] Keep every new layer adjacent: prove preservation only to the layer immediately below, then expose a composed top theorem.

## Executable Stack Recurrence Analysis Roadmap

This roadmap records the replacement of the former proof-carrying
`proof-carrying source-run stack-headroom boundary` boundary with an executable
static analysis that checks EVM operand-stack safety for accepted programs,
including recursive internal-call cycles whenever a finite bound can be proved.

Definition of done: the preferred public no-CALL/CALL-compatible theorem uses a
checked compiler entry point whose stack-safety success is computed by Lean code,
not by `decide` over a semantic `Prop`. Checked success produces a theorem that
every source-frame state aligned with the compiled target trace satisfies
`Structured.Preservation.Frame.SourceStackHeadroom`, hence the target trace
satisfies `state.stack.length + 17 <= 1024` at every gas-aware `EVM.X` replay
point. The old proof-carrying semantic headroom artifact has been deleted from the
preferred no-CALL path; remaining source-run headroom names are derived facts
or transitional theorem variants, not compiler-acceptance evidence.

Non-goals:

- Keep the EVM top-16 `DUP`/`SWAP` addressability problem separate from the
  recursive call-depth proof.  It is now tracked below as a liveness/layout
  allocation task; until that pass is checked, actual `StackOp.dup?`/
  `StackOp.swap?` failures remain a sound conservative rejection.
- Do not accept general unbounded recursion. If an internal-call cycle can run
  for an unbounded number of active frames for some accepted input/state, the
  stack-safe checked compiler must reject it.
- Do not use source fuel as the stack proof. Source fuel is a semantic
  execution bound; compiler acceptance must prove a stack bound from the program
  and accepted static resource information.
- Do not hide compiler-generated call-depth or ranking evidence inside source
  acceptedness unless that evidence is produced and checked by an executable
  analyzer theorem.

### Current Boundary To Replace

- [x] Existing structured stack measure:
  `returnStackWeight returns`, `sourceStackWeight source`, and
  `SourceStackHeadroom source := sourceStackWeight source + 17 <= 1024`.
- [x] Existing target bridge:
  `Frame.StateRel.target_stack_headroom_of_source_headroom` converts source
  frame headroom into concrete target EVM stack headroom.
- [x] Former public wrapper:
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticStackSafeNoReturnDataCopy?`
  hid `RecursiveBridgeActualSourceRunFrameStackHeadroom` behind a
  proof-carrying semantic headroom artifact.  That wrapper has now been removed from
  `NoCallRuntime`.
- [x] Replace the wrapper with an executable stack-resource check that returns
  data in `Type` plus a checked soundness theorem.
- [x] Staged checkpoint: the stack-safe no-CALL wrapper now requires an
  executable lowered-function call-depth check result in `Type` before the old
  semantic stack-headroom premise is consulted.
- [x] Additive executable-only no-CALL gates now exist:
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableStackSafeNoReturnDataCopy?`
  for the default executable checker and
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticRankedExecutableStackSafeNoReturnDataCopy?`
  for explicit checked ranked graphs. The default compatibility checker still
  has branch-local inferred/self/mutual/guarded result projections, while
  the preferred default gate consumes the resource-checked `Option Nat`
  `recursiveBridgeSourceResourceDepth?` route and reconstructs the
  theorem-facing `RecursiveBridgeExecutableSourceRecurrenceCheckResult` only
  after source-frame EVM stack capacity has also been checked.
- [x] Add preferred-gate source-side stack-resource projections:
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_stackResourceCheck`
  and `_stackResourceSafe` expose the semantic `StackResourceSafe` theorem
  produced by the executable source recurrence check result directly from the
  same checked compile success used by `LayerAudit`.
- [x] Delete or demote the proof-carrying stack artifact from the preferred
  `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM` path.

### Phase 0: Truth And Scope Audit

- [x] Inventory every place the current public theorem or checked compiler path
  mentions `proof-carrying source-run stack-headroom boundary`,
  `RecursiveBridgeActualSourceRunFrameStackHeadroom`,
  the now-deleted `RecursiveBridgeActualSourceFrameStackHeadroomBound`, and
  `RecursiveBridgeActualEVMStackHeadroomBound`.
- [x] Confirm the first executable analysis target is the lowered function
  program plus the structured/procedure runtime frame shape: function
  `FrameBound` gives the 16-slot visible/caller-frame limit, while structured
  `returns` carries hidden return frames.
- [ ] Confirm the source-facing theorem target:
  executable analysis success implies all actual structured source frames in
  any accepted run satisfy `SourceStackHeadroom`.
- [x] Confirm the target-facing theorem target:
  source frame headroom plus existing frame relation implies the gas-aware
  target replay headroom needed by `EVM.X`.
- [x] Record the theorem-boundary audit in `PROGRESS_LOG.md`.

### Phase 1: Stack-Effect Algebra

- [x] Add a small executable stack-effect API near the structured layer:
  `StackDelta`, `StackPeak`, `StackSummary`, or equivalent.
- [ ] For each `Structured.BasicOp`, compute:
  required input height, output delta, maximum transient stack growth, and
  whether the operation can suspend/open-call in the CALL-enabled branch.
- [x] For `Structured.BasicInstr` and `Structured.Code`, compute exact
  stack-height transformers over a symbolic visible height, returning `none`
  on possible underflow or unknown effect.
- [ ] Prove soundness:
  if code analysis succeeds at visible height `h`, any successful `Code.run`
  from a state with stack length `h` has the predicted final height and never
  exceeds the predicted peak.
- [x] Staged soundness checkpoint: proved final-stack-height soundness for
  `Structured.Code.run` when the executable analyzer succeeds over supported
  continuing primitive steps.
- [x] Staged peak checkpoint: proved `Code.RunStackBoundedBy`, so any
  successful straight-line `Code.run` stays below the analyzed peak at every
  instruction boundary for the supported continuing primitive fragment.
- [x] Strengthened straight-line peak checkpoint:
  `Code.runStackBoundedBy_of_analyzeFrom?` proves the per-instruction stack
  bound directly from executable analysis without requiring a completed run,
  and `Code.source_runResult_stackBoundPoints_of_analyzeFrom?` turns that
  bound into annotated assembly-source replay points.
- [x] Prove monotonicity:
  if a summary is safe at height `h`, it remains safe at `h + k` with peak
  shifted by `k`.
- [ ] Keep this phase independent of procedures and recursion.

### Phase 2: Structured Statement Summaries

- [ ] Define executable outcome summaries for statements and blocks, indexed by
  mode: regular, break, continue, leave, and terminal halt/revert.
- [ ] Track for each possible outcome:
  final visible stack delta, maximum visible-stack peak before that outcome,
  and call-site obligations encountered along the path.
- [ ] Prove sequence composition generically:
  `summary(s1; s2)` is sound from `summary(s1)` plus `summary(s2)` at each
  regular final height.
- [ ] Prove branch composition generically:
  `if`/`switch` summaries take the maximum peak of condition evaluation and
  selected branches, with all branch outcomes preserved.
- [ ] Prove loop summaries with explicit invariants:
  continue edges must return to the loop header height, break edges must match
  the loop exit shape, and the body peak is bounded by the loop invariant.
- [ ] Reject or report any construct whose existing `WF` permits stack-shape
  behavior the analyzer cannot summarize.

### Phase 3: Procedure And Call-Graph Extraction

- [ ] Compute one local non-recursive summary per procedure body with internal
  call sites left as symbolic edges.
- [ ] For each internal call edge, record:
  caller procedure, callee procedure, call-site prefix peak, visible-height
  delta at the call, callee argument count, callee return count, and normal
  return continuation height.
- [x] Prove the key internal-call weight equation:
  after `splitArgs?` and `pushReturn`, `sourceStackWeight` increases by exactly
  `1` over the caller pre-call weight.
- [ ] Prove call-return weight equations for regular and leave/terminal
  outcomes, including `attachReturns` and hidden return-frame popping.
- [x] Staged return-weight checkpoint:
  `popReturn?` plus `attachReturns?` proves the caller-restored
  `sourceStackWeight` is exactly one word less than the callee pre-return
  weight; terminal no-attach paths still need outcome-specific wiring.
- [ ] Prove local summary soundness assuming a symbolic bound for each callee.
- [x] Build an executable call graph over function/procedure names, including
  main as a distinguished root. Current checked integration uses the lowered
  function graph; `Structured.StackResource` also has a structured call graph
  skeleton.
- [x] Prove static call-depth checker soundness for the acyclic lowered
  function graph: every root-reachable `FunctionPath` has length bounded by
  the executable `StackDepthCheckResult.depth`.
- [x] Add endpoint-aware static paths and an active call-stack relation:
  `FunctionPathTo` records the current function reached by a root call path,
  `ActiveCallStack` tracks the proof-side internal function chain, and the
  executable `StackDepthCheckResult` bounds the active chain length.

Core recurrence model:

- [ ] Define procedure entry weight abstractly as
  `ambientHiddenWeight + argc(proc)`, where `ambientHiddenWeight` accounts for
  caller frames already in `returns`.
- [ ] Define `ProcExtraPeak[p]` as the maximum extra `sourceStackWeight` above
  procedure `p` entry over every execution path of `p`.
- [ ] For an internal call edge from `p` to `q`, prove and use:
  `calleeEntryWeight = callerPreCallWeight + 1`.  The `+1` is the hidden return
  token; the callee arguments replace the visible caller stack, but the caller
  stack is moved into `returns`, so no other weight is lost.
- [ ] For an acyclic call edge, the callee contribution is:
  `edgePrefixExtra + 1 + ProcExtraPeak[q]`.
- [ ] For a bounded recursive SCC with active-frame bound `D`, the SCC
  contribution is bounded by the maximum checked call path of length at most
  `D`, adding one hidden token per active internal call plus each procedure's
  local peak along that path.
- [ ] The checker accepts only when the root bound satisfies:
  `initialSourceStackWeight + ProcExtraPeak[root] + 17 <= 1024`.

### Phase 4: Acyclic Recurrence Solver

- [ ] Detect strongly connected components and topologically order the acyclic
  component graph.
- [ ] For acyclic components, solve exact maximum active-frame/stack peak by
  longest-path dynamic programming over call edges.
- [x] Staged acyclic hidden-return word-sum checkpoint:
  `FunctionPathFrameWords`, `Program.maxActiveFrameWords?`,
  `Program.stackFrameWordSumCheck?`, and
  `Program.maxActiveFrameWords?_sound` compute and prove a maximum accumulated
  hidden-return-frame word sum along acyclic function-call paths.  Cycles and
  unresolved callees are rejected by computation.  This is more precise than
  `maxSourceReturnFrameWords * maxFrames` for acyclic graphs.
- [x] Add the first exact accumulated-weight source/direct bridge:
  `FunctionPathFrameWordsTo`, `Program.ActiveCallFrameWords`,
  `ActiveHiddenFrameWordsContext`, and `SourceDirectWeightedFrameContext`
  relate the active function-name path to the concrete hidden return frames,
  prove concrete `returnStackWeight` is bounded by the active path's accumulated
  frame words, and derive `Frame.SourceStackHeadroom` directly from
  `StackFrameWordSumCheckResult`.  Main, root-call, internal-call, target-body
  context, and same-hidden-return state/layout update constructors are checked.
- [ ] Lift the hidden-return word-sum checker into the source/direct resource
  context, replacing the uniform `SourceDirectFrameWordsContext` budget with a
  checked accumulated-weight invariant over actual active call paths.  Remaining
  work: add the return/pop inversion and thread this context through the
  recursive preservation callback records before swapping the public gate.
- [ ] Compute procedure bounds:
  `ProcExtraPeak[p]` is the maximum additional `sourceStackWeight` above the
  procedure entry weight for all executions of `p`.
- [ ] Compute root bound from canonical entry:
  main entry visible stack plus hidden return weight plus `ProcExtraPeak[main]`
  plus the reserved 17 slots is at most 1024.
- [ ] Prove solver soundness by induction over the component topological order.
- [ ] Wire acyclic success into the checked compiler as the first executable
  replacement for the proof-carrying stack artifact.

### Phase 5: Bounded Recursive SCC Check Results

- [x] Define a checked `SCCRecurrenceCheckResult` in `Type`, generated or
  verified by executable code, not by arbitrary semantic `Prop`.
- [x] Checked result fields should include:
  SCC procedures, entry procedures, maximum active frames per procedure or per
  SCC, edge traversal bounds, and proof/check data explaining why every cycle
  decreases a finite measure or is otherwise finitely unfoldable.
  Current checked surface:
  `SCCRecurrenceCheckResult` packages the accepted guarded-zero SCC procedure
  names, entry ranked nodes, ranked edges, maximum active-frame count, and the
  executable guarded-zero backend result. The Yul bridge exposes the same
  data as `RecursiveBridgeExecutableSCCRecurrenceCheckResult`, with a
  `LayerAudit` tripwire proving it yields the theorem-facing
  `SourceRecurrenceBound`.
- [ ] Start with a simple fully executable check result:
  user/program-side finite unfolding bound for an SCC plus an executable check
  that all paths up to that bound either leave the SCC or are rejected.
- [x] Add the generic ranked call-state checker kernel:
  `CallDepth.Ranked` checks a finite graph of `(functionName, rank)` nodes,
  proves every accepted root path is bounded by the computed depth, accepts
  abstract finite countdown graphs, and rejects an unranked self-loop. The
  generic kernel alone does not validate a raw recursive source body; source
  patterns need a separate executable analyzer that ties ranks to reachable
  calls.
- [x] Add the ranked active-stack bridge:
  `CallDepth.Ranked.ActiveCallStack` relates runtime active function-name
  stacks to ranked node paths and proves the ranked check result gives the
  active-length bound consumed by `RuntimeCallStackShape.WithBound`.
- [x] Add executable ranked graph conformance checking:
  `graphConforms?` verifies that ranked roots cover real main-body internal
  calls and every ranked function node has a ranked successor for each
  syntactic internal call in that function body; its soundness theorem supplies
  the next ranked node during root and nested call threading.
- [x] Add `RankedResourceContext`: the ranked active-node path is packaged with
  source/direct stack-resource context, with checked constructors for main,
  root internal calls, nested internal calls, and returns over the shared
  generic stack budget.
- [x] Add the first state-sensitive call-summary proof interface suggested by
  the oracle architecture critique: `ConcreteCallChain` and `CallGraphSound`
  abstract over concrete frames, root frames, direct-call steps, and a
  `Matches : Node -> Frame -> Prop` relation.  The generic theorem
  `CallGraphSound.chain_to_path` turns any matched concrete call chain into a
  ranked graph `Path`, and the existing all-syntactic `ProgramConformance`
  checker is now exposed as one coarse function-name instance of this
  interface via `ProgramConformance.toCallGraphSound` and
  `CheckedProgramCheckResult.callGraphSound`.
- [x] Connect the state-sensitive call-summary interface to checked ranked
  depth: `CallGraphSound.chain_frame_count_bound` combines any
  `CallGraphSound` instance with `Program.RankedDepthCheckResult` to prove
  `depth + 1 <= check.depth` for concrete call chains, and
  `CheckedProgramCheckResult.directNameCallChain_frame_count_bound` gives this
  theorem for the existing coarse function-name conformance checker.
- [x] Factor graph path bounds away from ranked checker representations
  following oracle
  `resp_035b8a5ebe06bc7b006a1b43188f7c819899b0e1be12b74ca4`:
  `GraphStep`, `RootedGraphDepthBound`,
  `CallGraphSound.graph_chain`, and
  `CallGraphSound.chain_bound_of_graph_bound` are the generic backend, while
  `Program.RankedDepthCheckResult.toRootedGraphDepthBound` makes the existing
  ranked checker one implementation of that backend.
- [x] Add the common semantic call-depth contract:
  `CallChainDepthBound RootFrame DirectCall bound`, plus
  `CallGraphSound.callChainDepthBound_of_graph_bound` and
  `callChainDepthBound_of_ranked`, so checker frontends can discharge one
  depth-bound Prop instead of leaking recognizer-specific data.
- [x] Add the oracle-recommended height-bound backend:
  `HeightBound` proves any rooted transition system with decreasing edge
  heights has bounded concrete chains, and `GraphHeight.graphHeightBound?`
  is a small executable validator from node heights to
  `RootedGraphDepthBound`. This gives future raw source-recurrence checkers a
  simpler proof target than re-proving DFS longest-path algorithms.
- [x] Instantiate the state-sensitive call-summary interface for the
  `GuardedZeroCalls` checker over its abstract rank-frame model:
  `GuardedZeroCalls.CheckResult.callGraphSound` proves that every
  accepted abstract direct call `(rank 1 caller) -> (rank 0 callee)` is backed
  by a checked ranked edge, and
  `GuardedZeroCalls.CheckResult.abstractCallChain_frame_count_bound`
  derives the checked frame-count bound from the generic ranked-depth theorem.
- [x] Add a concrete guarded source-call frame model over actual argument
  words: `GuardedZeroCalls.SourceCallFrame` ranks singleton zero arguments as
  rank zero and singleton boolean-`!= 0` arguments as rank one, matching
  `Functions.Source.Expr.evalCondition`,
  `SourceDirectCall.not_from_rank_zero` proves rank-zero guarded frames cannot
  make guarded recursive calls, and
  `CheckResult.sourceCallGraphSound` /
  `sourceCallChain_frame_count_bound` / `sourceCallDepthBound` instantiate the generic
  `CallGraphSound`/graph-bound route for those argument-carrying frames.
- [x] Add source-semantic call extraction facts:
  `Functions.Source.ArgList.eval_single_lit`,
  `Functions.Source.Stmt.call_regular_parts`, and
  `Functions.Source.Stmt.call_halted_parts` expose branch-specific evaluated
  argument values, selected function, and callee `runBody` result from actual
  source `.call` executions. `Functions.Source.Stmt.call_ok_parts` packages
  the same facts for any successful call outcome.
- [x] Add guarded checker/source-frame bridge constructors:
  `sourceRootFrame_of_rootFromCall?_mem` and
  `CheckResult.sourceRootFrame_of_rootFromCall?` connect accepted
  literal root-call extraction to `SourceRootFrame`;
  `CheckResult.sourceDirectCall_of_shape_nonzero` connects checked
  guarded shapes plus actual nonzero argument values to `SourceDirectCall`;
  `CheckResult.shape_body_facts` exposes the exact one-parameter,
  no-return, guarded-zero-call function body shape.
- [x] Add actual-source-run bridge wrappers for the guarded frame model:
  `CheckResult.sourceRootFrame_of_call_run_rootFromCall?` consumes a
  real `Functions.Source.Stmt.run` call execution together with checked root
  extraction, and
  `CheckResult.sourceDirectCall_of_runBody_nonzero` consumes a real
  `Functions.Source.FunDef.runBody` execution plus a checked guarded shape and
  nonzero argument to produce the `SourceDirectCall` edge. The stronger
  `_parts` variants now also return `SourceCallRunParts` /
  `SourceRunBodyParts`, so those wrappers expose the actual evaluated
  arguments, lookup, and body-run facts they consume instead of treating source
  execution as an unused premise. The Yul guarded executable check result
  projects the same `_parts` facts.
- [x] Add the guarded-cycle source/direct resource-context constructor:
  `GuardedZeroCalls.CheckResult.callBodyOneToZero` threads
  `RankedResourceContext` through an internal call when the current ranked
  node is `(caller, 1)` and the executable checker accepted the
  `(caller, callee)` shape, producing the `(callee, 0)` successor context.
  `rootCallBody_of_sourceRootFrame` and
  `callBody_of_sourceDirectCall` are the source-frame-facing constructors that
  connect `SourceRootFrame`/`SourceDirectCall` to the ranked resource context,
  and the Yul guarded executable check result projects both. The remaining
  semantic obligation is to route the actual preservation trace through these
  source-frame constructors globally.
- [x] Add a branch-free theorem-facing source recurrence wrapper:
  `RecursiveBridgeExecutableSourceRecurrenceCheckResult` exposes only
  `maxFrames`, the checked budget, and `StackResourceSafe`, while
  `RecursiveBridgeExecutableStackCheckResult.toSourceRecurrenceCheck`
  hides the current inferred/self/mutual/guarded recognizer constructors.
  Both checked compile gates now project this wrapper via
  `_sourceRecurrenceCheck` and `_sourceRecurrenceSafe`.
- [x] Add the semantic call-depth contract bridge:
  `SourceCallDepth.Bound` is the theorem target for analysis-independent root
  and direct-call predicates, and `CheckResult.sourceCallDepthBound_of_covered`
  proves the guarded checker bound can be consumed only after callers prove
  their semantic root/direct-call predicates are covered by the checked
  root/edge relations. `GuardedSemanticDirectCall` now describes the guarded
  direct-call relation from source program syntax (`functionShape?` plus
  actual frame argument class), and
  `sourceDirectCall_of_guardedSemanticDirectCall` proves it is covered by the
  checked graph shapes. `GuardedSemanticRootFrame` now describes accepted
  guarded source-entry root calls from the program body syntax, independently
  of the checked `roots` list, and
  `sourceRootFrame_of_guardedSemanticRootFrame` proves those semantic roots
  are covered by checked roots. The guarded checker now exposes
  `sourceCallDepthBound_of_guardedSemantic`, a complete semantic
  root/direct-call depth bound for the currently accepted guarded fragment.
- [x] Prove this check result sound:
  no accepted execution can have more active frames in the SCC than the checked
  bound.
  Current checked surface:
  `SCCRecurrenceCheckResult.guardedSemanticRootChain_frame_count_bound` proves
  every guarded semantic root/direct-call chain has at most `maxFrames` frames,
  and `guardedSemanticFrameStack_length_le` packages the same fact for
  concrete active frame stacks. The Yul
  `RecursiveBridgeExecutableSCCRecurrenceCheckResult` projects both facts, and
  `LayerAudit` has a tripwire from executable SCC checker success to the
  exported frame-count bound.
- [ ] Combine SCC-local bounds with local per-procedure peaks:
  peak inside a bounded SCC is at most entry weight plus the maximum prefix
  peak along one bounded call path plus one hidden return-token word per active
  frame.
- [x] Reject SCCs with no checked finite-depth result.
  Current default recurrence/resource gates expose
  `sourceRecurrenceDepth?_none_of_default_branches_none` and
  `sourceResourceDepth?_none_of_default_branches_none`: if the acyclic
  analyzer fails and the checked SCC route returns `none`, both
  executable gates reject. The Yul bridge forwards the same negative
  projections, with `LayerAudit` tripwires.

### Phase 6: Ranking-Based Recursive Power

- [ ] Add interval/range abstract interpretation over relevant Yul/structured
  values so bounds can be inferred from guards like `x < C`, `x <= C`, and
  constant assignments.
- [ ] Add affine ranking check results:
  a measure is a bounded natural expression over procedure arguments/locals,
  each recursive edge proves the measure decreases, and all non-recursive paths
  preserve the measure domain.
- [ ] Add lexicographic ranking check results for mutual recursion.
- [ ] Add finite-state check results for enum-like recursion, dispatch tables,
  and bounded switches.
- [ ] Add path-sensitive guard refinement so mutually exclusive branches do not
  force worst-case joins too early.
- [ ] Add loop-call integration:
  loops that contain recursive calls must either have a loop-iteration bound or
  contribute to the same SCC ranking check result.
- [ ] Prove each ranking family sound by reducing it to the generic
  `SCCRecurrenceCheckResult` active-frame bound.

### Phase 7: Analyzer/Checker Split

- [x] Separate inference from checking:
  `inferStackRecurrences? program` may be heuristic and incomplete, while
  `checkStackRecurrenceCandidate? program check` is small, executable, and
  proved sound.
  Current API:
  `CallDepth.Ranked.StackRecurrenceCandidate` is the small sidecar format,
  `checkStackRecurrenceCandidate?` validates it, and
  `inferStackRecurrenceCandidate?`/`inferStackRecurrences?` are deliberately
  separate from the checker.
- [x] Add checked ranked result packaging:
  `checkedProgramCheck?` combines executable ranked-depth checking and
  executable ranked graph conformance into a single `CheckedProgramCheckResult`
  in `Type`, with theorem projections to stack budget and conformance.
- [x] Add a conservative built-in analyzer/checker path:
  `inferAcyclicCheck?` emits a rank-zero graph from the lowered
  function call graph and immediately validates it with
  `checkedProgramCheck?`. This gives the compiler tower an executable
  inference surface for acyclic programs while keeping recursive cycles rejected
  until a real guard/ranking analysis supplies path-sensitive ranked nodes.
- [x] Add the first path-sensitive executable recursive source checker:
  `CallDepth.Ranked.SelfGuardedOnce.checkResult?` recognizes the narrow
  lowered-functions pattern `f(counter) { if counter { f(0) } }` with literal
  root calls, assigns rank zero to zero roots and rank one to nonzero roots,
  rebuilds the finite ranked graph, and rechecks the depth/budget result.
  `CallDepth.Ranked.MutualGuardedOnce.checkResult?` extends the same
  finite rank-one idea to exactly two functions that guard on their own
  counter and call the other function with literal zero.  The default
  executable source-side check result now also tries
  `CallDepth.Ranked.GuardedZeroCalls.checkResult?`, which accepts any
  finite set of one-step guarded functions `if counter { callee(0) }` whose
  callees stay inside the checked function set.  The preferred public no-CALL
  gate combines that source recurrence check with inferred target assembly
  stack bounds.
- [x] Let the compiler use inference by default, then verify the inferred
  recurrence data with the checker.
  Current default:
  `recursiveBridgeExecutableStackCheck?` first delegates to
  `recursiveBridgeExecutableInferredRankedStackCheckResultAsStack?`, whose
  current analyzer emits a conservative rank-zero graph and validates it with
  `checkedProgramCheck?`. If that fails, it now tries the checked
  `SelfGuardedOnce`, `MutualGuardedOnce`, and generic `GuardedZeroCalls`
  source recurrence paths, so the default executable source-side check result
  accepts bounded one-step self, mutual, and larger finite recursive cycles.
- [x] Add default-branch equations for the executable source recurrence checker:
  `recursiveBridgeExecutableStackCheck?_of_inferredRanked`,
  `recursiveBridgeExecutableStackCheck?_of_selfGuardedOnceChecked`,
  `recursiveBridgeExecutableStackCheck?_of_mutualGuardedOnceChecked`,
  `recursiveBridgeExecutableStackCheck?_of_guardedZeroCallsChecked`, and
  `recursiveBridgeExecutableStackCheck?_none_of_branches_none` prove that
  the default checker accepts exactly through the inferred ranked branch or the
  checked guarded fallbacks, and rejects when all branches fail.
- [x] Permit optional explicit recurrence evidence only if it is checked by the same
  executable checker and is not trusted by theorem statements.
  Current explicit ranked route:
  `recursiveBridgeExecutableRankedStackCheck? program edges roots` first
  validates the supplied graph with `checkedProgramCheck?`, and the
  stack-check wrapper only exposes checked-success projections. The
  default public route still uses inferred check results.
- [x] Keep check-result formats stable and small enough that Lean proofs can
  reason about checker success without unfolding the whole analyzer.
  Current guarded projections expose `maxRank <= 1` and prove the checked graph
  is either empty, exactly the single `1 -> 0` self edge, or exactly the two
  `left(1) -> right(0)` / `right(1) -> left(0)` mutual edges.  The generic
  `GuardedZeroCalls` projection proves every accepted root has rank at most
  one, the checked function-name set is duplicate-free, every guarded callee
  stays inside that checked set, and every generated body edge goes from rank
  one to rank zero.
- [x] Add the raw executable depth sidecar for the source-recurrence boundary:
  `Program.rankedMaxRootDepth?`, `checkedProgramRecurrenceDepth?`,
  `inferAcyclicRecurrenceDepth?`, guarded-zero `checkedDepth?`, and
  `sourceRecurrenceDepth?` compute only an `Option Nat`. Their soundness
  theorems reconstruct a semantic `SourceRecurrenceBound` and the max-frame
  bound from raw success without proving equality of proof-carrying `Option`
  results or smuggling in the EVM stack-capacity check. The public raw route now
  uses the inferred acyclic analyzer or the generic guarded-zero analyzer; the
  older self/mutual recognizers remain checker-local compatibility machinery
  rather than public source-recurrence branches. The Yul raw wrapper now proves
  raw success gives a Yul-level `RecursiveBridgeSourceRecurrenceBound`; the
  preferred default compile gate consumes the stronger resource checker below.
- [x] Split source recurrence from source resource capacity:
  `sourceStackWordsForMaxFrames`, `sourceStackFitsEVM`,
  `SourceResourceBound`, and `sourceResourceDepth?` make the stack-capacity
  arithmetic an explicit checker result. The source-resource checker now runs
  an ordered list of recurrence analyzers via `firstSome?` and per-analyzer
  `resourceDepth?`, continuing past any analyzer whose sound bound is too large
  for the EVM stack. Resource success therefore proves a `SourceResourceBound`
  directly rather than pretending it is the same result as the first raw
  recurrence analyzer. The acyclic raw analyzer now uses the budget-free
  `checkedProgramRecurrenceDepth?`, so `sourceRecurrenceDepth?` can accept an
  acyclic depth-59 program while `sourceResourceDepth?` rejects it at the stack
  capacity layer. The preferred source stack gate now calls
  `recursiveBridgeSourceResourceDepth?`, and public projections expose a
  Yul-level `RecursiveBridgeSourceResourceBound` instead of relying only on the
  compatibility `StackResourceSafe` projection. `SourceResourceBound` now also
  exposes the exact `StackBudget`, `StackResourceSafeFromBase`, and
  direct base-context-to-headroom/resource-context constructors, keeping the
  actual active-depth/reachability premise explicit while letting preservation
  consume the semantic resource predicate rather than analyzer branch facts.
  The capacity check is now the explicit executable bound
  `sourceMaxFramesForEVM = 58`, with
  `sourceStackFitsEVM_iff_le_sourceMaxFramesForEVM` proving it equivalent to
  the stack-word formula.
  The no-CALL executable source stack gate now has an internal full-result
  checker,
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableStackSafeNoReturnDataCopyFull?`,
  that stores the accepted `asm`, `target`, and checked `sourceDepth`; the
  public pair-returning checker is a projection from that record. The preferred
  combined source-resource plus inferred-assembly-bound gate now has its own
  internal full-result checker,
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopyFull?`,
  which additionally stores the rechecked inferred assembly stack-bound
  result while keeping the public pair-returning checker as a projection.
  The public assembly-bound projection now chooses this retained full checked
  artifact first and returns its `assemblyBound` field, rather than recovering
  unrelated existential evidence from the pair-returning theorem. The
  public source-resource projection likewise routes through the retained
  `sourceDepth` field, so successful pair-returning compilation exposes the
  exact source resource result used by the full checker. The public
  stack-resource projection now also builds directly from the
  retained `RecursiveBridgeSourceResourceBound` evidence, and `LayerAudit`
  checks that its budget depth is the checked `sourceDepth`, avoiding the older
  route through separately chosen source-recurrence evidence.
- [x] Add a semantic source active-depth contract behind the resource checker:
  `SourceCallDepth.Contract`, `Contract.Valid`, and
  `SourceCallDepth.ActiveDepthBound` now separate the theorem-facing source
  active-depth predicate from analyzer-specific recurrence wrappers.
  `SourceResourceBound` derives this `activeDepth` evidence from its retained
  `SourceRecurrenceBound`, avoiding a second proof field that could drift from
  the executable recurrence evidence. The no-CALL Yul gate now exposes this
  through `RecursiveBridgeSourceActiveDepthBound`,
  `recursiveBridgeSourceResourceDepth?_sourceActiveDepthBound`, and the
  preferred combined checked projections
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_checked_sourceActiveDepthBound`
  /
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?_sourceActiveDepthBound`.
  The source-resource layer also has a semantic active-stack witness
  interface: `SourceCallDepth.ActiveStack` and
  `SourceCallDepth.ActiveStackWitness` prove the active-frame count from a
  valid contract depth bound, and `SourceResourceBound` can now derive
  source stack headroom or a `SourceDirectResourceContext` from that witness
  instead of consuming only a bare `active.length <= maxFrames` arithmetic
  premise. At the Yul boundary,
  `RecursiveBridgeSourceDirectActiveResourcePoint` fixes this witness to the
  retained `RecursiveBridgeSourceResourceBound` evidence at each trace point;
  `RecursiveBridgeActualSourceRunActiveResourcePoints` lifts that predicate
  across the gasless assembly source run and projects back into the existing
  compatibility `RecursiveBridgeActualSourceRunFrameStackResourcePoints`.
  The preferred combined compile gate now has an active-resource-point
  projection theorem, direct active-resource-to-context/headroom wrappers, and
  `LayerAudit` checks that this route can feed the public source-frame
  headroom interface.
  The active-stack witness now records a contract frame-name projection and a
  concrete constructor-built frame stack, so the semantic frames must map to the
  actual active function-name stack and be consecutive root/direct-call frames
  rather than merely sharing the active stack's length. `Program.ActiveCallStack`
  now carries the corresponding constructor-built name chain while preserving
  the old root-to-last path projection for existing proofs. The by-name
  contract has a checked constructor from this stronger `Program.ActiveCallStack`,
  giving preservation a direct path to populate the stronger witness for
  acyclic/name-graph resource bounds.
  The guarded-zero contract also has checked constructors for the empty stack,
  a semantic root frame, and one guarded semantic direct-call extension; these
  are the concrete witness forms needed by the current bounded-recursive
  checker.
  `SourceResourceBound.activeStackWitness_empty` now packages the generic
  empty-stack witness directly from the retained active-depth contract, and the
  corresponding empty-stack source-headroom/resource-context helpers avoid
  rebuilding that existential at entry points.
  For the acyclic/name-graph branch,
  `SourceResourceBound.activeStackWitness_of_programActive_byName` now turns
  the existing `Program.ActiveCallStack` invariant into the stronger semantic
  active-stack witness whenever the retained recurrence proof is the by-name
  constructor.
  `RecursiveBridgeSourceDirectActiveResourcePoint` now has preservation-facing
  `of_base`, `of_base_prefix`, `of_base_empty`, and `of_base_prefix_empty`
  constructors from
  `SourceDirectBaseContext`, the active-stack witness, and the ordinary frame
  relation, so future preservation lemmas can populate active resource points
  without reconstructing the compatibility transient resource package by hand.
  The base/resource contexts also have `withStateRel` same-frame update
  helpers plus `withStateRelLayout` variants for regular statements that grow
  or shrink the local layout under an explicit `layout.length <= 16` proof.
  Regular statement/open-block/scoped-block result relations now rebuild the
  same active base context from their source/direct `StateRel`; the Yul
  active-resource point has matching regular-result constructors. These are the
  non-call preservation bricks: source/direct state changes can reuse the same
  active call-stack evidence while replacing only the layout/hidden-return
  `StateRel` and structured frame relation.
  The by-name variants `of_base_byName` and `of_base_prefix_byName` consume the
  existing source/direct base context directly and derive the witness from the
  checked by-name recurrence branch.
  Remaining hardening: refine `Contract.Valid` into the final reachable
  preservation-trace active-depth/source-stack predicate instead of a small
  registry of known semantic contract families.
- [x] Move branch details behind checker-local soundness facts:
  successful
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`
  now exposes source-resource success and the reconstructed theorem-facing
  source recurrence bound. Branch-local facts such as
  empty-or-`1 -> 0`, mutual two-edge shape, duplicate-free checked names,
  callee closure, checked function-body call facts, and rank-one-to-zero edges
  remain available on the private checker results rather than being
  exported by the public compile-success theorem.
- [x] Add negative examples where the executable checker must reject unsafe
  recursive shapes.  Current examples reject unguarded self-recursion,
  non-decreasing guarded self-recursion, and guarded mutual recursion; the
  plain inferred checker still rejects the accepted `SelfGuardedOnce` program,
  proving that bounded recursive acceptance comes only from the path-sensitive
  fallback.

### Phase 8: Source-Run Headroom Theorem

- [x] Define the source/direct semantic `StackResourceSafe` surface produced by
  executable checker success.  Current checked location:
  `Functions.CallDepth.Program.StackResourceSafe` over the lowered function
  program, with `StackResourceCheckResult` projections for acyclic and ranked
  executable check results.
- [x] Prove the arithmetic bridge:
  `RuntimeFrameShape depth source` plus the executable budget
  `16 + 17 * depth + 17 <= 1024` implies
  `Structured.Preservation.Frame.SourceStackHeadroom source`.
- [x] Add the parameterized arithmetic bridge:
  `RuntimeFrameShape depth source`, a per-hidden-frame word bound, and an
  executable budget `16 + frameWords * depth + 17 <= 1024` imply
  `SourceStackHeadroom`.  The preferred source-side stack route now uses the
  frame-word-refined executable checker, after the source/direct callbacks were
  strengthened to derive the call-entry argument/caller-stack bound from actual
  preservation facts.
- [x] Thread call-entry frame-word evidence through the source/direct
  recursive callback surface.  The checked route now derives the needed
  `callee.params.length + callerStack.length <= 16` fact from the actual call
  prelude, argument evaluation, parameter insertion, and frame-bound access
  check, rather than exposing raw `splitArgs?` evidence at the callback
  boundary.
- [x] Add the refined source/direct context and checked executable resource
  route:
  `SourceDirectFrameWordsContext` carries per-hidden-frame word bounds,
  `callerFrameWords_le_programMax_of_splitArgs?` derives the pushed frame bound
  from actual `splitArgs?` evidence plus the executable program summary, and
  `SourceFrameWordsResourceBound` converts the program-summary stack-capacity
  check into `SourceStackHeadroom` for those refined contexts.
- [x] Add a verified weighted-frame refinement sidecar:
  `Program.maxActiveFrameWords?` and `Program.stackFrameWordSumCheck?` compute
  the maximum sum of actual per-frame `sourceReturnFrameWords` along each
  acyclic root path, with `LayerAudit` tripwires for checked-success projection
  and path-bound soundness.  The follow-up weighted source/direct context uses a
  pointwise active-name/hidden-frame relation, proves concrete source-stack
  headroom from the weighted checker, and has checked call-push plus return-pop
  threading through `SourceDirectWeightedFrameContext`.  The exact route now
  also has a checked resource wrapper,
  `SourceFrameWordSumResourceBound`, plus a Yul bridge wrapper
  `RecursiveBridgeSourceFrameWordSumResourceBound` and executable check
  `recursiveBridgeExecutableFrameWordSumStackCheck?`.  The Yul bridge now also
  has `RecursiveBridgeSourceDirectFrameWordSumPoint`, with main/call/return
  constructors and a point-to-source-headroom projection, plus
  `RecursiveBridgeActualSourceRunFrameWordSumPoints` to lift those checked
  weighted points across actual assembly-source runs and project them into the
  existing source-frame and EVM stack-headroom interfaces.  The no-CALL runtime
  now also has source-checked exact-sum compile gates,
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableFrameWordSumStackSafeNoReturnDataCopy?`
  and its assembly-inferred sibling, plus public sound/no-out-of-gas theorem
  roots over the exact accumulated hidden-frame check.  Import-level
  `LayerAudit` still points at the older frame-words-depth root until the
  parallel CALL-side `RecursiveBridgeSupport` rebuild lets the new
  `NoCallRuntime` olean be produced.
- [x] Lift the refined frame-word resource route through the Yul bridge:
  `RecursiveBridgeSourceFrameWordsResourceBound` and
  `recursiveBridgeSourceFrameWordsResourceDepth?` now expose the checked
  arity-sensitive source stack-capacity result at the imported-Yul boundary,
  with `LayerAudit` tripwires for soundness, active-depth projection, and
  refined-context-to-headroom.
- [x] Wire preservation call-entry callbacks to produce
  `SourceDirectFrameWordsContext` at every actual internal-call step, using the
  split-argument facts already produced by call-frame preparation rather than
  accepting caller-supplied frame-word premises.
  Current checked brick:
  `SourceDirectFrameWordsContext.callBodyTargetCtxOfArgCallerBound` and the
  Yul `RecursiveBridgeSourceDirectFrameWordsPoint` call-body constructor turn a
  concrete `callee.params.length + callerStack.length <= 16` call-entry fact
  into the refined hidden-frame word bound and then into source stack
  headroom. The recursive source/direct dispatcher now retains and passes that
  derived fact through `RecursiveCallbacks`/`RecursiveCallbacksUpTo`, and the
  actual call cases use the bound-aware direct-call preservation wrapper.
- [x] Add the local call-entry inequality derivation:
  `Access.exprSeq_results_le_width`, `ArgList.length_le_argExprsWidth`, and
  `CallPrelude.argCallerBound_of_access_insertMany_eval` prove that the
  existing argument prelude, source argument evaluation, parameter insertion,
  and frame-bound access check imply
  `callee.params.length + callerBase.evm.stack.length <= 16`. The recursive
  dispatcher still needs to retain/pass this fact into its callee-body callback.
- [x] Add the bound-aware direct-call preservation wrapper:
  `call_stmtRunBridge_from_source_run_program_with_layout_callBound` derives
  the call-entry inequality from the actual `CallPrelude` and passes it into a
  strengthened callee-body callback. This keeps the fact alive at the direct
  internal-call boundary; the remaining work is threading the stronger callback
  through the recursive callback records and all dispatcher adapters.
- [x] Add the source/direct frame-shape bridge:
  source/direct `StateRel`, a 16-slot layout bound, and a checked hidden-return
  shape imply `RuntimeFrameShape`.
- [x] Prove checked hidden-return shape evolution lemmas for the source/direct
  internal-call boundary: `splitArgs?` plus a shaped caller frame pushes a
  shaped hidden return frame, `popReturn?` recovers the tail shape, and
  `attachReturns?` composes with the frame-visible bound to recover headroom
  after return.
- [x] Add `RuntimeCallStackShape`: active static call chain, visible-stack
  bound, hidden-return length alignment, and caller-frame bounds now derive
  `RuntimeFrameShape` and `SourceStackHeadroom` from the executable depth
  result. Root/internal call push and return-pop/attach constructors are
  checked.
- [x] Add `SourceDirectResourceContext`: source/direct `StateRel` is packaged
  with `RuntimeCallStackShape`, with checked main, root-call, internal-call,
  and return constructors. This is the additive invariant future recursive
  callbacks can thread without touching the parallel CALL refactor.
- [x] Decouple runtime headroom shape from the acyclic proof route:
  `RuntimeCallStackShape` now carries the active-length bound explicitly, and
  exposes `WithBound` constructors for source/direct call and return threading.
  The current acyclic checker still derives those bounds, while future bounded
  recursive check results can supply them directly.
- [x] Refactor the runtime/source-direct resource boundary to consume a generic
  `StackBudget`; acyclic `StackDepthCheckResult` and ranked
  `RankedDepthCheckResult` both project into that budget, so later recursive
  analyzers do not need to fork the headroom proof.
- [ ] Prove:
  checker success implies every structured `Block.Eval` frame visited by any
  accepted execution has `SourceStackHeadroom`.
- [x] Prove the local semantic projection:
  `StackResourceSafe` turns any threaded `SourceDirectResourceContext` into
  `Frame.SourceStackHeadroom`, and successful acyclic/ranked executable compile
  gates recover this semantic theorem from checked compiler output.
- [x] Expose a checked-success theorem:
  `Functions.CallDepth.Program.stackResourceSafe_of_stackResourceChecked`
  turns boolean `stackResourceChecked` success into a verified
  `StackResourceCheckResult` and `StackResourceSafe` theorem.
- [ ] Use existing lowering/preservation annotations, or add an annotated
  preservation theorem if necessary, to convert `StackResourceSafe` into
  `RecursiveBridgeActualSourceRunFrameStackHeadroom`.
- [x] Add the trace-context conversion target:
  `RecursiveBridgeActualBlockTraceSourceDirectResourceContext` records the
  source/direct resource context plus structured `Frame.StateRel` at each
  actual block-trace point, and a checked theorem converts it to
  `RecursiveBridgeActualBlockTraceSourceStackHeadroom` using the executable
  check result's `StackResourceSafe`.
- [x] Add source-run context wrappers:
  `RecursiveBridgeActualSourceRunFrameStackResourceContext.toHeadroom` converts
  the trace-context package into the old
  `RecursiveBridgeActualSourceRunFrameStackHeadroom`, and acyclic/ranked
  executable theorem roots now consume the context package instead of direct
  source-frame headroom.
- [x] Add generic annotated preservation plumbing:
  `Structured.Preservation.SourceRunResultPoints`/`ARunResultPoints` record
  predicates at actual source/assembly replay points, and
  `BlockTraceResultPoints` converts annotated assembly-source runs into
  annotated target block traces using checked assembly compilation.
- [x] Add the direct target-trace annotation route:
  `Structured.Preservation.BlockTraceResultPoints.of_blockTraceResult_invariant`
  derives per-block target-trace points directly from an initial point plus a
  block-step invariant. The no-CALL runtime now has matching
  `RecursiveBridgeActual...of_blockTraceResult_invariant` wrappers, so target
  trace annotation no longer needs to detour through a reconstructed
  `Assembly.Source.runNResult` equality.
- [x] Add the concrete-headroom annotation bridge:
  `RecursiveBridgeActualBlockTraceStackHeadroom.of_sourceRunResultPoints`
  converts assembly-source points carrying
  `state.stack.length + 17 <= 1024` into the target block-trace headroom
  structure consumed by the gas-aware bridge.
- [x] Add the actual source-run EVM headroom point package:
  `RecursiveBridgeActualSourceRunEVMStackHeadroomPoints` records concrete
  stack-headroom points on the actual gasless assembly replay, then converts
  them through checked `Assembly.compile?` into
  `RecursiveBridgeActualEVMStackHeadroomBound`. Acyclic/ranked executable
  compile gates now have direct projections from this point package to the
  target-side gas-aware stack resource.
- [x] Add the invariant-to-points bridge:
  `SourceRunResultPoints.of_runNResult_invariant` constructs annotated assembly
  runs from an ordinary `runNResult`, an initial point, and a one-step
  preservation invariant. The no-CALL runtime wrapper
  `RecursiveBridgeActualSourceRunFrameStackResourcePoints.of_runNResult_invariant`
  specializes this to transient stack-resource points.
- [x] Add the active source-resource point bridge:
  `RecursiveBridgeSourceDirectActiveResourcePoint` now packages a budget-free
  source/direct base context, a checked `SourceCallDepth.ActiveStackWitness`,
  a derived transient resource context, and structured `Frame.StateRel`.
  Checked root-call, internal-call, and return constructors thread actual
  source/direct semantic call/return facts without deriving source resource
  facts from target stack headroom.  The guarded-recursive route now also has a
  general concrete semantic frame-stack-to-active-witness theorem.
- [x] Add the active-points-to-headroom bridge:
  `RecursiveBridgeActualSourceRunActiveResourcePoints.toFrameStackResourceContext`
  and `.toFrameStackHeadroom` convert honest active resource annotations plus
  checked assembly compilation directly into
  `RecursiveBridgeActualSourceRunFrameStackHeadroom`.  The remaining annotated
  preservation obligation is therefore exactly to produce active resource
  points from compiler preservation, not to rebuild compatibility resource
  contexts by hand.
- [x] Derive the initial source-run resource point:
  `RecursiveBridgeSourceDirectResourcePoint.initial` constructs the canonical
  empty-stack entry point from the executable stack-resource check result,
  `SourceDirect.StateRel.initial`, and `Frame.stateRel_initial`. Acyclic and
  ranked checked-gate wrappers now need only the actual run equality plus the
  remaining compiler-output one-step resource invariant.
- [x] Add the resource-point bridge:
  `RecursiveBridgeSourceDirectResourcePoint` packages a source/direct resource
  context plus a bounded transient structured stack prefix and structured
  `Frame.StateRel` at a target block boundary. This is deliberately stronger
  than raw target stack headroom but weaker than requiring a plain source/direct
  context at every compiler-temporary instruction. `RecursiveBridgeActualSourceRunFrameStackResourcePoints.toContext`
  and the acyclic/ranked checked-gate wrappers convert annotated source-run
  points into `RecursiveBridgeActualSourceRunFrameStackResourceContext`.
- [x] Add the resource-to-concrete-headroom projection:
  `RecursiveBridgeSourceDirectResourcePoint.to_stack_headroom` derives concrete
  target stack headroom from the source/direct transient context and
  `Frame.StateRel`, and
  `RecursiveBridgeActualSourceRunFrameStackResourcePoints.toEVMStackHeadroomPoints`
  maps stronger resource annotations to the concrete headroom point package.
  The acyclic/ranked executable compile gates also project resource points
  directly to `RecursiveBridgeActualEVMStackHeadroomBound`.
- [x] Add prefix algebra for compiler temporaries:
  `Frame.StateRel.with_visible_prefix`,
  `SourceDirectTransientResourceContext.of_prefix`, and
  `RecursiveBridgeSourceDirectResourcePoint.of_resourceContext_prefix`
  preserve the hidden-frame relation while placing checked temporary operands
  above a base source/direct resource context.
- [ ] Avoid adding a public per-block trace witness; it must be derived from
  the accepted source run and checked compiler output.

### Phase 9: Conservative Compiler Integration

- [x] Add the stack-resource checker to the structured `CompilationBounds` or
  an adjacent checked compiler resource package. Current staged location:
  `recursiveBridgeExecutableStackDepthCheckResult?` in the no-CALL runtime
  boundary.
- [x] Add the conservative accepted-fragment gate
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`.
  It first requires the executable source-side resource checker, then infers a
  word-PC assembly stack-bound table and rechecks that table into an
  `AssemblyBounds.ProgramBoundCheckResult`; neither the source recurrence/
  capacity facts nor the inferred table are trusted without checker success.
- [x] Add the frame-word-refined accepted-fragment gate
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundFrameWordsStackSafeNoReturnDataCopy?`.
  It replaces the source-side fixed-17 hidden-frame budget with
  `recursiveBridgeSourceFrameWordsResourceDepth?`, keeps the inferred assembly
  stack-bound recheck, and exposes public result/no-out-of-gas theorem wrappers
  with the same source-facing premises as the older executable stack-safe root.
- [x] Add checked-success projections for the preferred gate:
  base no-CALL/no-`RETURNDATACOPY` checked compile, executable stack-resource
  check result, semantic `StackResourceSafe`, source-resource success, and
  concrete EVM stack-headroom bound.
- [x] Staged checkpoint: the preferred public wrapper now uses this combined
  source-plus-target gate and derives the concrete target headroom facts
  internally. Source-frame headroom is kept on the honest annotated
  preservation route below, rather than reconstructed from target headroom
  alone.
- [x] Add honest preferred-gate projections to source-frame resource points,
  source-frame resource context, and
  `RecursiveBridgeActualSourceRunFrameStackHeadroom`. These now require the
  preservation one-step invariant for
  `RecursiveBridgeSourceDirectResourcePoint`, and the checked-compile wrappers
  exposing that invariant are private implementation lemmas rather than public
  theorem roots; only the concrete EVM headroom projection follows from the
  inferred assembly-bound result plus the preservation-produced
  `Assembly.Source.runNResult` equality by itself.
- [x] Checked-success projection checkpoint: the acyclic and ranked executable
  stack-safe compile gates now recover `RecursiveBridgeExecutableStackResourceCheckResult`
  and its `StackResourceSafe` theorem from the computed stack check result.
  The actual-trace `RecursiveBridgeActualSourceRunFrameStackHeadroom` projection
  remains the open annotated-preservation step.
- [x] Annotated source-run projection checkpoint: the acyclic and ranked
  executable stack-safe compile gates now derive
  `RecursiveBridgeActualSourceRunFrameStackResourceContext` from annotated
  source-run points and checked assembly compilation. The remaining work is to
  produce those annotated points from the preservation theorem output.
- [x] Staged executable projection checkpoint:
  the new acyclic and ranked executable gates prove the base checked compile
  result plus the checked stack result. They deliberately do not claim the
  semantic source-run headroom fact yet.
- [x] Add transitional theorem roots over executable stack gates plus an
  explicit `RecursiveBridgeActualSourceRunFrameStackHeadroom` premise. These
  remove the proof-carrying compile artifact from the theorem statement, but
  are not yet the definition of done because the headroom premise still must be
  derived from checked preservation annotations.
- [x] Derive the concrete target block-trace headroom package directly from
  actual `Assembly.Preservation.BlockTraceResult` and the checked assembly
  bound result. This removes the public target replay equality and
  per-block headroom witness from the preferred no-CALL roots.
- [x] Update `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM`
  and no-out-of-gas companion to the frame-word-refined executable-source plus
  inferred-assembly-bound roots. The preferred checked compile gate now requires
  both `recursiveBridgeSourceFrameWordsResourceDepth?` and
  `AssemblyBounds.inferProgramBoundCheckResult?` to succeed; the older
  fixed-17 source-resource gate remains as compatibility plumbing.
- [x] Add matching no-out-of-gas executable resource-context roots:
  the result theorem and no-out companion now both have acyclic/ranked
  executable stack-safe variants over
  `RecursiveBridgeActualSourceRunFrameStackResourceContext`.
- [x] Delete the old proof-carrying compile route from the no-CALL public
  theorem lane. Ranked wrappers that remain are executable checked routes or
  compatibility helpers; they are not the proof-carrying semantic stack
  artifact.
- [x] Defer general path-sensitive/ranked recursive-cycle acceptance. The public
  theorem is complete for the conservative accepted fragment: if the combined
  executable source-recurrence plus inferred assembly-bound gate accepts the
  program, the target stack-resource facts used by the gas-aware EVM bridge are
  derived internally.

### Phase 10: CALL Compatibility

- [ ] Ensure ordinary external `CALL` does not enter the internal-call
  recursion graph; it is an open external event, not a structured internal
  frame push.
- [ ] Account for CALL-family primitive stack effects in the stack-effect
  algebra: operands consumed, result words pushed, and no hidden internal
  return frame.
- [ ] For reentrant external responses, require only that the response resumes
  with the related shared state demanded by the open boundary; do not model
  callee stack frames.
- [ ] Compose the executable internal-stack checker with the CALL open
  request/response theorem once the CALL agent finishes the public spine.
- [ ] Add tests/examples mixing bounded internal recursion with external CALL
  suspensions.

### Phase 11: Tests And Counterexamples

- [x] Add accepted acyclic examples that compute exact small bounds.
- [x] Add direct recursion rejected as unbounded.
- [x] Add unresolved-root rejection examples for the executable depth checker.
- [x] Add mutual recursion rejected without checked finite-depth evidence.
- [x] Add bounded direct recursion accepted by finite unfolding for the first
  narrow source pattern: `SelfGuardedOnce.checkResult?` accepts the
  one-step guarded self-call case and rejects the same raw recursive body under
  the all-syntactic-calls conformance checker.
- [x] Add bounded mutual recursion accepted by finite unfolding for the first
  narrow two-function source pattern: `MutualGuardedOnce.checkResult?`
  accepts the one-step guarded mutual-call case while the all-syntactic-calls
  conformance checker still rejects the same raw recursive bodies.
- [x] Add bounded larger recursive cycles accepted by finite unfolding for the
  generic one-step source pattern: `GuardedZeroCalls.checkResult?`
  accepts a guarded three-function cycle where every recursive body calls the
  next function with literal zero, while the narrower self and mutual checkers
  reject that program.
- [x] Broaden the generic guarded-cycle root recognizer without weakening the
  recurrence proof: `GuardedZeroCalls.rootsFromStmt?` now structurally accepts
  bare literal root calls, `block` statements whose contents are accepted root
  statements, and `if` bodies whose contents are accepted root statements.
  The checker proves every extracted root is still a real syntactic internal
  call into the checked function set with rank at most one, and has
  native-decide examples accepting guarded three-function cycles with nested
  and composite main roots.
- [x] Broaden the generic guarded-cycle function-body recognizer in the same
  structural style: `GuardedZeroCalls.functionShape?` now accepts the guarded
  zero-call body through accepted `block` wrappers, proves every accepted
  function shape contributes an actual syntactic internal call in the checked
  function body, and exposes that fact through the preferred compile gate's
  source-recurrence branch theorem.
- [x] Add the abstract-frame `CallGraphSound` instance for
  `GuardedZeroCalls`, proving that checked `(functionName, rank)` frames and
  abstract direct calls compose through the same generic ranked path/depth
  theorem as future source-frame instances.
- [x] Expose the guarded abstract call-graph soundness and abstract chain
  frame-count bound through
  `RecursiveBridgeExecutableGuardedZeroCallsStackCheckResult`, so the Yul
  compile-gate check-result wrapper can project these checked facts without
  adding a public theorem premise.
- [x] Split the budget-free source/direct context from the compatibility
  resource context. `SourceDirectBaseContext` records state relation, active
  source call stack, visible-layout bound, return-frame count, and caller-stack
  visibility without proving headroom. `StackResourceSafeFromBase` consumes
  this base context plus the checked active-frame bound to derive
  `Frame.SourceStackHeadroom`; the older `StackResourceSafe` now routes through
  this base theorem and is kept as compatibility plumbing.
- [x] Add the guarded rank-one source/direct call-body constructor that consumes
  a checked `(caller, callee)` shape and advances the ranked resource context
  to the rank-zero callee frame.
- [x] Instantiate `CallGraphSound` for `GuardedZeroCalls` with a real
  path-sensitive frame-matching relation: rank zero means the checked argument
  is zero, rank one is the conservative/top state, zero-ranked guarded calls
  are unreachable, and rank-one guarded calls step to rank-zero callees.
- [x] Connect `GuardedZeroCalls.SourceDirectCall` to the actual
  `Functions.Source`/imported-Yul source execution facts: root calls and body
  calls in accepted guarded programs must produce the same argument-carrying
  frames used by `sourceCallGraphSound`, using the new source call extraction
  exact guarded-body-shape facts, and actual-run wrappers rather than merely
  matching the checker-local frame model.  Current checked facts include the
  `_parts` variants for root/body source-run extraction plus the
  analysis-independent `GuardedSemanticRootFrame` /
  `GuardedSemanticDirectCall` bound exposed through `SourceRecurrenceBound`.
- [x] Add exact source-resource-depth regression examples for bounded guarded
  recursion: the self, mutual, three-function, nested-root, and composite-root
  guarded-zero programs all check at depth `2`, while the unbounded guarded
  self-call and raw self-recursive program check to `none` at both the raw
  recurrence and source-resource gates.
- [x] Add bounded direct recursion accepted by the generic ranked call-state
  kernel. This is not yet wired to source-expression inference.
- [x] Add bounded mutual recursion accepted by the generic ranked call-state
  kernel. This is not yet wired to source-expression inference.
- [x] Add source-facing ranked conformance examples: a simple checked program
  whose ranked roots/edges cover the real call graph is accepted, and the same
  program with a missing ranked edge is rejected.
- [x] Add inferred-checker examples:
  `inferAcyclicCheck?` accepts the simple acyclic lowered function
  program and rejects a direct self-recursive function, confirming that the
  conservative analyzer does not smuggle in recursive-call boundedness.
- [ ] Add loop-contained recursion accepted only with loop and recursion bounds.
- [x] Add examples whose maximum stack is exactly `1024 - 17` accepted and
  exactly one word above rejected:
  `Structured.StackResource.Examples.pushMany 1007` is accepted by
  `Code.stackSafeFrom? 0 17 1024`, while `pushMany 1008` is rejected. The
  function call-depth checker also accepts the largest current acyclic budget
  boundary (`chainProgram 58`) and rejects the first overflow boundary
  (`chainProgram 59`).
- [x] Add assembly-bound checker examples: `pushPopAsm` and a zero-net-stack
  loop are accepted by `AssemblyBounds.programBoundOk?`, while a positive
  stack-growth loop is rejected.
- [ ] Add CALL-family examples showing external calls do not count as internal
  return-frame recursion.
- [x] Add regression tests proving the public theorem cannot be invoked with
  only the old proof-carrying stack artifact. `LayerAudit` now contains
  public-spine tripwire examples that apply the exported result and
  no-out-of-gas roots using only the combined executable source-recurrence plus
  inferred assembly-bound compile gate; repointing those aliases to an older
  headroom-premise root makes the file stop type-checking.

### Phase 12: Public Theorem And Audit Cleanup

- [x] Grep public theorem surfaces for:
  `proof-carrying source-run stack-headroom boundary`,
  `RecursiveBridgeActualSourceRunFrameStackHeadroom`,
  `StackResourceSafe`, `SCCRecurrenceCheckResult`, `Layout`, `Evidence`,
  `Obligation`, and `Replay`.
- [x] Any remaining public occurrence must be either a checked compiler theorem
  output or a deliberately source-facing semantic premise.  Current audit:
  `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM` and the
  no-out-of-gas companion take the combined executable checked compile success
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?
  program = some (asm, target)` as their only stack-related premise.  They do
  not take `RecursiveBridgeActualSourceRunFrameStackHeadroom`,
  `StackResourceSafe`, a source stack check result, a layout witness, or a replay
  obligation.  Remaining public `NoCallRuntime` occurrences are checked-success
  projection helpers derived from executable compiler gates; the checked-compile
  wrappers that still require a one-step
  `RecursiveBridgeSourceDirectResourcePoint` preservation invariant are private
  implementation lemmas rather than public theorem roots.
- [ ] Run focused checks:
  `lake env lean EvmCompiler/Structured/Preservation.lean`,
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`,
  `lake env lean EvmCompiler/LayerAudit.lean`, and the CALL public root once
  available.
- [x] Focused non-CALL public-boundary checkpoint:
  `lake env lean EvmCompiler/Structured/Preservation.lean`,
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`, and
  `lake env lean EvmCompiler/LayerAudit.lean` pass after the compositional
  source-resource checker refactor, and were re-run after the active-resource
  empty/by-name constructor cleanup. The remaining focused check is the CALL
  public root once the parallel CALL spine lands.
- [x] Focused stack-resource checkpoint:
  `lake build EvmCompiler.Functions.CallDepth EvmCompiler.Structured.StackResource`
  passes after adding the modules to the aggregate `Functions` and
  `Structured` imports.
- [x] Focused additive resource-context checkpoint:
  `lake env lean EvmCompiler/Structured/StackResource.lean`,
  `lake env lean EvmCompiler/Functions/CallDepth.lean`, and
  `lake env lean EvmCompiler/Functions/CallDepthExamples.lean` pass after the
  monotone straight-line analyzer theorem, source/direct resource context, and
  mutual-recursion rejection example.
- [x] Focused staged integration checkpoint:
  `lake env lean EvmCompiler/Functions/CallDepth.lean`,
  `lake env lean EvmCompiler/Functions/CallDepthExamples.lean`, and
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean` pass after decoupling
  active-length bounds from the acyclic-only path proof.
- [x] Focused ranked-kernel checkpoint:
  `lake env lean EvmCompiler/Functions/CallDepthRanked.lean`,
  `lake build EvmCompiler.Functions.CallDepthRanked`, and
  `lake env lean EvmCompiler/Functions.lean` pass.
- [x] Focused ranked conformance/resource-context checkpoint:
  `lake env lean EvmCompiler/Structured/StackResource.lean`,
  `lake env lean EvmCompiler/Functions/CallDepth.lean`,
  `lake env lean EvmCompiler/Functions/CallDepthExamples.lean`,
  `lake env lean EvmCompiler/Functions/CallDepthRanked.lean`,
  `lake env lean EvmCompiler/Functions.lean`,
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`,
  `lake env lean EvmCompiler/LayerAudit.lean`, and
  `lake build EvmCompiler.Functions.CallDepthRanked
  EvmCompiler.Functions.CallDepth EvmCompiler.Structured.StackResource` pass.
- [x] Focused executable public-root staging checkpoint:
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`,
  `lake env lean EvmCompiler/LayerAudit.lean`,
  `lake env lean EvmCompiler/Functions/CallDepth.lean`,
  `lake env lean EvmCompiler/Functions/CallDepthRanked.lean`, and
  `lake env lean EvmCompiler/Structured/StackResource.lean` pass after adding
  transitional executable-gate theorem roots. A full `lake build
  EvmCompiler.Yul.NoCallRuntime` is currently blocked by parallel CALL-owned
  `NoCallCreate` failures before the new `NoCallRuntime` olean can be emitted.
- [x] Focused semantic resource-check checkpoint:
  `lake build EvmCompiler.Functions.CallDepth`,
  `lake build EvmCompiler.Functions.CallDepthRanked`,
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`,
  `lake env lean EvmCompiler/Functions.lean`,
  `lake env lean EvmCompiler/Functions/CallDepthExamples.lean`, and
  `lake env lean EvmCompiler/Structured/StackResource.lean` pass after adding
  `StackResourceSafe`/`StackResourceCheckResult` projections and executable
  gate stack-resource result recovery.
- [x] Focused annotated resource-point checkpoint:
  `lake env lean EvmCompiler/Structured/Preservation.lean` and
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean` pass after adding generic
  source-run/block-trace point annotations plus acyclic/ranked conversion
  wrappers from those points to the executable resource context.
- [x] Focused checker/analyzer split checkpoint:
  `lake build EvmCompiler.Functions.CallDepthRanked`,
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`,
  `lake env lean EvmCompiler/LayerAudit.lean`, `git diff --check`, and the
  focused no-`sorry`/`admit`/`axiom`/`unsafe` scan pass after splitting
  `StackRecurrenceCandidate`, `checkStackRecurrenceCandidate?`,
  `inferStackRecurrenceCandidate?`, and `inferStackRecurrences?`.
- [x] Run `#print axioms` or local axiom scans for the new public theorem roots.
  Source-fed axiom print for the current `NoCallRuntime.lean` executable
  stack roots reports only the existing Lean/library axioms
  (`propext`, `Classical.choice`, `Quot.sound`, and `Lean.ofReduceBool` on the
  top theorem roots).  The checked-sidecar EVM headroom root reports only
  `propext`, `Classical.choice`, and `Quot.sound`; the inferred-bound EVM
  headroom root reports the same.
- [x] Focused executable assembly-bound checkpoint:
  `lake env lean EvmCompiler/Structured/StackResource.lean`,
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean`, and
  `git diff --check -- EvmCompiler/Structured/StackResource.lean` pass after
  adding the word-PC keyed assembly bound table, per-instruction and
  whole-program executable checkers, running successor-PC soundness, and the
  `programBoundOk?` theorem deriving source-run EVM stack-headroom points.
- [x] Focused no-CALL assembly-bound bridge checkpoint:
  `lake build EvmCompiler.Structured.StackResource` and
  `lake env lean EvmCompiler/Yul/NoCallRuntime.lean` pass after adding
  `RecursiveBridgeActualSourceRunEVMStackHeadroomPoints.of_assemblyBoundCheck`
  plus compile-gate projection helpers for EVM headroom points and frame
  resource points.
  A checked sidecar compiler boundary now exists:
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticAssemblyBoundStackSafeNoReturnDataCopy?`
  checks the emitted assembly against a supplied word-PC bound table and
  projects checked success to concrete EVM stack-headroom.  An inferred
  compiler boundary also exists, and the preferred public gate wraps it with
  the executable source recurrence checker:
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`
  first checks source recurrence safety, then runs the monotone assembly-bound
  inference pass, rechecks the inferred table into a result, derives the
  canonical empty-entry initial point, and projects checked success to concrete
  EVM stack-headroom without a supplied table.
- [x] Record a `PROGRESS_LOG.md` audit entry naming the final executable
  checker, soundness theorem, public root theorem, tests, and any remaining
  fundamental resource assumptions. Current conservative public root is exposed
  through `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM`;
  accepted no-CALL programs use
  `compileCheckedAssemblyTargetBytecodeResourcesFeaturesSourceStaticExecutableAssemblyInferredBoundStackSafeNoReturnDataCopy?`,
  which runs and rechecks the executable source recurrence checker and assembly
  bound inference pass before the theorem derives EVM stack headroom.
- [ ] Delete stale private compatibility wrappers after downstream callers move
  to the executable checked compiler boundary.  Current cleanup checkpoint:
  removed the unused explicit-ranked gas-aware theorem roots
  `...rankedExecutableStackSafeCompile_actualSourceRunFrameStackHeadroom...`
  and `...rankedExecutableStackSafeCompile_actualSourceRunFrameStackResourceContext...`
  for both result and no-out-of-gas forms, and removed the default executable
  stack-safe variants that still took
  `RecursiveBridgeActualSourceRunFrameStackHeadroom` or its resource-context
  wrappers directly.  It also removed the no-CALL gas-aware theorem roots that
  could be invoked with only a caller-supplied
  `RecursiveBridgeActualSourceRunEVMStackHeadroomPoints` package or with only
  the assembly-inferred stack-bound gate.  The obsolete global
  `RecursiveBridgeActualSourceFrameStackHeadroomBound` proof-carrying type has
  also been deleted; the live source-frame package is the actual-run-scoped
  `RecursiveBridgeActualSourceRunFrameStackHeadroom`, with preferred
  projections requiring the preservation one-step resource invariant.  The
  remaining direct residual/headroom gas-aware helper roots in
  `NoCallRuntime` have been marked `private`, so imports cannot call the
  target-headroom-premise route directly.  The checked ranked/default sidecar
  result/projection helpers remain available for future checker work.
  The target-headroom-only adapter that could manufacture source/direct resource
  points from raw EVM headroom, together with the checked compile wrappers that
  used it, has now been deleted; imports cannot use target stack bounds as a
  public substitute for source/direct resource preservation.
  The older gas-aware roots that exposed trace-check, instruction-core,
  actual-trace, or concrete headroom packages as theorem premises have also
  been demoted to private implementation lemmas.  The exported gas-aware
  result/no-out-of-gas surface now routes through the executable assembly-bound
  stack-safe compile gate, plus the expression-contract compatibility wrappers.

### Phase 13: Top-16 Layout Allocation

Goal: accept programs with many lexical locals whenever the compiled target can
keep every live source value needed by future execution inside the EVM
`DUP1..DUP16` / `SWAP1..SWAP16` addressable window, without adding a memory or
storage scratch assumption.

- [x] Boundary audit:
  a pure stack macro cannot faithfully read an arbitrary deep live value while
  preserving all values above it.  A sound compile-around route must either
  prove a non-observable spill discipline or prove that the target layout drops
  dead values before they become an addressability obstacle.  Because EVM
  memory is source-observable through `MLOAD`/`MSTORE`/`MSIZE`, and the state
  relation tracks both memory bytes and `activeWords`, a memory spill is sound
  only with a proved scratch discipline that restores memory and never expands
  the active memory region.  The preferred route before such a scratch contract
  is liveness/layout allocation, not an unmodeled memory spill.
- [x] Define executable source liveness summaries for `Functions.Source`:
  compute variables needed by each suffix, branch, loop condition/body/post,
  call argument/target assignment, `leave`, and regular function return.
  The summary should be conservative for loops and calls, and may reject when
  it cannot keep a finite live set under 16.
- [x] Add first checked target-layout access-window helpers:
  `Functions.LiveLayout` now has executable live-name summaries, dead-prefix
  trimming, exact name-index accessibility checks against the EVM top-16
  window, expression/return-name/statement access checks with temporary
  offsets, and soundness lemmas turning successful checks into usable
  source/direct accessibility facts.  The layout-window checker now also has
  completeness/iff lemmas pinning success to exactly the top-16 index condition
  after dead-prefix trimming.  The first SWAP-scheduling primitive is checked:
  `Layout.promoteAt`/`Layout.promoteName?` compute the layout effect of moving
  a selected live name to the top when its current slot is `SWAP16`-reachable,
  and prove the promoted top slot plus length preservation.  This is
  infrastructure only; compiler acceptance is not widened until the source/direct
  bridge consumes the live-layout relation and the lowerer emits a verified
  target reorder statement.
- [x] Add the verified backend reorder statement:
  `Locals.Stmt.promoteName` is backend-only/source-invalid, compiles through the
  checked `swapRestoreUpTo?` stack rotation, preserves the Locals source/direct
  state relation via `StateRel.promoteAt`, and is threaded through target layout
  preservation.  The source boundary explicitly rejects it, so it is available
  to the lowerer without becoming a new accepted source construct.  The lowerer
  still needs a deliberate interface rewrite before it can emit this statement
  to widen acceptance.
- [x] Add the checked prepared-layout promotion component:
  `Prepare.forStmtAboveSuffix?` now collects live-name and statement-access
  requirements, emits zero or more backend-only `promoteName` statements for
  SWAP16-reachable blocked names while preserving handler cleanup suffixes, and
  proves that successful preparation yields the exact `entryWindowOk?` and
  `StmtAccess.accessible?` facts for the final layout.  The target-side bridge
  proves both a single `promoteName` and the whole prepared prefix execute as
  target-only code preserving `SourceDirect.StateRel` and hidden returns.  The
  legacy no-op `Prepare.forStmt?` is private; the checked live-layout
  lowerer/preservation callback spine now uses the suffix-protected API.
- [x] Replace the current source-scope-sized `FrameBound` checker with a
  target-layout-aware access-window checker:
  `Functions.LiveLayout.Checked` now computes and verifies the live target
  layout against actual layout positions and temporary offsets, including exact
  accessibility for return names.  This is still a parallel checker; the public
  proof spine continues to use the old `FrameBound` route until the bridge is
  reproved.
- [x] Extend the local live-layout checker relation:
  successful executable checks produce `Checked.*.Sound` facts carrying the
  trimmed layout, exact live-name access facts, branch/loop sub-obligations,
  and return-name accessibility.  The remaining proof work is to connect this
  relation to the existing source/direct preservation theorem.
- [x] Add checked dead-drop code generation:
  before compiling each statement/suffix, pop target stack slots whose source
  variables are not live in that suffix.  Added a backend-only
  `Locals.Stmt.cleanupTo` construct, proved its Locals-to-Expressions
  preservation case, and added `Functions.LiveLayout.Lower`, which mirrors the
  executable checker and emits cleanup statements before each source statement
  and at block ends.  The many-dead-locals regression now lowers through this
  cleanup route to Expressions, and successful live lowering is proved to imply
  `Functions.LiveLayout.Checked.Program.check?`.  Successful function lowering
  now also exposes the exact lowered body, return accessibility, and generated
  procedure wrapper shape from `FunDef.toLocalsProc?`.  The emitted Locals
  statement lists now also have a checked static target-layout effect theorem:
  successful `Lower.Block.toLocals?` output has regular target layout effect
  exactly equal to the executable lowerer's `outLayout`.  Regular Locals target
  execution is now connected to that static effect: any successful regular
  `runOpen` of a block produced by executable live lowering ends with target
  context layout exactly equal to the lowerer's `outLayout`.
- [x] Prove the low-level non-restricting dead-prefix cleanup brick:
  running existing `runCleanupTo` down to a trimmed suffix preserves
  `Locals.SourceLowering.StateRel` for that suffix without changing the source
  store.  This justifies the target-side `POP`s for dead slots; the remaining
  work is to generate those pops at statement boundaries and prove the source
  continuation never reads the removed names.
- [ ] Reprove the source/direct bridge over the live-layout relation:
  statement, block, loop, call, `leave`, and regular-return preservation should
  consume the executable live-layout checker and produce the exact access facts
  required by `DUP`/`SWAP`.
  First bridge bricks are checked: `LiveCtxRel` relaxes the old same-scope
  context relation after dead-prefix cleanup, live result relations package
  trimmed target layouts, target-side cleanup-prefix composition is derived from
  executable `runCleanupTo`, the empty-block cleanup bridge is proved, and
  successful nonempty `StmtList.toLocals?` lowerings now decompose into the
  exact cleanup/head/tail pieces consumed by the checked cons compositor.
  Expression and initialized-`let` heads now have checked live statement
  bridges that consume actual `Lower.Stmt.toLocals?` output under the relaxed
  live context; assignment and terminal/terminal-argument heads now have the
  same bridge through the executable `StmtAccess.accessible?` check.
  Break/continue heads now preserve with explicit target-depth live cleanup
  facts rather than assuming the retained target suffix has the same length as
  the source handler scope; fixed-layout `CleanupScopeRel` facts still adapt
  into this relation, and trimming preserves it when the live set keeps the
  retained handler suffix.  `leave` now derives return values from executable
  return-name accessibility before proving target push-return plus cleanup.
  Scoped-block closure now has a live-layout adapter: regular block fallthrough
  cleans the target back to the outer layout while relating the source
  `restrictTo` through target-layout containment, and nonregular block outcomes
  pass through unchanged.  A raw `.block` statement bridge composes an open
  block bridge with the scoped closure under an explicit final-layout cleanup
  fact.  The statement-list bridge now also has an explicit-base-layout variant
  so tails may drop locals introduced by preceding heads while the enclosing
  block still closes to its outer layout.  The base-layout cleanup facts are
  now derived from executable lowerer success for `block`, `if`, and `switch`
  statement heads.  The loop false-condition and generic true/body/post
  compositor are checked.  Loop-specific statement/block bridge packages now
  preserve the exact loop layout for `break`/`continue` while erasing back to
  the ordinary live-layout bridges for non-loop callers.  Ordinary and
  loop-layout open-block bridges now have scoped-execution adapters, and the
  loop compositor now accepts body/post/recursive callbacks that return
  existential target fuel, choosing a large enough target loop fuel instead of
  forcing cleanup-emitting target blocks to run at the exact source inner fuel.
  The executable `Lower.Block.toLocals?` boundary is now packaged as a
  witness-shaped whole-block bridge over the checked nil/cons statement-list
  compositors, with source-fuel monotonicity for the empty-block case.  The
  bridge packages now also expose target-result extraction for an exact source
  run, and successful block lowering has an exact-source-run target-result
  wrapper for downstream public theorem wiring.  The cons-list lowerer boundary
  now also has a source-run-driven target-result driver: it inverts the actual
  source block run to recover the exact head run and passes the exact regular
  tail run into the recursive tail callback, avoiding a proof-carrying
  source-success bridge for the tail.  The whole-block lowerer boundary has the
  same source-run-driven callback shape, using the checked nil case for empty
  blocks and the cons driver for nonempty blocks.  Expression, initialized
  `let`, and assignment heads now also have exact-source-run wrappers, deriving
  the expression evaluation facts from the actual `Source.Stmt.run` instead of
  taking them as separate proof inputs.  Terminal, terminal-argument,
  break/continue, and `leave` heads now have the same source-run inversion
  wrappers; `let` still consumes the source freshness/scoping fact because the
  raw source step itself does not reject shadowing.
  A source-run `.block` head wrapper now derives the body open-run fact from the
  actual scoped source statement run, and a checked non-structural head
  dispatcher covers expression/`let`/assignment, break/continue/`leave`, and
  terminal heads from source scoping plus explicit handler/return-scope facts.
  Structural `if` and `switch` heads now have source-run wrappers too, deriving
  the condition/scrutinee evaluation fact from the actual source statement run
  before invoking the selected-body bridge callbacks.  A reusable
  non-loop/non-CALL dispatcher now covers atomic, block, `if`, and `switch`
  statement heads from actual source runs plus source scoping.  A broader
  non-CALL dispatcher now includes `for` by delegating the loop case to the
  existing exact-source-run loop wrapper while still excluding CALL for the
  parallel external-world work.  The whole-block source-run wrapper can now
  derive each non-CALL head bridge from executable access/scoping facts and the
  actual source run, while keeping recursive body/tail callbacks explicit.  An
  executable `NoInternalCall` checker now rejects `Functions.Stmt.call`, proves
  a source-facing no-internal-CALL proposition, and feeds the
  `LiveNonCallStmt` dispatcher condition.  The live-layout lowerer now has
  separate no-internal-CALL candidate gates through `toLocals`, `toExpressions`,
  and target compile, and `Functions.Source.Program` has a candidate checked
  compiler entry point composing that gate with the existing structured checked
  backend.  Checked inversion facts now expose the head/tail evidence of a
  no-internal-CALL block, the corresponding source-scoping head evidence, and
  switch-selection preservation for no-internal-CALL bodies.  Source-scope
  inversion facts now also expose nested block, selected switch body, and loop
  init/post/body scoping facts for structural callbacks.  The cons-list
  target-result wrapper now consumes the actual head's
  `NoInternalCall.Stmt.Holds` and `Scope.Stmt.Scoped` facts directly, so that
  piece no longer needs per-head supported/scoped callbacks.  The whole-block
  target-result wrapper now consumes whole-block no-internal-CALL and scoping
  evidence for its actual top-level head; nested body/tail/handler callbacks
  remain explicit.  The statement dispatchers now also have no-CALL-aware
  variants: the non-loop one passes derived no-internal-CALL facts for nested
  block/if/switch bodies into structural callbacks, and the full non-CALL one
  extends that shape through `for` by deriving init/post/body no-CALL plus
  source-scope facts before invoking loop callbacks.  A strengthened cons-list
  wrapper now uses that full dispatcher and exposes the derived nested no-CALL
  facts to block/if/switch/for callbacks, while leaving the older non-CALL-head
  compatibility wrapper unchanged.  The whole-block no-internal-CALL wrapper now
  has a sibling that consumes that strengthened cons wrapper and exposes the
  same derived nested no-CALL facts at the block boundary.  Atomic statement
  dispatch also has a case-local handler sibling, the non-loop dispatcher lifts
  that same shape through expression/let/assign/block/if/switch and terminal
  heads, no-CALL-aware non-loop/full dispatchers preserve it while deriving
  nested no-CALL facts, and the cons-list plus whole-block no-CALL structural
  wrappers now have case-local handler siblings.  Future public-spine wrappers
  can require break cleanup only for `.brk`, continue cleanup only for `.cont`,
  and return scope only for `.leave`.  The live-control layer now has checked
  projections that preserve break/continue cleanup facts through
  `trimDeadPrefix` when the live handler set is the same source scope, and it
  derives leave return-scope membership from `liveCtx.returns = returns`; the
  whole-block no-CALL structural wrapper has a live-control handler sibling
  that derives those trimmed handler facts from whole-context live-control plus
  untrimmed cleanup facts.  The bridge now also has function-body entry facts
  for live-control/live-context relation and a generic scoped-block closure
  lemma that turns exact open-block target-result facts into the
  `runScoped`-shaped result needed by `Source.Program.runState`; the no-CALL
  live-control whole-block wrapper is now closed through that lemma as a scoped
  preservation theorem, with recursive body/tail callbacks still explicit.
  Regular source statement/block execution now also preserves `LiveControlRel`,
  and `withoutLoopControl` has a live-control adapter, giving the future
  recursive tail/body discharge a checked way to recover handler facts after
  source context evolution.  Target cleanup-scope facts also have checked
  layout-growth algebra for locals pushed above retained handler suffixes, so
  regular target context growth can preserve cleanup-to-handler facts; this is
  now factored both as explicit prefix growth and as the more semantic
  `CleanupLayoutRel` suffix-retention form.  Function-body entry now also
  derives the break/continue cleanup-scope callbacks as vacuous facts from the
  checked source/target body contexts instead of requiring caller evidence.
  The live bridge can also recover break/continue `LiveCleanupScopeRel` facts
  from the stronger existing `SourceDirect.CtxRel`, giving old fixed-layout
  context proofs a checked adapter into the live-layout handler interface.
  `LiveCtxRel` now has a batch local-growth adapter for whole name prefixes,
  avoiding future repeated one-local proof plumbing when exact per-path local
  layout growth is derived.  The target side now also has a combined executable
  lowering/runtime layout fact: successful regular execution of the exact
  lowered block ends at the compiler-computed output layout, giving the next
  bridge rewrite a direct target-side equality instead of a coarse layout
  premise.  The open-block bridge now exposes this as a first-class exact
  target-output-layout relation; checked return-name accessibility over the
  compiler's `outLayout` can be transported to the actual regular target
  context, and any existing target-result theorem over executable lowering can
  be upgraded compositionally to carry that exact-output conjunct.
  The same exact target-output-layout fact now exists at statement granularity,
  so the cons/tail bridge can be reshaped to derive the head's actual regular
  exit layout before invoking the tail theorem, instead of asking the tail
  callback to work under an arbitrary post-head target layout.  A checked
  cons/tail target-result variant now performs exactly that derivation for the
  executable lowering components: in the regular-head case, the proof derives
  `targetCtxAfter.layout = nextLayout` from the lowered statement run before
  invoking the tail callback.  That target-layout equality is now threaded
  through the general executable statement-list wrapper, the statement-level
  no-internal-CALL structural/case-handler wrappers, the block-level
  target-result wrappers, the scoped wrappers, and the scoped callback bundles.
  The next correction is to keep that equality while making the sequential
  tail induction target explicit about its enclosing base layout.  A raw tail
  after a local declaration may legitimately clean back to the outer block
  layout, so requiring the tail to preserve its own entry layout is too strong
  for real lowering.  The preservation file now has a
  `LiveBlockOpenRunBridgeWithLayoutTo`-shaped open-block facade,
  `ScopedNoInternalCallRecursiveOpenBlockLayoutToCallbacksUpTo`, whose explicit
  `baseLayout` is the right target for these raw tails.  The same public-facing
  tail path now also receives the actual regular source-scope transition and
  the derived no-internal-CALL/scoped facts for the concrete `rest` suffix from
  the block's `stmt :: rest` split, rather than asking callers to supply those
  facts for an abstract tail.
  The empty-block cleanup-layout premise has also been classified precisely:
  it is not derivable from arbitrary successful nil lowering, because nil
  lowering may deliberately drop dead locals.  It is now checked as a derived
  fact for the shapes the public route should use: syntactically nonempty
  blocks, or nil blocks whose `after` set retains the whole entry layout; the
  common scoped-body `Checked.scopedAfter` case has a no-premise helper.  The
  scoped theorem's recursive body/tail/handler obligations are now packaged in
  `ScopedNoInternalCallCallbackBundle`, with a nil-safe wrapper for the same
  syntactically nonempty-or-retained-layout boundary and a specialized
  `Checked.scopedAfter` wrapper that removes the nil-safety premise entirely on
  the common scoped-body path.  The entry-facing wrapper can now also consume a
  recursive-only callback package plus the existing full `SourceDirect.CtxRel`,
  deriving the bundled `LiveCtxCleanupRel` facts internally.  The
  recursive-only callback package itself now consumes `LiveCtxCleanupRel`
  directly, with the full-`CtxRel` route left as a compatibility adapter.  Its
  checked zero-fuel base case closes all body/tail/loop obligations by
  contradiction from the impossible successful source run at fuel zero.  The
  non-recursive `ScopedNoInternalCallCallbackBundle` surface now stores the
  bundled `LiveCtxCleanupRel` field directly as well, so open/scoped wrappers
  project break/continue cleanup from one context invariant instead of carrying
  split fields.  The invariant open-block facade now also has checked
  body/if/switch derivation helpers under an explicit handler-live subset
  condition, via `blockBody_of_open_block_of_handler_live_subset`,
  `ifBody_of_open_block_of_handler_live_subset`, and
  `switchBody_of_open_block_of_handler_live_subset`.  This records the exact
  remaining boundary instead of assuming trimmed layouts retain handler slots
  unconditionally.  The liveness layer now also has checked structural
  membership facts for block, if, and selected switch bodies, and the open-block
  facade has shape-specialized block/if/switch helpers:
  `blockBody_of_open_block_of_body_handler_live_subset`,
  `ifBody_of_open_block_of_body_handler_live_subset`, and
  `switchBody_of_open_block_of_selected_body_handler_live_subset`.  These derive
  the required statement-live handler retention from body/selected-body live
  retention instead of taking raw statement-live subset premises.  The
  source-facing side now also records `LiveHandlerScopeRel`, with initial,
  loop-control, without-loop-control, and scope-growth lemmas, plus
  `LiveBefore.let_after_of_ne` and `LiveBefore.let_after_of_scoped_scope`.
  This makes the future path-sensitive break/continue liveness proof state the
  no-handler-shadowing fact explicitly instead of smuggling it through the
  callback cleanup relation.  The handler-scope relation now also preserves
  through regular source statement/block runs (`stmt_regular`, `block_regular`)
  and has scoped-`let` adapters for break/continue handler live sets
  (`breakLive_subset_let_liveBefore_of_scoped`,
  `continueLive_subset_let_liveBefore_of_scoped`), so later result-sensitive
  liveness induction can recover the handler-live subset facts from source-run
  evidence plus scoping rather than a raw cleanup-side premise.  The selected
  switch route now also derives selected-body scoping from whole-switch scoping
  and the actual `Source.Switch.select` result via
  `SourceScoped.blockScoped_of_switch_select_some`, and the open-block facade
  exposes
  `switchBody_of_open_block_of_selected_body_handler_live_subset_of_switch_scoped`;
  selected switch branches therefore no longer need a separate selected-body
  scoping premise before the remaining handler-live subset proof is derived.
  The bridge layer now also has a checked mode-sensitive cleanup surface,
  `LiveCtxOutcomeCleanupRel`, with trim preservation through
  `trimDeadPrefix_of_mode_live_subset`: a trimmed context can carry only the
  cleanup fact demanded by the actual source outcome (`break` needs break
  cleanup, `continue` needs continue cleanup, and regular/leave/halt need no
  handler cleanup).  This records the intended next refactor target explicitly
  instead of trying to prove both handler live sets are present on every
  successful run.  The block-open result relation now exposes
  `LiveBlockOpenResultRel.ctxRel` and
  `LiveBlockOpenResultRel.outcomeCleanup_of_not_break_continue`, and the
  bridge wrapper
  `LiveBlockOpenRunBridgeWithLayoutTo.target_result_with_noncontrol_outcome_cleanup_of_source`
  returns that outcome-sensitive cleanup fact for regular/leave/halt source
  results.  A tempting stronger shortcut, that nonregular open-block results
  return the original block context, is false because regular prefixes can grow
  the context before the eventual break/continue; the remaining control-outcome
  route must therefore preserve handler cleanup through those regular prefixes
  and derive the matching live-set retention at the actual control result.
  The preservation side now has the sibling callback facade
  `ScopedNoInternalCallRecursiveOpenBlockOutcomeCallbacksUpTo`, whose block
  callback consumes `LiveCtxOutcomeCleanupRel` instead of full
  `LiveCtxCleanupRel`.  Its zero/monotonicity lemmas, compatibility adapter back
  to the full-cleanup callback facade, and
  `block_trimDeadPrefix_of_mode_live_subset` adapter are checked; the adapter
  requires break-live retention only when the actual source outcome is `.brk`
  and continue-live retention only when it is `.cont`.  The generic nested
  block/if/switch helper layer now has matching outcome-aware helpers
  (`blockBody_of_open_block_of_mode_live_subset`,
  `ifBody_of_open_block_of_mode_live_subset`, and
  `switchBody_of_open_block_of_mode_live_subset`), so future recursive
  callbacks can use the mode-sensitive retention premises directly.  The
  block/if/selected-switch shape-specialized siblings now lift those conditional
  premises from body/selected-body liveness to statement liveness via the
  checked `LiveBefore` membership lemmas.
  It also derives the loop-init recursive callback directly:
  `forInit_of_open_block` applies the checked open-block callback family to the
  lowered init block, using `withoutLoopControl` to make handler cleanup
  vacuous and the loop `initAfter = scopedAfter cleanedLayout loopLive` shape
  supplied by the executable lowerer.  The
  exact-fuel package is also wrapped by the checked bounded
  facade `ScopedNoInternalCallRecursiveCallbacksUpTo`, with zero and monotonicity
  lemmas; this gives the future successor proof a compositional max-fuel
  induction target instead of a raw exact-fuel public premise.  That bounded
  family is now explicitly leave-frame-aware, matching the root-safe public
  invariant instead of quantifying over impossible arbitrary hidden-return
  contexts.  The scoped
  live-layout theorem can now consume that bounded facade directly, deriving the
  exact callback bundle internally from the checked `fuel <= maxFuel` fact, and
  the matching open-block target-result theorem now has the same callback-bundle,
  recursive-bundle, and bounded-facade wrappers.  This gives the successor proof
  the open-body/tail entry point it needs without reopening the structural
  callback list.  The successor route now also has an invariant-carrying
  open-block facade, `ScopedNoInternalCallRecursiveOpenBlockCallbacksUpTo`,
  modeled after the older fixed-layout `SourceDirect.RecursiveCallbacksUpTo`:
  callback obligations consume the actual source run plus no-CALL/scoping,
  `LiveCtxCleanupRel` (bundling `LiveCtxRel` with break/continue cleanup-scope
  facts), layout nodup, hidden-return, return-length, and live-control facts at
  the call site, so dead-prefix-trimmed layouts do not need to pretend they satisfy full
  `CtxRel`.  Its zero/monotonicity lemmas, first `fuel + 1` block successor
  bridge, and structure-level `succ_of_recursive_callbacksUpTo` wrapper are
  checked, so an exact recursive callback family now yields an open-block
  facade at the next fuel bound.  The facade now also has a checked
  `block_trimDeadPrefix_of_handler_live_subset` adapter: if the chosen live set
  keeps the current break/continue handler live sets, the same invariant block
  callback applies after `Layout.trimDeadPrefix`, deriving the trimmed
  `LiveCtxRel`, handler cleanup, and nodup facts internally.  Those context and
  handler-cleanup invariants are now bundled as `LiveCtxCleanupRel`, with
  checked adapters from full `SourceDirect.CtxRel`, through
  `withoutLoopControl`, and through handler-live-subset trims.  The open-block
  facade now consumes that bundle directly, so successor and trim adapters no
  longer thread context and handler cleanup as loose side facts.  The bundle
  now also preserves through whole-prefix local scope/layout growth, layouts
  that retain the previous layout as a cleanup suffix while staying inside the
  source scope, and the self loop-control setup used by target loops, reusing
  checked cleanup-suffix algebra instead of re-proving handler facts at each
  callback site.  The
  next step is still to extend that
  invariant-carrying facade through body/if/switch/tail/loop callback
  construction, either by deriving the handler-live subset facts from liveness
  at actual break/continue-producing paths or by splitting a weaker result-only
  facade where cleanup is not needed, and derive the full successor case from source
  acceptedness/checker output rather than expose the package at the public route.
  Remaining
  public-gate work is to discharge the recursive
  body/tail/handler callbacks from source acceptedness and compose the
  live-layout preservation result into the public `compile_preserves` shape.
- [x] Reshape the live-layout checker/lowerer around on-demand promotion:
  `Checked.StmtList.check?`, `Lower.StmtList.toLocals?`,
  `StmtList.toLocals?_cons_components`, and the open-block preservation
  callback surface now consume the suffix-protected prepared final layout and
  emitted promotion prefix before invoking the existing head bridge.  This
  removes rejection for `SWAP16`-reachable live values while keeping genuinely
  too-deep live values rejected until a separately modeled spill discipline
  exists.
- [ ] Wire the new checker into `Functions.Program.CompileAccepted`, then lift
  through Objects/Yul and the no-CALL public compile gate.  The existing
  fixed-layout `FrameBound` route should remain as compatibility until the
	  live-layout route covers the same accepted fragment and more.  Current
	  checkpoint: `Functions.Source.Program.compileLiveNoInternalCallChecked?`
	  exposes the live-layout/no-internal-CALL candidate compile gate and proves
	  executable no-CALL plus live-check success.  It now also proves that, when
	  the source program has `usesCallCreate = false`, the emitted assembly has
	  `Assembly.Program.usesCallCreate = false`.  A program-level source-run to
	  `Locals.Direct.Program.runState` wrapper now consumes successful
	  `toLocalsNoInternalCall?` plus
	  `ScopedNoInternalCallRecursiveCallbacksUpTo`; the final public semantic
	  preservation theorem still needs that callback family discharged from
	  source-facing acceptedness/checker facts before it can use the live route.
	  A newer wrapper,
	  `runState_toLocalsNoInternalCall_exists_of_all_recursiveCallbacksUpTo`,
	  now instantiates `maxFuel := fuel` internally, matching the eventual
	  `constructed/all_upTo` shape and leaving only the all-fuels callback
	  constructor to discharge.
	  The current all-fuels constructor frontier is a theorem-boundary issue, not
	  merely fuel arithmetic: `ScopedNoInternalCallCallbackBundle.blockBody`,
	  `ifBody`, and `switchBody` still quantify over arbitrary surrounding
	  statement shapes, while the checked statement dispatcher only consumes
	  those callbacks after matching `.block`, `.if_`, or selected `.switch`
	  heads.  The already-checked helper layer can derive those body callbacks
	  from mode-sensitive/handler-live retention facts, and the liveness
	  definition shows that arbitrary unrelated heads need not retain
	  `breakLive`/`continueLive`.  The next Lean repair is therefore to narrow the
	  callback surface to shape-specific body obligations, or to add a
	  shape-specific structural route for the live-layout public wrapper, before
	  attempting `all_upTo`; a broad constructor for the current callback bundle
	  would be an accidental assumption.  Current checked checkpoint:
	  `ScopedNoInternalCallShapeBodyCallbacks`,
	  `ScopedNoInternalCallShapeCallbackBundle`,
	  `ScopedNoInternalCallShapeRecursiveCallbackBundle`, and
	  `ScopedNoInternalCallShapeRecursiveCallbacksUpTo` now expose the
	  shape-indexed recursive interface with zero-fuel and monotonicity lemmas;
	  `noncall_liveStmtRunBridge_from_source_run_of_lower_noInternalCall_shape_handlers_of_leaveFrame`
	  is the checked statement-level dispatcher that consumes constructor-shape
	  equality witnesses before invoking recursive body callbacks.  The route now
	  also has checked cons/block composition through
	  `stmtList_cons_target_result_of_source_run_lower_with_layout_to_noInternalCall_head_shape_callbacks_tail_entryLayout_of_leaveFrame`
	  and
	  `block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame`.
	  The route is now lifted through the open-block, scoped-block, and
	  program-level public wrappers:
	  `Program.runState_toLocalsNoInternalCall_exists_of_shapeRecursiveCallbacksUpTo`
	  and
	  `Program.runState_toLocalsNoInternalCall_exists_of_all_shapeRecursiveCallbacksUpTo`.
	  These names are pinned by `LayerAudit`, so the broad callback family is no
	  longer the only public live-layout route.  The remaining work is to derive
	  the all-fuels shape-recursive callback family from source-facing checked
	  facts instead of accepting it as a theorem premise.  The route now has a
	  checked cleanup-relation successor surface,
	  `block_target_result_of_source_run_lower_with_layout_to_noInternalCall_live_control_shape_recursive_callbacksUpTo_tail_entryLayout_protected_scopedAfter_of_cleanup_of_leaveFrame`,
	  plus
	  `ScopedNoInternalCallShapeRecursiveCallbacksUpTo.block_succ_of_cleanup_of_leaveFrame`.
	  This avoids requiring full `SourceDirect.CtxRel` for recursive
	  live-layout bodies, which is too strong after trimming.  The next proof
	  step is to add the matching leave-frame/outcome-cleanup open-block
	  callback layer, so the all-fuels constructor can use mode-specific
	  break/continue cleanup instead of assuming full handler cleanup in body
	  contexts where the actual outcome does not need it.
	  The open-block successor facade now has both nonempty-hidden-return and
	  `LeaveFrameAvailable` variants, so the eventual constructor can handle the
	  public root case where `hiddenReturns = []` instead of relying on the
	  older nonempty-frame shortcut.  The inner bounded callback-family
	  invariant now carries the same leave-frame availability premise, so this
	  public-root route is no longer blocked by an overbroad all-context
	  callback quantifier.  Tail-entry adapter checkpoint: the executable
	  lowerer now exposes statement regular-output cleanup, and the preservation
	  layer has a cons-compositor wrapper where recursive tails prove their own
	  entry-layout relation while the head/prepare cleanup facts compose back to
	  the enclosing base layout.  The bounded family still needs to be
	  constructed against this narrower tail surface.  Additional scoped-layout
	  checkpoint: `Checked.scopedAfter` keeps entry-layout names
	  live as a set, so scoped bodies/branches now raise the preparation protected
	  depth to at least their entry-layout length before lowering.  This prevents
	  promotion from reordering the scoped reset suffix by construction while
	  still allowing newly introduced dead locals above it to be trimmed.  The
	  checker/lowerer, preservation callback interfaces, and `LayerAudit`
	  tripwires have been updated to the protected-context shape.  Exact
	  target regular-context facts are now checked for target statements,
	  statement lists, blocks, and live-layout lowerer runs: regular target
	  execution yields `runCtx = targetCtx.withLayout outLayout`, not merely
	  `runCtx.layout = outLayout`.  The remaining recursive-callback closure
	  should use the existing trace-aware protected scoped-after theorem.  The
	  callback bundle now records the trace-aware `tailEntry` field, including
	  the actual regular source head and tail runs, and the preservation layer
	  exposes protected scoped-after wrappers that consume that field through
	  callback bundles, recursive callback bundles, and bounded callback
	  families for both the nonempty-hidden-return route and the public
	  `LeaveFrameAvailable` root route.  The program-level source-run wrapper now
	  calls the scoped protected tail-entry theorem at `hiddenReturns = []`,
	  discharging the initial protected-entry bound locally instead of falling
	  back to the older weak-tail relation.  Remaining closure: construct
	  `tailEntry` from the bounded source-fuel callback family instead of
	  treating the callback bundle as a caller-supplied package.  The focused
	  `LayerAudit` pins now check the leave-frame-aware protected tail-entry route
	  and the scoped public-root wrapper names.
	  Exact frame-word note: the path-summed hidden-return headroom surface is
	  already checked in `Functions.CallDepth.SourceFrameWordSumResourceBound` and
	  pinned in `LayerAudit`; the remaining exactness work is to prefer that
	  source-facing sum route through the Yul public compile gates instead of the
	  max-frame-size-by-depth compatibility route wherever the CALL-owned bridge
	  build permits it.
- [x] Add regression examples:
  audit tripwires cover the key many-dead-locals acceptance case for the
  executable checker, plus the still-rejected genuinely deep live read without
  a modeled spill discipline.  The audit also pins
  `Layout.entryWindowOk?` to its exact index-in-trimmed-layout iff shape, so the
  remaining top-16 limitation is plainly the lack of spilling for truly-live
  deep locals.  It now also distinguishes SWAP-based layout promotion of a
  17th stack slot from still-impossible promotion of an 18th slot, and checks
  that the real `Checked.StmtList.check?`/`Lower.StmtList.toLocals?` path
  accepts a SWAP16-reachable deep read while rejecting the no-spill all-16-live
  boundary case.  The audit now also includes a two-deep-read case with one
  dead spacer in a 17-slot window: the real checker/lowerer accepts by repeatedly
  promoting live names until the dead spacer sinks below the live window.  The
  current scheduler now handles that case with the two necessary promotion
  statements by prioritizing statement access before final live-suffix order, so
  the remaining top-16 work is any future memory-backed spill discipline for
  genuinely-live deep locals.  `LayerAudit` now pins the key scratch-memory
  constraint: two target states related to the same Locals source state must
  have equal `toSharedState`, so a spill macro must restore memory, `activeWords`,
  return buffers, logs, and the rest of shared state exactly unless the source
  theorem is deliberately changed to expose scratch ownership.  The first
  source-facing scratch hook is now
  `StateRel.SpillScratch.ScratchWordReserved`: audit examples show offset zero
  is not reserved at `activeWords = 0` and is reserved once one memory word is
  active, but not necessarily byte-allocated in the underlying memory array.
  The source-lowering lemmas prove `mload`/`mstore` preserve
  `activeWords` under that predicate, and prove the converse iff facts: a
  private `MLOAD`/`MSTORE` at the scratch offset leaves `activeWords` unchanged
  exactly when the scratch word is reserved.  This pins the impossibility of
  using memory spilling from an arbitrary zero-active-memory state while
  preserving the current exact state theorem.  The stronger scratch bridge now
  proves a reserved `mload` preserves the whole `MachineState` and EVM
  `toSharedState`, splits the remaining exact spill-store/restore theorem into
  the byte-array `ScratchWordMemoryRestoreObligation`, and derives the
  whole-machine `ScratchWordOverwriteRestoreObligation` from that byte fact plus
  scratch reservation.  The byte-level overwrite/restore splice is now proved
  for exact 32-byte word writes by `byteArray_write32_restore_exact`.  The
  scratch-byte canonicality premise has been split into concrete pieces:
  allocated 32-byte memory reads are proved exact by
  `byteArray_readWithPadding32_allocated`, and
  `scratchWordBytesCanonical_of_readable` derives
  `ScratchWordBytesCanonical` from allocation, an explicit
  `ScratchWordReadable` guard for `lookupMemory`, and
  `WordByteEncodingModelSpec` for fixed-size/round-trip `UInt256` byte
  encoding.  The readable/reserved side is now derived from a concrete scratch
  policy: `ScratchWordWithinActiveNat` proves the old no-expansion
  `ScratchWordReserved`, and together with `ScratchWordAllocated` plus
  `ScratchActiveBytesNoOverflow` proves `ScratchWordReadable`; the composed
  `memoryRestore_of_allocated_withinActiveNat` and
  `overwriteRestore_of_allocated_withinActiveNat` theorem surfaces now expose
  exact restoration from that policy.  The dependency now exposes public
  `UInt256` list-byte length/round-trip lemmas, and the local byte-array bridge
  proves `ByteArray.toList = data.toList`, `List.toByteArray` data recovery,
  zero-padding data canonicality, and
  `wordByteEncodingModel_of_zeroPadding`.  Thus the full fixed-size/round-trip
  `WordByteEncodingModelSpec` follows from the existing zero-padding interface.
  The scratch policy now has a compiler-facing region surface:
  `ScratchRegionAllocatedNat`, `ScratchRegionWithinActiveNat`, and
  `scratchRegionWord` derive each slot's allocation, within-active bound,
  readability, memory-restore obligation, and whole-machine
  overwrite/restore obligation via `overwriteRestore_of_regionNat`.  A future
  spill scheduler can therefore discharge per-slot byte facts from one checked
  region contract instead of re-proving them ad hoc.  The remaining acceptance
  decision is whether a memory-spill route may require a source-facing
  preallocated/within-active scratch-region premise; under the current exact
  state theorem, it cannot soundly widen compilation for arbitrary starting
  machine states with no active/allocated scratch memory.  Because the existing
  Locals/Functions/Yul preservation stack threads exact
  `toSharedState` equality, switching to an observational memory relation would
  be a deliberate cross-layer refactor rather than a local scheduler tweak.  The
  current stack-only realization is
  now named `Locals.Ctx.promoteNameStackOnly?`, and the pure layout move is
  separated as `LiveLayout.Layout.promoteNameUnbounded?`; `LayerAudit` checks
  that an 18th-slot name has a valid unbounded layout promotion while both the
  stack-only layout helper and Locals backend still reject it.

### Acceptance Power Ladder

Each rung should be independently useful and checked before moving upward:

- [ ] Rung A: all acyclic internal-call graphs.
- [ ] Rung B: recursive SCCs with explicit finite active-frame evidence.
- [ ] Rung C: recursive SCCs with constant/range guards inferred by interval
  analysis.
- [ ] Rung D: affine and lexicographic ranking check results over bounded word
  ranges.
- [ ] Rung E: path-sensitive refinement for switches, loops, and mutually
  recursive dispatch patterns.
- [ ] Rung F: optional sidecar evidence checked by the same executable
  checker, so power can grow without enlarging trusted theorem assumptions.

### Architecture Risks

- [ ] Ranking inference over full Yul arithmetic is undecidable in general; the
  checker must stay sound and incomplete rather than clever and opaque.
- [ ] Worst-case 256-bit measures are usually too large for the 1024-word stack;
  useful accepted recursion needs small constant/range bounds, not merely
  "decreases a word".
- [ ] Existing structured preservation may not expose every intermediate frame
  annotation needed by the stack theorem. If so, add an annotated preservation
  theorem rather than reintroducing a public trace witness.
- [ ] Avoid broad `simp` over compiled programs in checker soundness proofs;
  prove small algebraic soundness lemmas for summaries and recurrence solver
  output.
- [ ] Keep CALL and internal recursion separate: external CALL reentrancy can
  mutate shared state, but it must not be counted as an internal return-frame
  stack push in this analyzer.
