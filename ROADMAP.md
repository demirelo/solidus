# Roadmap

## Audit Concerns To Fully Discharge

This is the current active goal. These items are not complete until the public
top theorem exports a full-Yul acceptedness surface, internally constructs the
Nethermind-Yul-to-source semantic bridge packages, and derives the gas-aware
`EVM.X` sufficient-gas/precondition evidence instead of taking it as an
external execution certificate.

Last updated: 2026-05-25 06:52 PDT.

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
   - [x] Add preferred gas-aware top wrappers that take full source
     acceptedness plus explicit feature coverage instead of the old bundled
     source-fragment acceptedness predicate.
   - [x] Export checked full-source-surface facts showing code-image and
     external call/create primitives are accepted by `Reference.Safe.Full`,
     while keeping the old rejection facts named as bridge-coverage facts.
   - [ ] Replace or refine `Reference.Safe.primitive` so accepted Yul no
     longer rejects code-image primitives solely because their bridge is
     missing.
   - [ ] Add checked semantics and compiler bridge support for
     `CODESIZE`/`CODECOPY` against the compiled object byte image.
   - [ ] Add checked semantics and compiler bridge support for
     `EXTCODESIZE`/`EXTCODECOPY`/`EXTCODEHASH`, or state and prove the exact
     external-account/code oracle relation that makes them full semantics
     rather than a fragment exclusion.
   - [ ] Add checked object/data builtin support for `datasize`, `dataoffset`,
     and `datacopy` in the checked Yul/object path, including the backend
     layout theorem and lowering to concrete `CODECOPY`.
   - [ ] Add checked semantics and compiler bridge support for
     `CALL`/`CALLCODE`/`DELEGATECALL`/`STATICCALL` and `CREATE`/`CREATE2`, or
     state and prove an explicit external-interaction oracle relation that is
     part of the full source/target semantics rather than a safety rejection.
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
   - [ ] Provide canonical terminal/revert contracts for
     `STOP`/`RETURN`/`REVERT`/`SELFDESTRUCT`.
     - [x] Prove the canonical `STOP` terminal step/existence lemmas for
       `Locals.Source.PrimitiveSemantics.structured`.
     - [x] Prove the canonical `RETURN` terminal step/existence lemmas.
     - [x] Prove the canonical `REVERT` terminal step/existence lemmas.
     - [x] Prove the canonical `SELFDESTRUCT` terminal step/existence lemmas.
     - [x] Bundle the four per-kind lemmas into the canonical
       `PrimitiveSound` terminal-step fields for
       `Locals.Source.PrimitiveSemantics.structured`.
   - [ ] Derive `RecursiveBridgeExprNoSuccessfulOutOfFuelContracts` from
     acceptedness/resource facts, or replace it with a smaller fundamental
     resource premise whose scope is exactly documented and exported.
   - [ ] Route the preferred top theorem through the canonical semantic
     constructors so users do not pass arbitrary semantic-contract packages.
     - [x] Add preferred gas-aware top wrappers specialized to the canonical
       structured primitive semantics, discharging the lower-tower
       `PrimitiveSound` field internally.

3. [ ] Derive gas-aware `EVM.X` sufficient-gas evidence
   - [x] Audit `Assembly.GasAware.XResultPreconditionAssumptions` and split
     fundamental gas/oracle assumptions from compiler-derived execution
     evidence. The preferred public wrapper now takes
     `Assembly.GasAware.XResultRunnerCompleteness asm target initial`, while
     the compiler theorem still derives the concrete `BlockTraceResult`
     internally.
   - [ ] Prove the needed `XResultPreconditionAssumptions` from the checked
     bytecode trace, target encoding/jumpdest correctness, gas oracle,
     out-of-gas policy, and explicit sufficient-gas bound.
   - [ ] Strengthen the preferred gas-aware top theorem so it existentially
     derives the gas bound and `EVM.X` agreement without taking an external
     `hX` certificate.

## Final Nethermind Yul Bridge Completion Steps

This is the checklist for the final blocker: construct the recursive
Nethermind-Yul-to-source-tower bridge internally, then thread it through the
dispatcher, assembly, bytecode, and gas-aware theorem surfaces. Mark an item
only when the corresponding Lean theorem exists, is exported through the public
bridge surface when relevant, and the current verification command has passed.

Last updated: 2026-05-24 22:04 PDT. Coarse blockers stay unchecked until every
indented subtask below them is checked. The proof route has pivoted slightly
top-down: finish the accepted-program recursive bridge spine first, then plug
the three user-call statement cases and remaining structured-control /
nonrelatable non-call cases into that accepted successor theorem.

Current assumption-cleanup checkpoint:

- [x] Record the current preferred top-boundary assumptions explicitly:
  - Source validity: `RecursiveBridgeSourceAccepted` bundles imported Yul
    acceptedness, lexical scoping, control-flow scoping, and user-call arity.
  - Lower resource validity: `RecursiveBridgeCompileResources` supplies
    `Objects.Source.Program.CompileAccepted` for the generated lower object;
    this is the stack/frame/accessibility resource boundary for the lower
    tower, not a semantic replay certificate.
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
  - Target entry/runtime: checked compiler success, initial shared-state
    relation, canonical entry PC/empty stack, code-size decode-window bound,
    jumpdest-scanner correctness, gas oracle, out-of-gas policy, and
    current-contract projection.
  - Discharged/generated facts at the top boundary: emitted no-call/create is
    proved from accepted source plus checked compilation; `DecodeSafety` is
    proved from checked assembler layout plus `TargetFitsDecodeWindow`; raw
    `RecursiveBridgeTargetRuntime` is no longer the preferred public input.
- [x] Classify the remaining `Reference.Safe.primitive` exclusions exactly.
  Code-image ops plus `CREATE`/`CREATE2` are imported-Nethermind-Yul
  semantics gaps; `CALL`/`CALLCODE`/`DELEGATECALL`/`STATICCALL` are the
  external-call boundary.
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
  - [x] Add a top-theorem wrapper
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_top_withAcceptedNoCallCreate`
    whose target-side inputs are only code-size decode-window,
    jumpdest/gas/out-of-gas/current-contract projection plus canonical entry
    PC/stack; it derives
    `asm.usesCallCreate = false` internally from source acceptedness and
    checked compile-target success.
  - [x] Add the bundled public no-call/create top package
    `RecursiveBridgeTopNoCallAssumptions` and theorem
    `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall`,
    so the preferred exported surface cannot hide a user-supplied arbitrary
    external-call agreement inside `RecursiveBridgeTargetRuntime`.
  - [x] Export audit projections for the preferred no-call/create top package:
    `sourceReferenceAccepted`, `lowerObjectCompileAccepted`, and
    `emittedNoCallCreate`, making clear which facts are source validity,
    explicit lower resource bounds, and checked compiler-derived facts.
  - [x] Export audit projections for the remaining bytecode target boundary:
    `targetFitsDecodeWindow` is an explicit resource/code-size bound, and
    `targetJumpdestCorrect` is the imported jumpdest-scanner boundary.
  - [x] Replace the public `DecodeSafety` premise with the resource bound
    `Assembly.Bytecode.TargetFitsDecodeWindow`. The actual `DecodeSafety`
    facts are now proved from checked assembler layout plus that byte-length
    bound by `Assembly.Bytecode.compile_decodeSafety`; `JumpdestCorrect`
    remains explicit because the imported EVMYulLean jumpdest scanner is
    opaque.
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
  - [x] Add the no-out-of-gas corollary
    `compile_whole_program_result_no_out_of_gas_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_X`.
  - [x] Export `LayerAudit` aliases
    `recursiveBridgeTopNoCallToEVMX` and
    `recursiveBridgeTopNoCallToEVMXNoOutOfGas`.
- [x] Expose the lower compiler-resource boundary through the standard
  source-facing package instead of only through a bespoke recursive-bridge
  resource record.
  - [x] Add `RecursiveBridgeCompileResources.of_sourceCompileAccepted`.
  - [x] Add the projection
    `RecursiveBridgeTopNoCallAssumptions.sourceCompileAccepted`.
  - [x] Add `RecursiveBridgeTopNoCallSourceCompileAssumptions`, whose public
    resource field is `Yul.Program.SourceCompileAccepted program`, and checked
    wrappers to the gasless result theorem and result-level `EVM.X` theorem.
  - [x] Export `LayerAudit` aliases
    `recursiveBridgeTopNoCallSourceCompileAssumptions`,
    `recursiveBridgeTopNoCallSourceCompileToGasAwareEVM`, and
    `recursiveBridgeTopNoCallSourceCompileToEVMX`.
  - [x] Export source-compile package audit projections for source
    acceptedness, source compile acceptedness, emitted no-call/create,
    target decode-window bound, and target jumpdest correctness, so the
    preferred top package has the same no-hidden-evidence audit surface as the
    older resource package.
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
    `RecursiveBridgePrimitiveContracts`,
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
    resource premise. `ExprEvalResultOkAt.of_noSuccessfulOutOfFuelAt` derives
    the non-checkpoint part from safe primitive checkpoint lemmas, while
    `RecursiveBridgeExprNoSuccessfulOutOfFuelContracts` states only that safe
    imported expression evaluation does not succeed with the historical
    `.OutOfFuel` marker. The preferred gas-aware aliases now route through this
    smaller expression-resource boundary.
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
    no-call/create canonical-observation result-level `EVM.X` theorem.
  - [x] The older gasless result bridge remains exported under the explicit
    names `recursiveBridgeTopToGaslessEVMResult` and
    `recursiveBridgeTopNoCallToGaslessEVMResult`.
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
  - [x] Add the new public wrapper names to the `#print axioms` audit tail and
    verify they report no `sorryAx`. Check:
    `/tmp/evm_new_public_axioms_check1.log`.
  - [x] Add the initial-shared wrapper to the `#print axioms` audit tail and
    verify it reports no `sorryAx`. Check:
    `/tmp/evm_initial_shared_axioms_check1.log`.
  - [x] Re-run `lake build EvmCompiler.LayerAudit` after the initial-shared
    wrapper. Check: `/tmp/evm_initial_shared_layeraudit_check1.log`.
  - [x] Add the bridge-accepted wrapper to the `#print axioms` audit tail and
    verify it reports no `sorryAx`; rerun the layer audit. Checks:
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
    original runtime-bundled result surface. The current default
    `recursiveBridgeTopToGasAwareEVM` alias is now the stricter source-compile
    no-call/create result-level `EVM.X` theorem; the gasless result bridge is
    retained under `recursiveBridgeTopToGaslessEVMResult`.
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
  `compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_X`,
  exported through `LayerAudit.ImportedYulBoundary.recursiveBridgeTopToGasAwareEVM`;
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
    the external-world/static-mode result contracts are proved.
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
   - Solidity front-half checkpoint: `scripts/solidity_to_yul_lean.py` invokes `solc --standard-json`, imports solc's Yul JSON AST structurally, emits bridge JSON or typed `EvmCompiler.Solidity.Frontend.Program`, accepts normalized bridge JSON back via `--input-format bridge-json`, documents that bridge contract with `scripts/bridge-json-v3.schema.json`, can persist creation/runtime bridge files with `--bridge-json-dir`, and provides conversions into the current `EvmCompiler.Yul.Program` backend entrypoint plus an object-preserving `EvmCompiler.Objects.Program` path. `EvmCompiler.Solidity.BridgeJson` decodes the normalized bridge JSON inside Lean, so the executable bytecode/artifact paths now keep solc-facing AST normalization in Python, write a temporary normalized-JSON sidecar, and hand Lean only that sidecar path before backend compilation; constructor-style `lean-ir` emission remains available for inspection. Generated Lean modules now expose both the checked backend handoff artifacts (`Yul.Program.compileChecked?`, `Assembly.compile?`, and encoded bytecode) and executable unchecked backend artifacts (`Program.compileUnchecked?` / `Program.bytecodeUnchecked?`) for the typed front-end path. The script also has `--format bytecode`, which asks Lean to compute `Program.bytecodeImageUnchecked?`: a code image with object/data pseudo-builtins resolved from this backend's emitted byte lengths and with child-object/data payload bytes appended. Runtime objects and creation objects can now emit bytecode hex from Solidity/Yul AST input without solc byte offsets. The typed front-end IR preserves data sections structurally as `DataSection` records with optional names and byte payloads instead of anonymous hex strings, records solc's mixed child-object/data payload order with `ObjectItemRef`, computes named local data-section `datasize` from those typed bytes, computes local named `dataoffset` from the emitted code image base and ordered payload stream, resolves child object `datasize`/`dataoffset` from recursively emitted child images, lowers `datacopy` to backend `codecopy`, and handles immutable placeholders in the executable image path by marker-computing Lean byte offsets for `loadimmutable` sites and expanding creation `setimmutable` patches to `mstore`. The executable smoke surface now includes dynamic calldata bytes/strings, `uint256[]` ABI round trips, environmental primitive reads, Solidity loops through solc's helper Yul, and memory struct allocation/field access through solc's memory helpers. The object-preserving path carries typed data sections and nested objects into the backend object layer, while still lowering each object's code through the existing Yul bridge. Remaining object/data blockers: object/data semantics are not proved, checked layout generation/payload append/immutable patching still need to move into the object backend theorem surface, and the current code-image bytecode lane is executable MVP plumbing rather than a preservation theorem.
   - Abstraction repair in progress: `Yul.SourceLowered.runState` is the compiler-facing lowering path into the repaired source tower (`Objects.Source` -> `Functions.Source` -> `Locals.Source`) so the imported-Yul bridge has a clean target that does not expose stack layouts or function return-frame conventions.
   - Target reference version: Lake pins `EvmYulLean` to the corrected fork branch `codex/solidity-switch-semantics` at `2cf8181c562abca3e35c600c9514e35c46260d46`, which includes selected-branch switch semantics, omitted-default-as-empty-block notation, and halting `SELFDESTRUCT` behavior.
   - Recursive theorem target: `SourceBridgeFacts.CheckedBlockLoweringSound` names the fuel-induction goal from checked Yul block lowering to `SourceResultBlockSound`; `SourceBridgeFacts.CheckedStmtBlockLoweringSound` names the single-statement version keyed to the actual `Stmt.toFunctionsList?` head/dispatcher lowerer; `SourceBridgeFacts.FreshCoversLayout` plus the fresh-aware `CheckedBlockLoweringSoundFresh` / `CheckedStmtBlockLoweringSoundFresh` variants capture the invariant that compiler-generated temporaries are fresh for the current source layout; `SourceBridgeFacts.CheckedDispatcherLoweringSound` is the root-dispatcher companion shaped around the exact `Stmt.toFunctionsList?` body equation produced by `Program.toObjects?`; and `Yul.Program.DispatcherSourceSound` bundles the dispatcher body soundness and result projection for the public source/assembly/bytecode wrappers. `checkedStmtBlockLoweringSound_stop_call` consumes real lowerer output for the no-temporary terminal target, and `checkedStmtBlockLoweringSoundFresh_selfdestruct_lit_call`, `checkedStmtBlockLoweringSoundFresh_return_lit_lit_call`, and `checkedStmtBlockLoweringSoundFresh_revert_lit_lit_call` consume real lowerer output plus the fresh-state/layout invariant for generated terminal preludes. `checkedDispatcherLoweringSound_of_stmtBlockLoweringSound` and `checkedDispatcherLoweringSound_of_stmtBlockLoweringSoundFresh` lift the single-statement theorem to the dispatcher theorem; `checkedDispatcherLoweringSound_selfdestruct_lit_call`, `checkedDispatcherLoweringSound_return_lit_lit_call`, and `checkedDispatcherLoweringSound_revert_lit_lit_call` package the generated-prelude literal terminal cases at the dispatcher boundary from only the dispatcher-shape equation, initial-scope equation, and terminal/revert contracts. The matching checked-spine assembly wrappers `compile_preserves_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted`, `compile_preserves_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted`, and `compile_preserves_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted` now route through those checked dispatcher constructors and generic result adapters instead of the older generated-prelude decomposition proof; the checked-spine bytecode/gas-aware wrappers `compile_whole_program_result_sound_of_dispatcher_return_lit_lit_prelude_call_checked_compileAccepted`, `compile_whole_program_result_sound_of_dispatcher_revert_lit_lit_prelude_call_checked_compileAccepted`, and `compile_whole_program_result_sound_of_dispatcher_selfdestruct_lit_prelude_call_checked_compileAccepted` compose the same checked assembly facts through the bytecode theorem. `LayerAudit` points the default assembly and bytecode aliases for those cases at the checked-spine wrappers while keeping older raw/compositional routes under explicit names. `Yul.Program.dispatcherSourceSound_of_checked_dispatcher_lowering` recovers the actual compiled dispatcher body from `toObjects?`, and `sourceBridge_of_checked_dispatcher_lowering_sound` plus the matching assembly/bytecode wrappers consume the checked dispatcher-lowering theorem target directly. `Reference.Imported.exists_exec_dispatcher_of_runResult_succ_ok`, `Yul.Program.DispatcherRunResultSound`, and `Yul.Program.DispatcherObservationSound` lift that boundary to the real imported `Reference.runResult`, with source-bridge/assembly/bytecode wrappers starting from a successful imported run plus ordinary/terminal/revert observation contracts instead of a raw dispatcher-body `exec` or prebuilt result adapter. This is the intended boundary for the full imported-Yul recursive proof: callers should not pass independent body/result callbacks once the checked constructor exists.
   - Imported-Yul argument order is now separated from lower stack-order primitive evaluation by `ExprArgStackPreludeSound`, `PrimitiveStackSoundAt`, and `exprValuePreludeSound_prim_of_arg_stack_prelude`: generated preludes can be proved once in the source tower, while per-primitive lemmas state only the named source-order-to-stack-order semantic contract. Zero-result state-changing primitives now have reusable binary/ternary contract constructors and concrete wrappers for `mstore`, `mstore8`, `mcopy`, `calldatacopy`, and `returndatacopy`, so higher bridge proofs do not expose the relation plumbing for those families. Terminal prelude composition now has the same source-facing shape via `generatedPrelude_runOpen_append_exists`, `sourceResultBlockRunBridge_terminalStackPrelude_of_exec`, `sourceResultBlockRunBridge_terminalStackPrelude_of_arg_sound`, and the public `SourceResultBlockSound` lift `sourceResultBlockSound_terminalStackPrelude_of_arg_sound`; `sourceResultBlockSound_selfdestruct_lit_prelude_call_compositional`, `sourceResultBlockSound_return_lit_lit_prelude_call_compositional`, and `sourceResultBlockSound_revert_lit_lit_prelude_call_compositional` are the first concrete terminal-prelude theorems routed through that wrapper. The clean `return(offset, size)`, `revert(offset, size)`, and `selfdestruct(recipient)` paths now also reach compositional dispatcher `SourceBridge`, assembly compile-preserves, and bytecode/gas-aware wrapper theorems.
   - Accepted compiler-facing subset currently includes literals, variables, primitive calls that map to the verified structured primitive surface including `gas`, blocks, lets, switches, optimizer-style `for`, break/continue/leave, user-function declarations, statement-level user calls, and one-result user-call expressions lowered through fresh temporaries.
   - Accepted imported-reference bridge subset is still narrower at the proof boundary: it rejects code-image and external-call/create primitives in `Reference.Safe` until the corresponding state/result relations are proved against the imported reference semantics. `RETURN`, `REVERT`, and `SELFDESTRUCT` are accepted at the safe-boundary; concrete dispatcher terminal coverage now reaches the gas-aware bytecode theorem for `stop()`, zero/literal `return`/`revert`, writable `selfdestruct(0)`, and the generated-prelude literal-argument terminal variants, with auto wrappers deriving generated temporary names, fresh-name distinctness, and literal argument lowerer evidence from compiler output.
   - Rejected by accepted lowering for now: call/create builtins, object pseudo-builtins, and any construct that fails lower-layer WF or bounded inline expansion.
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
   - [ ] Add explicit external-world/account-code call semantics and state relation before re-admitting `CREATE`, `CREATE2`, `CALL`, `CALLCODE`, `DELEGATECALL`, or `STATICCALL`.
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
   - Semantic blockers fixed in the target fork: selected-branch switch execution, omitted default notation, and halting `SELFDESTRUCT` behavior. Argument-lowering now binds each argument before later argument effects. Remaining bridge blockers are proof-side: replacing `Reference.SourceBridge.sourceRun` with recursive per-construct source-tower theorems, proving source-to-direct function-call preservation, proving object/data/code-image relations, generalizing primitive bridges beyond the current checked arithmetic/comparison/bitwise-shift/modular-arithmetic/nullary-environment/state/machine-state/first one-argument read/state-update and `KECCAK256` slice (`ADD`/`MUL`/`SUB`/`DIV`/`SDIV`/`MOD`/`SMOD`/`ADDMOD`/`MULMOD`/`EXP`/`SIGNEXTEND`/`LT`/`GT`/`SLT`/`SGT`/`EQ`/`AND`/`OR`/`XOR`/`BYTE`/`SHL`/`SHR`/`SAR`/`KECCAK256`/`ADDRESS`/`ORIGIN`/`CALLER`/`CALLVALUE`/`CALLDATALOAD`/`CALLDATASIZE`/`GASPRICE`/`PREVRANDAO`/`BASEFEE`/`BLOCKHASH`/`BLOBHASH`/`BLOBBASEFEE`/`COINBASE`/`TIMESTAMP`/`NUMBER`/`GASLIMIT`/`CHAINID`/`SELFBALANCE`/`BALANCE`/`MLOAD`/`SLOAD`/`TLOAD`/`RETURNDATASIZE`/`MSIZE`/`GAS`), handling compiler-only temporaries emitted by expression preludes via scoped cleanup or an explicit hidden-local relation, and discharging code-size, remaining account-map-dependent reads, memory-write/storage-write, external-call/create, revert, selfdestruct-result/static-mode, and out-of-gas resource contracts.

## Layer Standard

- [ ] Syntax, independent executable semantics, relational semantics when useful, WF/acceptance, lowering, adjacent preservation theorem, composed public theorem. Transparent adapter boundaries are allowed only when they introduce no new source constructs and are explicitly audited.
  - [x] Assembly through Functions have independent executable semantics over their own syntax and checked adjacent preservation.
  - [x] Objects is an audited transparent root-object adapter with `Object.run` / `Program.run` and checked `run_toFunctions` / `eval_toFunctions`.
  - [x] Yul's public source interpreter is independent: `Yul.Program.run` enters the imported Nethermind interpreter, and `Yul.Reference.runResult` is an alias to that same boundary.
  - [x] Yul's compiler connection has a checked imported-run/source-run/bytecode composition theorem at the accepted boundary. Remaining incompleteness is source-language coverage and semantic-contract discharge, not a missing recursive bridge proof.
- [x] Lower-layer capabilities pass through unless intentionally abstracted or explicitly rejected by the accepted subset.
- [x] Public theorem is same-observation for the accepted source run boundary, not a replay certificate boundary.
- [x] Layer audit gate: build, proof-hole scan, theorem names, remaining assumptions, and progress-log entry.
- [x] Root imports `EvmCompiler.LayerAudit`, a checked theorem-spine tripwire naming each adjacent preservation theorem and keeping the imported-Yul `SourceBridge` boundary visually separate from completed adjacent proofs.
  - [x] `EvmCompiler.LayerAudit` names every current interpreter boundary and adjacent connection proof, including the explicit transparent Objects adapter, the quarantined compiler-facing `Yul.Lowered.run`, and the final bundled imported-Yul recursive bridge theorem to the gas-aware EVM route.

## Proof Hardening

- [ ] Derive sufficient-gas witnesses from finite traces instead of taking them only as assumptions.
- [ ] Replace `JumpdestCorrect` with an imported or locally proved scanner theorem if EVMYulLean exposes enough internals.
- [ ] Keep every new layer adjacent: prove preservation only to the layer immediately below, then expose a composed top theorem.
