# Oracle Request: Public Open-CALL Compiler Theorem

We are in the Lean project:

`/Users/dan/Projects/evm-compiler`

I want a high-level theorem-boundary critique and proof-strategy review for the
CALL-capable public theorem of a formally verified Yul-to-EVM compiler.

## Desired Theorem, Informally

Replace the current no-CALL public theorem with a CALL-capable theorem:

Given an accepted Yul program and its checked compiler output, if imported-Yul
execution starts in a source state related to the compiled EVM/source-lowered
state, then for every finite selected trace of external CALL responses:

1. the imported Yul/open-source execution and compiled target/open execution
   expose the same external CALL request at each step;
2. both sides consume the same arbitrary external response at each step;
3. after each response, the outside world may have caused arbitrary caller
   account/storage mutation, but only responses admitted by the open boundary
   are considered, meaning the post-response source and target states remain in
   the relevant state relation;
4. when the finite trace ends, the source result and target result are related
   by the existing terminal/revert/outcome relation;
5. no concrete callee, chain world, precompile table, child-code branch,
   account-map transition system, or external-world state model is assumed.

Requested gas is intentionally abstract at this layer, but the requested-gas
operand is still part of the visible request identity. The theorem proves both
sides compute the same requested-gas operand; it does not prove a chain-specific
forwarded-gas formula.

The theorem should eventually replace the current public no-CALL spine:

```lean
theorem compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall
    {cfg : Reference.StateRelConfig}
    {terminalRel :
      Assembly.HaltKind -> Word -> Reference.State ->
        Objects.Source.State -> Prop}
    {revertRel : Reference.State -> Objects.Source.State -> Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {outcomeRel : Reference.OutcomeRel}
    {program : Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : EVMState}
    {referenceResult : Reference.Result}
    (hTop :
      RecursiveBridgeTopNoCallAssumptions cfg terminalRel revertRel prim
        outcomeRel program asm target shared store sourceFuel initial
        referenceResult) :
    ...
```

The CALL theorem should be path/open-trace based, not closed-result-only:
roughly, source open execution resolves along an arbitrary finite trace, and
the compiled target has some target fuel/cutoff that follows the same trace and
ends in a related result. One target fuel need not work for all possible
response trees.

## Existing Open External Boundary

File: `EvmCompiler/Yul/OpenExternal.lean`

```lean
inductive CallKind where
  | call
  | callcode
  | delegatecall
  | staticcall

structure CallRequest where
  kind : CallKind
  requestedGas : Word
  caller : Address
  recipient : Address
  codeAddress : Address
  transferValue : Word
  apparentValue : Word
  calldata : ByteArray
  permission : Bool

structure ReturnWindow where
  inOffset : Word
  inSize : Word
  outOffset : Word
  outSize : Word

structure CallSite where
  request : CallRequest
  returnWindow : ReturnWindow

structure CallResponse where
  success : Bool
  returnedGas : Word
  returnData : ByteArray
  internalMutation : ReentrantStateMutation

structure OpenCall (State : Type v) where
  site : CallSite
  resume : CallResponse -> State

inductive OpenResult (eps : Type u) (alpha : Type v) : Type (max u v) where
  | done : Except eps alpha -> OpenResult eps alpha
  | call : OpenCall (OpenResult eps alpha) -> OpenResult eps alpha
```

The path relation is the core observation model:

```lean
inductive OpenResultPathRel
    {eps1 : Type u} {eps2 : Type v} {alpha : Type w} {beta : Type}
    (callResponseRel :
      OpenCall (OpenResult eps1 alpha) ->
        OpenCall (OpenResult eps2 beta) -> CallResponse -> Prop)
    (doneRel : Except eps1 alpha -> Except eps2 beta -> Prop) :
    OpenTrace -> OpenResult eps1 alpha -> OpenResult eps2 beta -> Prop where
  | done ...
  | call
      {sourceCall : OpenCall (OpenResult eps1 alpha)}
      {targetCall : OpenCall (OpenResult eps2 beta)}
      {response : CallResponse} {trace : OpenTrace} :
      sourceCall.site = targetCall.site ->
      callResponseRel sourceCall targetCall response ->
      OpenResultPathRel callResponseRel doneRel trace
        (sourceCall.resume response) (targetCall.resume response) ->
      OpenResultPathRel callResponseRel doneRel
        ({ site := sourceCall.site, response := response } :: trace)
        (.call sourceCall) (.call targetCall)
```

So the theorem proves equality of the external request by equality of
`CallSite`, and universally quantifies over the response by path quantification.
The admissibility premise is where arbitrary reentrant internal mutation is
constrained only enough to preserve the source/target relation.

## Current Internal CALL Proof Architecture

File: `EvmCompiler/Yul/RecursiveBridgeSupport.lean`

The current locked plan is a mutual source-fuel induction with exactly three
frontiers:

1. ordinary statement sequences:
   `CALLOpenSeqPathLoweringFrontierAt`;
2. typed continuation statement sequences for generated control constructs:
   `CALLOpenSeqKontPathLoweringFrontierAt`;
3. direct generated loop continuation:
   `CALLOpenLoopContinuationPathLoweringFrontierAt`.

The recursive callbacks are:

```lean
def CALLOpenSeqPathRecursiveAt ...
def CALLOpenSeqKontPathRecursiveAt ...
def CALLOpenLoopContinuationPathRecursiveAt ...
```

with adapters:

```lean
theorem CALLOpenSeqPathRecursiveAt.of_frontiers_le ...
theorem CALLOpenSeqKontPathRecursiveAt.of_frontiers_le ...
theorem CALLOpenLoopContinuationPathRecursiveAt.of_frontiers_le ...
```

The one-head CALL frontier currently has this public-spine-facing shape:

```lean
theorem checkedOpenSeqPathLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_frontier_structural_single_expr_dispatch_canonical_terminal_of_programCALL_frontiers
    ...
    (hSeqFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec <= tailFuel ->
          CALLOpenSeqPathLoweringFrontierAt cfg ... sourceFuelRec)
    (hKontFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec <= tailFuel ->
          CALLOpenSeqKontPathLoweringFrontierAt cfg ... sourceFuelRec)
    (hLoopFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec <= tailFuel ->
          CALLOpenLoopContinuationPathLoweringFrontierAt cfg ... sourceFuelRec)
    ...
    (hOther : ... current residual fallback ...)
    : forall {compileFuel : Nat},
      CheckedOpenSeqPathLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx ...
```

The remaining local proof gate is the productive exact-fuel loop-continuation
frontier. Low fuel is already proved:

```lean
theorem callOpenLoopContinuationPathLoweringFrontierAt_low_fuel
    (hBound : bound <= 2) :
    CALLOpenLoopContinuationPathLoweringFrontierAt cfg ... bound
```

For productive loop fuel, the direct target contract is:

```lean
def SourceOpenLoopContinuationPathSoundWhenAtExactHiddenCtx
    (cfg : StateRelConfig) (layout outcomeLayout : List Name)
    ...
    (sourceFuel : Nat) (cond : AstExpr) (post body : List AstStmt)
    (codeOverride : Option AstContract)
    (lowerPost generatedBody : Functions.Block)
    (allowed : Except Exception State -> Prop) : Prop :=
  forall {source compiler trace sourceDone},
    SourceStateExactRel cfg layout source compiler ->
    OpenExternal.OpenResultResolves
      (OpenExternal.YulOpenResult.toOpenResult
        (OpenExternal.YulOpen.exec sourceFuel (.For cond post body)
          codeOverride source))
      trace sourceDone ->
    (SourceResultNotRegularOk sourceDone -> allowed sourceDone) ->
    SourceOpenTraceResponsesAdmissible cfg trace ->
    forall minimumTargetFuel,
      exists targetFuel,
        minimumTargetFuel <= targetFuel /\
        OpenExternal.OpenResultPathRel
          (SourceOpenLoopContinuationTraceCallResponseRel cfg)
          (SourceOpenLoopContinuationPathDoneRel cfg layout outcomeLayout
            terminalRel revertRel allowed)
          trace
          (OpenExternal.YulOpenResult.toOpenResult
            (OpenExternal.YulOpen.exec sourceFuel (.For cond post body)
              codeOverride source))
          (CompilerOpen.FunctionsOpen.Stmt.runForLoop prim program
            (ctx.withoutLoopControl) (.lit 1)
            (ctx.withoutLoopControl) lowerPost
            (ctx.withoutLoopControl.withLoopControl ctx.scope ctx.scope)
            generatedBody targetFuel compiler)
```

We have already Lean-checked direct `runForLoop` branch helpers covering:

1. condition stopped;
2. condition zero;
3. nonzero/body break;
4. nonzero/body stopping;
5. nonzero/body regular/post stopping;
6. nonzero/body continue/post stopping;
7. nonzero/body regular/post regular/recurse;
8. nonzero/body continue/post regular/recurse.

What remains is the orchestration theorem that combines those branches, then
the productive frontier theorem, then the mutual exact-fuel frontier induction,
then the public theorem wiring.

## Questions

Please critique the high-level theorem and proof architecture.

1. Is the public theorem boundary sound, or is there a hidden cheat in replacing
   a concrete external world with equal `CallSite`s plus arbitrary shared
   `CallResponse`s admitted by a relation-preserving predicate?
2. Is it acceptable that requested gas is part of `CallRequest`, while gas
   forwarding/feasibility is abstracted away at this layer?
3. Is the finite-path theorem the right quantification, as opposed to a single
   target fuel/cutoff working for all response trees?
4. Is the three-frontier source-fuel mutual induction the right proof
   architecture, especially the direct generated `runForLoop` frontier?
5. If not, what theorem shape would be more honest or easier to finish?
6. Assuming this route is correct, what is the cleanest sequence of Lean
   theorem statements to finish from the current state?

Constraints:

- Do not suggest reintroducing a concrete external world model unless the open
  theorem is actually false.
- Do not suggest direct `let CALL` or `assign CALL` scaffolding; nested CALLs
  should be expression-level and recursive.
- Do not keep compatibility routes; this project is unreleased.
- No `sorry`, no `admit`, no new axioms, and no weakening of theorem statements.
- If the theorem is too strong or under-specified, identify the exact missing
  observation or premise.

Useful failure would be:

- a counterexample to the theorem boundary;
- an explanation that the response/admissibility relation is too strong or too
  weak;
- a smaller theorem boundary that still captures real CALL equivalence;
- a precise Lean proof decomposition that avoids circular recursion.
