# Oracle Request: Live-Layout Recursive Callback Shape

Mode: hostile theorem-boundary critique / repair strategy.

Repo: `/Users/dan/Projects/evm-compiler`
File: `EvmCompiler/Functions/LiveLayoutPreservation.lean`

Context:

We are trying to remove the remaining `ScopedNoInternalCallRecursiveCallbacksUpTo`
premise from the live-layout stack-safety/equivalence path by proving an
all-fuels constructor, analogous to the already-working SourceDirect theorem:

```lean
-- EvmCompiler/Functions/SourceDirect.lean
theorem RecursiveCallbacksUpTo.all_upTo ...
```

The live-layout top wrapper now hides the arbitrary max fuel:

```lean
theorem Program.runState_toLocalsNoInternalCall_exists_of_all_recursiveCallbacksUpTo
    ...
    (hCallbacks :
      forall maxFuel,
        ScopedNoInternalCallRecursiveCallbacksUpTo prim sourceProgram
          targetProgram maxFuel) :
    exists targetFuel targetOutcome, ...
```

The remaining task is proving the `forall maxFuel` callback family from source
fuel/checker facts. There are already useful bounded callback records:

```lean
def ScopedNoInternalCallRecursiveCallbacksUpTo
    (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (maxFuel : Nat) : Prop :=
  forall {returns liveCtx after outLayout retc fuel sourceCtx targetCtx
      hiddenReturns source},
    fuel <= maxFuel ->
      SourceDirect.LeaveFrameAvailable sourceCtx hiddenReturns ->
      ScopedNoInternalCallRecursiveCallbackBundle prim sourceProgram
        targetProgram returns liveCtx after outLayout retc fuel sourceCtx
        targetCtx hiddenReturns source

def ScopedNoInternalCallRecursiveCallbackBundle ... : Prop :=
  SourceDirectBridge.LiveCtxCleanupRel retc sourceCtx targetCtx ->
    ScopedNoInternalCallCallbackBundle ...
```

There are also open-block bounded callbacks with a verified successor step:

```lean
theorem ScopedNoInternalCallRecursiveOpenBlockCallbacksUpTo.succ_of_recursive_callbacksUpTo
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    (hCallbacks :
      ScopedNoInternalCallRecursiveCallbacksUpTo prim sourceProgram
        targetProgram maxFuel) :
    ScopedNoInternalCallRecursiveOpenBlockCallbacksUpTo prim sourceProgram
      targetProgram (maxFuel + 1)
```

The apparent snag is the shape of `ScopedNoInternalCallCallbackBundle`.
For example, its `blockBody` field is:

```lean
structure ScopedNoInternalCallCallbackBundle ... where
  blockBody :
    forall {stmt rest restLive stmtLive liveLayout prep preparedLayout lowerStmt
        nextLayout lowerRest},
      restLive = StmtList.liveBefore liveCtx after rest ->
      stmtLive = Stmt.liveBefore liveCtx restLive stmt ->
      liveLayout = Layout.trimDeadPrefix targetCtx.layout stmtLive ->
      Prepare.forStmtAboveSuffix? liveCtx.protectedDepth returns liveLayout
        stmtLive stmt =
        some (prep, preparedLayout) ->
      Layout.entryWindowOk? preparedLayout stmtLive = true ->
      StmtAccess.accessible? returns preparedLayout stmt = true ->
      Lower.Stmt.toLocals? returns liveCtx preparedLayout restLive stmt =
        some (lowerStmt, nextLayout) ->
      Lower.StmtList.toLocals? returns liveCtx nextLayout after rest =
        some (lowerRest, outLayout) ->
      forall {cleaned},
        SourceDirect.StateRel preparedLayout hiddenReturns source cleaned ->
      forall {body lowerBody bodyLayout sourceOpenResult},
        NoInternalCall.Block.Holds body ->
        Scope.Block.Scoped sourceCtx.scope body ->
        Lower.Block.toLocals? returns
            (liveCtx.withProtectedLayout preparedLayout) preparedLayout
          (Checked.scopedAfter preparedLayout restLive) body =
          some (lowerBody, bodyLayout) ->
        Source.Block.runOpen prim sourceProgram sourceCtx fuel body source =
          .ok sourceOpenResult ->
        SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout prim
          sourceProgram targetProgram returns retc fuel sourceCtx
          (targetCtx.withLayout preparedLayout)
          hiddenReturns body lowerBody source cleaned
```

This looks over-strong: it quantifies over an arbitrary `stmt`, but the
`body` is not constrained to be the body of `.block body`. The lower statement
bridge only uses this callback after case-splitting `stmt = .block body`.
Indeed `nonloop_noncall_liveStmtRunBridge_from_source_run_of_lower_of_leaveFrame`
has a more shape-specific callback:

```lean
(hBlock :
  forall {body lowerBody bodyLayout sourceOpenResult},
    Scope.Block.Scoped sourceCtx.scope body ->
    Lower.Block.toLocals? returns
      (liveCtx.withProtectedLayout targetCtx.layout) targetCtx.layout
      (Checked.scopedAfter targetCtx.layout after) body =
      some (lowerBody, bodyLayout) ->
    Source.Block.runOpen prim sourceProgram sourceCtx fuel body source =
      .ok sourceOpenResult ->
    SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout prim sourceProgram
      targetProgram returns retc fuel sourceCtx targetCtx hiddenReturns
      body lowerBody source target)
```

The surrounding statement-list theorem lifts this through common
`restLive/stmtLive/preparedLayout` plumbing, but the public callback bundle
kept the broad arbitrary-`stmt` form.

Why this may be false:

* To use an open-block callback for `body`, we need
  `LiveCtxCleanupRel retc sourceCtx (targetCtx.withLayout preparedLayout)`.
* Deriving this through `Layout.trimDeadPrefix targetCtx.layout stmtLive` is
  only safe for break/continue cleanup when the handler live sets are kept.
* For arbitrary `stmt`, `stmtLive = Stmt.liveBefore liveCtx restLive stmt` need
  not contain `liveCtx.breakLive`/`continueLive`. Example shape: `stmt = .expr e`
  but the arbitrary `body` can break. The statement bridge will never ask for a
  block-body callback in the `.expr` case, but the record field does.

Question:

1. Is the `blockBody` field indeed too strong/false as an externally
   constructible obligation, or is there a generic invariant I am missing that
   makes `preparedLayout` cleanup-safe for arbitrary `stmt`?
2. If it is too strong, what is the cleanest repair strategy in Lean?
   My leading option is to replace the callback bundle fields with
   shape-specific obligations matching `nonloop_noncall_liveStmtRunBridge...`,
   e.g. `blockBody` only for `.block body`, `ifBody` only for `.if_ cond body`,
   `switchBody` only for selected switch bodies, `forInit/forLoop` only for
   `.for_ init cond post body`, while keeping `tail`/`tailEntry` tied to the
   actual `stmt/rest` decomposition.
3. Is there a smaller route that avoids refactoring the large theorem chain,
   perhaps by adding an intermediate shape-specific record and a wrapper theorem,
   without retaining an unconstructible broad callback field as a premise?

Constraints:

* No `sorry`, `admit`, new `axiom`, or trusted certificate/callback premise.
* Do not touch `EvmCompiler/Yul/RecursiveBridgeSupport.lean`; another agent is
  editing CALL support there.
* Accepted programs may be conservatively rejected for stack bounds, but any
  accepted program must have the source/target equivalence proof.
* We want to close the stack-too-deep proof route for the no-internal-CALL path
  before moving on to full spilling/top-16 ergonomics.

