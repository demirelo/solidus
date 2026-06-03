# Oracle follow-up: raw tail-entry invariant for live-layout stack guard

We are in `/Users/dan/Projects/evm-compiler`, Lean file:

`EvmCompiler/Functions/LiveLayoutPreservation.lean`

Prior oracle answer `resp_079c8c7f829f9b8a006a1f68db2e7881a2bb3ef64425eb4996`
recommended the outcome-sensitive open-block induction family:

```lean
structure ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame
    (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (maxFuel : Nat) : Prop where
  block :
    ∀ {returns liveCtx after outLayout retc fuel sourceCtx targetCtx hiddenReturns
       block lowerBlock source target sourceResult},
      fuel ≤ maxFuel →
      targetCtx.layout.length ≤ liveCtx.protectedDepth →
      Lower.Block.toLocals? returns liveCtx targetCtx.layout
          (Checked.scopedAfter targetCtx.layout after) block =
        some (lowerBlock, outLayout) →
      Source.Block.runOpen prim sourceProgram sourceCtx fuel block source =
        .ok sourceResult →
      SourceDirect.StateRel targetCtx.layout hiddenReturns source target →
      NoInternalCall.Block.Holds block →
      Scope.Block.Scoped sourceCtx.scope block →
      sourceCtx.scope.Nodup →
      SourceDirectBridge.LiveCtxOutcomeCleanupRel retc sourceCtx targetCtx
        sourceResult.1 →
      targetCtx.layout.Nodup →
      returns.length = retc →
      SourceDirect.LeaveFrameAvailable sourceCtx hiddenReturns →
      SourceDirectBridge.LiveControlRel liveCtx sourceCtx →
      SourceDirectBridge.LiveHandlerScopeRel liveCtx sourceCtx →
      liveCtx.returns = returns →
      SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout prim sourceProgram
        targetProgram returns retc fuel sourceCtx targetCtx hiddenReturns block
        lowerBlock source target
```

The one-step theorem already verified is:

```lean
theorem block_succ_of_shape_outcome_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
    ...
    (hCallbacks :
      ScopedNoInternalCallShapeOutcomeCallbackBundle prim sourceProgram
        targetProgram returns liveCtx (Checked.scopedAfter targetCtx.layout after)
        outLayout retc fuel sourceCtx targetCtx hiddenReturns source
        sourceResult) :
    SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout prim sourceProgram
      targetProgram returns retc (fuel + 1) sourceCtx targetCtx hiddenReturns
      block lowerBlock source target
```

The outcome-sensitive bundle has a `tailEntry` callback. It receives the
outer run and exact regular-head equality:

```lean
Source.Block.runOpen prim sourceProgram sourceCtx (fuel + 1)
  { stmts := stmt :: rest } source = .ok sourceResult →
Source.Stmt.run prim sourceProgram sourceCtx fuel stmt source =
  .ok sourceHeadResult →
sourceHeadResult = (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
sourceHeadResult.1.mode = .regular →
targetCtxAfter.layout = nextLayout →
targetCtxAfter = targetCtx.withLayout nextLayout →
sourceCtxAfter.scope = Scope.Stmt.outEnv sourceCtx.scope stmt →
NoInternalCall.Block.Holds { stmts := rest } →
Scope.Block.Scoped sourceCtxAfter.scope { stmts := rest } →
Source.Block.runOpen prim sourceProgram sourceCtxAfter fuel
  { stmts := rest } sourceAfter = .ok sourceTailResult →
SourceDirect.StateRel targetCtxAfter.layout hiddenReturns sourceAfter targetAfter →
SourceDirectBridge.LiveCtxRel retc sourceCtxAfter targetCtxAfter →
...
```

## New obstruction after trying to implement the recommendation

The previous recommendation said to prove:

```lean
SourceDirectBridge.LiveCtxOutcomeCleanupRel retc sourceCtxAfter targetCtxAfter
  sourceTailResult.1
```

and then call `hOpenCallbacks.block` recursively on `{ stmts := rest }`.

I now think that exact lemma is false as stated.

At tail entry, the lowering decomposition is:

```lean
Lower.Stmt.toLocals? returns liveCtx preparedLayout restLive stmt =
  some (lowerStmt, nextLayout)
Lower.StmtList.toLocals? returns liveCtx nextLayout after rest =
  some (lowerRest, outLayout)
```

The recursive tail starts at `targetCtxAfter.layout = nextLayout`. But
`Lower.StmtList.toLocals? returns liveCtx nextLayout after rest` may insert a
`Prepare.forStmtAboveSuffix?`/promotion step before the first statement in
`rest`. So `nextLayout` is a raw tail-entry layout, not necessarily a layout
that already contains all names required to clean up a later break/continue
outcome in `rest`.

This is why the existing tail bridge asks only for:

```lean
SourceDirectBridge.LiveCtxRel retc sourceCtxAfter targetCtxAfter
```

at tail entry. Demanding `LiveCtxOutcomeCleanupRel ... sourceTailResult.1`
there seems to smuggle in the result of the tail's own prepare step.

## Existing useful fact

`Lower.StmtList.toLocals?_cons_components` exposes that the tail lowering itself
starts by computing:

```lean
restLive = StmtList.liveBefore ctx after rest'
stmtLive = Stmt.liveBefore ctx restLive stmt'
liveLayout = Layout.trimDeadPrefix layout stmtLive
Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
  stmtLive stmt' = some (prep, preparedLayout)
Layout.entryWindowOk? preparedLayout stmtLive = true
StmtAccess.accessible? returns preparedLayout stmt' = true
Stmt.toLocals? returns ctx preparedLayout restLive stmt' =
  some (lowerStmt, nextLayout')
StmtList.toLocals? returns ctx nextLayout' after rest' =
  some (lowerRest, outLayout)
```

That suggests the induction invariant may need a separate "raw entry block" or
"stmt-list entry" mode, not only the clean-entry outcome open-block mode.

## Question

What is the simplest sound induction invariant/theorem family here?

Please be concrete and critique these options:

1. Add a second recursive family:
   `RawTailEntryCallbacksUpTo` / `StmtListEntryCallbacksUpTo`, whose block
   theorem assumes only `LiveCtxRel` at the raw `layout` supplied to
   `Lower.StmtList.toLocals?`, plus protected-depth, `Nodup`, source scoping,
   live control/handler facts. Its proof peels the first statement of the list,
   runs cleanup/preparation, and only then uses outcome cleanup for the concrete
   prepared head/body cases. Empty list requires ordinary cleanup from
   `Layout.trimDeadPrefix layout after`.
2. Strengthen `ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame`
   so its `block` theorem accepts raw entry with `LiveCtxRel` plus lowering
   evidence, and internally proves cleanup after the first prepare step. This
   risks making the clean-entry/body helper lemmas messier.
3. Prove tail `LiveCtxOutcomeCleanupRel` at `nextLayout` anyway from
   `Source.Block.runOpen` + handler live-before facts. I suspect this is false
   because preparation/promotion may be necessary before the first tail stmt.
4. Avoid callback bundles and prove the program theorem by direct fuel
   recursion over `Source.Block.runOpen` / statement-list structure. This may
   duplicate existing one-step theorem machinery, but maybe it gives the right
   mutually recursive invariant naturally.

If possible, sketch exact Lean theorem statements for the recommended route,
especially:

- the raw-tail entry theorem;
- how it calls or replaces the existing
  `block_succ_of_shape_outcome_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame`;
- how the empty tail case should derive the final regular-layout relation; and
- what facts about `StmtList.liveBefore`, `Checked.scopedAfter`, and
  `Prepare.forStmtAboveSuffix?` are actually needed.

Constraints:

- No `sorry`, no new axioms, no public proof-carrying callback/certificate input.
- Do not touch `EvmCompiler/Yul/RecursiveBridgeSupport.lean`; CALL work is in
  parallel there.
- Conservative rejection is acceptable; accepted programs must be sound.
