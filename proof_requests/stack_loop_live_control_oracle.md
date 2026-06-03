# Oracle request: loop body live-control invariant for verified live-layout compiler

## Context

Repository: `/Users/dan/Projects/evm-compiler`.

File under work: `EvmCompiler/Functions/LiveLayoutPreservation.lean`.

We are trying to remove the remaining proof-carrying-looking `forLoop` callback from the stack-guard/live-layout proof. The current public goal is to derive all target-side facts from executable lowering/checker evidence.

The relevant callback field currently says, roughly:

```lean
forLoop :
  ... →
  Lower.Block.toLocals? ... init = some (lowerInit, loopLayout) →
  ExprAccess.expr? 0 loopLayout cond = true →
  Lower.Block.toLocals? ... loopLayout ... post = some (lowerPost, postLayout) →
  Lower.Block.toLocals? ... loopLayout ... body = some (lowerBody, bodyLayout) →
  Source.Block.runOpen ... sourceCtx.withoutLoopControl fuel.pred init source =
    .ok (Source.Outcome.regular sourceAfterInit, sourceInitCtx) →
  Locals.Direct.Block.runOpen ... (targetCtx.withLayout preparedLayout).withoutLoopControl
    initTargetFuel lowerInit cleaned =
    .ok (Structured.Outcome.regular targetAfterInit, targetInitCtx) →
  Source.Stmt.runForLoop ... sourceInitCtx cond
    sourceInitCtx.withoutLoopControl post
    (sourceInitCtx.withLoopControl sourceInitCtx.scope sourceInitCtx.scope)
    body fuel.pred sourceAfterInit =
    .ok sourceLoop →
  SourceDirect.StateRel targetInitCtx.layout hiddenReturns sourceAfterInit targetAfterInit →
  SourceDirectBridge.LiveCtxRel retc sourceInitCtx targetInitCtx →
  ∃ loopTargetFuel targetLoop,
    Locals.Direct.Stmt.runForLoop targetProgram targetInitCtx cond
      targetInitCtx.withoutLoopControl lowerPost
      (targetInitCtx.withLoopControl targetInitCtx.layout.length)
      lowerBody loopTargetFuel targetAfterInit =
      .ok targetLoop ∧
    SourceDirect.StmtOutcomeRel returns targetInitCtx.layout hiddenReturns
      sourceLoop targetLoop
```

There is an existing loop bridge:

```lean
theorem runForLoop_from_exact_source_run_live_with_block_bridges
  ...
  (hCtx : LiveCtxRel retc loopCtx targetLoopCtx)
  (hPostCtx : LiveCtxRel retc postBase targetPostBase)
  (hBodyCtx : LiveCtxRel retc bodyBase targetBodyBase)
  (hTargetPostLayout : targetPostBase.layout = targetLoopCtx.layout)
  (hTargetBodyLayout : targetBodyBase.layout = targetLoopCtx.layout)
  (hPostBreakNone : postBase.breakScope? = none)
  (hPostContinueNone : postBase.continueScope? = none)
  (hNoDup : targetLoopCtx.layout.Nodup)
  (hOwned : Locals.Source.Expr.SourceOwned cond)
  (hAccess : Locals.SourceLowering.Expr.Accessible targetLoopCtx.layout 0 cond)
  (hRel : SourceDirect.StateRel targetLoopCtx.layout hiddenReturns source target)
  (hSourceRun : Source.Stmt.runForLoop ... (fuel + 1) source = .ok sourceLoop)
  (hBody : ∀ ..., Source.Block.runScoped ... body fuel ... = .ok sourceBody →
     StateRel targetLoopCtx.layout ... →
     LiveLoopBlockOpenRunBridgeWithLayout ... body lowerBody ...)
  (hPost : ∀ ..., Source.Block.runScoped ... post fuel ... = .ok sourcePost →
     StateRel targetPostBase.layout ... →
     LiveBlockOpenRunBridgeWithLayout ... post lowerPost ...)
  (hLoop : recursive call on lower fuel)
  : ∃ targetFuel targetLoop, ...
```

We can derive these facts locally:

* `targetInitCtx.layout = loopLayout` from `TargetLayout.Lower.block_runOpen_regular_layout_of_lower hLowerInit ... hTargetInit`.
* `loopLayout.Nodup` from `Lower.Block.toLocals?_checked hLowerInit` and `Checked.Block.check?_nodup`.
* condition accessibility from `ExprAccess.expr?_sound hCond`, rewritten by `targetInitCtx.layout = loopLayout`.
* post/base context facts from `LiveCtxRel.withoutLoopControl hInitCtx`.
* body/base context facts from `LiveCtxRel.withLoopControl_self hInitCtx`.

## Bottleneck

The recursive proof for the loop body wants to use the shape open-block callback family:

```lean
ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.block
```

That callback requires:

```lean
LiveCtxOutcomeCleanupRel retc sourceCtx targetCtx sourceResult.1
targetCtx.layout.Nodup
LiveControlRel liveCtx sourceCtx
LiveHandlerScopeRel liveCtx sourceCtx
```

For a loop body, the source context is:

```lean
sourceInitCtx.withLoopControl sourceInitCtx.scope sourceInitCtx.scope
```

but the live-layout compiler lowers the body using:

```lean
let postAfter := Checked.scopedAfter loopLayout loopMentioned
let bodyAfter := Checked.scopedAfter loopLayout postLive
let bodyLoopCtx :=
  liveCtx.withLoop (Checked.scopedAfter loopLayout restLive) bodyAfter
let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
Lower.Block.toLocals? returns bodyCheckCtx loopLayout bodyAfter body = ...
```

`Checked.scopedAfter loopLayout restLive = NameSet.union restLive loopLayout`.

So the live handler set contains the live target loop layout plus outer live names, but it generally does **not** have the same membership as the full post-init source scope. Dead init locals, and dead outer locals, can be in `sourceInitCtx.scope` but absent from `loopLayout` and from `restLive`/`postLive`.

This makes the existing `LiveControlRel` too strong for loop bodies:

```lean
def LiveControlRel (live : Ctx) (source : Source.Ctx) : Prop :=
  (∀ scope, source.breakScope? = some scope →
    SourceDirect.SameScope live.breakLive scope) ∧
  (∀ scope, source.continueScope? = some scope →
    SourceDirect.SameScope live.continueLive scope) ∧
  ...
```

For loop bodies, what we actually need semantically is not same-scope equality with every source local. We need break/continue outcomes to preserve `SourceDirect.StateRel loopLayout ...`, i.e. the target loop layout, ignoring dead source locals.

There is already:

```lean
LiveLoopBlockOpenRunBridgeWithLayout
```

which upgrades an ordinary open-block bridge using explicit `hBreakLoopState` and `hContinueLoopState` facts:

```lean
LiveLoopBlockOpenRunBridgeWithLayout.of_open_with_layout_of_loop_stateRel
```

But building the ordinary bridge itself still wants `LiveControlRel`.

## Question

What is the best principled verified-compiler strategy here?

Options I see:

1. Introduce a loop-specific relaxed live-control invariant, something like
   `LiveLoopControlRel live source loopLayout`, requiring enough membership and cleanup facts to prove `StateRel loopLayout` for break/continue, rather than `SameScope live.breakLive source.scope`. Then add a loop-body open-block theorem/callback family using that invariant.

2. Make the compiler more conservative for loops so `loopLayout`/body live handler sets include the full source handler scopes. This may be simpler but could undo liveness benefits and increase stack pressure.

3. Thread a target-output-layout fact through init bridges and try to keep using the existing open-block callbacks. This seems insufficient because the body `LiveControlRel` still fails.

Please critique these options, identify any false premise, and suggest the smallest sound Lean proof architecture that removes the `forLoop` callback premise without changing the source semantics. I prefer a compositional invariant over ad hoc per-loop cases, but it must be realistic to implement in this codebase.

Useful failure would be: "this cannot be done with the current callback theorem without duplicating/opening it", or a concrete theorem statement for the relaxed loop-body bridge.
