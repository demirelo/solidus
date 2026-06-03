# Oracle request: tail outcome cleanup invariant for live-layout stack guard

We are in `/Users/dan/Projects/evm-compiler`, Lean file:

`EvmCompiler/Functions/LiveLayoutPreservation.lean`

Goal context: conservative stack-too-deep acceptance is wired into the compiler path. The remaining proof-boundary work is to remove the public-ish premise

```lean
ScopedNoInternalCallShapeRecursiveCallbacksUpTo prim sourceProgram targetProgram maxFuel
```

by deriving it internally from source fuel/checker facts. The current candidate route is via the already-defined outcome-sensitive open-block facade:

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

The helper already verified:

```lean
theorem block_succ_of_shape_outcome_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
  ...
  (hCallbacks :
    ScopedNoInternalCallShapeOutcomeCallbackBundle prim sourceProgram targetProgram
      returns liveCtx (Checked.scopedAfter targetCtx.layout after)
      outLayout retc fuel sourceCtx targetCtx hiddenReturns source sourceResult) :
  SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout prim sourceProgram
    targetProgram returns retc (fuel + 1) sourceCtx targetCtx hiddenReturns
    block lowerBlock source target
```

The `ScopedNoInternalCallShapeOutcomeCallbackBundle.tailEntry` was recently strengthened so, at tail-entry sites, it receives:

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

Existing facts available:

```lean
SourceDirect.SourceRun.stmt_regular_scope_nodup
SourceDirect.LeaveFrameAvailable.of_stmt_regular
SourceDirectBridge.LiveControlRel.stmt_regular
SourceDirectBridge.LiveHandlerScopeRel.stmt_regular
HandlerRunLiveBefore.stmtList_breakLive_mem_of_brk_run
HandlerRunLiveBefore.stmtList_continueLive_mem_of_cont_run
```

Problem:

The naive tail proof would call `hOpenCallbacks.block` recursively on the tail block `{ stmts := rest }` at fuel `fuel`, but that facade requires

```lean
SourceDirectBridge.LiveCtxOutcomeCleanupRel retc sourceCtxAfter targetCtxAfter sourceTailResult.1
```

at the tail entry. We only have:

```lean
SourceDirectBridge.LiveCtxRel retc sourceCtxAfter targetCtxAfter
```

from the head statement relation. This is not an accident: `targetCtxAfter.layout = nextLayout`, and `nextLayout` may not already contain all variables live for a later `break`/`continue`; the lowering for the tail can insert promotions before the next statement. So requiring outcome cleanup at tail entry seems too strong.

Question:

What is the right formally verified induction invariant to finish this route without smuggling target-side facts?

Candidate ideas:

1. A tail-specific open-block facade that assumes only `LiveCtxRel` at entry, plus source scoping/Nodup/handler-scope/control/leave-frame, and proves the same target result by doing the first tail-step preparation before requiring outcome cleanup.
2. A mutually recursive facade with separate entry modes:
   - block-at-clean-entry: `LiveCtxOutcomeCleanupRel` available,
   - tail-at-raw-entry: only `LiveCtxRel`, but lowering shape `Lower.StmtList.toLocals? returns liveCtx nextLayout after rest` is available.
3. Prove `LiveCtxOutcomeCleanupRel` at `nextLayout` from the tail source run anyway, using `HandlerRunLiveBefore` plus checker facts; I suspect this is false because promotions may be needed before the next tail statement.

Please critique these and recommend the simplest sound invariant/theorem statement. If possible, sketch the exact Lean theorem family and how the tail field of `ScopedNoInternalCallShapeOutcomeCallbackBundle` should be constructed.

Constraints:

- No `sorry`, new axioms, or proof-carrying public callback/certificate input.
- Do not touch `EvmCompiler/Yul/RecursiveBridgeSupport.lean` (parallel CALL work).
- It is okay if the accepted language remains conservative; accepted programs must be sound.
- We want the public theorem to stop taking the shape-recursive callback family as an input.
