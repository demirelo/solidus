# Oracle Request: Shape Callback Induction Boundary

We are in `/Users/dan/Projects/evm-compiler`, Lean project `EvmCompiler`.
Please advise on the right induction invariant/proof architecture for removing
a public compiler-shaped callback-family premise from the stack-guard theorem.

## Goal

The public-ish theorem

```lean
EvmCompiler.Functions.LiveLayout.SourceTarget.Program.runState_toLocalsNoInternalCall_exists_of_shapeRecursiveCallbacksUpTo
```

currently takes

```lean
hCallbacks :
  ScopedNoInternalCallShapeRecursiveCallbacksUpTo prim sourceProgram
    targetProgram maxFuel
```

and the wrapper takes `∀ maxFuel, ...`. This is not intended to be a public
assumption. It should be derived internally by induction on source fuel from
the executable lowering/checker facts, `NoInternalCall`, scoping, and stack
layout invariants.

The current bottleneck is designing/proving the successor/all-fuels constructor
for the *shape* callback families without accidentally requiring full cleanup
facts for break/continue outcomes.

## Relevant declarations

File: `EvmCompiler/Functions/LiveLayoutPreservation.lean`.

### Shape recursive callback family

```lean
def ScopedNoInternalCallShapeRecursiveCallbackBundle
    (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns : List Name) (liveCtx : Ctx) (after outLayout : List Name)
    (retc fuel : Nat) (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (hiddenReturns : List Structured.ReturnDest)
    (source : Source.State) : Prop :=
  SourceDirectBridge.LiveCtxCleanupRel retc sourceCtx targetCtx →
    ScopedNoInternalCallShapeCallbackBundle prim sourceProgram targetProgram
      returns liveCtx after outLayout retc fuel sourceCtx targetCtx
      hiddenReturns source

def ScopedNoInternalCallShapeRecursiveCallbacksUpTo
    (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (maxFuel : Nat) : Prop :=
  ∀ {returns : List Name} {liveCtx : Ctx} {after outLayout : List Name}
    {retc fuel : Nat} {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State},
    fuel ≤ maxFuel →
      targetCtx.layout.length ≤ liveCtx.protectedDepth →
      sourceCtx.scope.Nodup →
      targetCtx.layout.Nodup →
      returns.length = retc →
      SourceDirect.LeaveFrameAvailable sourceCtx hiddenReturns →
      SourceDirectBridge.LiveControlRel liveCtx sourceCtx →
      SourceDirectBridge.LiveHandlerScopeRel liveCtx sourceCtx →
      liveCtx.returns = returns →
      ScopedNoInternalCallShapeRecursiveCallbackBundle prim sourceProgram
        targetProgram returns liveCtx after outLayout retc fuel sourceCtx
        targetCtx hiddenReturns source
```

We have `zero`, `mono`, and this block bridge:

```lean
theorem ScopedNoInternalCallShapeRecursiveCallbacksUpTo.block_succ_of_cleanup_of_leaveFrame
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    (hCallbacks :
      ScopedNoInternalCallShapeRecursiveCallbacksUpTo prim sourceProgram
        targetProgram maxFuel)
    ...
    (hFuelLe : fuel ≤ maxFuel)
    ...
    (hCtxCleanup :
      SourceDirectBridge.LiveCtxCleanupRel retc sourceCtx targetCtx)
    ...
    SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout prim sourceProgram
      targetProgram returns retc (fuel + 1) sourceCtx targetCtx hiddenReturns
      block lowerBlock source target
```

That theorem only handles one block at successor fuel if a smaller callback
family is supplied; it does not construct the callback family.

### Outcome-sensitive open-block callback family

This was introduced to avoid requiring full cleanup for break/continue:

```lean
structure ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame
    (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (maxFuel : Nat) : Prop where
  block :
    ∀ ...,
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

It has `zero`, `mono`, and many helper theorems in the namespace:

```lean
block_trimDeadPrefix_of_mode_live_subset
blockBody_of_open_block_of_mode_live_subset
loopBlockBody_of_open_block_of_mode_live_subset
blockBody_of_open_block_of_outer_mode_live_subset
blockBody_of_open_block_of_body_mode_live_subset
blockBody_of_open_block_of_body_mode_live_subset_of_run
blockBody_of_open_block_of_outer_outcome_cleanup
blockBody_of_open_block_of_outer_outcome_cleanup_of_run
ifBody_of_open_block_of_body_mode_live_subset
ifBody_of_open_block_of_body_mode_live_subset_of_run
ifBody_of_open_block_of_outer_outcome_cleanup_of_run
switchBody_of_open_block_of_selected_body_mode_live_subset
switchBody_of_open_block_of_selected_body_mode_live_subset_of_run
switchBody_of_open_block_of_outer_outcome_cleanup_of_run
forInit_of_open_block
```

The body helper signatures all consume this same open-block outcome callback
family at `maxFuel`.

### One-step outcome bundle bridge

The structural theorem can prove a block at `fuel + 1` from a concrete
outcome callback bundle:

```lean
theorem block_succ_of_shape_outcome_callback_bundle_tail_entryLayout_protected_scopedAfter_of_leaveFrame
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
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

The bundle has body callbacks, `outcomeCleanup`, and `tailEntry`.

## Recent verified helper

File: `EvmCompiler/Functions/LiveLayout.lean`.

We added:

```lean
Checked.Block.check?_layoutRel
Checked.Stmt.check?_layoutRel
Checked.StmtList.check?_layoutRel
Checked.Block.check?_nodup
Checked.Stmt.check?_nodup
Checked.StmtList.check?_nodup
```

These derive checked output layout membership and `Nodup` from source scoping,
input target-layout subset, and input target-layout `Nodup`. This should help
for the loop-init `loopLayout.Nodup` obligation.

## Bottleneck / question

What is the clean induction structure?

Candidate A:
1. Prove
   `ScopedNoInternalCallShapeRecursiveOpenBlockOutcomeCallbacksUpToOfLeaveFrame.succ`
   from the same family at `maxFuel`.
2. Build `∀ n, OpenBlockOutcomeCallbacksUpTo n` by induction from `zero`.
3. Use that to build `ScopedNoInternalCallShapeRecursiveCallbacksUpTo n`
   and remove the public callback premise.

But when constructing the concrete
`ScopedNoInternalCallShapeOutcomeCallbackBundle` for the successor step,
`tailEntry` seems to require proving the rest block at fuel `fuelPred` after a
regular head. It gets only `LiveCtxRel retc sourceCtxAfter targetCtxAfter`, not
a full cleanup relation. To call the outcome open-block family on the rest, we
need `LiveCtxOutcomeCleanupRel ... sourceTailResult.1`. Is that derivable from
existing premises (`LiveControlRel`, `LiveHandlerScopeRel`, regular head facts,
source scoping/run facts), or should the callback/bundle type be strengthened?

Candidate B:
Use mutual induction between:
- shape recursive callback bundles/up-to, and
- shape open-block outcome callbacks/up-to.

Candidate C:
Avoid callback-family construction and prove the program theorem by direct
source-fuel induction over `Source.Block.runOpen` / `runScoped`, using the
existing one-step block bridge only as a local lemma.

Please advise which route is principled and likely simplest in Lean. If
Candidate A is right, please specify the exact missing lemma for `tailEntry`
and the shape of its statement. If Candidate B/C is better, please describe the
minimal invariant and theorem statements to add.

Constraints:
- No `sorry`, no new axioms.
- Do not touch `EvmCompiler/Yul/RecursiveBridgeSupport.lean`; another agent is
  working on CALL there.
- We want accepted programs to fail compilation conservatively rather than
  making target-side assumptions.
