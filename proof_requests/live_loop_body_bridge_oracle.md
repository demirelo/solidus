# Oracle request: live-layout loop body bridge

We are in `/Users/dan/Projects/evm-compiler`, Lean project `evm-compiler`.
Please advise on the smallest principled proof/interface change for the live-layout
compiler preservation proof. No `sorry`, no new axioms.

## Goal

We need to finish the conservative stack-too-deep proof cleanup. The remaining
hard obligation is deriving the recursive `forLoop` callback internally.
The callback ultimately needs this body bridge:

```lean
SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayout prim
  sourceProgram targetProgram returns targetLoopCtx.layout retc fuel
  bodyBase targetBodyBase hiddenReturns body lowerBody
  sourceAfterCond targetAfterCond
```

The ordinary live block bridge is insufficient:

```lean
SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout ...
```

because for non-regular block outcomes its result relation hides the cleanup
layout behind an existential. For loop bodies, `break` and `continue` must be
related specifically at the loop layout.

## Relevant definitions

In `EvmCompiler/Functions/LiveLayoutBridge.lean`:

```lean
def LiveBlockOpenResultRel (retc : Nat) (returns : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match sourceResult.1.mode, targetResult.1.mode with
  | .regular, .regular =>
      SourceDirect.StateRel targetResult.2.layout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | _, _ =>
      ∃ outcomeLayout,
        SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
          sourceResult.1 targetResult.1 ∧
          LiveCtxRel retc sourceResult.2 targetResult.2

def LiveLoopBlockOpenResultRel (retc : Nat) (returns loopLayout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match sourceResult.1.mode, targetResult.1.mode with
  | .regular, .regular =>
      SourceDirect.StateRel targetResult.2.layout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | .brk, .brk
  | .cont, .cont =>
      SourceDirect.StateRel loopLayout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | .leave, .leave
  | .halt _, .halt _ =>
      SourceDirect.StmtOutcomeRel returns loopLayout hiddenReturns
        sourceResult.1 targetResult.1 ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | _, _ => False
```

I added and verified:

```lean
theorem LiveLoopBlockOpenResultRel.of_liveBlockOpenResultRel_of_loop_stateRel
    (hRel : LiveBlockOpenResultRel retc returns hiddenReturns sourceResult targetResult)
    (hBreak :
      sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
      sourceResult targetResult
```

This makes the missing fact explicit but does not prove it.

## Existing precedent

In `EvmCompiler/Functions/SourceDirect.lean`, the direct layer already has:

```lean
def LoopBlockOpenResultRel ...
def LoopBlockOpenRunBridgeWithLayout ...
theorem runOpen_cons_from_source_run_with_loop_layout ...
theorem runScoped_from_loop_open_bridge_with_layout ...
```

That structural proof keeps `break`/`continue` related at `loopLayout`.
The live-layout layer has the loop-specific relation/bridge types and
`blockScoped_from_loop_open_bridge_with_layout`, but does not yet seem to have
the structural preservation theorem that constructs
`LiveLoopBlockOpenRunBridgeWithLayout`.

## Current live structural theorem

In `EvmCompiler/Functions/LiveLayoutPreservation.lean`, the existing theorem:

```lean
block_target_result_of_source_run_lower_with_layout_to_noInternalCall_structural_callbacks_live_control_handlers_tail_entryLayout_protected_scopedAfter_of_leaveFrame
```

constructs:

```lean
∃ targetFuel targetResult,
  Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel lowerBlock target =
    .ok targetResult ∧
  LiveBlockOpenResultRel retc returns hiddenReturns sourceResult targetResult ∧
  LiveBlockOpenRegularLayoutRelTo targetCtx.layout sourceResult targetResult
```

It uses a shape callback bundle including `blockBody`, `ifBody`, `switchBody`,
`forInit`, `forLoop`, and `tailEntry`.

## Question

What is the best minimal proof architecture to finish the loop-body bridge?

Options I see:

1. Duplicate/adapt the live structural block theorem so its result relation is
   `LiveLoopBlockOpenResultRel`, mirroring `SourceDirect.runOpen_cons_from_source_run_with_loop_layout`.
2. Strengthen the existing live structural theorem to optionally return both
   ordinary and loop-specific result relations when the caller supplies a loop
   layout and exact break/continue cleanup facts.
3. Add a separate loop-specific callback field/interface and derive it by the
   same fuel induction, avoiding changes to the ordinary theorem.
4. Some smaller trick I am missing that proves the `hBreak`/`hContinue`
   state relations without replaying the structural proof.

Please recommend the route that is least invasive but semantically honest, and
spell out the theorem statements/callback changes that should be introduced.
If option 4 is impossible, explain exactly why the existential ordinary result
relation cannot be safely strengthened afterward.
