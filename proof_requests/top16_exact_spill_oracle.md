# Oracle request: top-16 exact spill boundary

We are working in `/Users/dan/Projects/evm-compiler`, a Lean 4 formally
verified compiler from a Yul-like source down to EVM semantics.

## Problem

The compiler currently handles EVM `DUP1..DUP16`/`SWAP1..SWAP16` limits by:

- dead-prefix cleanup at live-layout boundaries;
- stack-only promotion for locals reachable by the SWAP window;
- rejecting genuinely-live locals deeper than the window.

The public theorem intentionally preserves exact shared EVM/Yul state, including
machine memory and `activeWords`, except for already-modeled gas erasure. Source
Yul can use memory operations such as `MLOAD`, `MSTORE`, and `MSIZE`, so memory
is source-observable.

We want to avoid "stack too deep" at arbitrary scale, but not by hiding an
invalid state change.

## Relevant checked facts already in the repo

`EvmCompiler/Locals/Compiler.lean`

- `Locals.Ctx.promoteNameStackOnly?`:
  - computes stack-only promotion;
  - uses `Ctx.swapRestoreUpTo?`;
  - succeeds only when the selected local index is in the SWAP window.

`EvmCompiler/Functions/LiveLayout.lean`

- `LiveLayout.Layout.promoteNameUnbounded?` computes the pure layout move
  without the SWAP-window check.
- The lowerer/checker still uses stack-only promotion and rejects the unbounded
  case when not stack-reachable.

`EvmCompiler/Locals/SourceLowering.lean`, namespace
`StateRel.SpillScratch`

Already checked:

- `ScratchWordReserved`, `ScratchWordWithinActiveNat`,
  `ScratchWordAllocated`, `ScratchWordReadable`;
- `ScratchWordMemoryRestoreObligation`;
- `ScratchWordOverwriteRestoreObligation`;
- `mload_machine_eq`: reserved `MLOAD` does not change `MachineState`;
- `mstore_restore_loaded_machine_eq`: if the original word is loaded and then
  restored, `(machine.mstore offset value).mstore offset (machine.mload offset).1 = machine`;
- `ScratchRegionReady` and executable `scratchRegionReady?`:
  bundles allocated region, within-active region, and no active-word overflow;
  exposes slot-level reservation/readability/restore projections.

## Tension

A naive memory-backed `DUPN` macro like "save top values to scratch until the
deep local becomes reachable, promote it, reload saved values" seems to leave
scratch memory changed unless it restores original scratch bytes. But restoring
original scratch bytes seems to require remembering those original bytes
somewhere. If they are stored on the stack, they may block the depth reduction;
if they are stored in more scratch memory, the problem recurs.

If instead we require compiler-private scratch that source cannot observe, the
current exact `toSharedState` theorem must change to an observational relation
or a source-facing memory-separation assumption.

## Request

Please critique the architecture and give a principled route:

1. Is there a pure EVM stack/memory macro that can promote an arbitrary deep
   stack item while preserving all stack values and restoring arbitrary initial
   memory/activeWords exactly, under only a finite preallocated scratch-region
   readiness premise?
2. If yes, sketch the macro and the key invariant/proof shape in a way that can
   be formalized compositionally in Lean.
3. If no, give the cleanest impossibility argument/invariant and the best
   formally verified compiler architecture instead.
4. Specifically, should we:
   - introduce compiler-private scratch into the source/target state relation,
   - require a source-facing memory-separation/zero-scratch precondition,
   - restrict accepted Yul memory operations,
   - or prefer another stack-layout/register-allocation strategy?

Constraints:

- No `sorry`, no axioms, no hidden compiler-generated evidence in public
  theorem statements.
- Public accepted-program theorem currently aims at any starting state; if that
  goal is incompatible with arbitrary-scale locals plus observable memory, say
  so explicitly.
- CALL/external-world work is parallel and out of scope except that future CALL
  support must not invalidate the stack/scratch story.
