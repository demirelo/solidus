# Aristotle Request: Public Open-CALL Compiler Theorem

We are in the Lean project:

`/Users/dan/Projects/evm-compiler`

Task: review and, if feasible, help implement the high-level CALL-capable
compiler theorem route. The full public theorem is probably too large for one
shot, so the most useful output is either:

1. a patch proving the next concrete theorem(s) in the current route; or
2. a precise decomposition showing which Lean theorem should be proved first,
   why it is non-circular, and how it composes into the public theorem.

Do not weaken theorem statements. Do not introduce `sorry`, `admit`, `axiom`,
or nonstandard proof holes.

## Desired Public Theorem

The current public theorem is no-CALL:

File: `EvmCompiler/Yul/NoCallRuntime.lean`

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

The intended CALL-capable public theorem should instead be open/path based:
for every finite selected external response trace of imported-Yul execution,
the compiled target execution follows the same trace, exposes the same external
call request at each step, consumes the same arbitrary response, and ends in a
related result. There should be no concrete callee/world/precompile/child-code
model. Reentrant effects are represented by an arbitrary response-side internal
mutation that is accepted only when it preserves the relevant source/target
state relation.

## Existing Open External Model

File: `EvmCompiler/Yul/OpenExternal.lean`

Important declarations:

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

inductive OpenResultPathRel
    {eps1 : Type u} {eps2 : Type v} {alpha : Type w} {beta : Type}
    (callResponseRel :
      OpenCall (OpenResult eps1 alpha) ->
        OpenCall (OpenResult eps2 beta) -> CallResponse -> Prop)
    (doneRel : Except eps1 alpha -> Except eps2 beta -> Prop) :
    OpenTrace -> OpenResult eps1 alpha -> OpenResult eps2 beta -> Prop
```

The `call` constructor of `OpenResultPathRel` requires `sourceCall.site =
targetCall.site`, so request equality is direct. The response is universally
chosen by the path. `callResponseRel` is the only restriction on arbitrary
response/internal mutation.

## Current Internal CALL Frontier Layer

File: `EvmCompiler/Yul/RecursiveBridgeSupport.lean`

The intended proof architecture is a mutual source-fuel induction with exactly
three internal frontier members:

```lean
def CALLOpenSeqPathLoweringFrontierAt ...
def CALLOpenSeqKontPathLoweringFrontierAt ...
def CALLOpenLoopContinuationPathLoweringFrontierAt ...

def CALLOpenSeqPathRecursiveAt ...
def CALLOpenSeqKontPathRecursiveAt ...
def CALLOpenLoopContinuationPathRecursiveAt ...

theorem CALLOpenSeqPathRecursiveAt.of_frontiers_le ...
theorem CALLOpenSeqKontPathRecursiveAt.of_frontiers_le ...
theorem CALLOpenLoopContinuationPathRecursiveAt.of_frontiers_le ...
```

The one-head CALL frontier from exact frontiers is already present:

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
```

There is still a residual `hOther` fallback in this one-head theorem and in an
older private structural dispatcher. The goal is to remove it after proving
the productive loop-continuation frontier and applying the exhaustive
CALL-capable frontier to sequence induction.

## Concrete Local Target To Prefer

The most important next theorem is the productive exact-fuel loop-continuation
frontier.

Low fuel exists:

```lean
theorem callOpenLoopContinuationPathLoweringFrontierAt_low_fuel
    {cfg : StateRelConfig}
    ...
    {bound : Nat}
    (hBound : bound <= 2) :
    CALLOpenLoopContinuationPathLoweringFrontierAt cfg terminalRel revertRel
      prim yulProgram program bound
```

The direct target contract is:

```lean
def SourceOpenLoopContinuationPathSoundWhenAtExactHiddenCtx
    (cfg : StateRelConfig) (layout outcomeLayout : List Name)
    (terminalRel :
      Assembly.HaltKind -> Word -> State -> Objects.Source.State -> Prop)
    (revertRel : State -> Objects.Source.State -> Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (sourceFuel : Nat) (cond : AstExpr) (post body : List AstStmt)
    (codeOverride : Option AstContract)
    (lowerPost generatedBody : Functions.Block)
    (allowed : Except Exception State -> Prop) : Prop
```

We have Lean-checked branch helper theorems covering these direct
`runForLoop` cases:

- condition stopped;
- condition zero;
- nonzero/body break;
- nonzero/body stopping;
- nonzero/body regular/post stopping;
- nonzero/body continue/post stopping;
- nonzero/body regular/post regular/recurse;
- nonzero/body continue/post regular/recurse.

The expected next theorem shape is a direct orchestration theorem, a sibling of
the existing outer loop-head splitters, but targeting
`SourceOpenLoopContinuationPathSoundWhenAtExactHiddenCtx` and
`CompilerOpen.FunctionsOpen.Stmt.runForLoop` directly rather than routing
through the outer `Stmt.run` shell.

Likely target name:

```lean
sourceOpenLoopContinuationPathSound_generated_condition_body_post_block_of_callbacks
```

or similar. It should consume condition/body/post recursion callbacks and the
direct recursive `CALLOpenLoopContinuationPathRecursiveAt` callback, do the
same source inversion branch split as the outer loop-head helper, and apply the
eight direct branch helpers above.

After that, prove something like:

```lean
theorem callOpenLoopContinuationPathLoweringFrontierAt_succ_succ_succ_of_smaller
    ...
    (hSeqFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec <= fuel.succ.succ ->
          CALLOpenSeqPathLoweringFrontierAt cfg ... sourceFuelRec)
    (hKontFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec <= fuel.succ.succ ->
          CALLOpenSeqKontPathLoweringFrontierAt cfg ... sourceFuelRec)
    (hLoopFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec <= fuel.succ.succ ->
          CALLOpenLoopContinuationPathLoweringFrontierAt cfg ... sourceFuelRec)
    : CALLOpenLoopContinuationPathLoweringFrontierAt cfg ... fuel.succ.succ.succ
```

Please adjust the exact fuel indices if the existing `YulOpen.exec (.For ...)`
normalization requires a different offset. Existing normalization:

```lean
theorem yulOpen_toOpenResult_exec_for_succ_succ_succ_eq_runLoopSource
```

## Existing Templates To Inspect

Outer loop-head splitters to mirror:

- `sourceOpenLoopHeadStmtPathSound_generated_condition_split_of_cond_open`
- `sourceOpenLoopHeadStmtPathSound_generated_nonzero_body_split_of_callbacks`
- `sourceOpenLoopHeadStmtPathSound_generated_nonzero_body_regular_post_split_of_callbacks`
- `sourceOpenLoopHeadStmtPathSound_generated_nonzero_body_continue_post_split_of_callbacks`
- `sourceOpenLoopHeadStmtPathSound_generated_nonzero_body_post_split_of_callbacks`
- `sourceOpenLoopHeadStmtPathSound_generated_condition_body_post_split_of_callbacks`
- `sourceOpenLoopHeadPathSound_generated_condition_body_post_block_of_callbacks`
- `sourceOpenLoopHeadPathSound_generated_condition_body_post_block_of_checked_facts`
- `sourceOpenLoopHeadPathSound_generated_condition_body_post_block_of_loop_callback`

Direct branch helpers to search:

- `sourceOpenLoopContinuationPathRel_generated_zero_of_raw_condition_values`
- `sourceOpenLoopContinuationPathRel_generated_condition_stopped_of_raw_condition`
- `sourceOpenLoopContinuationPathRel_generated_nonzero_body_break_of_raw_condition_values`
- `sourceOpenLoopContinuationPathRel_generated_nonzero_body_stopping_of_raw_condition_values`
- `sourceOpenLoopContinuationPathRel_generated_nonzero_body_regular_post_stopping`
- `sourceOpenLoopContinuationPathRel_generated_nonzero_body_continue_post_stopping`
- `sourceOpenLoopContinuationPathRel_generated_nonzero_body_regular_post_regular_loop`
- `sourceOpenLoopContinuationPathRel_generated_nonzero_body_regular_post_regular_loop_of_continuation`
- `sourceOpenLoopContinuationPathRel_generated_nonzero_body_continue_post_regular_loop`
- `sourceOpenLoopContinuationPathRel_generated_nonzero_body_continue_post_regular_loop_of_continuation`

## Constraints

- Preserve theorem statements unless you explain that a statement is false.
- Do not add compatibility wrappers or direct let/assign CALL scaffolding.
- Do not reintroduce a concrete external-world model.
- Nested CALLs should be handled at expression/recursive sequence level.
- No `sorry`, `admit`, `axiom`, generated fake axioms, or weakening.
- Prefer small helper lemmas if necessary.

Validation command:

```bash
lake env lean EvmCompiler/Yul/RecursiveBridgeSupport.lean
```

If you return a patch, it must pass the validation command locally. If you do
not return a patch, please return the exact theorem sequence and the first Lean
target you would attempt.
