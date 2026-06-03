# CALL Loop-Continuation Frontier Consult

Repo: `/Users/dan/Projects/evm-compiler`

File of interest: `/Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean`

Requested mode: critique and repair the theorem architecture. If the proposed theorem is too strong, too weak, or has the wrong induction measure, say so concretely. If it is basically right, give the proof route and name the helper lemmas to add first.

## Project Goal

We are proving a formally verified Yul-to-EVM-ish compiler path. For Yul `CALL`, the current architecture avoids a concrete external world model. Instead, executions produce selected finite open traces of external calls; the theorem proves the Yul source and compiler target issue the same calls and then universally quantifies over shared admissible responses.

The current bottleneck is generated `for` loops with CALLs. Ordinary source sequence recursion and typed-continuation recursion cover the loop body and post block, but the generated target loop recurses through

```lean
CompilerOpen.FunctionsOpen.Stmt.runForLoop
```

directly after a regular post. So we added a third frontier member for the direct generated loop continuation.

## Key Existing Definitions

The direct loop-continuation contract is:

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
            (ctx.withoutLoopControl) (.lit (EvmYul.UInt256.ofNat 1))
            (ctx.withoutLoopControl) lowerPost
            (ctx.withoutLoopControl.withLoopControl ctx.scope ctx.scope)
            generatedBody targetFuel compiler)
```

The exact-fuel loop frontier is:

```lean
def CALLOpenLoopContinuationPathLoweringFrontierAt
    (cfg : StateRelConfig)
    (terminalRel :
      Assembly.HaltKind -> Word -> State -> Objects.Source.State -> Prop)
    (revertRel : State -> Objects.Source.State -> Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (yulProgram : Program) (program : Functions.Program)
    (bound : Nat) : Prop :=
  forall {headCompileFuel : Nat}
    {reserved layout outcomeLayout : List Name}
    {ctx : Functions.Source.Ctx}
    {allowed : Except Exception State -> Prop}
    {canBreak canContinue canLeave : Bool}
    {cond : AstExpr} {post body : List AstStmt}
    {freshState freshStateAfterCond freshStateAfterPost freshState' :
      Fresh.State}
    {preCond : List Functions.Stmt}
    {lowerCond : Functions.Expr 1}
    {lowerPost lowerBody : Functions.Block},
    Safe.CallSafe.stmt (.For cond post body) ->
    ControlFlow.ScopedStmt canBreak canContinue canLeave
      (.For cond post body) ->
    UserCallArity.StmtOk yulProgram.contract (.For cond post body) ->
    SourceLexical.StmtScoped layout (.For cond post body) ->
    SourceNamesReserved reserved (Stmt.names (.For cond post body)) ->
    FreshCoversLayout (reserved ++ layout) freshState ->
    Expr.lower1? freshState cond =
      some (preCond, lowerCond, freshStateAfterCond) ->
    Stmt.List.toBlockFuel? headCompileFuel freshStateAfterCond post =
      some (lowerPost, freshStateAfterPost) ->
    Stmt.List.toBlockFuel? headCompileFuel freshStateAfterPost body =
      some (lowerBody, freshState') ->
    (forall {sourceResult}, allowed sourceResult ->
      SourceResultRelatable sourceResult) ->
    (forall {sourceResult}, allowed sourceResult ->
      SourceResultOutcomeLayoutSupported ctx layout outcomeLayout
        sourceResult) ->
    (forall name : Name, name in layout -> name in ctx.scope) ->
    SourceOpenLoopContinuationPathSoundWhenAtExactHiddenCtx cfg layout
      outcomeLayout terminalRel revertRel prim program ctx bound cond post body
      (some yulProgram.contract) lowerPost
      { stmts :=
          preCond ++
            [Functions.Stmt.if_
              (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
              { stmts := [Functions.Stmt.brk] }] ++
            lowerBody.stmts }
      allowed
```

Low-fuel is already proved:

```lean
theorem callOpenLoopContinuationPathLoweringFrontierAt_low_fuel
    {cfg : StateRelConfig}
    {terminalRel :
      Assembly.HaltKind -> Word -> State -> Objects.Source.State -> Prop}
    {revertRel : State -> Objects.Source.State -> Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {yulProgram : Program} {program : Functions.Program}
    {bound : Nat}
    (hBound : bound <= 2) :
    CALLOpenLoopContinuationPathLoweringFrontierAt cfg terminalRel revertRel
      prim yulProgram program bound
```

The Yul normalizer says:

```lean
theorem yulOpen_toOpenResult_exec_for_succ_succ_succ_eq_runLoopSource
    (fuel : Nat) (cond : AstExpr) (post body : List AstStmt)
    (codeOverride : Option AstContract) (state : State) :
    OpenExternal.YulOpenResult.toOpenResult
        (OpenExternal.YulOpen.exec fuel.succ.succ.succ
          (.For cond post body) codeOverride state) =
      runLoopSource fuel cond post body codeOverride state
```

Inside `runLoopSource fuel`, the post-regular recursive path uses:

```lean
OpenExternal.YulOpen.exec fuel (.For cond post body) codeOverride stateAfterPost
```

So the recursive `.For` call is smaller by 3 at the outer theorem boundary, but appears at the same `fuel` parameter once we are inside `runLoopSource`.

Existing branch helpers include:

```lean
theorem runLoopSourceAfterPost_regular_resolves_inv_loop_ok_source :
  ... ->
    exists loopDone,
      OpenExternal.OpenResultResolves
        (OpenExternal.YulOpenResult.toOpenResult
          (OpenExternal.YulOpen.exec fuel (.For cond post body) codeOverride
            (.Ok sharedPost storePost)))
        trace loopDone /\
      sourceDone = loopDone

theorem runLoopSource_resolves_body_regular_post_regular_loop_of_evalValues_nonzero :
  ... ->
  OpenExternal.OpenResultResolves
    (runLoopSource fuel cond post body codeOverride (.Ok shared store))
    (((trace ++ bodyTrace) ++ postTrace) ++ loopTrace)
    loopDone

theorem compilerOpen_generated_runForLoop_resolves_body_regular_or_continue_post_regular_loop :
  ... ->
  OpenExternal.OpenResultResolves
    (CompilerOpen.FunctionsOpen.Stmt.runForLoop prim program
      (ctx.withoutLoopControl) (.lit (EvmYul.UInt256.ofNat 1))
      (ctx.withoutLoopControl) lowerPost
      (ctx.withoutLoopControl.withLoopControl ctx.scope ctx.scope)
      generatedBody
      (Nat.max bodyFuel (Nat.max postFuel loopFuel)).succ compiler)
    (bodyTrace ++ (postTrace ++ loopTrace)) (.ok loopOutcome)
```

There are also statement-level loop splitters for the outer statement shell, e.g.

```lean
sourceOpenLoopHeadStmtPathSound_generated_nonzero_body_regular_post_split_of_callbacks
sourceOpenLoopHeadPathSound_generated_condition_body_post_block_of_loop_callback
```

Those target outer `Stmt.run` wrappers. The direct loop-continuation theorem must target `Stmt.runForLoop` itself.

## Candidate Theorem We Think We Need

I think the missing theorem should be a productive exact-fuel frontier step, proved by strong induction on outer source fuel, not by a concrete world model and not by a public all-callees oracle:

```lean
theorem callOpenLoopContinuationPathLoweringFrontierAt_productive_of_smaller_frontiers
    {cfg : StateRelConfig}
    {terminalRel :
      Assembly.HaltKind -> Word -> State -> Objects.Source.State -> Prop}
    {revertRel : State -> Objects.Source.State -> Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {yulProgram : Program} {program : Functions.Program}
    {bound : Nat}
    (context : ProgramCALLBridgeContext yulProgram program)
    (hBodyFuelAdequate :
      SourceOpenInternalUserCallBodyFuelAdequateUpTo cfg yulProgram.contract
        bound)
    (hSeqFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec < bound ->
          CALLOpenSeqPathLoweringFrontierAt cfg terminalRel revertRel prim
            yulProgram program sourceFuelRec)
    (hKontFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec < bound ->
          CALLOpenSeqKontPathLoweringFrontierAt cfg terminalRel revertRel prim
            yulProgram program sourceFuelRec)
    (hLoopFrontier :
      forall {sourceFuelRec : Nat},
        sourceFuelRec < bound ->
          CALLOpenLoopContinuationPathLoweringFrontierAt cfg terminalRel
            revertRel prim yulProgram program sourceFuelRec)
    (hPrim :
      forall {layout : List Name} {fuel : Nat}
        {yulPrim : EvmYul.Operation .Yul} {op : Structured.BasicOp},
        Safe.primitive yulPrim ->
        Prim.toBasicOp? yulPrim = some op ->
          PrimitiveStackSoundAtArity cfg layout prim fuel yulPrim op) :
    CALLOpenLoopContinuationPathLoweringFrontierAt cfg terminalRel revertRel
      prim yulProgram program bound
```

This may need an explicit `3 <= bound` hypothesis and may split into low/productive theorems instead:

```lean
theorem callOpenLoopContinuationPathLoweringFrontierAt_succ_succ_succ
    ... (fuel : Nat)
    (hSeqFrontier : forall {n}, n <= fuel -> CALLOpenSeqPathLoweringFrontierAt ... n)
    (hKontFrontier : forall {n}, n <= fuel -> CALLOpenSeqKontPathLoweringFrontierAt ... n)
    (hLoopFrontier : forall {n}, n <= fuel -> CALLOpenLoopContinuationPathLoweringFrontierAt ... n) :
    CALLOpenLoopContinuationPathLoweringFrontierAt ... fuel.succ.succ.succ
```

The final public proof would then be a strong induction producing all three frontiers:

1. `CALLOpenSeqPathLoweringFrontierAt ... fuel`
2. `CALLOpenSeqKontPathLoweringFrontierAt ... fuel`
3. `CALLOpenLoopContinuationPathLoweringFrontierAt ... fuel`

and the generated `For` dispatcher consumes the third member locally.

## Questions

1. Is this the right architecture, or should the direct loop-continuation theorem instead be proved by induction on `OpenResultResolves`/the selected trace?
2. Are the smaller-frontier hypotheses above sufficient, or do we need a different mutual induction package because condition expressions/user calls need `ProgramCALLBridgeContext` and body-fuel adequacy?
3. Can the existing outer loop-head splitters be reused safely to prove the direct `runForLoop` continuation theorem, or should we add sibling direct splitters targeting `Stmt.runForLoop`?
4. What is the minimal productive theorem statement that will not become a compatibility scaffold?
5. Please identify the exact branch decomposition for `runLoopSource fuel`: condition error/zero/nonzero, body break/leave/error/regular/continue, post error/leave/regular, and how the post-regular recursive loop should consume `hLoopFrontier`.

Constraints:

- No `sorry`, `admit`, or new axioms.
- Do not weaken theorem statements.
- Do not add a concrete external-world model.
- Do not expose `hLoopRec`, `hOther`, replay certificates, or all-callees assumptions at the public proof boundary.
- Prefer deleting temporary direct-let/assign CALL scaffolding eventually; final route should be expression/sequence recursive.
- Validation command for any patch: `lake env lean EvmCompiler/Yul/RecursiveBridgeSupport.lean`.
