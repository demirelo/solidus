We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: prove or reduce the generated-For CALL loop-continuation frontier theorem below. If the full theorem is too large for one patch, return the smallest useful helper theorem(s) and explain exactly how they compose. Do not weaken any existing theorem statements.

File: /Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

Current architecture:

- Source and target are open semantics with finite selected traces of external calls.
- We are not modeling a concrete external world.
- CALL preservation means source and target make the same selected calls and preserve results for all shared admissible responses.
- Ordinary sequence recursion is packaged as `CALLOpenSeqPathLoweringFrontierAt`.
- Typed generated-control sequence recursion is packaged as `CALLOpenSeqKontPathLoweringFrontierAt`.
- Generated loop continuation recursion is packaged as `CALLOpenLoopContinuationPathLoweringFrontierAt`.

Relevant declarations already in the file:

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

def CALLOpenSeqPathLoweringFrontierAt
    (cfg : StateRelConfig)
    (terminalRel :
      Assembly.HaltKind -> Word -> State -> Objects.Source.State -> Prop)
    (revertRel : State -> Objects.Source.State -> Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (yulProgram : Program) (program : Functions.Program)
    (bound : Nat) : Prop

def CALLOpenSeqKontPathLoweringFrontierAt
    (cfg : StateRelConfig)
    (terminalRel :
      Assembly.HaltKind -> Word -> State -> Objects.Source.State -> Prop)
    (revertRel : State -> Objects.Source.State -> Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (yulProgram : Program) (program : Functions.Program)
    (bound : Nat) : Prop

def CALLOpenLoopContinuationPathLoweringFrontierAt
    (cfg : StateRelConfig)
    (terminalRel :
      Assembly.HaltKind -> Word -> State -> Objects.Source.State -> Prop)
    (revertRel : State -> Objects.Source.State -> Prop)
    (prim : Objects.Source.PrimitiveSemantics)
    (yulProgram : Program) (program : Functions.Program)
    (bound : Nat) : Prop

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

theorem yulOpen_toOpenResult_exec_for_succ_succ_succ_eq_runLoopSource
    (fuel : Nat) (cond : AstExpr) (post body : List AstStmt)
    (codeOverride : Option AstContract) (state : State) :
    OpenExternal.YulOpenResult.toOpenResult
        (OpenExternal.YulOpen.exec fuel.succ.succ.succ
          (.For cond post body) codeOverride state) =
      runLoopSource fuel cond post body codeOverride state

theorem runLoopSourceAfterPost_regular_resolves_inv_loop_ok_source
theorem runLoopSource_resolves_body_regular_post_regular_loop_of_evalValues_nonzero
theorem compilerOpen_generated_runForLoop_resolves_body_regular_or_continue_post_regular_loop
theorem sourceOpenLoopHeadPathSound_generated_condition_body_post_block_of_loop_callback
theorem lower1?_sourceExprRawPreludeOpenPathSoundWhen_callSafe_expr_of_lower1?_actual_fuel_recursive
theorem CALLOpenSeqPathRecursiveAt.of_frontiers_le
theorem CALLOpenSeqKontPathRecursiveAt.of_frontiers_le
theorem CALLOpenLoopContinuationPathRecursiveAt.of_frontiers_le
```

Theorem we want, modulo small arithmetic adjustments:

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
      prim yulProgram program bound := by
  -- expected structure:
  -- * if `bound <= 2`, use `callOpenLoopContinuationPathLoweringFrontierAt_low_fuel`.
  -- * otherwise write `bound = fuel.succ.succ.succ`, unfold the frontier,
  --   normalize source `exec` using
  --   `yulOpen_toOpenResult_exec_for_succ_succ_succ_eq_runLoopSource`.
  -- * split the selected source path through `runLoopSource`.
  -- * prove condition with
  --   `lower1?_sourceExprRawPreludeOpenPathSoundWhen_callSafe_expr_of_lower1?_actual_fuel_recursive`.
  -- * prove body with a recursive kont frontier at smaller fuel.
  -- * prove post with recursive seq frontier at smaller fuel.
  -- * in the post-regular branch, use `hLoopFrontier` at the recursive
  --   smaller source fuel and rebuild target `runForLoop` with
  --   `compilerOpen_generated_runForLoop_resolves_body_regular_or_continue_post_regular_loop`.
  -- * use existing source branch lemmas such as
  --   `runLoopSourceAfterPost_regular_resolves_inv_loop_ok_source` and
  --   `runLoopSource_resolves_body_regular_post_regular_loop_of_evalValues_nonzero`.
  sorry
```

Important nuance:

`runLoopSource fuel` itself calls `YulOpen.exec fuel (.For cond post body)` after a regular post, but the source theorem at outer fuel `fuel.succ.succ.succ` normalizes to `runLoopSource fuel`. So this should be a smaller recursive source fuel at the theorem boundary. Please verify the arithmetic before committing to the statement.

PROVIDED SOLUTION:

Prefer proving a direct sibling of the existing outer-loop splitters if needed. The existing outer helpers target `CompilerOpen.FunctionsOpen.Stmt.run`; this theorem needs target `CompilerOpen.FunctionsOpen.Stmt.runForLoop`. Do not solve the problem by adding an `hOther` fallback, a public `hLoopRec` assumption, a concrete external-world model, or a replay certificate. The final public induction should build the three frontiers mutually by source fuel and then feed them into the existing generated `For` dispatcher.

Constraints:

- Keep theorem statements unchanged unless you explain why the candidate statement is false.
- Do not introduce axioms.
- Do not leave `sorry` or `admit` in source files.
- Do not rely on `sorryAx` or generated nonstandard axioms.
- Avoid `native_decide`.
- Prefer small helper lemmas near the existing loop splitters if the full theorem is too large.
- Return a patch or a complete replacement proof and explain the key Lean dependencies.

Validation command:

```bash
lake env lean EvmCompiler/Yul/RecursiveBridgeSupport.lean
```
