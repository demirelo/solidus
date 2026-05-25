We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: add and prove arity-aware zero-output primitive hidden-sequence bridge
theorems in:

File: /Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

Please prove new sibling theorems, without weakening existing theorem
statements and without using sorry/admit/axioms:

```lean
theorem sourceRegularSeqRunBridgeHidden_cons_expr_prim_of_lower_preludeRegular_general_arity
    {cfg : StateRelConfig} {layout layoutAfter : List Name}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore}
    {compiler : Objects.Source.State}
    {rest : List AstStmt} {lowerHead : List Functions.Stmt}
    {lowerTail : Functions.Block}
    {yulPrim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {args : List AstExpr} {freshState freshState' : Fresh.State}
    {pre : List Functions.Stmt} {argExprs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {values : List Word}
    (sourceFuel lowerFuel : Nat)
    (codeOverride : Option AstContract)
    (hLower :
      Stmt.toFunctionsListFuel? lowerFuel.succ freshState
          (.ExprStmtCall (.Call (.inl yulPrim) args)) =
        some (lowerHead, freshState'))
    (hTerminal : Prim.terminal? yulPrim = none)
    (hBasic : Prim.toBasicOp? yulPrim = some op)
    (hLowerArgs :
      Expr.List.lowerBound1? freshState args =
        some (pre, argExprs, freshState'))
    (hSeq :
      Expr.List.toStackSeq? argExprs
          (Expressions.Structured.BasicOp.inputs op) =
        some seq)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 0)
    (hRel : SourceStateRel cfg layout (.Ok shared store) compiler)
    (hEval :
      EvmYul.Yul.evalValues sourceFuel.succ
          (.Call (.inl yulPrim) args) codeOverride (.Ok shared store) =
        .ok (.Ok sharedAfter storeAfter, values))
    (hArgs :
      SourceArgStackPreludeRegular cfg layout prim program ctx sourceFuel args
        codeOverride pre seq)
    (hPrim :
      PrimitiveStackSoundAtArity cfg layout prim sourceFuel yulPrim op)
    (hTail :
      ∀ {compilerAfterPre compilerAfterExpr : Objects.Source.State}
        {ctxAfterPre : Functions.Source.Ctx} {preFuel : Nat},
      Functions.Source.Block.runOpen prim program ctx preFuel
          { stmts := pre } compiler =
        .ok (Functions.Source.Outcome.regular compilerAfterPre, ctxAfterPre) →
      Locals.Source.Expr.eval prim (Expr.cast hOutputs (.prim op seq))
          compilerAfterPre =
        .ok (compilerAfterExpr, values) →
      SourceStateRel cfg layout (.Ok sharedAfter storeAfter)
        compilerAfterExpr →
      SourceRegularSeqRunBridgeHidden cfg layout layoutAfter prim program
        ctxAfterPre sourceFuel.succ rest codeOverride
        (.Ok sharedAfter storeAfter) compilerAfterExpr lowerTail) :
    SourceRegularSeqRunBridgeHidden cfg layout layoutAfter prim program ctx
      sourceFuel.succ.succ
      (.ExprStmtCall (.Call (.inl yulPrim) args) :: rest)
      codeOverride (.Ok shared store) compiler
      { stmts := lowerHead ++ lowerTail.stmts }
```

and the singleton wrapper:

```lean
theorem sourceRegularSeqRunBridgeHidden_single_expr_prim_of_lower_preludeRegular_general_arity
  -- same statement as sourceRegularSeqRunBridgeHidden_single_expr_prim_of_lower_preludeRegular_general
  -- but with hPrim : PrimitiveStackSoundAtArity ... instead of PrimitiveStackSoundAt ...
```

Current context:

- Strict versions exist nearby:
  `sourceRegularSeqRunBridgeHidden_cons_expr_prim_of_lower_preludeRegular_general`
  and
  `sourceRegularSeqRunBridgeHidden_single_expr_prim_of_lower_preludeRegular_general`.
- Arity-aware lower0 helper now exists:
  `lower0?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegular_arity`.
- The proof should copy the strict structure but call the arity lower0 helper.
- The needed argument arity is derivable from:
  `Expr.List.lowerBound1?_length_lowerArgs_eq hLowerArgs` and
  `exprList_toStackSeq?_length_eq hSeq`.

PROVIDED SOLUTION:

For the cons theorem:
1. Copy the strict theorem proof.
2. Replace the call to
   `lower0?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegular`
   with
   `lower0?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegular_arity`.
3. No primitive-specific semantics should be unfolded.
4. The singleton theorem should delegate to the new cons theorem with an empty
   tail exactly as the strict singleton delegates to the strict cons theorem.

Constraints:

- Keep all existing theorem statements unchanged.
- Do not introduce axioms.
- Do not leave sorry/admit.
- Do not weaken definitions.
- Prefer adding only these new theorem siblings and small local helper facts if
  absolutely needed.

Validation command:

```bash
lake build EvmCompiler.Yul.RecursiveBridgeSupport
```
