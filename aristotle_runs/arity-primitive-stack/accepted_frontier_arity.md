We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: add and prove an arity-aware accepted exact-fuel statement frontier.

File: /Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

Current verified local baseline:

- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal_arity`
  exists and builds locally.
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal_frontier_arity`
  exists and builds locally.
- The strict theorem
  `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_programAccepted_frontier`
  still takes:

```lean
(hPrimSound :
  ∀ {fuel : Nat} {yulPrim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp},
    fuel < bound.succ →
    Safe.primitive yulPrim →
    Prim.toBasicOp? yulPrim = some op →
    PrimitiveStackSoundAt cfg layout prim fuel yulPrim op)
```

and calls the strict expression-statement primitive frontier:

```lean
checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal_frontier
```

Goal:

Add a sibling theorem:

```lean
theorem checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_programAccepted_frontier_arity
    {cfg : StateRelConfig} {reserved layout outcomeLayout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {yulProgram : Program} {program : Functions.Program}
    {context : ProgramBridgeContext yulProgram program} {bound : Nat}
    {ctx : Functions.Source.Ctx}
    {sourceStmt : AstStmt}
    {allowed : Except Exception State → Prop}
    {canBreak canContinue canLeave : Bool}
    (hRecursive :
      ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNames cfg
        terminalRel revertRel prim yulProgram program context bound)
    (hSafe : Safe.stmt sourceStmt)
    (hScoped :
      ControlFlow.ScopedStmt canBreak canContinue canLeave sourceStmt)
    (hStmtOk : UserCallArity.StmtOk yulProgram.contract sourceStmt)
    (hSourceScoped : SourceLexical.StmtScoped layout sourceStmt)
    (hAllowed :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultRelatable sourceResult)
    (hCompat :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultOutcomeLayoutCompatible ctx layout outcomeLayout
          sourceResult)
    (hScope : ctx.scope = layout)
    (hPrimTerminal :
      ∀ {yulPrim : EvmYul.Operation .Yul} {kind : Assembly.HaltKind}
        {args : List AstExpr},
        Safe.stmt (.ExprStmtCall (.Call (.inl yulPrim) args)) →
        ControlFlow.ScopedStmt canBreak canContinue canLeave
          (.ExprStmtCall (.Call (.inl yulPrim) args)) →
        UserCallArity.StmtOk yulProgram.contract
          (.ExprStmtCall (.Call (.inl yulPrim) args)) →
        SourceLexical.StmtScoped layout
          (.ExprStmtCall (.Call (.inl yulPrim) args)) →
        Prim.terminal? yulPrim = some kind →
        CheckedStmtBlockLoweringSoundWhenFreshNamesAtExact cfg reserved layout
          outcomeLayout terminalRel revertRel prim program ctx bound.succ
          (.ExprStmtCall (.Call (.inl yulPrim) args))
          (some yulProgram.contract) allowed)
    (hPrimSound :
      ∀ {fuel : Nat} {yulPrim : EvmYul.Operation .Yul}
        {op : Structured.BasicOp},
        fuel < bound.succ →
        Safe.primitive yulPrim →
        Prim.toBasicOp? yulPrim = some op →
        PrimitiveStackSoundAtArity cfg layout prim fuel yulPrim op)
    (hResultOk :
      ∀ {fuel : Nat} {expr : AstExpr},
        fuel < bound.succ →
        Safe.expr expr →
        SourceExprScoped layout expr →
        UserCallArity.ExprOk yulProgram.contract expr →
        ExprEvalResultOkAt cfg layout fuel expr
          (some yulProgram.contract)) :
    CheckedStmtBlockLoweringSoundWhenFreshNamesAtExact cfg reserved layout
      outcomeLayout terminalRel revertRel prim program ctx bound.succ
      sourceStmt (some yulProgram.contract) allowed
```

PROVIDED SOLUTION:

1. Copy the proof of
   `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_programAccepted_frontier`.
2. In the `hPrimExpr` branch, when `Prim.toBasicOp? yulPrim = some op` and
   `outputs op = 0`, call the arity theorem:

```lean
checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal_frontier_arity
```

instead of the strict frontier.
3. For one-output let/assign primitive branches, either:
   - keep using existing strict branches only if strict facts are still required
     by their current theorem shape, by locally converting arity to strict is NOT
     allowed, or
   - preferably add arity siblings if straightforward.

If the full theorem cannot be closed because let/assign frontiers are still
strict, return the largest checked prefix: a theorem for expression-statement
frontier dispatch only, or a clear list of the next strict theorem siblings
needed.

Constraints:

- Do not prove or assume arity implies strict.
- Do not add primitive-specific cases.
- Do not weaken existing theorem statements.
- No sorry/admit/axiom.
- Preserve existing strict theorems as compatibility.

Validation command:

```bash
lake build EvmCompiler.Yul.RecursiveBridgeSupport
```
