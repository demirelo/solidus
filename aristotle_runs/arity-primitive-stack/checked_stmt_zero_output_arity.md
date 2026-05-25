We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: add and prove arity-aware checked-statement bridge theorems for
non-terminal zero-output primitive expression statements.

File: /Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

Please prove arity-aware siblings of these existing strict theorems:

- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_of_preludeRegular_success`
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal`

The new theorem names should be:

```lean
checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_of_preludeRegular_success_arity
checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal_arity
```

Each new theorem should have the same statement as the strict version except:

- replace `hPrim : PrimitiveStackSoundAt cfg layout prim sourceFuel yulPrim op`
  with
  `hPrim : PrimitiveStackSoundAtArity cfg layout prim sourceFuel yulPrim op`;
- add an explicit arity premise if needed:
  `hArgArity : args.length = Expressions.Structured.BasicOp.inputs op`.

Current context:

- We are migrating the compiler bridge away from the false/too-strong strict
  primitive-stack contract. Some imported Nethermind nullary primitives are
  permissive at raw `primCall`; the compiler/source boundary enforces exact
  arity, so the correct bridge is `PrimitiveStackSoundAtArity`.
- Arity-aware expression helpers already exist:
  `exprValuePreludeSound_prim_of_arg_stack_preludeRegular_arity`,
  `exprValuePreludeSound_prim_of_arg_stack_preludeRegularAt_arity`,
  `lower0?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegular_arity`,
  and `lower0?_prim_exprValuePreludeSound_of_lowerBound1?_preludeRegularAt_arity`.
- The hard strict theorem still directly applies:
  `rcases hPrim hRelArgs hPrimCall with ...`
  in the productive primitive branch. The arity proof must derive the raw
  primitive argument length from successful imported `evalArgs`.

PROVIDED SOLUTION:

For the `..._of_preludeRegular_success_arity` theorem:

1. Copy the strict proof of
   `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_of_preludeRegular_success`.
2. Replace the call to
   `sourceRegularSeqRunBridgeHidden_single_expr_prim_of_lower_preludeRegular_general`
   with the arity sibling from the other Aristotle task:
   `sourceRegularSeqRunBridgeHidden_single_expr_prim_of_lower_preludeRegular_general_arity`.
   If it is not present yet, add it first or inline the same proof idea.

For the `..._actual_or_arg_terminal_arity` theorem:

1. Copy the strict proof of
   `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal`.
2. In the productive `primCall` branch, derive:
   `argValues.length = Expressions.Structured.BasicOp.inputs op`.
   The relevant hypothesis is the successful imported argument evaluation
   returned by `exec_block_expr_prim_call_evalArgs_split_of_relatable`; use
   `Imported.evalArgs_length_of_ok` and the explicit `hArgArity`.
3. Apply the arity primitive bridge using that length equality.
4. Continue exactly as the strict proof does.
5. The argument-terminal branch should remain unchanged.

Constraints:

- Do not weaken existing theorem statements.
- Do not introduce axioms.
- Do not leave sorry/admit.
- Do not add primitive-specific cases.
- If helper lemmas are needed, keep them local and general.

Validation command:

```bash
lake build EvmCompiler.Yul.RecursiveBridgeSupport
```
