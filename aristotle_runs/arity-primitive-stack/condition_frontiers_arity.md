We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: migrate the next hard arity-aware primitive proof frontier in
`EvmCompiler/Yul/RecursiveBridgeSupport.lean`.

Goal: prove arity-aware siblings for the condition-expression statement
frontiers that currently require strict `PrimitiveStackSoundAt`, without
weakening any existing theorem and without adding `sorry`, `admit`, or axioms.

The project already has these checked arity facts:

- `lower1?_exprEvalPreludeSound_of_argRegularAllScopedAt_arity`
- `lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt_arity`
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_expr_prim_actual_or_arg_terminal_frontier_arity`
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_let_prim_actual_or_arg_terminal_frontier_arity`
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_assign_prim_actual_or_arg_terminal_frontier_arity`

The next theorem family should be arity siblings of:

- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_of_programAcceptedCondition`
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_if_of_programAcceptedCondition_frontier`
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_switch_of_programAcceptedScrutinee`
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_switch_of_programAcceptedScrutinee_frontier`
- if feasible, `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition`
- if feasible, `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition_frontier`

The desired changes are mechanical but must avoid the false lemma
`PrimitiveStackSoundAtArity -> PrimitiveStackSoundAt`.  Instead:

1. Change primitive premises from
   `PrimitiveStackSoundAt cfg layout prim fuel yulPrim op`
   to
   `PrimitiveStackSoundAtArity cfg layout prim fuel yulPrim op`.
2. Where the proof calls
   `lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt`,
   call
   `lower1?_exprEvalPreludeSound_of_argRegularAllCheckedAt_arity`.
3. Where the proof calls an arity-aware sub-frontier already available, use the
   `_arity` version.
4. Do not try to prove strict soundness from arity soundness.
5. Preserve all old strict theorems unchanged as compatibility.

Important caveat:

Some lower generated-control theorem may still demand strict `hPrimIszero`.
If a full `for`/`if`/`switch` arity sibling cascades into such a blocker,
return the largest locally checkable prefix and explain the exact strict
premise that still needs an arity sibling. Do not add fake assumptions.

Validation command:

```bash
lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

Constraints:

- Keep theorem statements for existing theorems unchanged.
- Do not introduce axioms.
- Do not leave `sorry` or `admit`.
- Do not rely on `sorryAx`.
- Prefer small helper lemmas/sibling theorems over one giant rewrite.
- Return a patch or precise replacement proof.
