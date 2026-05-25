We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: add arity-aware versions of the generated `for` nonzero/body-regular
bridge lemmas in `EvmCompiler/Yul/RecursiveBridgeSupport.lean`, without
weakening existing theorems and without using `sorry`, `admit`, or axioms.

File:
/Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

Context:
- We are migrating the recursive Yul bridge from strict `PrimitiveStackSoundAt`
  obligations to honest `PrimitiveStackSoundAtArity` obligations.
- The file already has arity-aware generated-loop lemmas for:
  - guard skip: `sourceForGeneratedGuardSkipRunOpen_of_eval_domain_nonzero_arity`
  - body break / leave / halt
  - body continue plus post branches
- The remaining generated-loop frontier is the body-regular branch.

Please prove arity-aware siblings of the body-regular generated-loop lemmas,
placed near their strict siblings. At minimum:

1. `sourceForGeneratedGuardBodyRegularRunScoped_of_eval_domain_nonzero_arity`
2. `sourceForGeneratedBodyRegularPostHaltStmtRun_of_eval_domain_nonzero_arity`
3. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_of_eval_domain_nonzero_arity`
4. `sourceForGeneratedBodyRegularPostHaltStmtRun_of_eval_domain_nonzero_hidden_scope_arity`
5. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_of_eval_domain_nonzero_hidden_scope_arity`
6. `sourceForGeneratedBodyRegularPostHaltStmtRunExists_of_eval_domain_nonzero_hidden_scope_arity`
7. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_exists_of_eval_domain_nonzero_hidden_scope_arity`
8. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_halt_of_blockSound_arity`
9. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_leave_of_blockSound_arity`
10. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_leave_of_blockSound_hidden_scope_arity`
11. `sourceRegularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero_arity`
12. `sourceRegularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero_hidden_scope_arity`
13. `sourceRegularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_blockSound_arity`
14. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero_arity`
15. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_eval_domain_nonzero_hidden_scope_arity`
16. `sourceNonregularStmtRunHiddenExact_for_generated_body_regular_post_regular_of_blockSound_arity`

Do not copy unrelated later infrastructure declarations such as contract record
definitions or singleton helper declarations. Stop each copied theorem at the
next theorem/doc boundary.

Informal proof / guidance:
PROVIDED SOLUTION:
These should mostly mirror the strict body-regular siblings. Replace the
primitive premise

```lean
PrimitiveStackSoundAt cfg layout prim sourceFuel.succ
  (.CompBit .ISZERO : EvmYul.Operation .Yul) .iszero
```

with

```lean
PrimitiveStackSoundAtArity cfg layout prim sourceFuel.succ
  (.CompBit .ISZERO : EvmYul.Operation .Yul) .iszero
```

and call the arity-aware generated guard/body lemmas, especially
`sourceForGeneratedGuardBodyRegularRunScoped_of_eval_domain_nonzero_arity`,
instead of the strict ones. For block-sound wrappers, call the new arity-aware
exact/hidden-scope sibling rather than the old strict theorem.

Constraints:
- Keep existing theorem statements unchanged.
- Do not introduce axioms.
- Do not leave `sorry` or `admit`.
- Do not rely on `sorryAx` or generated nonstandard axioms.
- Avoid unrelated refactors.

Validation command:
lake build EvmCompiler.Yul.RecursiveBridgeSupport

After proving, run axiom checks for newly added theorems and confirm they only
use standard Lean axioms such as `propext`, `Classical.choice`, and `Quot.sound`.
