We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: add arity-aware versions of the generated `for` nonzero/body-break
bridge lemmas in `EvmCompiler/Yul/RecursiveBridgeSupport.lean`, without
weakening existing theorems and without using `sorry`, `admit`, or axioms.

File:
/Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean

Context:
- We are migrating the recursive Yul bridge away from strict
  `PrimitiveStackSoundAt` obligations and toward
  `PrimitiveStackSoundAtArity`.
- The current file already has arity-aware guard-prefix lemmas:
  - `sourceGeneratedIszeroCondition_true_of_exact_zero_arity`
  - `sourceGeneratedIszeroCondition_false_of_exact_nonzero_arity`
  - `sourceForGeneratedGuardSkipRunOpen_of_exact_nonzero_arity`
  - `sourceForGeneratedGuardSkipRunOpen_of_eval_domain_nonzero_arity`
- The strict body-break lemmas currently begin around
  `sourceForGeneratedGuardBodyBreakRunScoped_of_eval_domain_nonzero`.

Please prove these new theorems, placed next to their strict siblings:

1. `sourceForGeneratedGuardBodyBreakRunScoped_of_eval_domain_nonzero_arity`

Same statement as `sourceForGeneratedGuardBodyBreakRunScoped_of_eval_domain_nonzero`,
except the primitive premise should be:

```lean
(hPrim :
  PrimitiveStackSoundAtArity cfg layout prim sourceFuel.succ
    (.CompBit .ISZERO : EvmYul.Operation .Yul) .iszero)
```

and the proof should call
`sourceForGeneratedGuardSkipRunOpen_of_eval_domain_nonzero_arity`.

2. `sourceForGeneratedBodyBreakStmtRun_of_eval_domain_nonzero_arity`

Same statement as `sourceForGeneratedBodyBreakStmtRun_of_eval_domain_nonzero`,
except the primitive premise should use `PrimitiveStackSoundAtArity`, and the
proof should call
`sourceForGeneratedGuardBodyBreakRunScoped_of_eval_domain_nonzero_arity`.

3. `sourceForGeneratedBodyBreakStmtRun_of_eval_domain_nonzero_hidden_scope_arity`

Same statement as
`sourceForGeneratedBodyBreakStmtRun_of_eval_domain_nonzero_hidden_scope`,
except the primitive premise should use `PrimitiveStackSoundAtArity`, and the
proof should call
`sourceForGeneratedGuardBodyBreakRunScoped_of_eval_domain_nonzero_arity`.

Optional, if straightforward:

4. `sourceRegularStmtRunHiddenExact_for_generated_body_break_of_eval_domain_nonzero_arity`

Same as the strict theorem of the same base name, but arity-aware and calling
`sourceForGeneratedBodyBreakStmtRun_of_eval_domain_nonzero_arity`.

5. `sourceRegularStmtRunHiddenExact_for_generated_body_break_of_eval_domain_nonzero_hidden_scope_arity`

Same as the strict hidden-scope theorem of the same base name, but arity-aware
and calling
`sourceForGeneratedBodyBreakStmtRun_of_eval_domain_nonzero_hidden_scope_arity`.

Informal proof / guidance:
PROVIDED SOLUTION:
These should be mostly copy-and-replace proofs from the strict siblings. Do
not try to prove a general theorem from `PrimitiveStackSoundAtArity` to
`PrimitiveStackSoundAt`. For the generated guard path, use the local arity-aware
guard-prefix lemma; that is the compositional point of this migration.

Constraints:
- Keep existing theorem statements unchanged.
- Do not introduce axioms.
- Do not leave `sorry` or `admit`.
- Do not rely on `sorryAx` or generated nonstandard axioms.
- Avoid unrelated refactors.
- Prefer small helper lemmas only if they are genuinely reusable for the rest
  of the generated-loop arity migration.

Validation command:
lake build EvmCompiler.Yul.RecursiveBridgeSupport

After proving, run axiom checks for any newly added theorem and confirm they
only use standard Lean axioms such as `propext`, `Classical.choice`, and
`Quot.sound`.
