We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: complete the arity-aware checked `for` frontier theorem in `EvmCompiler/Yul/RecursiveBridgeSupport.lean`.

Target theorems:
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition_arity`
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_programAcceptedLoop_and_checked_condition_frontier_arity`

Context:
Arity-aware generated-loop branch lemmas exist for break, leave, halt, continue/post, and regular/post. If hidden-scope wrappers are missing, prove the narrow missing `_arity` siblings needed by these target theorems.

Goal:
The target theorems should take `PrimitiveStackSoundAtArity` for generated ISZERO, not strict `PrimitiveStackSoundAt`, and should call arity-aware dependencies throughout.

Constraints:
- Keep existing theorem statements unchanged.
- No axioms, `sorry`, or `admit`.
- Do not prove/use arity-implies-strict.
- Keep changes scoped to the `for` arity frontier.

Validation:
`lake build EvmCompiler.Yul.RecursiveBridgeSupport`
Axiom-audit the two target theorems and any new helpers.
