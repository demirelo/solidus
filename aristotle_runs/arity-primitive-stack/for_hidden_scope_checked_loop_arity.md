We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: prove arity-aware siblings for the checked generated `for` hidden-scope loop theorem chain in `EvmCompiler/Yul/RecursiveBridgeSupport.lean`.

Context:
The post-regular/generated-loop branch substrate is being migrated to `PrimitiveStackSoundAtArity`. The remaining checked-loop blocker includes:
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_checked_loop`
- closely adjacent wrapper lemmas between this theorem and `..._postRegular`

Goal:
Add `_arity` theorem siblings for the checked-loop hidden-scope layer, replacing strict ISZERO primitive soundness with `PrimitiveStackSoundAtArity`, and calling arity-aware dependencies such as `..._postRegular_arity` once available.

If a dependency is missing, isolate the smallest missing theorem and prove it too if local and mechanical; otherwise report the precise missing dependency.

Constraints:
- Keep theorem statements unchanged.
- No axioms, `sorry`, or `admit`.
- Do not derive strict primitive soundness from arity-aware primitive soundness.
- Avoid broad copies that duplicate later declarations.

Validation:
`lake build EvmCompiler.Yul.RecursiveBridgeSupport`
Axiom-audit all new theorems.
