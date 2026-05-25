We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: prove arity-aware siblings for the generated `for` hidden-scope/post-regular theorem chain in `EvmCompiler/Yul/RecursiveBridgeSupport.lean`.

Context:
The generated-loop branch lemmas now have arity-aware siblings for body break, leave, halt, continue/post, and regular/post. The next blocker for the checked `for` arity theorem is the internal chain around:
- `checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_for_of_hiddenScope_and_postRegular`
- any immediately adjacent hidden-scope generated-loop wrapper it calls

Goal:
Add `_arity` theorem siblings for this post-regular hidden-scope layer, replacing the strict `hPrim` premise:

```lean
PrimitiveStackSoundAt cfg layout prim sourceFuel.succ
  (.CompBit .ISZERO : EvmYul.Operation .Yul) .iszero
```

with:

```lean
PrimitiveStackSoundAtArity cfg layout prim sourceFuel.succ
  (.CompBit .ISZERO : EvmYul.Operation .Yul) .iszero
```

and call the already-proved `_arity` generated-loop branch lemmas instead of strict ones.

Constraints:
- Keep existing theorem statements unchanged.
- Do not introduce axioms, `sorry`, or `admit`.
- Do not prove/use a false arity-implies-strict lemma.
- Avoid copying unrelated infrastructure declarations.

Validation:
`lake build EvmCompiler.Yul.RecursiveBridgeSupport`
Then axiom-audit new theorems; only `propext`, `Classical.choice`, and `Quot.sound` should appear.
