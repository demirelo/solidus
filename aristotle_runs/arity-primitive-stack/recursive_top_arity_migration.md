We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: migrate the recursive bridge/top theorem spine from strict primitive
stack contracts to arity-aware primitive stack contracts.

Primary files:

- /Users/dan/Projects/evm-compiler/EvmCompiler/Yul/RecursiveBridgeSupport.lean
- /Users/dan/Projects/evm-compiler/EvmCompiler/Yul/NoCallRuntime.lean

Goal:

Add arity-aware theorem variants so the public no-call/top route can consume:

```lean
RecursiveBridgePrimitiveStackArityContracts cfg prim
RecursiveBridgePrimitiveArityContracts cfg prim
RecursiveBridgeSemanticCoreArityContracts cfg terminalRel revertRel prim program
RecursiveBridgeSemanticArityContracts cfg terminalRel revertRel prim outcomeRel program shared store
```

instead of the strict packages:

```lean
RecursiveBridgePrimitiveStackContracts cfg prim
RecursiveBridgeSemanticCoreContracts cfg terminalRel revertRel prim program
RecursiveBridgeSemanticContracts cfg terminalRel revertRel prim outcomeRel program shared store
```

Current context:

- The oracle advised that the strict contract is semantically too strong for
  raw imported Nethermind primitives. The correct public boundary is arity-aware.
- Strict implies arity, but arity does not imply strict.
- Existing arity packages and constructors already exist near the bottom of
  `RecursiveBridgeSupport.lean`:
  `RecursiveBridgePrimitiveStackArityContracts`,
  `RecursiveBridgePrimitiveArityContracts`,
  `RecursiveBridgeSemanticCoreArityContracts`,
  `RecursiveBridgeSemanticArityContracts`,
  and strict-to-arity compatibility constructors.
- `NoCallRuntime.lean` still has strict theorem wrappers such as:
  `compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_XRunner`
  and
  `compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_XRunner`.

Please add arity-aware variants rather than deleting strict variants. Suggested
names can append `_arity` before `_X`/`_XRunner`, for example:

```lean
compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_compileAccepted_arity
compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_referenceNoOutOfFuel_arity
compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_semanticArityContracts
compile_whole_program_result_sound_of_programAcceptedRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonical_arity_X
compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_canonicalSplitResourceBoundaries_arity_XRunner
compile_whole_program_result_sound_of_fullSourceCoveredRecursiveBridgeAllBoundsReserved_topNoCall_sourceCompile_structuredPrimitive_arity_XRunner
```

PROVIDED SOLUTION:

1. Start at the lowest theorem in the public spine that currently passes
   `hPrimSound : PrimitiveStackSoundAt ...` to
   `programAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved_allBounds`.
2. Add an arity-aware version of that recursive all-bounds constructor if
   needed. It should use arity-aware expression/statement bridge siblings for
   primitive calls.
3. Thread the arity primitive contract upward through the same theorem wrappers.
4. Keep the strict versions as compatibility wrappers by converting strict to
   arity with `primitiveStackSoundAtArity_of_stackSoundAt` /
   `RecursiveBridgePrimitiveStackArityContracts.of_strict`.
5. The final structured primitive wrapper should eventually ask for
   `RecursiveBridgePrimitiveStackArityContracts cfg
      Locals.Source.PrimitiveSemantics.structured`
   or construct that package internally from canonical structured facts.

Constraints:

- Do not weaken theorem conclusions.
- Do not introduce axioms, sorry, or admit.
- Do not try to prove arity implies strict.
- Do not add primitive-specific cases to recursive bridge proofs.
- Preserve old strict theorem names where possible as wrappers.
- If the whole migration is too large, return the largest checked prefix with
  clear theorem names and no holes.

Validation commands:

```bash
lake build EvmCompiler.Yul.RecursiveBridgeSupport
lake build EvmCompiler.Yul.NoCallRuntime
```
