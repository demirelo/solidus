# Structured Recursive Bridge Formalization Log

## Current status

The structured primitive stack contract is now derived internally as an
arity-aware contract.

Verified commands:

```bash
lake build EvmCompiler.Yul.Reference
lake build EvmCompiler.Yul.RecursiveBridgeSupport
```

## Proved in this branch

- Added arity-aware structured primitive facts for the previously uncovered
  safe primitive families:
  `keccak256`, `balance`, `calldataload`, `blockhash`, `blobhash`, `pop`,
  `sload`, `sstore`, `tload`, `tstore`, `log0` through `log4`, and `invalid`.
- Added
  `Reference.SourceBridgeFacts.primitiveStackSoundAtArity_structured_of_safe_toBasicOp`,
  which derives `PrimitiveStackSoundAtArity` for
  `Locals.Source.PrimitiveSemantics.structured` from `Safe.primitive` and
  `Prim.toBasicOp?`.
- Added derived contract packages:
  `RecursiveBridgePrimitiveStackArityContracts.structured` and
  `RecursiveBridgePrimitiveArityContracts.structured`.

## Remaining bottleneck

The public no-call structured XRunner wrappers still expose
`RecursiveBridgePrimitiveStackContracts cfg Locals.Source.PrimitiveSemantics.structured`.
That is the old strict stack contract.

The next proof slice is to thread `PrimitiveStackSoundAtArity` through the
final recursive/top theorem chain.  Existing arity lemmas cover expression,
statement, generated control, and exact frontier levels, but the final
`checkedSeqKont...programAccepted...` and all-bounds/top theorem spine still
uses `PrimitiveStackSoundAt`.

## Next narrow target

Add arity variants of the typed-continuation sequence frontier wrappers used by
`ProgramAcceptedRecursiveSourceBridgeWhenUpToAtExactCompatNamesReserved.succ_of_typed_sequence_frontier_terminal_args_supported`,
starting with the primitive `let`, `assign`, and expression-statement frontier
wrappers, then lift the all-bounds theorem to consume
`RecursiveBridgePrimitiveArityContracts`.
