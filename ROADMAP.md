# Roadmap

Last updated: 2026-05-25 21:43 PDT.

This roadmap describes the current plan after the proof-tower reset. The old
plan tried to harden the previous compiler directly. The current plan is
different: rebuild the tower around explicit adjacent semantic layers, with
stack details quarantined in `TypedCfg` and below.

## North Star

Build a formally verified compiler tower where each theorem relates exactly one
source interpreter to the next target interpreter.

```text
Nethermind/Solidity Yul reference semantics
  -> StackFreeCfg
  -> TypedCfg
  -> labeled assembly
  -> concrete EVM bytecode
  -> gas-aware EVM boundary
```

The public top theorem should expose only source acceptedness, initial-state
relation, explicit object/data/external-world contracts, and gas/resource
bounds. It must not expose generated layouts, stack-depth witnesses, return
tokens, dispatch tables, replay certificates, per-callee preservation oracles,
label-resolution evidence, or bytecode proof internals.

## Layer Boundary Rules

- Every layer has its own independent interpreter.
- Every compiler proof is adjacent: source layer to immediate target layer.
- Higher layers must not mention implementation details hidden by lower layers.
- Source semantics for a layer must fully abstract the feature introduced by
  that layer.
- Shared primitive semantics may pass through unchanged only when primitives
  are not the abstraction being introduced.
- `Accepted`/`WF` may reject malformed or semantically invalid programs, but
  must not hide proof gaps as source-language restrictions.
- Compiler-generated evidence must be constructed internally by checked Lean
  theorems or remain an unfinished checkpoint.

## Layer Contracts

### StackFreeCfg

Purpose: the first real source-facing target above the stack machine.

Owns:

- variables and lexical scopes as a varstore;
- expressions over values;
- structured control: `if`, `switch`, `for`, `break`, `continue`;
- procedures with params, returns, calls, and `leave`;
- terminal EVM halts distinct from Yul `leave`;
- source invalid/error/out-of-fuel outcomes;
- shared EVM/Yul primitive state through a value-level primitive adapter.

Must not expose:

- EVM stack shape, stack suffixes, `DUP`, `SWAP`, `POP`;
- labels, byte offsets, concrete PCs;
- return tokens, dispatch tables, or assembly layout.

Current status:

- [x] Syntax exists.
- [x] Independent semantics exists.
- [x] Source acceptedness/checker exists.
- [x] Compiler to checked `TypedCfg` exists.
- [x] Contract/observation surface exists.
- [x] Initial adjacent preservation interface exists.
- [x] Local state/shape vocabulary exists for the proof below this boundary.
- [x] Adjacent proof support has been extracted to
  `EvmCompiler.StackFreeCfg.PreservationSupport`, keeping stack-shape lemmas
  out of the public preservation interface.
- [x] Compositional compiler-shape lemmas exist for expression arity,
  declarations, and assignments.
- [ ] Complete adjacent proof: `StackFreeCfg -> TypedCfg`.
- [ ] Audit final public theorem for stack leakage.

### TypedCfg

Purpose: a typed symbolic stack CFG that quarantines all stack discipline.

Owns:

- symbolic labels with declared input shapes;
- typed stack slots and runtime stack conformance checks;
- local stack effects such as load/store/init/return locals;
- lexical `unwind`;
- typed `jump`, `jumpi`, procedure call/return, and terminal halts;
- fuel/resource behavior for typed-CFG execution.

Must not pretend to be stack-free:

- shapes and stack slots are allowed here;
- generated return continuations and dispatch are allowed here;
- these concepts must not escape into `StackFreeCfg` or Yul theorem surfaces.

Current status:

- [x] Syntax exists.
- [x] Typechecker exists.
- [x] Independent semantics exists.
- [x] Contract surface exists.
- [x] Lowering to labeled assembly exists.
- [x] Adjacent preservation boundary exists in
  `EvmCompiler.TypedCfg.Preservation`.
- [x] Ordinary `push` now produces generic `.word` shape slots, while exact
  literal slots remain available for explicit contracts.
- [x] Typed syntax no longer imports the assembly umbrella/proof modules; it
  imports only assembly syntax and shared EVM state types. Typed semantics
  imports primitive semantics directly and does not run by lowering.
- [x] Typed `.fallthrough` lowers to assembly `STOP`, so semantic completion
  cannot physically fall into later emitted blocks.
- [ ] Complete adjacent proof: `TypedCfg -> labeled assembly`.
- [ ] Audit generated labels/tokens/dispatch uniqueness at this boundary.

### Labeled Assembly

Purpose: symbolic EVM-like bytecode with labels instead of byte offsets.

Owns:

- opcode-level stack behavior;
- symbolic jump labels;
- `JUMPDEST` correctness before concrete byte encoding;
- gasless execution semantics matching EVM behavior except gas.

Current status:

- [x] Syntax/semantics/assembler exists.
- [x] Gasless labeled-assembly-to-EVM proof surface has been restored.
- [x] Gas/oracle/external runtime premises were split away from the gasless
  theorem and kept at the gas-aware boundary.
- [ ] Eliminate or justify `Bytecode.JumpdestCorrect`; it remains due to the
  imported opaque jumpdest scanner.
- [ ] Keep final gas-aware assumptions explicit and separate.

### Yul To StackFreeCfg

Purpose: bridge the targeted Nethermind/Solidity Yul semantics into the
stack-free source language.

Owns:

- exact imported Yul source surface and revision;
- Yul declarations, assignments, blocks, loops, switches, functions, calls;
- Yul argument evaluation order;
- Yul scoping, including block cleanup and loop-init scope;
- Yul `leave` as procedure exit, not EVM `RETURN`;
- object/data pseudo-builtins through explicit layout contracts;
- `verbatim` rejection or a separate explicit contract;
- external-world operations through shared semantics or an explicit oracle
  relation.

Must not expose:

- typed-CFG shapes;
- EVM stack layouts;
- assembly labels;
- return-token dispatch;
- bytecode PCs or gas details.

Current status:

- [x] Compiler exists.
- [x] `lowerGate` exists with inspectable rejection reasons.
- [x] Source-facing WF/coverage checkers exist.
- [x] Contract/observation surface exists.
- [x] Initial adjacent preservation interface exists.
- [x] Gate equivalence lemmas exist.
- [ ] Inventory the full imported Yul source surface against the compiler.
- [ ] Finish object/data/external-world contracts needed for the source claim.
- [ ] Complete adjacent proof: `Nethermind/Solidity Yul -> StackFreeCfg`.
- [ ] Audit final public theorem for lower-layer leakage.

## Active Proof Plan

The proof work now proceeds bottom-up along adjacent boundaries, while keeping
the theorem statements top-down clean.

1. [x] Restore and audit the labeled-assembly-to-EVM proof checkpoint.
2. [ ] Prove `TypedCfg -> labeled assembly`.
3. [ ] Prove `StackFreeCfg -> TypedCfg`.
4. [ ] Prove `Yul -> StackFreeCfg`.
5. [ ] Compose the adjacent theorems into the public top theorem.
6. [ ] Add the final gas-aware wrapper with explicit sufficient-gas/resource
   assumptions.

Parallel worker threads, when used, should own disjoint adjacent proof files:

- `EvmCompiler/TypedCfg/Preservation.lean`
- `EvmCompiler/StackFreeCfg/Preservation.lean`
- `EvmCompiler/YulToStackFreeCfg/Preservation.lean`

The parent thread integrates only patches that respect the layer boundaries.

## Immediate Checklist

- [x] Review the three worker outputs for boundary cleanliness. Worker B's
  StackFreeCfg support was usable; Worker A produced no final result before
  being closed; Worker C was unavailable.
- [x] Integrate any green, adjacent-only proof support.
- [ ] Finish `TypedCfg -> labeled assembly` enough that generated label/token
  evidence is internal to the pass.
- [ ] Finish `StackFreeCfg -> TypedCfg` successor/statement theorem without
  exposing stack details in the public theorem.
- [ ] Finish `Yul -> StackFreeCfg` bridge after the StackFree theorem shape is
  stable.
- [ ] After every meaningful checkpoint: run the narrow build, scan for
  `sorry`/`admit`/`axiom`/`unsafe`, update `PROGRESS_LOG.md`, and commit.

## Completion Criteria

The compiler tower is not complete until:

- each layer has syntax, semantics, acceptedness/WF, compiler, relation, and
  adjacent preservation theorem;
- each public theorem quantifies over the source interpreter of its own layer;
- no public theorem takes compiler-generated evidence as an input;
- all accepted source constructs are either supported or explicitly rejected by
  a user-approved source contract;
- all lower-layer assumptions are either discharged or confined to the final
  gas/resource/imported-semantics boundary;
- the composed top theorem mentions only the allowed source-level assumptions.
