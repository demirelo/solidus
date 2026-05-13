# Roadmap

## Public Spine

accepted structured-control AST -> labeled assembly AST -> resolved EVM assembly -> gasless EVMYulLean operation semantics -> emitted EVM bytecode bridge -> gas-aware EVMYulLean `X` bridge

## Layer Contract

- [x] Fresh Lean package imports EVMYulLean.
- [x] Labeled assembly has syntax, layout, semantics, and target-resolution checks.
- [x] Resolved EVM assembly has executable semantics.
- [x] Assembler has a checked preservation theorem for the verified slice.
- [x] Whole-program assembler theorem covers every successful current-PC source step.
- [x] AST-level `compile?` entrypoint has an accepted-input checker and whole-run block-trace theorem.
- [x] Byte encoding is a one-way deployable-code lowering, not a parser in the source compiler path.
- [x] `PUSH32` payload encoding is proved against EVMYulLean `decode`.
- [x] Compiled target code has a proved byte-layout invariant.
- [x] Contextual EVMYulLean `decode` facts cover encoded target instructions at non-wrapping PCs.
- [x] Whole-target EVMYulLean `decode` and `fetchInstr` correctness holds under explicit decode-safety bounds.
- [x] EVMYulLean jumpdest scanner dependence is isolated as the explicit `JumpdestCorrect` assumption boundary.
- [x] Public top theorem `compile_whole_program_sound` exposes bytecode, gas, outside-world, out-of-gas, and projection assumptions in Lean.
- [x] Gas-aware `X` bridge theorem exposes a reusable `XBridgeCertificate`, a direct existential sufficient-gas theorem, and a no-out-of-gas corollary.
- [x] Structured-control layer has syntax, a fuel-indexed source evaluator, compiler to labeled assembly, and top theorem composing through the existing assembly/bytecode bridge under an explicit replay certificate.
- [x] Structured-control proof spine has relational `Eval` semantics, executable-run-to-`Eval`, source-run sequencing, and prefix PC-layout lemmas for the replay derivation.
- [ ] Derive the structured replay certificate by induction over the structured evaluator, eliminating the current caller-provided proof object from the structured top theorem.
- [ ] Full gas-aware EVM `Ξ` refinement is a later theorem layer with explicit gas/out-of-gas assumptions.

## Milestones

- [x] First source-to-resolved-EVM theorem for labels, push, jump, jumpi, and shared primitive ops.
- [x] Whole-program current-step theorem from `assemble? program = some target`.
- [x] Whole-program AST compiler theorem from `compile? program = some target`.
- [ ] Current-contract memory/storage slice.
- [ ] Gas oracle/refinement relation for `GAS`.
- [ ] External-call oracle/refinement relation.
- [x] Byte encoder boundary plus local `PUSH32` and one-byte opcode decode facts.
- [x] Byte encoder correctness against EVMYulLean decoding/fetching for complete target programs under explicit PC/extract bounds.
- [x] EVMYulLean `X` runner bridge under explicit sufficient-gas certificate.
- [x] Structured-control AST with `code`, `ifElse`, and Yul-shaped `for` compiles to labeled assembly and composes with the lower bridge via `Structured.AssemblyReplay`.
- [x] First PC-aware structured compiler infrastructure: `Eval` induction principle, `ARun` bind, `pcAfter`, and basic-instruction prefix-step projection.
- [ ] Structured compiler preservation derives `AssemblyReplay` directly for every successful structured run.
- [ ] Derive `SufficientGasForX` from the finite block trace and EVMYulLean gas-cost/precheck functions.
- [ ] EVMYulLean jumpdest scanner correctness for complete target programs, if `D_J_aux` becomes transparent or a library theorem is added.
- [ ] Full gas-aware simulation against EVMYulLean `Ξ`.

## AST-First Compiler Interface

The intended frontend target is the labeled assembly AST, not parsed bytecode.
Parsing bytecode is unnecessary for compiling a future source language into this
layer: the source compiler can produce `Assembly.Program` directly and compose
with `compile_runN_block_trace_projected_sound`. The bytecode bridge is a final
deployment boundary proving that the resolved target program encodes to EVM
bytes whose EVMYulLean `decode`/`fetchInstr` behavior matches the target blocks,
under `RuntimeAssumptions`.
