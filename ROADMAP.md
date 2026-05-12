# Roadmap

## Public Spine

accepted labeled assembly AST -> resolved EVM assembly -> gasless EVMYulLean operation semantics -> optional emitted EVM bytecode bridge

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
- [ ] Full gas-aware EVM `Ξ` refinement is a later theorem layer with explicit gas/out-of-gas assumptions.

## Milestones

- [x] First source-to-resolved-EVM theorem for labels, push, jump, jumpi, and shared primitive ops.
- [x] Whole-program current-step theorem from `assemble? program = some target`.
- [x] Whole-program AST compiler theorem from `compile? program = some target`.
- [ ] Current-contract memory/storage slice.
- [ ] Gas oracle/refinement relation for `GAS`.
- [ ] External-call oracle/refinement relation.
- [x] Byte encoder boundary plus local `PUSH32` and one-byte opcode decode facts.
- [ ] Byte encoder correctness against EVMYulLean decoding for complete target programs.
- [ ] Full gas-aware simulation against EVMYulLean `Ξ`.
