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
- [x] Contextual EVMYulLean `decode` facts cover encoded target instructions at non-wrapping PCs.
- [x] Whole-target EVMYulLean `decode` and `fetchInstr` correctness holds under explicit decode-safety bounds.
- [x] EVMYulLean jumpdest scanner dependence is isolated as the explicit `JumpdestCorrect` assumption boundary.
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
- [ ] EVMYulLean jumpdest scanner correctness for complete target programs, if `D_J_aux` becomes transparent or a library theorem is added.
- [ ] Full gas-aware simulation against EVMYulLean `Ξ`.

## AST-First Compiler Interface

The intended frontend target is the labeled assembly AST, not parsed bytecode.
Parsing bytecode is unnecessary for compiling a future source language into this
layer: the source compiler can produce `Assembly.Program` directly and compose
with `compile_runN_block_trace_projected_sound`. The bytecode bridge is a final
deployment boundary proving that the resolved target program encodes to EVM
bytes whose EVMYulLean `decode`/`fetchInstr` behavior matches the target blocks,
under `DecodeSafety` and `JumpdestCorrect`.
