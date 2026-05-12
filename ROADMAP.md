# Roadmap

## Public Spine

accepted labeled assembly AST -> resolved EVM assembly -> gasless EVMYulLean operation semantics

## Layer Contract

- [x] Fresh Lean package imports EVMYulLean.
- [x] Labeled assembly has syntax, layout, semantics, and target-resolution checks.
- [x] Resolved EVM assembly has executable semantics.
- [x] Assembler has a checked preservation theorem for the verified slice.
- [x] Whole-program assembler theorem covers every successful current-PC source step.
- [ ] Byte encoding and full gas-aware EVM `Ξ` refinement are later lowerings.

## Milestones

- [x] First source-to-resolved-EVM theorem for labels, push, jump, jumpi, and shared primitive ops.
- [x] Whole-program current-step theorem from `assemble? program = some target`.
- [ ] Current-contract memory/storage slice.
- [ ] Gas oracle/refinement relation for `GAS`.
- [ ] External-call oracle/refinement relation.
- [ ] Byte encoder correctness against EVMYulLean decoding.
- [ ] Full gas-aware simulation against EVMYulLean `Ξ`.
