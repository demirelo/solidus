# Progress Log

- 2026-05-12 12:20:21 - setup - initialized git and added initial Lean package scaffold targeting EVMYulLean v4.22.0 dependency.
- 2026-05-12 12:59:29 - proof - added labeled assembly syntax, assembler, gasless semantics, and preservation/projection theorem; command `/Users/dan/.elan/bin/lake build`; result green.
- 2026-05-12 12:59:29 - audit - checked `source_step_current_projected_sound` and `stepAt_emit_sound`; only standard Lean/mathlib axioms reported: `propext`, `Classical.choice`, `Quot.sound`.
- 2026-05-12 13:07:19 - proof - proved `assemble_source_step_current_projected_sound`, deriving current-PC emitted target block coverage from `assemble? program = some target`; command `/Users/dan/.elan/bin/lake build`; result green.
- 2026-05-12 13:07:19 - audit - checked `assemble_source_step_current_projected_sound`; only standard Lean/mathlib axioms reported: `propext`, `Classical.choice`, `Quot.sound`.
- 2026-05-12 13:35:51 - proof - added independent assembly accepted checker, `compile?`, `Source.runN`, emitted-block target runs, and whole-program theorem `compile_runN_block_trace_projected_sound`; command `/Users/dan/.elan/bin/lake build`; result green.
- 2026-05-12 13:35:51 - audit - checked `compile_runN_block_trace_projected_sound` and `source_compiled_runN_sound`; only standard Lean/mathlib axioms reported: `propext`, `Classical.choice`, `Quot.sound`.
- 2026-05-12 13:41:15 - proof - added one-way byte encoder boundary `Bytecode.EncodingCorrect`, local decode facts for one-byte opcodes, and bridge theorem `compile_runN_bytecode_bridge`; command `/Users/dan/.elan/bin/lake build`; result green.
- 2026-05-12 13:41:15 - oracle - asked for `PUSH32` payload decode proof against EVMYulLean `ByteArray.extract'`; conversation `20260512-203926-evmyul-push32-byte-decode-proof-88bc371d`; status pending.
- 2026-05-12 13:54:11 - proof - replaced private `toBytes!` dependency with public `toBytesLE`, proved `fromBytes_toBytesLE`, `encodeWord32_length`, `uint256Of_extract_push32_payload`, and `decode_push32_encode`; command `/Users/dan/.elan/bin/lake build`; result green.
- 2026-05-12 14:08:53 - proof - added target byte-size/layout API (`codeLayoutFrom`, `emitFrom_layout`, `assemble_layout`, `compile_layout`) and `fetchInstr_of_decodeAt`; command `/Users/dan/.elan/bin/lake build`; result green.
- 2026-05-12 14:16:50 - proof - proved contextual byte decoder facts `decode_push32_at_prefix`, `decode_single_byte_at_prefix`, and `decode_encodeInstr_at_prefix` under explicit non-wrapping PC and `ByteArray.extract'` small-index hypotheses; command `/Users/dan/.elan/bin/lake build`; result green.
- 2026-05-12 14:25:35 - proof - added `DecodeSafety`, whole-target `compile_decode_correct`, and `compile_fetch_correct` for compiled `ByteArray` under explicit PC/extract bounds; command `/Users/dan/.elan/bin/lake build`; result green.
