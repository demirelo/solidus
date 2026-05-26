# Typed CFG Rewrite

This branch is compiler-first. The proof-heavy modules are archived on
`codex/proof-modules-before-typed-cfg-rewrite`; this branch should refactor the
compiler architecture before rebuilding preservation proofs.

## Core Design

Control flow carries an explicit stack contract. The compiler should not recover
stack shape from generated EVM jumps after the fact.

This document uses "CFG" in the typed stack-machine sense. The typed CFG is not
stack-free internally: it is the boundary where symbolic stack shapes become
explicit and checked. The abstraction goal is that layers above it do not expose
concrete stack slots, `DUP`/`SWAP`, return-token encodings, or bytecode jumps in
their source semantics. If we later want a stack-free block-parameter CFG, it
should sit above this typed stack CFG and lower into it.

Use the judgment:

```text
compileStmt Γ K stmt
```

where:

```text
Γ = current local-variable stack layout
K = control context:
    break    -> target label + required stack shape
    continue -> target label + required stack shape
    leave    -> function-exit label + required stack shape
```

A compiled statement starting in shape `Γ` either:

1. falls through normally with the expected `Γ'`;
2. jumps to `K.break` with exactly `K.break.shape`;
3. jumps to `K.continue` with exactly `K.continue.shape`;
4. jumps to `K.leave` with exactly `K.leave.shape`;
5. halts the EVM execution.

## Control Effects

Separate Yul `leave` from EVM terminal opcodes:

```text
leave               : structured function exit
return(offset,size) : EVM halt, no successor stack shape
revert(offset,size) : EVM halt/revert, no successor stack shape
stop                : EVM halt, no successor stack shape
```

Every label is a typed join point:

```text
L_post        expects Π · loop_vars
L_after_loop  expects Π · outer_vars
L_fun_exit    expects Π · return_pc · return_values
```

Every branch normalizes the current stack to the target shape before jumping.
The destination word consumed by `JUMP`/`JUMPI` belongs to the typed assembler
layer, not the source control-flow contract.

## Statement Baseline

Expressions and statements have different stack rules:

```text
compileExpr Γ e    : Γ -> Γ · values(e)
compileStmt Γ stmt : Γ -> Γ'
```

No expression temporaries survive statement boundaries. `if` and `switch`
evaluate their condition/scrutinee, consume that temporary, and run every branch
from the same baseline shape.

## Lexical Unwinding

Every syntactic construct owns the stack slots it introduces, and every
control-flow edge leaving that construct must run cleanup before reaching the
target continuation.

Blocks create lexical stack regions:

```text
entry shape:     Π
inside block:    Π · locals
normal exit:     pop locals, return to Π
break exit:      pop locals, then jump to K.break
continue exit:   pop locals, then jump to K.continue
leave exit:      pop locals, then jump to K.leave
```

Use one reusable operation:

```text
unwind(current_shape, target_shape)
```

For verification, cleanup landing pads are acceptable and probably preferable:
each scope can own one cleanup path per escaping effect.

## Loops

For:

```yul
for { init } cond { post } { body }
```

install:

```text
continue -> L_post
break    -> L_after_loop
leave    -> inherited function-exit target
```

Shape discipline:

```text
outer shape:         Π
after init:          Π · loop_init_vars
L_cond expects:      Π · loop_init_vars
L_body expects:      Π · loop_init_vars
L_post expects:      Π · loop_init_vars
L_after_loop expects Π
```

`continue` preserves loop-init variables; `break` exits the whole loop scope.

## Functions

Each function has one epilogue:

```text
L_fun_exit expects function-frame-shape
```

Every `leave` unwinds to that epilogue. The epilogue alone implements the
calling convention: arrange return values, remove the callee frame, and return
to the caller continuation.

## Compiler Pipeline

Target pipeline:

```text
Yul / higher source
  -> stack-free source semantics
  -> compiler-owned stack layout / continuation contracts
  -> typed CFG
  -> typed assembly / symbolic labels
  -> labeled assembly
  -> EVM bytecode
```

The stack-free source layer above typed CFG should have an independent
interpreter over variables, scopes, expression values, procedure/function
results, and Yul-style control modes. Its compiler is where locals become
symbolic stack slots, where expression arity becomes stack effects, and where
`break`/`continue`/`leave` become unwinds to typed continuations. Once that
compiler boundary is in place, higher layers should not need to mention stack
shape directly.

This layer must still be a real structured-control language, not just a
stack-free expression language. In particular it must include conditionals,
`switch`, `for` loops, `break`, `continue`, `leave`, and terminal EVM halts
with Yul-like mode propagation. Loops own the `break`/`continue` handlers; a
function/procedure layer above or alongside it owns the `leave` handler.

Variables and scopes intentionally arrive in the next layer up. They will
change the compiled stack shape, but that change belongs to the locals
compiler, not to the locals source semantics: a declaration extends the typed
CFG shape with symbolic local slots, assignments update those slots, and every
normal or abrupt block exit unwinds to the enclosing continuation shape. Higher
layers should see only a varstore/scope semantics, while typed CFG sees the
symbolic stack contract that implements it. Concrete `DUP`/`SWAP`/`POP`
sequences are not a higher-layer concern; they belong to the typed CFG backend
that realizes symbolic local-slot operations and unwinds as labeled assembly.

The symbolic local/cleanup effects at the typed CFG boundary are:

- `declareLocal x`: reclassify the current top word as local slot `x`; this is
  a shape-only effect and emits no runtime instruction;
- `loadLocal x depth`: duplicate the checked local slot at `depth`; the backend
  realizes this as the corresponding `DUPn`;
- `storeLocal x depth`: consume the top word and update the checked local slot
  at `depth`; the backend realizes this as `SWAPn; POP`;
- `unwind targetShape`: pop the dead lexical region until the current shape is
  exactly `targetShape`.

The typed CFG semantics now has both a block stepper and a fuelled whole-CFG
runner. Instruction execution is shape-aware: the interpreter checks each
symbolic instruction against the current shape, executes the corresponding EVM
state transition, and threads the output shape forward. In particular,
`unwind` is not a ghost annotation in the semantics; it executes the same
sequence of conceptual pops that the backend lowers to assembly `POP`s.

Procedure/function control is also part of typed CFG, not an assembly-only
convention. A typed CFG program carries procedure metadata:

```text
name, entry label, argument count, return count
```

The checker enforces that the procedure entry label expects exactly its
argument words, that a `call f k` starts with enough argument words and that
return label `k` expects the callee's return words plus the preserved caller
shape, and that `ret f` exits with exactly the declared return words.

The typed CFG interpreter represents calls with a semantic return frame:

```text
call f k : split args from caller tail, run f on args only, remember k + tail
ret f    : attach return values to the remembered caller tail, jump to k
```

This is intentionally cleaner than the concrete EVM implementation. The
typed-CFG-to-assembly lowering realizes the same effect with hidden return
tokens and generated dispatch blocks, so return-token plumbing is quarantined
below typed CFG.

## Yul Surface Audit

The typed CFG should be broad enough that Yul does not force a redesign later:

- ordinary EVM/Yul primitives pass through `TypedCfg.Instr.prim` and reuse the
  shared EVMYulLean primitive semantics;
- nonterminal external interaction opcodes such as `CREATE`, `CALL`,
  `CALLCODE`, `DELEGATECALL`, `CREATE2`, and `STATICCALL` are typed from the
  EVM opcode stack arity table and lower as ordinary primitives;
- terminal opcodes `STOP`, `RETURN`, `REVERT`, and `SELFDESTRUCT` are CFG
  terminators, not ordinary fallthrough instructions, and the checker enforces
  their operand arity;
- Yul `leave` remains a structured function/procedure exit to an epilogue
  continuation, distinct from EVM `RETURN`;
- object/data builtins such as `datasize`, `dataoffset`, and `datacopy` should
  be resolved in the object/frontend layer before typed CFG, so they do not add
  new CFG control semantics.

Internal procedure call/return is now in the typed CFG path. The old direct
assembly convention is no longer the public procedure semantics; it survives
only as the lower backend implementation strategy for typed `call`/`ret`.

Delay clever stack-slot reuse. Use lexical stack regions first; liveness-based
slot reuse can be a later optimization pass with its own proof.

## Current Rule

`break`/`continue`/`leave` are not bare jumps. They are:

```text
unwind to a typed continuation
```

The proof should later follow this architecture rather than force this compiler
back into the old direct AST-to-assembly shape.
