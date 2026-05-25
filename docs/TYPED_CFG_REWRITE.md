# Typed CFG Rewrite

This branch is compiler-first. The proof-heavy modules are archived on
`codex/proof-modules-before-typed-cfg-rewrite`; this branch should refactor the
compiler architecture before rebuilding preservation proofs.

## Core Design

Control flow carries an explicit stack contract. The compiler should not recover
stack shape from generated EVM jumps after the fact.

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
  -> stack-contract source compiler
  -> typed CFG
  -> typed assembly / symbolic labels
  -> labeled assembly
  -> EVM bytecode
```

Delay clever stack-slot reuse. Use lexical stack regions first; liveness-based
slot reuse can be a later optimization pass with its own proof.

## Current Rule

`break`/`continue`/`leave` are not bare jumps. They are:

```text
unwind to a typed continuation
```

The proof should later follow this architecture rather than force this compiler
back into the old direct AST-to-assembly shape.
