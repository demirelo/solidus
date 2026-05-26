# Typed CFG Rewrite

This branch is compiler-first. The proof-heavy modules are archived on
`codex/proof-modules-before-typed-cfg-rewrite`; this branch should refactor the
compiler architecture before rebuilding preservation proofs.

## Core Design

Control flow carries an explicit stack contract. The compiler should not recover
stack shape from generated EVM jumps after the fact.

This document uses "CFG" in the typed stack-machine sense. The current
`EvmCompiler.TypedCfg` is **not** the layer that abstracts the stack away from
its own syntax. It is the stack-quarantine layer: symbolic stack shapes become
explicit, checked, and then lowered to concrete EVM stack code.

The abstraction goal is one layer higher. Layers above typed CFG should not
expose concrete stack slots, raw `DUP`/`SWAP`/`POP`, return-token encodings, or
bytecode jumps in their source semantics. If we want a CFG that is itself
stack-free, it should sit above this typed stack CFG and lower into it.

Put differently:

```text
stack-free source/control/locals/functions semantics
  -> typed stack CFG with explicit symbolic shapes and stack effects
  -> labeled assembly
  -> concrete EVM bytecode
```

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

The current `EvmCompiler.Control` module is a first stack-free structured
control source layer with an independent interpreter. It is not yet the full
stack-free CFG/block-parameter abstraction we want for the rest of the tower.
That future layer should have no `pop`/`dup`/`swap`, no stack shapes, no return
tokens, and no bytecode jumps in its source semantics. Its blocks should talk
in terms of source values, variables, scopes, control modes, and procedure
results; its compiler should be the only place that chooses typed-CFG shapes,
local depths, unwinds, and procedure entry/return layouts.

A good target shape for that layer is:

```text
StackFreeCfg.Program
  procedures : name -> params/results/body
  blocks     : label -> statements + source-level terminator

Statement effects:
  primitive expression/statement effects over source values and EVM state
  lexical scope entry/exit over a varstore
  assignment/declaration/function-call binding once locals/functions are added

Terminators:
  goto label
  branch condition thenLabel elseLabel
  switch value cases defaultLabel
  break / continue / leave as Yul-style modes at structured boundaries
  procedure return with result values
  terminal EVM halt
```

The compiler from this stack-free CFG to `TypedCfg` should establish the first
real stack abstraction theorem: every source continuation/value environment is
realized by a declared typed-CFG shape, and every source control transfer lowers
to an `unwind` plus typed jump/call/ret without exposing that machinery above
the boundary.

## Stack-Free CFG Design

The next layer should be stack-free in its syntax, semantics, and public proof
interface. It can still compile to `TypedCfg`, but no theorem above this layer
should mention typed-CFG shapes, stack depths, concrete stack tails, `DUP`,
`SWAP`, `POP`, or return tokens.

A good source state for this layer is:

```text
State = {
  evm      : shared EVM/Yul state with the runtime stack hidden by invariant,
  store    : Name -> Option Word,
  scopes   : lexical scope stack / visible-name set,
  procs    : procedure environment
}
```

The source semantics may reuse the shared primitive EVM/Yul meaning, but only
through value-level adapters:

```text
evalExpr(e, state) : Except Error (state, values)
runPrimitive(op, args, state) : Except Error (state, values)
runTerminal(kind, args, state) : Except Error (halted state)
```

Expression evaluation returns values, not stack fragments.

Suggested syntax:

```text
Program ::= procedures + main Block

Proc ::= name, params, returns, body Block

Block ::= List Stmt

Stmt ::=
  | expr(op, args)                    -- zero-result primitive statement
  | let(names, optional expr)          -- initializes locals in current scope
  | assign(names, expr)                -- updates existing locals
  | if(cond, thenBlock)
  | switch(scrutinee, cases, default?)
  | for(initBlock, cond, postBlock, bodyBlock)
  | break
  | continue
  | leave
  | call(optional result names, name, args)
  | terminal(kind, args)               -- STOP/RETURN/REVERT/SELFDESTRUCT
  | block(body)                        -- only if we need explicit bracketed
                                       -- lexical scope as a statement
```

If we keep this as a structured layer, `if`/`switch`/`for` stay as statements.
If we later normalize it to a true block-parameter CFG, the equivalent
terminators are:

```text
goto label(args)
branch cond thenLabel(args) elseLabel(args)
switch value cases defaultLabel(args)
returnProcedure(values)
halt(kind, args)
```

The important abstraction is the same in either presentation: block parameters
and variables are source values, not stack slots.

Outcomes:

```text
Outcome ::=
  | regular(state)
  | break(state)
  | continue(state)
  | leave(state)
  | returned(values, state)            -- for procedure body semantics if useful
  | halt(kind, state)
  | error(error, state)
  | outOfFuel(state)
```

Yul `leave` remains distinct from EVM `RETURN`: `leave` exits the current
procedure through its declared return variables; EVM `RETURN` is a terminal
halt.

Block semantics should own lexical cleanup:

```text
runBlock(fuel, block, state):
  push lexical scope
  run statements
  on regular/break/continue/leave/halt/error:
    restrict/drop locals introduced by the block
    propagate the same mode
```

Loop semantics installs source-level handlers:

```text
for init cond post body:
  run init; break/continue from init is invalid
  while cond != 0:
    run body
      regular/continue -> run post, then loop
      break            -> regular after loop
      leave/halt/error -> propagate
    break/continue from post is invalid
```

Procedure semantics:

```text
call f(args):
  evaluate args in Yul order
  create a fresh procedure store containing params and zeroed returns
  run f.body
  on regular or leave:
    read declared return variables
    restore caller store/scope
    bind returned values at the call site
  on halt/error:
    propagate terminal/error state
  break/continue escaping a procedure is invalid
```

This source procedure model intentionally has no return PC, return token, or
caller stack tail. The compiler to `TypedCfg` is responsible for choosing the
procedure entry shape, epilogue label, return continuation, and `call`/`ret`
lowering.

### Successor Theorem Shape

Yes: this layer should be proved with a recursive successor theorem for
statement sequences. The public theorem should be about source runs and the
compiled typed CFG, but the recursion should be statement-list shaped.

For a statement sequence:

```text
SeqSound(layout, ctx, stmts, entryLabel, exitKont)
```

means:

```text
For any source state σ and target run state τ related by layout,
running the compiled typed CFG from entryLabel simulates runBlock/runSeq:

regular σ'   -> reaches the regular continuation with τ' related to σ'
break σ'     -> reaches ctx.break with τ' related to σ'
continue σ'  -> reaches ctx.continue with τ' related to σ'
leave σ'     -> reaches ctx.leave with τ' related to σ'
halt kind σ' -> typed CFG halts with the same terminal observation
error/outOfFuel -> maps to the explicit target error/resource policy
```

The successor rule should be:

```text
SeqSound(ctx, []).

SeqSound(ctx, s :: rest) follows from:
  HeadSound(ctx with regular = tailEntry, s)
  TailSound(ctx, rest, tailEntry)
```

with the critical split:

```text
if s runs regular:
  target reaches tailEntry, then TailSound proves rest

if s runs break/continue/leave/halt/error:
  target reaches the appropriate continuation/terminal result,
  and rest is ignored
```

This is the compositional proof shape we want. It avoids one monolithic CFG
replay certificate and mirrors Yul's own mode-propagating statement semantics.

### Compiler Responsibility

The compiler from this stack-free layer to `TypedCfg` owns all stack facts:

```text
source variables/results/live values
  -> typed-CFG Shape
  -> local depths for load/store
  -> unwind target shape for every abrupt edge
  -> procedure entry/return shapes
  -> typed call/ret labels
```

Those facts should appear in the compiler's layout relation and preservation
proof, not in the stack-free source interpreter and not in any higher layer's
theorem statement.

Variables and scopes are now part of `StackFreeCfg`, the first stack-free
source layer above typed CFG. Its source semantics is a varstore/scope
interpreter: declarations extend the visible source environment, assignments
update named variables, and block/loop/procedure exits restrict the varstore
back to the source-visible scope. The compiler from `StackFreeCfg` to
`TypedCfg` is the only layer that maps those source variables to symbolic stack
slots. Higher layers should see only the varstore/scope semantics, while typed
CFG sees the symbolic stack contract that implements it. Concrete
`DUP`/`SWAP`/`POP` sequences are not a higher-layer concern; they belong to the
typed CFG backend that realizes symbolic local-slot operations and unwinds as
labeled assembly.

The symbolic local/cleanup effects at the typed CFG boundary are:

- `declareLocal x`: reclassify the current top word as local slot `x`; this is
  a shape-only effect and emits no runtime instruction;
- `declareLocals xs`: reclassify the top `xs.length` words as a lexical group
  of source locals in source order, reversing the top segment so local lookup
  by name agrees with multi-value declarations;
- `initLocals xs`: push zero-initialized local slots for procedure return
  variables;
- `loadLocal x depth`: duplicate the checked local slot at `depth`; the backend
  realizes this as the corresponding `DUPn`;
- `storeLocal x depth`: consume the top word and update the checked local slot
  at `depth`; the backend realizes this as `SWAPn; POP`;
- `assignLocals xs`: consume `xs.length` result values and update the existing
  checked local slots by name;
- `returnLocals xs`: gather the named return locals in source order and discard
  the callee frame, producing exactly the procedure return values;
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
call f k : split args from caller tail, run f on args only, remember f + k + tail
ret f    : require the top frame is for f, attach return values to its tail, jump to k
```

This is intentionally cleaner than the concrete EVM implementation. The
typed-CFG-to-assembly lowering realizes the same effect with hidden return
tokens and generated dispatch blocks, so return-token plumbing is quarantined
below typed CFG.

There are two backend entry points:

- `CheckedProgram.lower?` produces labeled assembly, preserving symbolic labels
  for the existing assembly layer. This backend is partial for procedure
  arities that cannot be realized with the current `DUP`/`SWAP` token-dispatch
  convention.
- `CheckedProgram.assemble?` additionally runs the labeled-assembly acceptedness
  and assembler gate, so generated dispatch-label collisions or unresolved
  jumps fail at the typed-CFG backend boundary.

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
  new CFG control semantics;
- raw `PC` should not be exposed above typed CFG. Yul has no `pc` builtin, and
  any future source-level PC-like operation should be modeled as an explicit
  oracle rather than by reusing the isolated primitive adapter's synthetic
  program counter.

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
