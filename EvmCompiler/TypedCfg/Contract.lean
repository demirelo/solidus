import EvmCompiler.TypedCfg.Semantics

namespace EvmCompiler
namespace TypedCfg

/-!
Execution contract for the typed stack CFG.

This layer is the stack-quarantine boundary below StackFreeCfg. Its public
semantics may mention stack shapes, labels, and typed procedure control. Higher
source layers should not import those concepts directly; they should go through
their adjacent compiler relation.
-/

namespace Program

/--
The raw executor only gives a meaningful suspension when the program is
unambiguous and the current label is a valid block boundary for the current
runtime stack.
-/
def CanSuspendAt (program : Program) (label : Label) (state : RunState) : Prop :=
  program.runtimeWellFormed? = true ∧
    ∃ block,
      program.findBlock? label = some block ∧
        block.input.matchesStack state.evm.stack = true

/--
Minimal public classification of typed-CFG outcomes.

The full `Outcome` intentionally remains available at this layer because this
is where labels, stacks, and return frames are part of the semantics. This
classification is mainly a stable guide for adjacent proof statements.
-/
inductive OutcomeClass where
  | fallthrough
  | jump
  | halt
  | invalid
  | outOfFuel
  deriving DecidableEq, Repr

def classifyOutcome : Outcome → OutcomeClass
  | .fallthrough _ => .fallthrough
  | .jump _ _ => .jump
  | .halt _ _ => .halt
  | .invalid _ => .invalid
  | .outOfFuel _ _ => .outOfFuel

end Program

end TypedCfg
end EvmCompiler
