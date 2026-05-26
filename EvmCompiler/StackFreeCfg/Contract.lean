import EvmCompiler.StackFreeCfg.Semantics

namespace EvmCompiler
namespace StackFreeCfg

/-!
Source-facing contract for `StackFreeCfg`.

This module intentionally contains no lowering facts and no references to
`TypedCfg`. It is the public surface that higher layers and bridge proofs should
use when talking about StackFreeCfg execution results.
-/

/--
The observable source result of a StackFreeCfg run.

The varstore is always scoped to `scope`. This makes lexical cleanup part of
the observation contract, including abrupt control flow and resource exhaustion.
Lower-layer implementation details such as stack slots, labels, return tokens,
or byte offsets are deliberately absent.
-/
structure Observation where
  shared : SharedState
  vars : Store.T
  scope : List Name
  mode : Mode

namespace Observation

def ofOutcome (outcome : Outcome) : Observation :=
  { shared := outcome.state.shared
    vars := Store.restrictTo outcome.scope outcome.state.vars
    scope := outcome.scope
    mode := outcome.mode }

def regular? (obs : Observation) : Bool :=
  obs.mode == .regular

def terminal? (obs : Observation) : Bool :=
  match obs.mode with
  | .halt _ => true
  | _ => false

def abrupt? (obs : Observation) : Bool :=
  match obs.mode with
  | .brk | .cont | .leave => true
  | _ => false

def resource? (obs : Observation) : Bool :=
  obs.mode == .outOfFuel

def invalid? (obs : Observation) : Bool :=
  obs.mode == .invalid

end Observation

def observeResult : Except Exception Outcome → Except Exception Observation
  | .ok outcome => .ok (Observation.ofOutcome outcome)
  | .error error => .error error

namespace Program

/--
Run a program and immediately project to the source-facing observation.

This is the preferred boundary for theorem statements above StackFreeCfg.
Preservation proofs below this layer may mention layouts and stacks internally,
but higher layers should relate to this projection.
-/
def runObserved (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (shared : SharedState) : Except Exception Observation :=
  observeResult (EvmCompiler.StackFreeCfg.Program.run prim fuel program shared)

def runStateObserved (prim : PrimitiveSemantics) (fuel : Nat)
    (program : Program) (state : State) : Except Exception Observation :=
  observeResult
    (EvmCompiler.StackFreeCfg.Program.runState prim fuel program state)

end Program

end StackFreeCfg
end EvmCompiler
