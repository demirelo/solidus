import EvmCompiler.Yul.Syntax
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace Yul

abbrev ReferenceState := EvmYul.Yul.State
abbrev ReferenceException := EvmYul.Yul.Exception

inductive ReferenceResult where
  | regular (state : ReferenceState)
  | yulHalt (state : ReferenceState) (value : Word)
  | revert (stateBeforeRevert : ReferenceState)

namespace Program

def installContract (program : Program) : ReferenceState → ReferenceState
  | .Ok shared store =>
      .Ok
        { shared with
          executionEnv :=
            { shared.executionEnv with code := program.contract } }
        store
  | .OutOfFuel => .OutOfFuel
  | .Checkpoint jump => .Checkpoint jump

def runRegular (fuel : Nat) (program : Program) (state : ReferenceState) :
    Except ReferenceException ReferenceState :=
  match
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) with
  | .ok (state', _rets) => .ok state'
  | .error exception => .error exception

/--
Independent Yul source interpreter for the imported Nethermind AST.
-/
def run (fuel : Nat) (program : Program) (state : ReferenceState) :
    Except ReferenceException ReferenceResult :=
  match
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) with
  | .ok (state', _rets) => .ok (.regular state')
  | .error (.YulHalt state' value) => .ok (.yulHalt state' value)
  | .error (.Revert stateBeforeRevert) => .ok (.revert stateBeforeRevert)
  | .error exception => .error exception

end Program

end Yul
end EvmCompiler
