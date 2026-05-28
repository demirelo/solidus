import EvmCompiler.Objects.Compiler
import EvmCompiler.Functions.GasParametric

namespace EvmCompiler
namespace Objects

namespace Object

def run (fuel : Nat) : Object → EVMState → Except EVMException Outcome
  | .mk _name code _data _objects, state =>
      Functions.Program.run fuel code state

def runWithGasOracle (fuel : Nat) : Object → Structured.GasOracle → Nat →
    EVMState → Except EVMException (Outcome × Nat)
  | .mk _name code _data _objects, oracle, cursor, state =>
      Functions.Program.runWithGasOracle fuel code oracle cursor state

inductive Eval :
    Nat → Object → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {object : Object}
      {initial : EVMState} {outcome : Outcome}
      (hRun : object.run fuel initial = .ok outcome) :
      Eval fuel object initial outcome

theorem eval_of_run {fuel : Nat} {object : Object}
    {initial : EVMState} {outcome : Outcome}
    (hRun : object.run fuel initial = .ok outcome) :
    Eval fuel object initial outcome := by
  exact Eval.ofRun hRun

end Object

namespace Program

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  program.root.run fuel state

def runWithGasOracle (fuel : Nat) (program : Program)
    (oracle : Structured.GasOracle) (cursor : Nat) (state : EVMState) :
    Except EVMException (Outcome × Nat) :=
  program.root.runWithGasOracle fuel oracle cursor state

inductive Eval :
    Nat → Program → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program}
      {initial : EVMState} {outcome : Outcome}
      (hRun : run fuel program initial = .ok outcome) :
      Eval fuel program initial outcome

theorem eval_of_run {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hRun : run fuel program initial = .ok outcome) :
    Eval fuel program initial outcome := by
  exact Eval.ofRun hRun

end Program

end Objects
end EvmCompiler
