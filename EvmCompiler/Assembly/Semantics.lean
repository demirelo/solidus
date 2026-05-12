import EvmCompiler.Assembly.Assembler
import EvmYul.Semantics
import EvmYul.EVM.State
import EvmYul.EVM.StateOps

namespace EvmCompiler
namespace Assembly

abbrev EVMState := EvmYul.EVM.State
abbrev EVMException := EvmYul.EVM.ExecutionException

namespace Target

def stepInstr (instr : TargetInstr) (state : EVMState) : Except EVMException EVMState :=
  match instr with
  | .push32 value =>
      .ok <| state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33)
  | .jump =>
    match state.stack.pop with
    | some (stack, dest) =>
        .ok { state with pc := dest, stack := stack }
    | none =>
        .error .StackUnderflow
  | .jumpi =>
    match state.stack.pop2 with
    | some (stack, dest, cond) =>
        let pc' :=
          if cond != EvmYul.UInt256.ofNat 0 then
            dest
          else
            state.pc + EvmYul.UInt256.ofNat 1
        .ok { state with pc := pc', stack := stack }
    | none =>
        .error .StackUnderflow
  | .jumpdest =>
      .ok state.incrPC
  | .prim op =>
      EvmYul.step op.toEVM none state

def runList : List TargetInstr → EVMState → Except EVMException EVMState
  | [], state => .ok state
  | instr :: rest, state => do
      let state' ← stepInstr instr state
      runList rest state'

def step (target : TargetProgram) (state : EVMState) : Except EVMException EVMState :=
  match target.fetch state.pc.toNat with
  | some instr => stepInstr instr state
  | none => .error .InvalidInstruction

def runN (target : TargetProgram) : Nat → EVMState → Except EVMException EVMState
  | 0, state => .ok state
  | fuel + 1, state => do
      let state' ← step target state
      runN target fuel state'

end Target

namespace Source

def invalid {α : Type} : Except EVMException α :=
  .error .InvalidInstruction

def jumpPc (dest : Nat) (state : EVMState) : EVMState :=
  { state with pc := EvmYul.UInt256.ofNat dest }

def jumpiFallthroughPc (state : EVMState) : Word :=
  state.pc + EvmYul.UInt256.ofNat Instr.push32Size + EvmYul.UInt256.ofNat 1

def stepAt (program : Program) (_pc : Nat) (instr : Instr)
    (state : EVMState) : Except EVMException EVMState :=
  match instr with
  | .label _ =>
      Target.stepInstr TargetInstr.jumpdest state
  | .prim op =>
      Target.stepInstr (TargetInstr.prim op) state
  | .push value =>
      Target.stepInstr (TargetInstr.push32 value) state
  | .jump target => do
      let dest ← (Program.labelPc program target).elim invalid pure
      pure (jumpPc dest state)
  | .jumpi target => do
      let dest ← (Program.labelPc program target).elim invalid pure
      match state.stack.pop with
      | some (stack, cond) =>
          let pc' :=
            if cond != EvmYul.UInt256.ofNat 0 then
              EvmYul.UInt256.ofNat dest
            else
              jumpiFallthroughPc state
          pure { state with pc := pc', stack := stack }
      | none =>
          .error .StackUnderflow

def step (program : Program) (state : EVMState) : Except EVMException EVMState :=
  match Program.instrAtPc program state.pc.toNat with
  | some (pc, instr) => stepAt program pc instr state
  | none => .error .InvalidInstruction

end Source

def emitCurrent? (program : Program) (state : EVMState) : Option (List TargetInstr) := do
  let (pc, instr) ← Program.instrAtPc program state.pc.toNat
  let located ← emitInstr? program pc instr
  some (located.map LocatedTarget.instr)

/--
The observable state relation for the gasless layer.

The first verified slice actually proves exact equality against the gasless
target semantics. This projection names the intended claim boundary for the
later full-EVM theorem, where EVM gas accounting and execution counters will be
erased before comparison.
-/
def eraseGas (state : EVMState) : EVMState :=
  { state with
    gasAvailable := EvmYul.UInt256.ofNat 0
    execLength := 0
  }

end Assembly
end EvmCompiler
