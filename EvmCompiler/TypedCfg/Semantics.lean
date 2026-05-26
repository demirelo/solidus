import EvmCompiler.TypedCfg.Typing

namespace EvmCompiler
namespace TypedCfg

inductive Outcome where
  | fallthrough (state : EVMState)
  | jump (target : Label) (state : EVMState)
  | returnDispatch (state : EVMState)
  | halt (kind : Assembly.HaltKind) (state : EVMState)
  | invalid (state : EVMState)

namespace Instr

def run (instr : Instr) (state : EVMState) : Except EVMException EVMState :=
  match instr with
  | .push value =>
      .ok (state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33))
  | .prim op =>
      op.step state
  | .pop =>
      Assembly.PrimOp.pop.step state
  | .dup depth =>
      match depth with
      | 0 => Assembly.PrimOp.dup1.step state
      | 1 => Assembly.PrimOp.dup2.step state
      | 2 => Assembly.PrimOp.dup3.step state
      | 3 => Assembly.PrimOp.dup4.step state
      | 4 => Assembly.PrimOp.dup5.step state
      | 5 => Assembly.PrimOp.dup6.step state
      | 6 => Assembly.PrimOp.dup7.step state
      | 7 => Assembly.PrimOp.dup8.step state
      | 8 => Assembly.PrimOp.dup9.step state
      | 9 => Assembly.PrimOp.dup10.step state
      | 10 => Assembly.PrimOp.dup11.step state
      | 11 => Assembly.PrimOp.dup12.step state
      | 12 => Assembly.PrimOp.dup13.step state
      | 13 => Assembly.PrimOp.dup14.step state
      | 14 => Assembly.PrimOp.dup15.step state
      | _ => Assembly.PrimOp.dup16.step state
  | .swap depth =>
      match depth with
      | 0 => Assembly.PrimOp.swap1.step state
      | 1 => Assembly.PrimOp.swap2.step state
      | 2 => Assembly.PrimOp.swap3.step state
      | 3 => Assembly.PrimOp.swap4.step state
      | 4 => Assembly.PrimOp.swap5.step state
      | 5 => Assembly.PrimOp.swap6.step state
      | 6 => Assembly.PrimOp.swap7.step state
      | 7 => Assembly.PrimOp.swap8.step state
      | 8 => Assembly.PrimOp.swap9.step state
      | 9 => Assembly.PrimOp.swap10.step state
      | 10 => Assembly.PrimOp.swap11.step state
      | 11 => Assembly.PrimOp.swap12.step state
      | 12 => Assembly.PrimOp.swap13.step state
      | 13 => Assembly.PrimOp.swap14.step state
      | 14 => Assembly.PrimOp.swap15.step state
      | _ => Assembly.PrimOp.swap16.step state
  | .unwind _target =>
      .ok state

end Instr

namespace Block

def runBody : List Instr → EVMState → Except EVMException EVMState
  | [], state => .ok state
  | instr :: rest, state => do
      let state' ← instr.run state
      runBody rest state'

def runTerm (term : Terminator) (state : EVMState) : Outcome :=
  match term with
  | .fallthrough => .fallthrough state
  | .jump target => .jump target state
  | .jumpi target fallthrough =>
      match state.stack.pop with
      | none => .invalid state
      | some (stack, cond) =>
          let state' := { state with stack := stack }
          if cond = EvmYul.UInt256.ofNat 0 then
            .jump fallthrough state'
          else
            .jump target state'
  | .returnDispatch _ => .returnDispatch state
  | .halt kind => .halt kind state
  | .invalid => .invalid state

def run (block : Block) (state : EVMState) :
    Except EVMException Outcome := do
  let state' ← runBody block.body state
  .ok (runTerm block.term state')

end Block

namespace Program

def step (program : Program) (label : Label) (state : EVMState) :
    Except EVMException Outcome :=
  match program.findBlock? label with
  | none => .ok (.invalid state)
  | some block => block.run state

end Program

end TypedCfg
end EvmCompiler
