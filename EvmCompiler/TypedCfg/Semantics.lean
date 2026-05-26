import EvmCompiler.TypedCfg.Typing

namespace EvmCompiler
namespace TypedCfg

structure ReturnFrame where
  procName : Name
  returnLabel : Label
  callerStack : EvmYul.Stack Word
  retc : Nat

structure RunState where
  evm : EVMState
  returns : List ReturnFrame := []

namespace RunState

def initial (state : EVMState) : RunState where
  evm := state
  returns := []

def withEVM (state : RunState) (evm : EVMState) : RunState :=
  { state with evm := evm }

def pushReturn (state : RunState) (procName : Name) (returnLabel : Label)
    (callerStack : EvmYul.Stack Word) (retc : Nat) : RunState :=
  { state with
    returns := { procName, returnLabel, callerStack, retc } :: state.returns }

def popReturn? (state : RunState) : Option (ReturnFrame × RunState) :=
  match state.returns with
  | [] => none
  | frame :: rest => some (frame, { state with returns := rest })

end RunState

namespace StackFrame

def splitArgs? (argc : Nat) (stack : EvmYul.Stack Word) :
    Option (EvmYul.Stack Word × EvmYul.Stack Word) :=
  if argc ≤ stack.length then
    some (stack.take argc, stack.drop argc)
  else
    none

def attachReturns? (frame : ReturnFrame) (stack : EvmYul.Stack Word) :
    Option (EvmYul.Stack Word) :=
  if stack.length = frame.retc then
    some (stack ++ frame.callerStack)
  else
    none

end StackFrame

namespace Slot

def matchesValue (slot : Slot) (value : Word) : Bool :=
  match slot with
  | .literal expected => value == expected
  | .word | .local _ | .temp _ _ | .returnPC _ | .returnValue _ _ => true

end Slot

namespace Shape

def matchesStack : Shape → EvmYul.Stack Word → Bool
  | [], [] => true
  | slot :: shapeRest, value :: stackRest =>
      slot.matchesValue value && matchesStack shapeRest stackRest
  | _, _ => false

end Shape

inductive Outcome where
  | fallthrough (state : RunState)
  | jump (target : Label) (state : RunState)
  | halt (kind : Assembly.HaltKind) (state : RunState)
  | invalid (state : RunState)

namespace Instr

namespace StackOps

def pushZeros : Nat → EvmYul.Stack Word → EvmYul.Stack Word
  | 0, stack => stack
  | n + 1, stack => pushZeros n (EvmYul.UInt256.ofNat 0 :: stack)

def replaceFirst? (name : Name) (value : Word) :
    Shape → EvmYul.Stack Word → Option (EvmYul.Stack Word)
  | [], [] => none
  | .local slotName :: shapeRest, old :: stackRest =>
      if slotName = name then
        some (value :: stackRest)
      else do
        let updated ← replaceFirst? name value shapeRest stackRest
        some (old :: updated)
  | _slot :: shapeRest, old :: stackRest => do
      let updated ← replaceFirst? name value shapeRest stackRest
      some (old :: updated)
  | _, _ => none

def assignValues? : List Name → List Word → Shape → EvmYul.Stack Word →
    Option (EvmYul.Stack Word)
  | [], [], _shape, stack => some stack
  | name :: names, value :: values, shape, stack => do
      let stack' ← replaceFirst? name value shape stack
      assignValues? names values shape stack'
  | _, _, _, _ => none

def readLocal? (name : Name) : Shape → EvmYul.Stack Word → Option Word
  | [], [] => none
  | .local slotName :: shapeRest, value :: stackRest =>
      if slotName = name then
        some value
      else
        readLocal? name shapeRest stackRest
  | _slot :: shapeRest, _value :: stackRest =>
      readLocal? name shapeRest stackRest
  | _, _ => none

def readLocals? (names : List Name) (shape : Shape)
    (stack : EvmYul.Stack Word) : Option (EvmYul.Stack Word) :=
  match names with
  | [] => some []
  | name :: rest => do
      let value ← readLocal? name shape stack
      let values ← readLocals? rest shape stack
      some (value :: values)

end StackOps

def runPopMany : Nat → EVMState → Except EVMException EVMState
  | 0, state => .ok state
  | n + 1, state => do
      let state' ← Assembly.PrimOp.pop.step state
      runPopMany n state'

def runDup (depth : Nat) (state : EVMState) : Except EVMException EVMState :=
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
  | 15 => Assembly.PrimOp.dup16.step state
  | _ => .error .InvalidInstruction

def runSwap (depth : Nat) (state : EVMState) :
    Except EVMException EVMState :=
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
  | 15 => Assembly.PrimOp.swap16.step state
  | _ => .error .InvalidInstruction

def run (instr : Instr) (state : EVMState) : Except EVMException EVMState :=
  match instr with
  | .push value =>
      .ok (state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33))
  | .prim op =>
      op.step state
  | .pop =>
      Assembly.PrimOp.pop.step state
  | .dup depth =>
      runDup depth state
  | .swap depth =>
      runSwap depth state
  | .declareLocal _name =>
      .ok state
  | .declareLocals names =>
      if names.length ≤ state.stack.length then
        .ok state
      else
        .error .StackUnderflow
  | .initLocals names =>
      .ok { state with stack := StackOps.pushZeros names.length state.stack }
  | .loadLocal _name depth =>
      runDup depth state
  | .storeLocal _name depth => do
      let state' ← runSwap depth state
      Assembly.PrimOp.pop.step state'
  | .assignLocals _names =>
      .error .InvalidInstruction
  | .returnLocals _names =>
      .error .InvalidInstruction
  | .unwind _target =>
      .error .InvalidInstruction

def runWithShape? (instr : Instr) (shape : Shape) (state : EVMState) :
    Except EVMException (EVMState × Shape) :=
  match instr.type? shape with
  | none => .error .InvalidInstruction
  | some output => do
      let state' ←
        match instr with
        | .unwind target =>
            runPopMany (shape.length - target.length) state
        | .assignLocals names =>
            if names.length ≤ state.stack.length then
              let values := state.stack.take names.length
              let rest := state.stack.drop names.length
              let shapeRest := Shape.pop names.length shape
              match StackOps.assignValues? names values shapeRest rest with
              | some stack => .ok { state with stack := stack }
              | none => .error .InvalidInstruction
            else
              .error .StackUnderflow
        | .returnLocals names =>
            match StackOps.readLocals? names shape state.stack with
            | some stack => .ok { state with stack := stack }
            | none => .error .InvalidInstruction
        | _ =>
            instr.run state
      .ok (state', output)

end Instr

namespace Block

def runBodyWithShape? :
    List Instr → Shape → EVMState → Except EVMException (EVMState × Shape)
  | [], shape, state => .ok (state, shape)
  | instr :: rest, shape, state => do
      let (state', shape') ← instr.runWithShape? shape state
      runBodyWithShape? rest shape' state'

def runBody (body : List Instr) (state : EVMState) :
    Except EVMException EVMState := do
  let (state', _shape) ← runBodyWithShape? body [] state
  .ok state'

def runTerm (program : Program) (term : Terminator) (state : RunState) :
    Except EVMException Outcome :=
  match term with
  | .fallthrough => .ok (.fallthrough state)
  | .jump target => .ok (.jump target state)
  | .jumpi target fallthrough =>
      match state.evm.stack.pop with
      | none => .ok (.invalid state)
      | some (stack, cond) =>
          let state' := state.withEVM { state.evm with stack := stack }
          if cond = EvmYul.UInt256.ofNat 0 then
            .ok (.jump fallthrough state')
          else
            .ok (.jump target state')
  | .call name returnLabel =>
      match program.findProc? name with
      | none => .ok (.invalid state)
      | some proc =>
          match StackFrame.splitArgs? proc.argc state.evm.stack with
          | none => .error .StackUnderflow
          | some (args, callerStack) =>
              let evm := { state.evm with stack := args }
              let state' :=
                (state.withEVM evm).pushReturn name returnLabel callerStack
                  proc.retc
              .ok (.jump proc.entry state')
  | .ret name =>
      match program.findProc? name, state.popReturn? with
      | some proc, some (frame, returned) =>
          if frame.procName = name ∧ frame.retc = proc.retc then
            match StackFrame.attachReturns? frame state.evm.stack with
            | none => .ok (.invalid state)
            | some stack =>
                let evm := { state.evm with stack := stack }
                .ok (.jump frame.returnLabel (returned.withEVM evm))
          else
            .ok (.invalid state)
      | _, _ => .ok (.invalid state)
  | .halt kind => do
      let evm ← kind.toPrimOp.step state.evm
      let state' := state.withEVM evm
      .ok (.halt kind state')
  | .invalid => .ok (.invalid state)

def run (program : Program) (block : Block) (state : RunState) :
    Except EVMException Outcome := do
  if !block.input.matchesStack state.evm.stack then
    .ok (.invalid state)
  else
  let (evm, _shape) ← runBodyWithShape? block.body block.input state.evm
  runTerm program block.term (state.withEVM evm)

end Block

namespace Program

def step (program : Program) (label : Label) (state : RunState) :
    Except EVMException Outcome :=
  match program.findBlock? label with
  | none => .ok (.invalid state)
  | some block => block.run program state

def runFrom : Nat → Program → Label → RunState → Except EVMException Outcome
  | 0, _program, _label, state => .ok (.invalid state)
  | fuel + 1, program, label, state => do
      let outcome ← step program label state
      match outcome with
      | .jump target state' => runFrom fuel program target state'
      | .fallthrough _ | .halt _ _ | .invalid _ =>
          .ok outcome

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  runFrom fuel program program.entry (RunState.initial state)

end Program

end TypedCfg
end EvmCompiler
