import EvmCompiler.StackFreeCfg.Semantics

namespace EvmCompiler
namespace StackFreeCfg

/-!
Canonical primitive adapter for StackFreeCfg.

The core StackFreeCfg interpreter is stack-free and parametric in
`PrimitiveSemantics`. This file is the explicit boundary that reuses the shared
EVM/Yul primitive semantics by running a primitive on an isolated argument
vector and projecting only shared state plus result values back to StackFreeCfg.
-/

abbrev EVMState := Assembly.EVMState

def liftPrimitive {α : Type} :
    Except Assembly.EVMException α → Except Exception α
  | .ok value => .ok value
  | .error error => .error (.primitive error)

namespace PrimitiveSemantics

def rejectedSourceOp : Assembly.PrimOp → Bool
  | .pc
  | .dup1 | .dup2 | .dup3 | .dup4
  | .dup5 | .dup6 | .dup7 | .dup8
  | .dup9 | .dup10 | .dup11 | .dup12
  | .dup13 | .dup14 | .dup15 | .dup16
  | .swap1 | .swap2 | .swap3 | .swap4
  | .swap5 | .swap6 | .swap7 | .swap8
  | .swap9 | .swap10 | .swap11 | .swap12
  | .swap13 | .swap14 | .swap15 | .swap16 => true
  | _ => false

def isolatedState (shared : SharedState) (args : List Word) : EVMState :=
  { toSharedState := shared
    pc := EvmYul.UInt256.ofNat 0
    stack := args
    execLength := 0 }

def canonical : PrimitiveSemantics where
  eval op shared args := do
    if rejectedSourceOp op || op.haltKind?.isSome then
      invalid
    else
      match op.stackEffect? with
      | none => invalid
      | some (inputArity, outputArity) =>
          if args.length = inputArity then
            let state' ← liftPrimitive (op.step (isolatedState shared args))
            if state'.stack.length = outputArity then
              .ok (state'.toSharedState, state'.stack)
            else
              invalid
          else
            invalid
  terminal kind shared args := do
    if args.length = kind.argCount then
      let state' ←
        liftPrimitive (kind.toPrimOp.step (isolatedState shared args))
      .ok state'.toSharedState
    else
      invalid

end PrimitiveSemantics

namespace Program

def runCanonical (fuel : Nat) (program : Program) (shared : SharedState) :
    Except Exception Outcome :=
  runState PrimitiveSemantics.canonical fuel program { shared := shared }

end Program

end StackFreeCfg
end EvmCompiler
