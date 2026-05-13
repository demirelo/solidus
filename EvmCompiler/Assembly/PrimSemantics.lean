import EvmCompiler.Assembly.Assembler
import EvmYul.Semantics
import EvmYul.EVM.State
import EvmYul.EVM.StateOps

namespace EvmCompiler
namespace Assembly

/--
Small semantic families for EVM primitives that can be sequenced as ordinary
non-control instructions.

This classifier is deliberately separate from `PrimOp.toEVM`: byte encoding
still records the concrete EVM opcode, while proofs can reason through these
compact public EVMYul helper functions instead of unfolding the full
`EvmYul.step` dispatcher.
-/
inductive PrimStep where
  | bin (f : EvmYul.Primop.Binary)
  | un (f : EvmYul.Primop.Unary)
  | tri (f : EvmYul.Primop.Ternary)
  | executionEnv
      (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
  | unaryExecutionEnv
      (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
  | machineState (f : EvmYul.MachineState → Word)
  | binaryMachineState
      (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
  | binaryMachineStateWithResult
      (f : EvmYul.MachineState → Word → Word → Word × EvmYul.MachineState)
  | ternaryMachineState
      (f : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
  | state (f : EvmYul.State EvmYul.OperationType.EVM → Word)
  | unaryState
      (f : EvmYul.State EvmYul.OperationType.EVM → Word →
        EvmYul.State EvmYul.OperationType.EVM × Word)
  | binaryState
      (f : EvmYul.State EvmYul.OperationType.EVM → Word → Word →
        EvmYul.State EvmYul.OperationType.EVM)
  | ternaryCopy
      (f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
        Word → EvmYul.SharedState EvmYul.OperationType.EVM)
  | quaternaryCopy
      (f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
        Word → Word → EvmYul.SharedState EvmYul.OperationType.EVM)
  | pop
  | mload
  | returndatacopy
  | dup (n : Nat)
  | swap (n : Nat)
  | log0
  | log1
  | log2
  | log3
  | log4
  | invalid

namespace PrimStep

def run (step : PrimStep) (state : EvmYul.EVM.State) :
    Except EvmYul.EVM.ExecutionException EvmYul.EVM.State :=
  match step with
  | .bin f => EvmYul.EVM.execBinOp f state
  | .un f => EvmYul.EVM.execUnOp f state
  | .tri f => EvmYul.EVM.execTriOp f state
  | .executionEnv f => EvmYul.EVM.executionEnvOp f state
  | .unaryExecutionEnv f => EvmYul.EVM.unaryExecutionEnvOp f state
  | .machineState f => EvmYul.EVM.machineStateOp f state
  | .binaryMachineState f => EvmYul.EVM.binaryMachineStateOp f state
  | .binaryMachineStateWithResult f => EvmYul.EVM.binaryMachineStateOp' f state
  | .ternaryMachineState f => EvmYul.EVM.ternaryMachineStateOp f state
  | .state f => EvmYul.EVM.stateOp f state
  | .unaryState f => EvmYul.EVM.unaryStateOp f state
  | .binaryState f => EvmYul.EVM.binaryStateOp f state
  | .ternaryCopy f => EvmYul.EVM.ternaryCopyOp f state
  | .quaternaryCopy f => EvmYul.EVM.quaternaryCopyOp f state
  | .pop =>
      match state.stack.pop with
      | some ⟨stack, _⟩ => .ok <| state.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .mload =>
      match state.stack.pop with
      | some ⟨stack, μ₀⟩ =>
          let (value, mState') := state.toMachineState.mload μ₀
          let state' := { state with toMachineState := mState' }
          .ok <| state'.replaceStackAndIncrPC (stack.push value)
      | none => .error .StackUnderflow
  | .returndatacopy =>
      match state.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ =>
          let mState' := state.toMachineState.returndatacopy μ₀ μ₁ μ₂
          let state' := { state with toMachineState := mState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .dup n => EvmYul.dup n state
  | .swap n => EvmYul.swap n state
  | .log0 =>
      match state.stack.pop2 with
      | some ⟨stack, μ₀, μ₁⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[] state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .log1 =>
      match state.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[μ₂] state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .log2 =>
      match state.stack.pop4 with
      | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[μ₂, μ₃] state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .log3 =>
      match state.stack.pop5 with
      | some ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[μ₂, μ₃, μ₄]
              state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .log4 =>
      match state.stack.pop6 with
      | some ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[μ₂, μ₃, μ₄, μ₅]
              state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .invalid => .error .InvalidInstruction

end PrimStep

namespace PrimOp

/--
Continuing primitives admitted by structured control as ordinary statements.

Excluded here: `STOP`, `RETURN`, `REVERT`, `SELFDESTRUCT`, the call/create
family, and `PC`. Those are control-boundary or PC-dependent opcodes and need
an outcome-aware source semantics rather than normal statement sequencing.
-/
def continuingStep? : PrimOp → Option PrimStep
  | .add => some (.bin EvmYul.UInt256.add)
  | .mul => some (.bin EvmYul.UInt256.mul)
  | .sub => some (.bin EvmYul.UInt256.sub)
  | .div => some (.bin EvmYul.UInt256.div)
  | .sdiv => some (.bin EvmYul.UInt256.sdiv)
  | .mod => some (.bin EvmYul.UInt256.mod)
  | .smod => some (.bin EvmYul.UInt256.smod)
  | .addmod => some (.tri EvmYul.UInt256.addMod)
  | .mulmod => some (.tri EvmYul.UInt256.mulMod)
  | .exp => some (.bin EvmYul.UInt256.exp)
  | .signextend => some (.bin EvmYul.UInt256.signextend)
  | .lt => some (.bin EvmYul.UInt256.lt)
  | .gt => some (.bin EvmYul.UInt256.gt)
  | .slt => some (.bin EvmYul.UInt256.slt)
  | .sgt => some (.bin EvmYul.UInt256.sgt)
  | .eq => some (.bin EvmYul.UInt256.eq)
  | .iszero => some (.un EvmYul.UInt256.isZero)
  | .and => some (.bin EvmYul.UInt256.land)
  | .or => some (.bin EvmYul.UInt256.lor)
  | .xor => some (.bin EvmYul.UInt256.xor)
  | .not => some (.un EvmYul.UInt256.lnot)
  | .byte => some (.bin EvmYul.UInt256.byteAt)
  | .shl => some (.bin (flip EvmYul.UInt256.shiftLeft))
  | .shr => some (.bin (flip EvmYul.UInt256.shiftRight))
  | .sar => some (.bin EvmYul.UInt256.sar)
  | .address =>
      some (.executionEnv
        (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner))
  | .balance => some (.unaryState EvmYul.State.balance)
  | .origin =>
      some (.executionEnv
        (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender))
  | .caller =>
      some (.executionEnv
        (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source))
  | .callvalue => some (.executionEnv EvmYul.ExecutionEnv.weiValue)
  | .calldataload =>
      some (.unaryState (fun s v => (s, EvmYul.State.calldataload s v)))
  | .calldatasize =>
      some (.executionEnv
        (.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.calldata))
  | .calldatacopy =>
      some (.ternaryCopy EvmYul.SharedState.calldatacopy)
  | .codesize =>
      some (.executionEnv
        (.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.code))
  | .codecopy => some (.ternaryCopy EvmYul.SharedState.codeCopy)
  | .gasprice =>
      some (.executionEnv (.ofNat ∘ EvmYul.ExecutionEnv.gasPrice))
  | .extcodesize => some (.unaryState EvmYul.State.extCodeSize)
  | .extcodecopy =>
      some (.quaternaryCopy EvmYul.SharedState.extCodeCopy')
  | .returndatasize =>
      some (.machineState EvmYul.MachineState.returndatasize)
  | .returndatacopy => some .returndatacopy
  | .extcodehash => some (.unaryState EvmYul.State.extCodeHash)
  | .blockhash =>
      some (.unaryState (fun s v => (s, EvmYul.State.blockHash s v)))
  | .coinbase =>
      some (.state (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase))
  | .timestamp => some (.state EvmYul.State.timeStamp)
  | .number => some (.state EvmYul.State.number)
  | .prevrandao => some (.executionEnv EvmYul.prevRandao)
  | .gaslimit => some (.state EvmYul.State.gasLimit)
  | .chainid => some (.state EvmYul.State.chainId)
  | .selfbalance => some (.state EvmYul.State.selfbalance)
  | .basefee => some (.executionEnv EvmYul.basefee)
  | .blobhash => some (.unaryExecutionEnv EvmYul.blobhash)
  | .blobbasefee =>
      some (.executionEnv EvmYul.ExecutionEnv.getBlobGasprice)
  | .pop => some .pop
  | .mload => some .mload
  | .mstore => some (.binaryMachineState EvmYul.MachineState.mstore)
  | .sload => some (.unaryState EvmYul.State.sload)
  | .sstore => some (.binaryState EvmYul.State.sstore)
  | .mstore8 => some (.binaryMachineState EvmYul.MachineState.mstore8)
  | .msize => some (.machineState EvmYul.MachineState.msize)
  | .tload => some (.unaryState EvmYul.State.tload)
  | .tstore => some (.binaryState EvmYul.State.tstore)
  | .mcopy => some (.ternaryMachineState EvmYul.MachineState.mcopy)
  | .keccak256 =>
      some (.binaryMachineStateWithResult EvmYul.MachineState.keccak256)
  | .dup1 => some (.dup 1)
  | .dup2 => some (.dup 2)
  | .dup3 => some (.dup 3)
  | .dup4 => some (.dup 4)
  | .dup5 => some (.dup 5)
  | .dup6 => some (.dup 6)
  | .dup7 => some (.dup 7)
  | .dup8 => some (.dup 8)
  | .dup9 => some (.dup 9)
  | .dup10 => some (.dup 10)
  | .dup11 => some (.dup 11)
  | .dup12 => some (.dup 12)
  | .dup13 => some (.dup 13)
  | .dup14 => some (.dup 14)
  | .dup15 => some (.dup 15)
  | .dup16 => some (.dup 16)
  | .swap1 => some (.swap 1)
  | .swap2 => some (.swap 2)
  | .swap3 => some (.swap 3)
  | .swap4 => some (.swap 4)
  | .swap5 => some (.swap 5)
  | .swap6 => some (.swap 6)
  | .swap7 => some (.swap 7)
  | .swap8 => some (.swap 8)
  | .swap9 => some (.swap 9)
  | .swap10 => some (.swap 10)
  | .swap11 => some (.swap 11)
  | .swap12 => some (.swap 12)
  | .swap13 => some (.swap 13)
  | .swap14 => some (.swap 14)
  | .swap15 => some (.swap 15)
  | .swap16 => some (.swap 16)
  | .log0 => some .log0
  | .log1 => some .log1
  | .log2 => some .log2
  | .log3 => some .log3
  | .log4 => some .log4
  | .invalid => some .invalid
  | .stop | .pc | .create | .call | .callcode | .return | .delegatecall
  | .create2 | .staticcall | .revert | .selfdestruct =>
      none

def step (op : PrimOp) (state : EvmYul.EVM.State) :
    Except EvmYul.EVM.ExecutionException EvmYul.EVM.State :=
  match op.continuingStep? with
  | some step => step.run state
  | none => EvmYul.step op.toEVM none state

theorem step_eq_continuingStep_run {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) (state : EvmYul.EVM.State) :
    op.step state = step.run state := by
  unfold PrimOp.step
  simp [hStep]

theorem step_eq_evm_step_of_not_continuing {op : PrimOp}
    (hStep : op.continuingStep? = none) (state : EvmYul.EVM.State) :
    op.step state = EvmYul.step op.toEVM none state := by
  unfold PrimOp.step
  simp [hStep]

end PrimOp

end Assembly
end EvmCompiler
