import EvmCompiler.Yul.PrimSemantics

namespace EvmCompiler
namespace Yul

namespace OpenExternal

universe u v w

abbrev Word := EvmYul.UInt256
abbrev Address := EvmYul.AccountAddress
abbrev Stack := EvmYul.Stack Word

/--
The external call-family operations that should be compared as open
interactions with the outside world.

This deliberately excludes `CREATE`/`CREATE2`; contract creation needs its own
request shape because the returned address and deployed code are part of the
observable interaction.
-/
inductive CallKind where
  | call
  | callcode
  | delegatecall
  | staticcall
  deriving DecidableEq, Repr

def CallKind.toYulOperation : CallKind → EvmYul.Operation .Yul
  | .call => .System .CALL
  | .callcode => .System .CALLCODE
  | .delegatecall => .System .DELEGATECALL
  | .staticcall => .System .STATICCALL

def CallKind.toEVMOperation : CallKind → EvmYul.Operation .EVM
  | .call => .CALL
  | .callcode => .CALLCODE
  | .delegatecall => .DELEGATECALL
  | .staticcall => .STATICCALL

def CallKind.ofYulOperation? : EvmYul.Operation .Yul → Option CallKind
  | .System .CALL => some .call
  | .System .CALLCODE => some .callcode
  | .System .DELEGATECALL => some .delegatecall
  | .System .STATICCALL => some .staticcall
  | _ => none

def CallKind.ofEVMOperation? : EvmYul.Operation .EVM → Option CallKind
  | .CALL => some .call
  | .CALLCODE => some .callcode
  | .DELEGATECALL => some .delegatecall
  | .STATICCALL => some .staticcall
  | _ => none

@[simp] theorem CallKind.ofYulOperation?_toYulOperation
    (kind : CallKind) :
    CallKind.ofYulOperation? kind.toYulOperation = some kind := by
  cases kind <;> rfl

@[simp] theorem CallKind.ofEVMOperation?_toEVMOperation
    (kind : CallKind) :
    CallKind.ofEVMOperation? kind.toEVMOperation = some kind := by
  cases kind <;> rfl

/--
The request that is visible to the external environment.

`recipient` is the account whose balance/call frame is targeted, while
`codeAddress` is the account whose code is executed. These differ for
`CALLCODE` and `DELEGATECALL`.
-/
structure CallRequest where
  kind : CallKind
  requestedGas : Word
  caller : Address
  recipient : Address
  codeAddress : Address
  transferValue : Word
  apparentValue : Word
  calldata : ByteArray
  permission : Bool

/--
Local continuation data for applying an external response.

These offsets are not part of the call made to the outside world, but both
interpreters must agree on them before consuming the same response.
-/
structure ReturnWindow where
  inOffset : Word
  inSize : Word
  outOffset : Word
  outSize : Word

/-- A complete open call site: external request plus local return-copy window. -/
structure CallSite where
  request : CallRequest
  returnWindow : ReturnWindow

/--
The syntactic operand bundle shared by Yul call arguments and EVM stack
operands. `valueArg` is meaningful for `CALL`/`CALLCODE`; for
`DELEGATECALL`/`STATICCALL` the semantic transfer and apparent value are
derived from the current context instead.
-/
structure CallOperands where
  requestedGas : Word
  address : Word
  valueArg : Word
  inOffset : Word
  inSize : Word
  outOffset : Word
  outSize : Word

namespace CallOperands

def returnWindow (operands : CallOperands) : ReturnWindow where
  inOffset := operands.inOffset
  inSize := operands.inSize
  outOffset := operands.outOffset
  outSize := operands.outSize

end CallOperands

/--
The caller-local state needed to form a CALL-family request.

The relation below records exactly the cross-semantics facts needed to show
both computed requests are equal. Chain-specific gas forwarding and account-map
resource behavior live outside this request identity.
-/
structure CallContext (τ : EvmYul.OperationType) where
  machine : EvmYul.MachineState
  codeOwner : Address
  source : Address
  weiValue : Word
  permission : Bool

namespace CallContext

variable {τ : EvmYul.OperationType}

def ofYulSharedState (state : EvmYul.SharedState .Yul) :
    CallContext .Yul where
  machine := state.toMachineState
  codeOwner := state.executionEnv.codeOwner
  source := state.executionEnv.source
  weiValue := state.executionEnv.weiValue
  permission := state.executionEnv.perm

def ofEVMSharedState (state : EvmYul.SharedState .EVM) :
    CallContext .EVM where
  machine := state.toMachineState
  codeOwner := state.executionEnv.codeOwner
  source := state.executionEnv.source
  weiValue := state.executionEnv.weiValue
  permission := state.executionEnv.perm

def ofYulState (state : EvmYul.Yul.State) : CallContext .Yul where
  machine := state.toMachineState
  codeOwner := state.executionEnv.codeOwner
  source := state.executionEnv.source
  weiValue := state.executionEnv.weiValue
  permission := state.executionEnv.perm

def ofEVMState (state : EvmYul.EVM.State) : CallContext .EVM where
  machine := state.toMachineState
  codeOwner := state.executionEnv.codeOwner
  source := state.executionEnv.source
  weiValue := state.executionEnv.weiValue
  permission := state.executionEnv.perm

def calldata (context : CallContext τ) (window : ReturnWindow) : ByteArray :=
  context.machine.memory.readWithPadding
    window.inOffset.toNat window.inSize.toNat

def caller (context : CallContext τ) : CallKind → Address
  | .call => context.codeOwner
  | .callcode => context.codeOwner
  | .delegatecall => context.source
  | .staticcall => context.codeOwner

def recipient (context : CallContext τ) (target : Address) :
    CallKind → Address
  | .call => target
  | .callcode => context.codeOwner
  | .delegatecall => context.codeOwner
  | .staticcall => target

def transferValue (_context : CallContext τ) (operands : CallOperands) :
    CallKind → Word
  | .call => operands.valueArg
  | .callcode => operands.valueArg
  | .delegatecall => EvmYul.UInt256.ofNat 0
  | .staticcall => EvmYul.UInt256.ofNat 0

def apparentValue (context : CallContext τ) (operands : CallOperands) :
    CallKind → Word
  | .call => operands.valueArg
  | .callcode => operands.valueArg
  | .delegatecall => context.weiValue
  | .staticcall => EvmYul.UInt256.ofNat 0

def effectivePermission (context : CallContext τ) : CallKind → Bool
  | .staticcall => false
  | _ => context.permission

def callSite (context : CallContext τ)
    (kind : CallKind) (operands : CallOperands) : CallSite :=
  let target := EvmYul.AccountAddress.ofUInt256 operands.address
  let window := operands.returnWindow
  let recipient := context.recipient target kind
  let transferValue := context.transferValue operands kind
  { request :=
      { kind := kind
        requestedGas := operands.requestedGas
        caller := context.caller kind
        recipient := recipient
        codeAddress := target
        transferValue := transferValue
        apparentValue := context.apparentValue operands kind
        calldata := context.calldata window
        permission := context.effectivePermission kind }
    returnWindow := window }

end CallContext

/--
The exact caller-local agreement needed to prove two extracted call sites are
the same. The final bridge should construct this from the existing source/target
state relation, not assume it at the public theorem boundary.
-/
structure CallContextRel
    (source : CallContext .Yul) (target : CallContext .EVM) : Prop where
  memory : source.machine.memory = target.machine.memory
  codeOwner : source.codeOwner = target.codeOwner
  sourceAddress : source.source = target.source
  weiValue : source.weiValue = target.weiValue
  permission : source.permission = target.permission

namespace CallContextRel

theorem callSite_eq {source : CallContext .Yul}
    {target : CallContext .EVM}
    (hRel : CallContextRel source target)
    (kind : CallKind) (operands : CallOperands) :
    source.callSite kind operands = target.callSite kind operands := by
  cases kind <;>
    simp [CallContext.callSite, CallContext.caller, CallContext.recipient,
      CallContext.transferValue, CallContext.apparentValue,
      CallContext.effectivePermission, CallContext.calldata, hRel.memory,
      hRel.codeOwner, hRel.sourceAddress, hRel.weiValue, hRel.permission]

end CallContextRel

namespace CallKind

def inputArity : CallKind → Nat
  | .call => 7
  | .callcode => 7
  | .delegatecall => 6
  | .staticcall => 6

def toBasicOp : CallKind → Structured.BasicOp
  | .call => .call
  | .callcode => .callcode
  | .delegatecall => .delegatecall
  | .staticcall => .staticcall

@[simp] theorem inputs_toBasicOp (kind : CallKind) :
    Expressions.Structured.BasicOp.inputs kind.toBasicOp =
      kind.inputArity := by
  cases kind <;> rfl

@[simp] theorem outputs_toBasicOp (kind : CallKind) :
    Expressions.Structured.BasicOp.outputs kind.toBasicOp = 1 := by
  cases kind <;> rfl

def canonicalOperands : CallKind → CallOperands → CallOperands
  | .call, operands => operands
  | .callcode, operands => operands
  | .delegatecall, operands =>
      { operands with valueArg := EvmYul.UInt256.ofNat 0 }
  | .staticcall, operands =>
      { operands with valueArg := EvmYul.UInt256.ofNat 0 }

def args : CallKind → CallOperands → List Word
  | .call, operands =>
      [operands.requestedGas, operands.address, operands.valueArg,
        operands.inOffset, operands.inSize, operands.outOffset,
        operands.outSize]
  | .callcode, operands =>
      [operands.requestedGas, operands.address, operands.valueArg,
        operands.inOffset, operands.inSize, operands.outOffset,
        operands.outSize]
  | .delegatecall, operands =>
      [operands.requestedGas, operands.address, operands.inOffset,
        operands.inSize, operands.outOffset, operands.outSize]
  | .staticcall, operands =>
      [operands.requestedGas, operands.address, operands.inOffset,
        operands.inSize, operands.outOffset, operands.outSize]

@[simp] theorem args_length (kind : CallKind) (operands : CallOperands) :
    (kind.args operands).length = kind.inputArity := by
  cases kind <;> rfl

def yulOperands? : CallKind → List Word → Option CallOperands
  | .call, gas :: address :: value :: inOffset :: inSize ::
      outOffset :: outSize :: _ =>
      some
        { requestedGas := gas
          address := address
          valueArg := value
          inOffset := inOffset
          inSize := inSize
          outOffset := outOffset
          outSize := outSize }
  | .callcode, gas :: address :: value :: inOffset :: inSize ::
      outOffset :: outSize :: _ =>
      some
        { requestedGas := gas
          address := address
          valueArg := value
          inOffset := inOffset
          inSize := inSize
          outOffset := outOffset
          outSize := outSize }
  | .delegatecall, gas :: address :: inOffset :: inSize ::
      outOffset :: outSize :: _ =>
      some
        { requestedGas := gas
          address := address
          valueArg := EvmYul.UInt256.ofNat 0
          inOffset := inOffset
          inSize := inSize
          outOffset := outOffset
          outSize := outSize }
  | .staticcall, gas :: address :: inOffset :: inSize ::
      outOffset :: outSize :: _ =>
      some
        { requestedGas := gas
          address := address
          valueArg := EvmYul.UInt256.ofNat 0
          inOffset := inOffset
          inSize := inSize
          outOffset := outOffset
          outSize := outSize }
  | _, _ => none

def evmOperands? : CallKind → Stack → Option (Stack × CallOperands)
  | .call, stack =>
      match stack.pop7 with
      | some ⟨rest, gas, address, value, inOffset, inSize, outOffset, outSize⟩ =>
          some
            (rest,
              { requestedGas := gas
                address := address
                valueArg := value
                inOffset := inOffset
                inSize := inSize
                outOffset := outOffset
                outSize := outSize })
      | none => none
  | .callcode, stack =>
      match stack.pop7 with
      | some ⟨rest, gas, address, value, inOffset, inSize, outOffset, outSize⟩ =>
          some
            (rest,
              { requestedGas := gas
                address := address
                valueArg := value
                inOffset := inOffset
                inSize := inSize
                outOffset := outOffset
                outSize := outSize })
      | none => none
  | .delegatecall, stack =>
      match stack.pop6 with
      | some ⟨rest, gas, address, inOffset, inSize, outOffset, outSize⟩ =>
          some
            (rest,
              { requestedGas := gas
                address := address
                valueArg := EvmYul.UInt256.ofNat 0
                inOffset := inOffset
                inSize := inSize
                outOffset := outOffset
                outSize := outSize })
      | none => none
  | .staticcall, stack =>
      match stack.pop6 with
      | some ⟨rest, gas, address, inOffset, inSize, outOffset, outSize⟩ =>
          some
            (rest,
              { requestedGas := gas
                address := address
                valueArg := EvmYul.UInt256.ofNat 0
                inOffset := inOffset
                inSize := inSize
                outOffset := outOffset
                outSize := outSize })
      | none => none

@[simp] theorem yulOperands?_args
    (kind : CallKind) (operands : CallOperands) (suffix : List Word) :
    kind.yulOperands? (kind.args operands ++ suffix) =
      some (kind.canonicalOperands operands) := by
  cases kind <;> rfl

@[simp] theorem yulOperands?_exact_args
    (kind : CallKind) (operands : CallOperands) :
    kind.yulOperands? (kind.args operands) =
      some (kind.canonicalOperands operands) := by
  simpa using yulOperands?_args kind operands []

@[simp] theorem evmOperands?_args
    (kind : CallKind) (operands : CallOperands) (stackRest : Stack) :
    kind.evmOperands? (kind.args operands ++ stackRest) =
      some (stackRest, kind.canonicalOperands operands) := by
  cases kind <;> rfl

def yulCallSite?
    (state : EvmYul.Yul.State) (kind : CallKind) (args : List Word) :
    Option CallSite :=
  match kind.yulOperands? args with
  | some operands =>
      some ((CallContext.ofYulState state).callSite kind operands)
  | none => none

def evmCallSite?
    (state : EvmYul.EVM.State) (kind : CallKind) :
    Option (Stack × CallSite) :=
  match kind.evmOperands? state.stack with
  | some (rest, operands) =>
      some (rest, (CallContext.ofEVMState state).callSite kind operands)
  | none => none

theorem callSite_eq_of_yul_evm_operands
    {yulState : EvmYul.Yul.State} {evmState : EvmYul.EVM.State}
    {kind : CallKind} {args : List Word} {stackRest : Stack}
    {operands : CallOperands}
    (hRel :
      CallContextRel
        (CallContext.ofYulState yulState)
        (CallContext.ofEVMState evmState))
    (hYul : kind.yulOperands? args = some operands)
    (hEVM : kind.evmOperands? evmState.stack = some (stackRest, operands)) :
    kind.yulCallSite? yulState args =
      some ((CallContext.ofEVMState evmState).callSite kind operands) ∧
    kind.evmCallSite? evmState =
      some (stackRest,
        (CallContext.ofEVMState evmState).callSite kind operands) := by
  constructor
  · simp [yulCallSite?, hYul,
      CallContextRel.callSite_eq hRel kind operands]
  · simp [evmCallSite?, hEVM]

theorem callSite_eq_of_args
    {yulState : EvmYul.Yul.State} {evmState : EvmYul.EVM.State}
    (hRel :
      CallContextRel
        (CallContext.ofYulState yulState)
        (CallContext.ofEVMState evmState))
    (kind : CallKind) (operands : CallOperands) (stackRest : Stack) :
    kind.yulCallSite? yulState (kind.args operands) =
      some
        ((CallContext.ofEVMState evmState).callSite kind
          (kind.canonicalOperands operands)) ∧
    kind.evmCallSite?
        ({ evmState with stack := kind.args operands ++ stackRest }
          : EvmYul.EVM.State) =
      some
        (stackRest,
          (CallContext.ofEVMState evmState).callSite kind
            (kind.canonicalOperands operands)) := by
  have hRel' :
      CallContextRel
        (CallContext.ofYulState yulState)
        (CallContext.ofEVMState
          ({ evmState with stack := kind.args operands ++ stackRest }
            : EvmYul.EVM.State)) := by
    simpa [CallContext.ofEVMState] using hRel
  have hSites :=
    callSite_eq_of_yul_evm_operands
      (yulState := yulState)
      (evmState :=
        ({ evmState with stack := kind.args operands ++ stackRest }
          : EvmYul.EVM.State))
      (kind := kind)
      (args := kind.args operands)
      (stackRest := stackRest)
      (operands := kind.canonicalOperands operands)
      hRel' (by simp) (by simp)
  simpa [CallContext.ofEVMState] using hSites

end CallKind

/--
An arbitrary response from the outside world.

`Effect` is intentionally abstract. It can later be instantiated with a concrete
post-world delta, an account-map transformer, a trace token, or `PUnit` for
tests that only care about status/gas/return data. The compiler theorem should
quantify over this response rather than proving facts about one chosen world.
-/
structure CallResponse (Effect : Type u) where
  success : Bool
  returnedGas : Word
  returnData : ByteArray
  effect : Effect

namespace CallResponse

def statusWord {Effect : Type u} (response : CallResponse Effect) : Word :=
  if response.success then EvmYul.UInt256.ofNat 1 else EvmYul.UInt256.ofNat 0

end CallResponse

/--
The caller-local memory update induced by a response. This is shared by the Yul
and EVM sides; the EVM gas-aware continuation may additionally consume
`response.returnedGas`.
-/
def ReturnWindow.finishMachine
    (window : ReturnWindow) (machine : EvmYul.MachineState)
    (returnData : ByteArray) : EvmYul.MachineState :=
  machine.finishExternalCall returnData
    window.inOffset window.inSize window.outOffset window.outSize

/--
An open external call: a visible request plus a continuation for every possible
response.

The continuation consumes the response as data. It is intentionally not a
function from a concrete blockchain world.
-/
structure OpenCall (Effect : Type u) (State : Type v) where
  site : CallSite
  resume : CallResponse Effect → State

/--
The theorem shape for the open external boundary.

Both sides must issue the same `CallSite`. Then, for every possible response,
the same response is fed to both continuations and the resulting states remain
related. This is the universal quantification over arbitrary outside-world
behavior; there is no premise constraining which responses are allowed.
-/
structure OpenCallRel
    {Effect : Type u} {SourceState : Type v} {TargetState : Type w}
    (stateRel : SourceState → TargetState → Prop)
    (source : OpenCall Effect SourceState)
    (target : OpenCall Effect TargetState) : Prop where
  sameSite : source.site = target.site
  preservesAllResponses :
    ∀ response, stateRel (source.resume response) (target.resume response)

namespace OpenCallRel

theorem preserves_response
    {Effect : Type u} {SourceState : Type v} {TargetState : Type w}
    {stateRel : SourceState → TargetState → Prop}
    {source : OpenCall Effect SourceState}
    {target : OpenCall Effect TargetState}
    (hRel : OpenCallRel stateRel source target)
    (response : CallResponse Effect) :
    stateRel (source.resume response) (target.resume response) :=
  hRel.preservesAllResponses response

end OpenCallRel

end OpenExternal

end Yul
end EvmCompiler
