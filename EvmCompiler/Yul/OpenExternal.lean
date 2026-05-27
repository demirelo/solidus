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

Gas mechanics are intentionally abstracted here, but the requested-gas operand
is still part of the request identity. The theorem proves that the source and
target computed the same requested gas, without proving any chain-specific
forwarded-gas formula or feasibility condition at this boundary.
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
derived from the current context instead. `requestedGas` is opaque request data
at the open external boundary; forwarded gas is deliberately not computed here.
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
both computed requests are equal. Gas forwarding/feasibility and account-map
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

@[simp] theorem toBasicOp?_toYulOperation (kind : CallKind) :
    Prim.toBasicOp? kind.toYulOperation = some kind.toBasicOp := by
  cases kind <;> rfl

@[simp] theorem terminal?_toYulOperation (kind : CallKind) :
    Prim.terminal? kind.toYulOperation = none := by
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

/--
Call site observed by the stack-free primitive semantics.

The primitive source tower receives values in source order. Its structured
backend runs the EVM primitive on `values.reverse`, so a CALL-family primitive
site is extracted from that reconstructed stack and accepted only at exact
arity.
-/
def primitiveCallSite?
    (shared : EvmYul.SharedState .EVM) (kind : CallKind)
    (values : List Word) : Option CallSite :=
  match kind.evmOperands? values.reverse with
  | some ([], operands) =>
      some ((CallContext.ofEVMSharedState shared).callSite kind operands)
  | _ => none

@[simp] theorem primitiveCallSite?_args_reverse
    (shared : EvmYul.SharedState .EVM)
    (kind : CallKind) (operands : CallOperands) :
    primitiveCallSite? shared kind (kind.args operands).reverse =
      some
        ((CallContext.ofEVMSharedState shared).callSite kind
          (kind.canonicalOperands operands)) := by
  cases kind <;> rfl

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

namespace CallSite

def finishShared {Effect : Type u} {τ : EvmYul.OperationType}
    (site : CallSite) (shared : EvmYul.SharedState τ)
    (response : CallResponse Effect) : EvmYul.SharedState τ :=
  { shared with
    toMachineState :=
      site.returnWindow.finishMachine shared.toMachineState
        response.returnData }

def finishYulState {Effect : Type u}
    (site : CallSite) (state : EvmYul.Yul.State)
    (response : CallResponse Effect) : EvmYul.Yul.State :=
  state.setSharedState
    (site.finishShared state.toSharedState response)

end CallSite

/--
An open external call: a visible request plus a continuation for every possible
response.

The continuation consumes the response as data. It is intentionally not a
function from a concrete blockchain world.
-/
structure OpenCall (Effect : Type u) (State : Type v) where
  site : CallSite
  resume : CallResponse Effect → State

namespace CallKind

def yulOpenCall?
    {Effect : Type u} (state : EvmYul.Yul.State) (kind : CallKind)
    (args : List Word) :
    Option (OpenCall Effect (EvmYul.Yul.State × List Word)) :=
  match kind.yulCallSite? state args with
  | some site =>
      some
        { site := site
          resume := fun response =>
            (site.finishYulState state response,
              [response.statusWord]) }
  | none => none

def primitiveSharedOpenCall?
    {Effect : Type u} (shared : EvmYul.SharedState .EVM)
    (kind : CallKind) (values : List Word) :
    Option (OpenCall Effect (EvmYul.SharedState .EVM × List Word)) :=
  match primitiveCallSite? shared kind values with
  | some site =>
      some
        { site := site
          resume := fun response =>
            (site.finishShared shared response,
              [response.statusWord]) }
  | none => none

def evmOpenCall?
    {Effect : Type u} (state : EvmYul.EVM.State) (kind : CallKind) :
    Option (OpenCall Effect EvmYul.EVM.State) :=
  match kind.evmCallSite? state with
  | some (rest, site) =>
      some
        { site := site
          resume := fun response =>
            { state with
              toSharedState :=
                site.finishShared state.toSharedState response
              stack := response.statusWord :: rest } }
  | none => none

@[simp] theorem primitiveSharedOpenCall?_args_reverse
    {Effect : Type u} (shared : EvmYul.SharedState .EVM)
    (kind : CallKind) (operands : CallOperands) :
    primitiveSharedOpenCall? (Effect := Effect) shared kind
        (kind.args operands).reverse =
      some
        { site :=
            (CallContext.ofEVMSharedState shared).callSite kind
              (kind.canonicalOperands operands)
          resume := fun response =>
            (((CallContext.ofEVMSharedState shared).callSite kind
                (kind.canonicalOperands operands)).finishShared shared
                response,
              [response.statusWord]) } := by
  cases kind <;> rfl

@[simp] theorem evmOpenCall?_args
    {Effect : Type u} (state : EvmYul.EVM.State)
    (kind : CallKind) (operands : CallOperands) (baseStack : Stack) :
    evmOpenCall? (Effect := Effect)
        ({ state with stack := kind.args operands ++ baseStack }
          : EvmYul.EVM.State) kind =
      some
        { site :=
            (CallContext.ofEVMState state).callSite kind
              (kind.canonicalOperands operands)
          resume := fun response =>
            { state with
              toSharedState :=
                ((CallContext.ofEVMState state).callSite kind
                    (kind.canonicalOperands operands)).finishShared
                  state.toSharedState response
              stack := response.statusWord :: baseStack } } := by
  cases kind <;> rfl

end CallKind

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

theorem trans
    {Effect : Type u} {LeftState : Type v} {MidState : Type w}
    {RightState : Type}
    {leftRel : LeftState → MidState → Prop}
    {rightRel : MidState → RightState → Prop}
    {left : OpenCall Effect LeftState}
    {mid : OpenCall Effect MidState}
    {right : OpenCall Effect RightState}
    (hLeft : OpenCallRel leftRel left mid)
    (hRight : OpenCallRel rightRel mid right) :
    OpenCallRel
      (fun leftResult rightResult =>
        ∃ midResult, leftRel leftResult midResult ∧
          rightRel midResult rightResult)
      left right where
  sameSite := hLeft.sameSite.trans hRight.sameSite
  preservesAllResponses := by
    intro response
    exact
      ⟨mid.resume response, hLeft.preservesAllResponses response,
        hRight.preservesAllResponses response⟩

end OpenCallRel

/--
Result relation between the stack-free primitive CALL continuation and the
EVM-stack continuation at the same primitive boundary.

Only the shared state and caller stack suffix are compared here. Program
counter, execution length, and gas accounting remain lower-level resource
concerns; this relation records the open external effect and the local stack
result needed by expression lowering.
-/
def PrimitiveEVMResultRel (baseStack : Stack) :
    EvmYul.SharedState .EVM × List Word → EvmYul.EVM.State → Prop :=
  fun primitiveResult evmResult =>
    evmResult.toSharedState = primitiveResult.1 ∧
      evmResult.stack = primitiveResult.2.reverse ++ baseStack

namespace CallKind

theorem primitiveSharedOpenCallRel_evmOpenCall_of_args
    {Effect : Type u} {shared : EvmYul.SharedState .EVM}
    (state : EvmYul.EVM.State)
    (hShared : state.toSharedState = shared)
    (kind : CallKind) (operands : CallOperands) (baseStack : Stack) :
    ∃ primitiveCall :
        OpenCall Effect (EvmYul.SharedState .EVM × List Word),
    ∃ evmCall : OpenCall Effect EvmYul.EVM.State,
      primitiveSharedOpenCall? (Effect := Effect) shared kind
          (kind.args operands).reverse =
        some primitiveCall ∧
      evmOpenCall? (Effect := Effect)
          ({ state with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State) kind =
        some evmCall ∧
      OpenCallRel (PrimitiveEVMResultRel baseStack)
        primitiveCall evmCall := by
  subst shared
  let site :=
    (CallContext.ofEVMState state).callSite kind
      (kind.canonicalOperands operands)
  let primitiveCall :
      OpenCall Effect (EvmYul.SharedState .EVM × List Word) :=
    { site := site
      resume := fun response =>
        (site.finishShared state.toSharedState response,
          [response.statusWord]) }
  let evmCall : OpenCall Effect EvmYul.EVM.State :=
    { site := site
      resume := fun response =>
        { state with
          toSharedState := site.finishShared state.toSharedState response
          stack := response.statusWord :: baseStack } }
  refine ⟨primitiveCall, evmCall, ?_, ?_, ?_⟩
  · cases kind <;> rfl
  · cases kind <;> rfl
  · constructor
    · rfl
    · intro response
      simp [primitiveCall, evmCall, PrimitiveEVMResultRel]

end CallKind

end OpenExternal

end Yul
end EvmCompiler
