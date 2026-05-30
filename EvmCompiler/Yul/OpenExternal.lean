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

set_option linter.unusedSimpArgs false in
theorem CallKind.toYulOperation_eq_ofYulOperation?
    {yulOp : EvmYul.Operation .Yul} {kind : CallKind}
    (hKind : CallKind.ofYulOperation? yulOp = some kind) :
    yulOp = kind.toYulOperation := by
  cases kind <;> cases yulOp <;>
    simp [CallKind.ofYulOperation?, CallKind.toYulOperation] at hKind
  all_goals
    try rename_i subop
    try cases subop <;>
      simp [CallKind.ofYulOperation?, CallKind.toYulOperation] at hKind
  all_goals
    cases hKind
    rfl

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

def ofBasicOp? : Structured.BasicOp → Option CallKind
  | .call => some .call
  | .callcode => some .callcode
  | .delegatecall => some .delegatecall
  | .staticcall => some .staticcall
  | _ => none

@[simp] theorem ofBasicOp?_toBasicOp (kind : CallKind) :
    ofBasicOp? kind.toBasicOp = some kind := by
  cases kind <;> rfl

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

set_option linter.unusedSimpArgs false in
theorem toBasicOp_eq_ofYulOperation?
    {yulOp : EvmYul.Operation .Yul} {kind : CallKind}
    {op : Structured.BasicOp}
    (hKind : CallKind.ofYulOperation? yulOp = some kind)
    (hBasic : Prim.toBasicOp? yulOp = some op) :
    op = kind.toBasicOp := by
  cases kind <;> cases yulOp <;>
    simp [CallKind.ofYulOperation?, Prim.toBasicOp?,
      CallKind.toBasicOp] at hKind hBasic
  all_goals
    try rename_i subop
    try cases subop <;>
      simp [CallKind.ofYulOperation?, Prim.toBasicOp?,
        CallKind.toBasicOp] at hKind hBasic
  all_goals
    cases hKind
    cases hBasic
    rfl

theorem inputArity_eq_inputs_ofYulOperation?
    {yulOp : EvmYul.Operation .Yul} {kind : CallKind}
    {op : Structured.BasicOp}
    (hKind : CallKind.ofYulOperation? yulOp = some kind)
    (hBasic : Prim.toBasicOp? yulOp = some op) :
    Expressions.Structured.BasicOp.inputs op = kind.inputArity := by
  have hOp : op = kind.toBasicOp :=
    toBasicOp_eq_ofYulOperation? hKind hBasic
  subst op
  simp

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

theorem exists_operands_of_reverse_args_length
    (kind : CallKind) {values : List Word}
    (hLength : values.length = kind.inputArity) :
    ∃ operands : CallOperands,
      values = (kind.args operands).reverse := by
  cases kind
  · cases values with
    | nil => simp [CallKind.inputArity] at hLength
    | cons outSize values =>
      cases values with
      | nil => simp [CallKind.inputArity] at hLength
      | cons outOffset values =>
        cases values with
        | nil => simp [CallKind.inputArity] at hLength
        | cons inSize values =>
          cases values with
          | nil => simp [CallKind.inputArity] at hLength
          | cons inOffset values =>
            cases values with
            | nil => simp [CallKind.inputArity] at hLength
            | cons value values =>
              cases values with
              | nil => simp [CallKind.inputArity] at hLength
              | cons address values =>
                cases values with
                | nil => simp [CallKind.inputArity] at hLength
                | cons requestedGas values =>
                  cases values with
                  | nil =>
                    exact
                      ⟨{ requestedGas := requestedGas
                         address := address
                         valueArg := value
                         inOffset := inOffset
                         inSize := inSize
                         outOffset := outOffset
                         outSize := outSize }, rfl⟩
                  | cons _ _ => simp [CallKind.inputArity] at hLength
  · cases values with
    | nil => simp [CallKind.inputArity] at hLength
    | cons outSize values =>
      cases values with
      | nil => simp [CallKind.inputArity] at hLength
      | cons outOffset values =>
        cases values with
        | nil => simp [CallKind.inputArity] at hLength
        | cons inSize values =>
          cases values with
          | nil => simp [CallKind.inputArity] at hLength
          | cons inOffset values =>
            cases values with
            | nil => simp [CallKind.inputArity] at hLength
            | cons value values =>
              cases values with
              | nil => simp [CallKind.inputArity] at hLength
              | cons address values =>
                cases values with
                | nil => simp [CallKind.inputArity] at hLength
                | cons requestedGas values =>
                  cases values with
                  | nil =>
                    exact
                      ⟨{ requestedGas := requestedGas
                         address := address
                         valueArg := value
                         inOffset := inOffset
                         inSize := inSize
                         outOffset := outOffset
                         outSize := outSize }, rfl⟩
                  | cons _ _ => simp [CallKind.inputArity] at hLength
  · cases values with
    | nil => simp [CallKind.inputArity] at hLength
    | cons outSize values =>
      cases values with
      | nil => simp [CallKind.inputArity] at hLength
      | cons outOffset values =>
        cases values with
        | nil => simp [CallKind.inputArity] at hLength
        | cons inSize values =>
          cases values with
          | nil => simp [CallKind.inputArity] at hLength
          | cons inOffset values =>
            cases values with
            | nil => simp [CallKind.inputArity] at hLength
            | cons address values =>
              cases values with
              | nil => simp [CallKind.inputArity] at hLength
              | cons requestedGas values =>
                cases values with
                | nil =>
                  exact
                    ⟨{ requestedGas := requestedGas
                       address := address
                       valueArg := EvmYul.UInt256.ofNat 0
                       inOffset := inOffset
                       inSize := inSize
                       outOffset := outOffset
                       outSize := outSize }, rfl⟩
                | cons _ _ => simp [CallKind.inputArity] at hLength
  · cases values with
    | nil => simp [CallKind.inputArity] at hLength
    | cons outSize values =>
      cases values with
      | nil => simp [CallKind.inputArity] at hLength
      | cons outOffset values =>
        cases values with
        | nil => simp [CallKind.inputArity] at hLength
        | cons inSize values =>
          cases values with
          | nil => simp [CallKind.inputArity] at hLength
          | cons inOffset values =>
            cases values with
            | nil => simp [CallKind.inputArity] at hLength
            | cons address values =>
              cases values with
              | nil => simp [CallKind.inputArity] at hLength
              | cons requestedGas values =>
                cases values with
                | nil =>
                  exact
                    ⟨{ requestedGas := requestedGas
                       address := address
                       valueArg := EvmYul.UInt256.ofNat 0
                       inOffset := inOffset
                       inSize := inSize
                       outOffset := outOffset
                       outSize := outSize }, rfl⟩
                | cons _ _ => simp [CallKind.inputArity] at hLength

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
An abstract mutation of contract-visible internal state while the caller frame is
suspended at an external call.

The external callee is not modeled as stateful here. Reentrancy is
over-approximated by letting the call response carry an arbitrary transformer of
the caller-visible chain state. We intentionally do not expose an account map,
created-account set, precompile table, child-code lookup, or any other concrete
world model at this boundary. The caller-local machine frame is still updated
only by the return-data copy/status continuation below, and the proof boundary
decides which arbitrary returned transformers preserve the Yul/EVM state
relation.
-/
structure ReentrantStateMutation where
  apply :
    {τ : EvmYul.OperationType} → EvmYul.State τ → EvmYul.State τ

namespace ReentrantStateMutation

def identity : ReentrantStateMutation where
  apply := fun state => state

end ReentrantStateMutation

/--
An arbitrary external-call response.

The black-box callee can return any status/returndata pair. It can also have
triggered arbitrary reentrant execution before returning, represented by
`internalMutation`. The compiler proof quantifies over all responses whose
opaque internal-state transformer preserves the relevant source/target relation,
instead of proving facts about a concrete scheduler, precompile table, account
map, created-account set, or child-code semantics.
-/
structure CallResponse where
  success : Bool
  returnedGas : Word
  returnData : ByteArray
  internalMutation : ReentrantStateMutation

namespace CallResponse

def statusWord (response : CallResponse) : Word :=
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

def finishShared {τ : EvmYul.OperationType}
    (site : CallSite) (shared : EvmYul.SharedState τ)
    (response : CallResponse) : EvmYul.SharedState τ :=
  { shared with
    toState := response.internalMutation.apply shared.toState
    toMachineState :=
      site.returnWindow.finishMachine shared.toMachineState
        response.returnData }

def finishYulState
    (site : CallSite) (state : EvmYul.Yul.State)
    (response : CallResponse) : EvmYul.Yul.State :=
  state.setSharedState
    (site.finishShared state.toSharedState response)

@[simp] theorem finishYulState_ok
    (site : CallSite) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (response : CallResponse) :
    site.finishYulState (.Ok shared store) response =
      .Ok (site.finishShared shared response) store := by
  simp [finishYulState, EvmYul.Yul.State.setSharedState,
    EvmYul.Yul.State.toSharedState]

end CallSite

/--
An open external call: a visible request plus a continuation for every possible
response.

The continuation consumes the response as data. It is intentionally not a
function from a concrete callee/chain interpreter.
-/
structure OpenCall (State : Type v) where
  site : CallSite
  resume : CallResponse → State

/--
Generic open result for interpreters that may suspend at an external call.

`YulOpenResult` below predates this generic carrier and is kept as the imported
Yul-facing result shape. New compiler-side open semantics can use this type
directly and relate to Yul through `YulOpenResult.toOpenResult`.
-/
inductive OpenResult (ε : Type u) (α : Type v) : Type (max u v) where
  | done : Except ε α → OpenResult ε α
  | call : OpenCall (OpenResult ε α) → OpenResult ε α

namespace OpenResult

def ok {ε : Type u} {α : Type v} (value : α) : OpenResult ε α :=
  .done (.ok value)

def error {ε : Type u} {α : Type v} (err : ε) : OpenResult ε α :=
  .done (.error err)

def bind {ε : Type u} {α : Type v} {β : Type w}
    (result : OpenResult ε α) (next : α → OpenResult ε β) :
    OpenResult ε β :=
  match result with
  | .done (.ok value) => next value
  | .done (.error err) => .done (.error err)
  | .call externalCall =>
      .call
        { site := externalCall.site
          resume := fun response =>
            bind (externalCall.resume response) next }

def map {ε : Type u} {α : Type v} {β : Type w}
    (f : α → β) (result : OpenResult ε α) : OpenResult ε β :=
  bind result (fun value => .ok (f value))

theorem bind_congr_next {ε : Type u} {α : Type v} {β : Type w}
    (result : OpenResult ε α) {next next' : α → OpenResult ε β}
    (hNext : ∀ value, next value = next' value) :
    bind result next = bind result next' := by
  exact
    (OpenResult.rec
      (motive_1 := fun result =>
        ∀ {next next' : α → OpenResult ε β},
          (∀ value, next value = next' value) →
            bind result next = bind result next')
      (motive_2 := fun externalCall =>
        ∀ {next next' : α → OpenResult ε β},
          (∀ value, next value = next' value) →
            bind (.call externalCall) next = bind (.call externalCall) next')
      (done := by
        intro result next next' hNext
        cases result <;> simp [bind, hNext])
      (call := by
        intro _ hCall next next' hNext
        exact hCall hNext)
      (mk := by
        intro _ _ ih next next' hNext
        simp [bind]
        funext response
        exact ih response hNext)
      result) hNext

end OpenResult

namespace OpenCallResponseRel

/--
Pull an open-call response relation back through continuations on both sides.

This is the response-relation counterpart of `OpenResult.bind`: a suspended
computation resumes its current call first, then enters the supplied
continuation.
-/
def comapBind
    {ε₁ : Type _} {ε₂ : Type _}
    {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}
    (callResponseRel :
      OpenCall (OpenResult ε₁ γ) →
        OpenCall (OpenResult ε₂ δ) → CallResponse → Prop)
    (sourceNext : α → OpenResult ε₁ γ)
    (targetNext : β → OpenResult ε₂ δ) :
    OpenCall (OpenResult ε₁ α) →
      OpenCall (OpenResult ε₂ β) → CallResponse → Prop :=
  fun sourceCall targetCall response =>
    callResponseRel
      { site := sourceCall.site
        resume := fun response =>
          OpenResult.bind (sourceCall.resume response) sourceNext }
      { site := targetCall.site
        resume := fun response =>
          OpenResult.bind (targetCall.resume response) targetNext }
      response

/--
Pull an open-call response relation back through a continuation on the target
side only.
-/
def comapRightBind
    {ε₁ : Type _} {ε₂ : Type _}
    {α : Type _} {β : Type _} {δ : Type _}
    (callResponseRel :
      OpenCall (OpenResult ε₁ α) →
        OpenCall (OpenResult ε₂ δ) → CallResponse → Prop)
    (targetNext : β → OpenResult ε₂ δ) :
    OpenCall (OpenResult ε₁ α) →
      OpenCall (OpenResult ε₂ β) → CallResponse → Prop :=
  fun sourceCall targetCall response =>
    callResponseRel sourceCall
      { site := targetCall.site
        resume := fun response =>
          OpenResult.bind (targetCall.resume response) targetNext }
      response

end OpenCallResponseRel

namespace CallKind

def yulOpenCall?
    (state : EvmYul.Yul.State) (kind : CallKind)
    (args : List Word) :
    Option (OpenCall (EvmYul.Yul.State × List Word)) :=
  match kind.yulCallSite? state args with
  | some site =>
      some
        { site := site
          resume := fun response =>
            (site.finishYulState state response,
              [response.statusWord]) }
  | none => none

def primitiveSharedOpenCall?
    (shared : EvmYul.SharedState .EVM)
    (kind : CallKind) (values : List Word) :
    Option (OpenCall (EvmYul.SharedState .EVM × List Word)) :=
  match primitiveCallSite? shared kind values with
  | some site =>
      some
        { site := site
          resume := fun response =>
            (site.finishShared shared response,
              [response.statusWord]) }
  | none => none

def evmOpenCall?
    (state : EvmYul.EVM.State) (kind : CallKind) :
    Option (OpenCall EvmYul.EVM.State) :=
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

theorem yulOpenCall?_resume_ok_store
    {kind : CallKind} {args : List Word}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {call : OpenCall (EvmYul.Yul.State × List Word)}
    (hCall : yulOpenCall? (.Ok shared store) kind args = some call)
    (response : CallResponse) :
    ∃ sharedAfter,
      (call.resume response).1 = .Ok sharedAfter store := by
  unfold yulOpenCall? at hCall
  cases hSite : kind.yulCallSite? (.Ok shared store) args with
  | none =>
      simp [hSite] at hCall
  | some site =>
      simp [hSite] at hCall
      cases hCall
      exact ⟨site.finishShared shared response, by simp⟩

theorem yulOpenCall?_resume_ok
    {kind : CallKind} {args : List Word}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {call : OpenCall (EvmYul.Yul.State × List Word)}
    (hCall : yulOpenCall? (.Ok shared store) kind args = some call)
    (response : CallResponse) :
    ∃ sharedAfter,
      call.resume response =
        (.Ok sharedAfter store, [response.statusWord]) := by
  unfold yulOpenCall? at hCall
  cases hSite : kind.yulCallSite? (.Ok shared store) args with
  | none =>
      simp [hSite] at hCall
  | some site =>
      simp [hSite] at hCall
      cases hCall
      exact ⟨site.finishShared shared response, by simp⟩

def yulPrimitiveEvalValuesOpenCall?
    (state : EvmYul.Yul.State) (prim : EvmYul.Operation .Yul)
    (args : List Word) :
    Option
      (OpenCall
        (Except EvmYul.Yul.Exception
          (EvmYul.Yul.State × List Word))) :=
  match CallKind.ofYulOperation? prim with
  | some kind =>
      match yulOpenCall? state kind args with
      | some sourceCall =>
          some
            { site := sourceCall.site
              resume := fun response => .ok (sourceCall.resume response) }
      | none => none
  | none => none

theorem yulPrimitiveEvalValuesOpenCall?_resume_ok
    {prim : EvmYul.Operation .Yul} {args : List Word}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {call :
      OpenCall
        (Except EvmYul.Yul.Exception
          (EvmYul.Yul.State × List Word))}
    (hCall :
      yulPrimitiveEvalValuesOpenCall? (.Ok shared store) prim args =
        some call)
    (response : CallResponse) :
    ∃ sharedAfter,
      call.resume response =
        .ok (.Ok sharedAfter store, [response.statusWord]) := by
  unfold yulPrimitiveEvalValuesOpenCall? at hCall
  cases hKind : CallKind.ofYulOperation? prim with
  | none =>
      simp [hKind] at hCall
  | some kind =>
      cases hOpen : yulOpenCall? (.Ok shared store) kind args with
      | none =>
          simp [hKind, hOpen] at hCall
      | some sourceCall =>
          simp [hKind, hOpen] at hCall
          cases hCall
          rcases yulOpenCall?_resume_ok hOpen response with
            ⟨sharedAfter, hResume⟩
          exact ⟨sharedAfter, by simp [hResume]⟩

end CallKind

/--
Result of evaluating imported Yul while leaving external CALL-family
interactions open.

`done` matches the ordinary imported evaluator result. `call` records a visible
external request and a continuation for every possible response. This is the
small interaction tree used by the open CALL proof: the outside world is not
interpreted here.
-/
inductive YulOpenResult (α : Type u) where
  | done : Except EvmYul.Yul.Exception α → YulOpenResult α
  | call : OpenCall (YulOpenResult α) → YulOpenResult α

namespace YulOpenResult

def ok {α : Type u} (value : α) : YulOpenResult α :=
  .done (.ok value)

def error {α : Type u} (err : EvmYul.Yul.Exception) : YulOpenResult α :=
  .done (.error err)

def bind {α : Type u} {β : Type v} (result : YulOpenResult α)
    (next : α → YulOpenResult β) : YulOpenResult β :=
  match result with
  | .done (.ok value) => next value
  | .done (.error err) => .done (.error err)
  | .call externalCall =>
      .call
        { site := externalCall.site
          resume := fun response =>
            bind (externalCall.resume response) next }

def map {α : Type u} {β : Type v}
    (f : α → β) (result : YulOpenResult α) : YulOpenResult β :=
  bind result (fun value => .ok (f value))

def liftExceptCall {α : Type u}
    (call : OpenCall (Except EvmYul.Yul.Exception α)) :
    OpenCall (YulOpenResult α) where
  site := call.site
  resume := fun response => .done (call.resume response)

def toOpenResult {α : Type u} :
    YulOpenResult α → OpenResult EvmYul.Yul.Exception α
  | .done result => .done result
  | .call externalCall =>
      .call
        { site := externalCall.site
          resume := fun response =>
            toOpenResult (externalCall.resume response) }

theorem toOpenResult_bind {α : Type u} {β : Type v}
    (result : YulOpenResult α) (next : α → YulOpenResult β) :
    toOpenResult (bind result next) =
      OpenResult.bind (toOpenResult result) (fun value =>
        toOpenResult (next value)) := by
  exact
    (YulOpenResult.rec
      (motive_1 := fun result =>
        ∀ next : α → YulOpenResult β,
          toOpenResult (bind result next) =
            OpenResult.bind (toOpenResult result) (fun value =>
              toOpenResult (next value)))
      (motive_2 := fun externalCall =>
        ∀ next : α → YulOpenResult β,
          toOpenResult (bind (.call externalCall) next) =
            OpenResult.bind (toOpenResult (.call externalCall)) (fun value =>
              toOpenResult (next value)))
      (done := by
        intro result next
        cases result <;> rfl)
      (call := by
        intro _ hCall next
        exact hCall next)
      (mk := by
        intro _ _ ih next
        simp [bind, toOpenResult, OpenResult.bind]
        funext response
        exact ih response next)
      result) next

@[simp] theorem liftExceptCall_resume {α : Type u}
    (call : OpenCall (Except EvmYul.Yul.Exception α))
    (response : CallResponse) :
    (liftExceptCall call).resume response =
      .done (call.resume response) :=
  rfl

end YulOpenResult

namespace YulOpen

abbrev State := EvmYul.Yul.State
abbrev Expr := EvmYul.Yul.Ast.Expr
abbrev Stmt := EvmYul.Yul.Ast.Stmt
abbrev Contract := EvmYul.Yul.Ast.YulContract
abbrev Exception := EvmYul.Yul.Exception

def headResult
    (result : YulOpenResult (State × List Word)) :
    YulOpenResult (State × Word) :=
  YulOpenResult.bind result fun pair =>
    .done (EvmYul.Yul.head' (.ok pair))

def reverseResult
    (result : YulOpenResult (State × List Word)) :
    YulOpenResult (State × List Word) :=
  YulOpenResult.map
    (fun pair => (pair.1, pair.2.reverse))
    result

def consResult (arg : Word)
    (result : YulOpenResult (State × List Word)) :
    YulOpenResult (State × List Word) :=
  YulOpenResult.map
    (fun pair => (pair.1, arg :: pair.2))
    result

def callFunction? (functionName? : Option EvmYul.Yul.Ast.YulFunctionName)
    (code : Contract) : Option EvmYul.Yul.Ast.FunctionDefinition :=
  match functionName? with
  | none =>
      some (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
        [code.dispatcher])
  | some functionName => code.functions.lookup functionName

mutual

/--
Open analogue of imported `Yul.evalArgs`.

Evaluation follows the imported fuel/list order, but any nested CALL-family
primitive reached by `eval` can suspend and expose an open request before the
tail arguments are evaluated.
-/
def evalArgs (fuel : Nat) (args : List Expr)
    (codeOverride : Option Contract) (state : State) :
    YulOpenResult (State × List Word) :=
  match fuel with
  | 0 => .error .OutOfFuel
  | .succ fuel' =>
      match args with
      | [] => .ok (state, [])
      | arg :: rest =>
          evalTail fuel' rest codeOverride
            (eval fuel' arg codeOverride state)

/-- Open analogue of imported `Yul.evalTail`. -/
def evalTail (fuel : Nat) (args : List Expr)
    (codeOverride : Option Contract)
    (head : YulOpenResult (State × Word)) :
    YulOpenResult (State × List Word) :=
  YulOpenResult.bind head fun headPair =>
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
        consResult headPair.2
          (evalArgs fuel' args codeOverride headPair.1)

/--
Open analogue of imported `Yul.evalValues`.

Non-external primitive calls still delegate to the imported closed primitive
semantics after their arguments are evaluated. CALL-family primitive calls
suspend at `CallKind.yulPrimitiveEvalValuesOpenCall?`, and internal user calls
run through `YulOpen.call` so CALL-family operations in callee bodies remain
visible to the open boundary.
-/
def evalValues (fuel : Nat) (expr : Expr)
    (codeOverride : Option Contract) (state : State) :
    YulOpenResult (State × List Word) :=
  match fuel with
  | 0 => .error .OutOfFuel
  | .succ fuel' =>
      match expr with
      | .Call (.inl prim) args =>
          YulOpenResult.bind
            (reverseResult (evalArgs fuel' args.reverse codeOverride state))
            fun pair =>
              match CallKind.yulPrimitiveEvalValuesOpenCall?
                  pair.1 prim pair.2 with
              | some call =>
                  .call (YulOpenResult.liftExceptCall call)
              | none => .done (EvmYul.Yul.primCall fuel' pair.1 prim pair.2)
      | .Call (.inr functionName) args =>
          YulOpenResult.bind
            (reverseResult (evalArgs fuel' args.reverse codeOverride state))
            fun pair =>
              call fuel' pair.2 functionName codeOverride pair.1
      | .Var id =>
          match state.lookup? id with
          | some value => .ok (state, [value])
          | none => .error (.UnknownIdentifier id)
      | .Lit value =>
          .ok (state, [value])

/-- Open analogue of imported `Yul.eval`. -/
def eval (fuel : Nat) (expr : Expr)
    (codeOverride : Option Contract) (state : State) :
    YulOpenResult (State × Word) :=
  headResult (evalValues fuel expr codeOverride state)

def execPrimCall (fuel : Nat) (prim : EvmYul.Operation .Yul)
    (vars : List EvmYul.Identifier)
    (argsResult : YulOpenResult (State × List Word)) :
    YulOpenResult State :=
  YulOpenResult.bind argsResult fun pair =>
    match CallKind.yulPrimitiveEvalValuesOpenCall? pair.1 prim pair.2 with
    | some call =>
        YulOpenResult.bind (.call (YulOpenResult.liftExceptCall call))
          fun result =>
            .done (EvmYul.Yul.multifill' vars (.ok result))
    | none =>
        .done (EvmYul.Yul.multifill' vars
          (EvmYul.Yul.primCall fuel pair.1 prim pair.2))

def execCall (fuel : Nat) (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (vars : List EvmYul.Identifier) (codeOverride : Option Contract)
    (argsResult : YulOpenResult (State × List Word)) :
    YulOpenResult State :=
  YulOpenResult.bind argsResult fun pair =>
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
        YulOpenResult.bind
          (call fuel' pair.2 functionName codeOverride pair.1)
          fun callResult =>
            .done (EvmYul.Yul.multifill' vars (.ok callResult))

/--
Open analogue of imported `Yul.execSeq`.

The control-flow behavior is the imported interpreter's behavior, but any
statement head that reaches a CALL-family primitive can suspend before the tail
is executed.
-/
def execSeq (fuel : Nat) (stmts : List Stmt)
    (codeOverride : Option Contract) (state : State) :
    YulOpenResult State :=
  match fuel with
  | 0 => .error .OutOfFuel
  | .succ fuel' =>
      match stmts with
      | [] => .ok state
      | stmt :: rest =>
          YulOpenResult.bind (exec fuel' stmt codeOverride state) fun state' =>
            match state' with
            | .Ok _ _ => execSeq fuel' rest codeOverride state'
            | .OutOfFuel => .ok state'
            | .Checkpoint _ => .ok state'

/-- Open analogue of imported `Yul.exec`. -/
def exec (fuel : Nat) (stmt : Stmt)
    (codeOverride : Option Contract) (state : State) :
    YulOpenResult State :=
  match fuel with
  | 0 => .error .OutOfFuel
  | .succ fuel' =>
      match stmt with
      | .Block stmts =>
          YulOpenResult.bind (execSeq fuel' stmts codeOverride state) fun state' =>
            .ok (state'.restrictStoreTo state.store)
      | .Let vars exprOption =>
          match EvmYul.Yul.checkDeclaration state vars with
          | .error err => .error err
          | .ok () =>
              match exprOption with
              | .none => .ok (state.zeroFill vars)
              | .some expr =>
                  YulOpenResult.bind (evalValues fuel' expr codeOverride state)
                    fun result =>
                      .done (EvmYul.Yul.multifill' vars (.ok result))
      | .Assign vars expr =>
          match EvmYul.Yul.checkAssignment state vars with
          | .error err => .error err
          | .ok () =>
              YulOpenResult.bind (evalValues fuel' expr codeOverride state)
                fun result =>
                  .done (EvmYul.Yul.multifill' vars (.ok result))
      | .If cond body =>
          YulOpenResult.bind (eval fuel' cond codeOverride state) fun result =>
            if result.2 ≠ EvmYul.UInt256.ofNat 0 then
              exec fuel' (.Block body) codeOverride result.1
            else
              .ok result.1
      | .ExprStmtCall expr =>
          match expr with
          | .Call (.inl prim) args =>
              execPrimCall fuel' prim []
                (reverseResult (evalArgs fuel' args.reverse codeOverride state))
          | .Call (.inr functionName) args =>
              execCall fuel' functionName [] codeOverride
                (reverseResult (evalArgs fuel' args.reverse codeOverride state))
          | _ => .error .InvalidExpression
      | .Switch cond cases defaultBody =>
          YulOpenResult.bind (eval fuel' cond codeOverride state) fun result =>
            exec fuel'
              (.Block (EvmYul.Yul.selectSwitchCase result.2 defaultBody cases))
              codeOverride result.1
      | .For cond post body =>
          loop fuel' cond post body codeOverride state
      | .Continue =>
          .ok (EvmYul.Yul.State.setContinue state)
      | .Break =>
          .ok (EvmYul.Yul.State.setBreak state)
      | .Leave =>
          .ok (EvmYul.Yul.State.setLeave state)

/-- Open analogue of imported `Yul.loop`. -/
def loop (fuel : Nat) (cond : Expr) (post body : List Stmt)
    (codeOverride : Option Contract) (state : State) :
    YulOpenResult State :=
  match fuel with
  | 0 => .error .OutOfFuel
  | 1 => .error .OutOfFuel
  | fuel' + 1 + 1 =>
      YulOpenResult.bind
        (eval fuel' cond codeOverride (EvmYul.Yul.State.mkOk state))
        fun condResult =>
          if condResult.2 = EvmYul.UInt256.ofNat 0 then
            .ok (EvmYul.Yul.State.overwrite? condResult.1 state)
          else
            YulOpenResult.bind
              (exec fuel' (.Block body) codeOverride condResult.1)
              fun bodyResult =>
                match bodyResult with
                | .OutOfFuel =>
                    .ok (EvmYul.Yul.State.overwrite? bodyResult state)
                | .Checkpoint (.Break _ _) =>
                    .ok
                      (EvmYul.Yul.State.overwrite?
                        (EvmYul.Yul.State.reviveJump bodyResult) state)
                | .Checkpoint (.Leave _ _) =>
                    .ok (EvmYul.Yul.State.overwrite? bodyResult state)
                | .Checkpoint (.Continue _ _) | _ =>
                    YulOpenResult.bind
                      (exec fuel' (.Block post) codeOverride
                        (EvmYul.Yul.State.reviveJump bodyResult))
                      fun postResult =>
                        let stateAfterPost :=
                          EvmYul.Yul.State.overwrite? postResult state
                        match postResult with
                        | .OutOfFuel => .ok stateAfterPost
                        | .Checkpoint (.Leave _ _) => .ok stateAfterPost
                        | _ =>
                            YulOpenResult.bind
                              (exec fuel' (.For cond post body) codeOverride
                                stateAfterPost)
                              fun loopResult =>
                                .ok
                                  (EvmYul.Yul.State.overwrite? loopResult state)

/--
Open analogue of imported `Yul.call` for internal user functions.

This runs the selected callee body through `YulOpen.exec`, so CALL-family
primitive operations inside the callee body remain visible as open external
interactions. When an executing-contract override is present, internal function
resolution uses that fixed code image directly. The account map is consulted
only for executions without an override: reentrant external responses may
mutate account state, but they do not replace the code image of the already
executing frame.
-/
def call (fuel : Nat) (args : List Word)
    (functionName? : Option EvmYul.Yul.Ast.YulFunctionName)
    (codeOverride : Option Contract) (state : State) :
    YulOpenResult (State × List Word) :=
  match fuel with
  | 0 => .error .OutOfFuel
  | .succ fuel' =>
      let code? : Option Contract :=
        match codeOverride with
        | some code => some code
        | none =>
            match state.sharedState.accountMap.find?
                state.executionEnv.codeOwner with
            | none => none
            | some yulContract => some yulContract.code
      match code? with
      | none =>
          .error (.MissingContract (s!"{state.executionEnv.codeOwner}"))
      | some code =>
          match callFunction? functionName? code with
          | none =>
              .error (.MissingContractFunction (functionName?.getD ".none"))
          | some f =>
              let state₁ :=
                EvmYul.Yul.State.mkOk
                  (EvmYul.Yul.State.initcall f.params f.rets args state)
              YulOpenResult.bind
                (exec fuel' (.Block f.body) codeOverride state₁)
                fun state₂ =>
                  let state₃ :=
                    EvmYul.Yul.State.setStore
                      (EvmYul.Yul.State.overwrite?
                        (EvmYul.Yul.State.reviveJump state₂) state)
                      state
                  .ok (state₃, List.map state₂.lookup! f.rets)

end

/--
An executing-contract override resolves an internal user call without
consulting mutable account state.

This is the decomposition used by compiler preservation after arbitrary
related external responses: the fixed source contract and lowered target
program remain aligned even if reentrant execution changed the caller account.
-/
theorem call_succ_eq_bind_body_of_override_function
    (fuel : Nat) (args : List Word)
    (functionName? : Option EvmYul.Yul.Ast.YulFunctionName)
    (contract : Contract) (state : State)
    {f : EvmYul.Yul.Ast.FunctionDefinition}
    (hFunction :
      callFunction? functionName? contract = some f) :
    call fuel.succ args functionName? (some contract) state =
      YulOpenResult.bind
        (exec fuel (.Block f.body) (some contract)
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall f.params f.rets args state)))
        fun state₂ =>
          let state₃ :=
            EvmYul.Yul.State.setStore
              (EvmYul.Yul.State.overwrite?
                (EvmYul.Yul.State.reviveJump state₂) state)
              state
          .ok (state₃, List.map state₂.lookup! f.rets) := by
  simp [call, hFunction]

theorem call_succ_eq_bind_body_of_find_function
    (fuel : Nat) (args : List Word)
    (functionName? : Option EvmYul.Yul.Ast.YulFunctionName)
    (codeOverride : Option Contract) (state : State)
    {yulContract : EvmYul.Account .Yul} {f : EvmYul.Yul.Ast.FunctionDefinition}
    (hFind :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner =
        some yulContract)
    (hFunction :
      callFunction? functionName? (codeOverride.getD yulContract.code) =
        some f) :
    call fuel.succ args functionName? codeOverride state =
      YulOpenResult.bind
        (exec fuel (.Block f.body) codeOverride
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall f.params f.rets args state)))
        fun state₂ =>
          let state₃ :=
            EvmYul.Yul.State.setStore
              (EvmYul.Yul.State.overwrite?
                (EvmYul.Yul.State.reviveJump state₂) state)
              state
          .ok (state₃, List.map state₂.lookup! f.rets) := by
  cases codeOverride with
  | none =>
      have hFunction' :
          callFunction? functionName? yulContract.code = some f := by
        simpa using hFunction
      simp [call, hFind, hFunction']
  | some code =>
      have hFunction' :
          callFunction? functionName? code = some f := by
        simpa using hFunction
      simp [call, hFunction']

theorem evalValues_prim_call_suspends_of_evalArgs_done
    {fuel : Nat} {prim : EvmYul.Operation .Yul} {args : List Expr}
    {codeOverride : Option Contract} {state stateAfterArgs : State}
    {rawValues : List Word}
    {call :
      OpenCall
        (Except EvmYul.Yul.Exception (State × List Word))}
    (hArgs :
      evalArgs fuel args.reverse codeOverride state =
        .done (.ok (stateAfterArgs, rawValues)))
    (hCall :
      CallKind.yulPrimitiveEvalValuesOpenCall?
          stateAfterArgs prim rawValues.reverse =
        some call) :
    evalValues fuel.succ (.Call (.inl prim) args) codeOverride state =
      .call (YulOpenResult.liftExceptCall call) := by
  simp [evalValues, reverseResult, YulOpenResult.map, YulOpenResult.bind,
    YulOpenResult.ok, YulOpenResult.liftExceptCall, hArgs, hCall]

theorem evalValues_prim_call_closed_of_evalArgs_done_no_open
    {fuel : Nat} {prim : EvmYul.Operation .Yul} {args : List Expr}
    {codeOverride : Option Contract} {state stateAfterArgs : State}
    {rawValues : List Word}
    (hArgs :
      evalArgs fuel args.reverse codeOverride state =
        .done (.ok (stateAfterArgs, rawValues)))
    (hCall :
      CallKind.yulPrimitiveEvalValuesOpenCall?
          stateAfterArgs prim rawValues.reverse =
        none) :
    evalValues fuel.succ (.Call (.inl prim) args) codeOverride state =
      .done
        (EvmYul.Yul.primCall fuel stateAfterArgs prim rawValues.reverse) := by
  simp [evalValues, reverseResult, YulOpenResult.map, YulOpenResult.bind,
    YulOpenResult.ok, hArgs, hCall]

theorem execPrimCall_done_eq_closed
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {vars : List EvmYul.Identifier}
    {argsResult : YulOpenResult (State × List Word)}
    {closedArgs : Except Exception (State × List Word)}
    {result : Except Exception State}
    (hArgs : argsResult = .done closedArgs)
    (hOpen :
      execPrimCall fuel prim vars argsResult = .done result) :
    EvmYul.Yul.execPrimCall fuel prim vars closedArgs = result := by
  subst argsResult
  cases closedArgs with
  | error err =>
      simpa [execPrimCall, EvmYul.Yul.execPrimCall, YulOpenResult.bind]
        using hOpen
  | ok pair =>
      rcases pair with ⟨stateAfterArgs, values⟩
      cases hCall :
          CallKind.yulPrimitiveEvalValuesOpenCall?
            stateAfterArgs prim values with
      | none =>
          simp [execPrimCall, EvmYul.Yul.execPrimCall, YulOpenResult.bind,
            hCall] at hOpen ⊢
          exact hOpen
      | some call =>
          simp [execPrimCall, YulOpenResult.bind, hCall] at hOpen

def overwriteLoopResult (state : State) :
    Except Exception State → Except Exception State
  | .error err => .error err
  | .ok loopState =>
      .ok (EvmYul.Yul.State.overwrite? loopState state)

theorem bind_done_overwrite_result_eq_closed
    {state : State} {loopResult result : Except Exception State}
    (h :
      YulOpenResult.bind (.done loopResult)
          (fun loopState =>
            YulOpenResult.ok
              (EvmYul.Yul.State.overwrite? loopState state)) =
        .done result) :
    overwriteLoopResult state loopResult = result := by
  cases loopResult <;>
    simpa [YulOpenResult.bind, YulOpenResult.ok, overwriteLoopResult] using h

set_option maxHeartbeats 800000 in
mutual
  theorem evalArgs_done_eq_closed
      {fuel : Nat} {args : List Expr} {codeOverride : Option Contract}
      {state : State}
      {result : Except Exception (State × List Word)}
      (hOpen :
        evalArgs fuel args codeOverride state = .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.evalArgs fuel args codeOverride state = result := by
    cases fuel with
    | zero =>
        simpa [evalArgs, EvmYul.Yul.evalArgs, YulOpenResult.error] using hOpen
    | succ fuel' =>
        cases args with
        | nil =>
            simpa [evalArgs, EvmYul.Yul.evalArgs, YulOpenResult.ok]
              using hOpen
        | cons head tail =>
            cases hHead : eval fuel' head codeOverride state with
            | done headResult =>
                have hOpenTail :
                    evalTail fuel' tail codeOverride (.done headResult) =
                      .done result := by
                  simpa [evalArgs, hHead] using hOpen
                have hHeadClosed :
                    EvmYul.Yul.eval fuel' head codeOverride state =
                      headResult :=
                  eval_done_eq_closed hHead hNoOverride
                have hTailClosed :
                    EvmYul.Yul.evalTail fuel' tail codeOverride
                        headResult =
                      result :=
                  evalTail_done_eq_closed
                    (fuel := fuel') (args := tail)
                    (codeOverride := codeOverride)
                    (headResult := headResult) hOpenTail hNoOverride
                simpa [EvmYul.Yul.evalArgs, hHeadClosed] using hTailClosed
            | call call =>
                simp [evalArgs, evalTail, YulOpenResult.bind, hHead] at hOpen

  theorem evalTail_done_eq_closed
      {fuel : Nat} {args : List Expr} {codeOverride : Option Contract}
      {headResult : Except Exception (State × Word)}
      {result : Except Exception (State × List Word)}
      (hOpen :
        evalTail fuel args codeOverride (.done headResult) = .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.evalTail fuel args codeOverride headResult = result := by
    cases headResult with
    | error err =>
        simpa [evalTail, EvmYul.Yul.evalTail, YulOpenResult.bind] using hOpen
    | ok headPair =>
        rcases headPair with ⟨stateAfterHead, value⟩
        cases fuel with
        | zero =>
            simpa [evalTail, EvmYul.Yul.evalTail, YulOpenResult.bind,
              YulOpenResult.error] using hOpen
        | succ fuel' =>
            simp [evalTail, EvmYul.Yul.evalTail, YulOpenResult.bind,
              consResult, YulOpenResult.map, YulOpenResult.ok] at hOpen ⊢
            cases hArgs :
                evalArgs fuel' args codeOverride stateAfterHead with
            | done argsResult =>
                have hArgsClosed :
                    EvmYul.Yul.evalArgs fuel' args codeOverride
                        stateAfterHead =
                      argsResult :=
                  evalArgs_done_eq_closed hArgs hNoOverride
                cases argsResult with
                | error err =>
                    simp [hArgs, hArgsClosed, YulOpenResult.bind,
                      EvmYul.Yul.cons'] at hOpen ⊢
                    exact hOpen
                | ok argsPair =>
                    rcases argsPair with ⟨stateAfterArgs, values⟩
                    simp [hArgs, hArgsClosed, YulOpenResult.bind,
                      EvmYul.Yul.cons'] at hOpen ⊢
                    exact hOpen
            | call call =>
                simp [hArgs, YulOpenResult.bind] at hOpen

  theorem evalValues_done_eq_closed
      {fuel : Nat} {expr : Expr} {codeOverride : Option Contract}
      {state : State}
      {result : Except Exception (State × List Word)}
      (hOpen :
        evalValues fuel expr codeOverride state = .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.evalValues fuel expr codeOverride state = result := by
    cases fuel with
    | zero =>
        simpa [evalValues, EvmYul.Yul.evalValues, YulOpenResult.error]
          using hOpen
    | succ fuel' =>
        cases expr with
        | Lit value =>
            simpa [evalValues, EvmYul.Yul.evalValues, YulOpenResult.ok]
              using hOpen
        | Var id =>
            cases hLookup : state.lookup? id with
            | none =>
                simpa [evalValues, EvmYul.Yul.evalValues, hLookup,
                  YulOpenResult.error] using hOpen
            | some value =>
                simpa [evalValues, EvmYul.Yul.evalValues, hLookup,
                  YulOpenResult.ok] using hOpen
        | Call callee args =>
            cases callee with
            | inl prim =>
                simp [evalValues, EvmYul.Yul.evalValues, reverseResult,
                  YulOpenResult.map] at hOpen ⊢
                cases hArgs :
                    evalArgs fuel' args.reverse codeOverride state with
                | done argsResult =>
                    have hArgsClosed :
                        EvmYul.Yul.evalArgs fuel' args.reverse codeOverride
                            state =
                          argsResult :=
                      evalArgs_done_eq_closed hArgs hNoOverride
                    cases argsResult with
                    | error err =>
                        simp [hArgs, hArgsClosed, YulOpenResult.bind,
                          YulOpenResult.ok, EvmYul.Yul.reverse'] at hOpen ⊢
                        exact hOpen
                    | ok argsPair =>
                        rcases argsPair with ⟨stateAfterArgs, values⟩
                        cases hCall :
                            CallKind.yulPrimitiveEvalValuesOpenCall?
                              stateAfterArgs prim values.reverse with
                        | none =>
                            simp [hArgs, hArgsClosed, hCall,
                              YulOpenResult.bind,
                              YulOpenResult.ok,
                              EvmYul.Yul.reverse'] at hOpen ⊢
                            exact hOpen
                        | some call =>
                            simp [hArgs, hCall, YulOpenResult.bind,
                              YulOpenResult.ok] at hOpen
                | call call =>
                    simp [hArgs, YulOpenResult.bind] at hOpen
            | inr functionName =>
                simp [evalValues, EvmYul.Yul.evalValues, reverseResult,
                  YulOpenResult.map] at hOpen ⊢
                cases hArgs :
                    evalArgs fuel' args.reverse codeOverride state with
                | done argsResult =>
                    have hArgsClosed :
                        EvmYul.Yul.evalArgs fuel' args.reverse codeOverride
                            state =
                          argsResult :=
                      evalArgs_done_eq_closed hArgs hNoOverride
                    cases argsResult with
                    | error err =>
                        simp [hArgs, hArgsClosed, YulOpenResult.bind,
                          YulOpenResult.ok, EvmYul.Yul.reverse'] at hOpen ⊢
                        exact hOpen
                    | ok argsPair =>
                        rcases argsPair with ⟨stateAfterArgs, values⟩
                        cases hCall :
                            call fuel' values.reverse (some functionName)
                              codeOverride stateAfterArgs with
                        | done callResult =>
                            have hCallClosed :
                                EvmYul.Yul.call fuel' values.reverse
                                    (some functionName) codeOverride
                                    stateAfterArgs =
                                  callResult :=
                              call_done_eq_closed hCall hNoOverride
                            simp [hArgs, hArgsClosed, hCall, hCallClosed,
                              YulOpenResult.bind, YulOpenResult.ok,
                              EvmYul.Yul.reverse'] at hOpen ⊢
                            exact hOpen
                        | call externalCall =>
                            simp [hArgs, hCall, YulOpenResult.bind,
                              YulOpenResult.ok] at hOpen
                | call call =>
                    simp [hArgs, YulOpenResult.bind] at hOpen

  theorem eval_done_eq_closed
      {fuel : Nat} {expr : Expr} {codeOverride : Option Contract}
      {state : State}
      {result : Except Exception (State × Word)}
      (hOpen :
        eval fuel expr codeOverride state = .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.eval fuel expr codeOverride state = result := by
    simp [eval, EvmYul.Yul.eval, headResult] at hOpen ⊢
    cases hValues : evalValues fuel expr codeOverride state with
    | done valuesResult =>
        have hValuesClosed :
            EvmYul.Yul.evalValues fuel expr codeOverride state =
              valuesResult :=
          evalValues_done_eq_closed hValues hNoOverride
        cases valuesResult with
        | error err =>
            simp [hValues, hValuesClosed, YulOpenResult.bind,
              EvmYul.Yul.head'] at hOpen ⊢
            exact hOpen
        | ok valuesPair =>
            rcases valuesPair with ⟨stateAfter, values⟩
            simp [hValues, hValuesClosed, YulOpenResult.bind,
              EvmYul.Yul.head'] at hOpen ⊢
            exact hOpen
    | call call =>
        simp [hValues, YulOpenResult.bind] at hOpen

  theorem execCall_done_eq_closed
      {fuel : Nat} {functionName : EvmYul.Yul.Ast.YulFunctionName}
      {vars : List EvmYul.Identifier} {codeOverride : Option Contract}
      {argsResult : YulOpenResult (State × List Word)}
      {closedArgs : Except Exception (State × List Word)}
      {result : Except Exception State}
      (hArgs : argsResult = .done closedArgs)
      (hOpen :
        execCall fuel functionName vars codeOverride argsResult =
          .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.execCall fuel functionName vars codeOverride closedArgs =
        result := by
    subst argsResult
    cases closedArgs with
    | error err =>
        simpa [execCall, EvmYul.Yul.execCall, YulOpenResult.bind] using hOpen
    | ok pair =>
        rcases pair with ⟨stateAfterArgs, values⟩
        cases fuel with
        | zero =>
            simpa [execCall, EvmYul.Yul.execCall, YulOpenResult.bind,
              YulOpenResult.error] using hOpen
        | succ fuel' =>
            cases hCall :
                call fuel' values (some functionName) codeOverride
                  stateAfterArgs with
            | done callResult =>
                have hCallClosed :
                    EvmYul.Yul.call fuel' values (some functionName)
                        codeOverride stateAfterArgs =
                      callResult :=
                  call_done_eq_closed hCall hNoOverride
                cases callResult with
                | error err =>
                    simp [execCall, EvmYul.Yul.execCall, hCall, hCallClosed,
                      YulOpenResult.bind] at hOpen ⊢
                    exact hOpen
                | ok callPair =>
                    simp [execCall, EvmYul.Yul.execCall, hCall, hCallClosed,
                      YulOpenResult.bind] at hOpen ⊢
                    exact hOpen
            | call externalCall =>
                simp [execCall, hCall, YulOpenResult.bind] at hOpen

  theorem execSeq_done_eq_closed
      {fuel : Nat} {stmts : List Stmt} {codeOverride : Option Contract}
      {state : State} {result : Except Exception State}
      (hOpen :
        execSeq fuel stmts codeOverride state = .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.execSeq fuel stmts codeOverride state = result := by
    cases fuel with
    | zero =>
        simpa [execSeq, EvmYul.Yul.execSeq, YulOpenResult.error] using hOpen
    | succ fuel' =>
        cases stmts with
        | nil =>
            simpa [execSeq, EvmYul.Yul.execSeq, YulOpenResult.ok] using hOpen
        | cons stmt rest =>
            cases hHead : exec fuel' stmt codeOverride state with
            | done headResult =>
                have hHeadClosed :
                    EvmYul.Yul.exec fuel' stmt codeOverride state =
                      headResult :=
                  exec_done_eq_closed hHead hNoOverride
                cases headResult with
                | error err =>
                    simp [execSeq, EvmYul.Yul.execSeq, hHead, hHeadClosed,
                      YulOpenResult.bind] at hOpen ⊢
                    exact hOpen
                | ok stateAfter =>
                    cases stateAfter with
                    | Ok shared store =>
                        have hTailOpen :
                            execSeq fuel' rest codeOverride
                                (.Ok shared store) =
                              .done result := by
                          simpa [execSeq, hHead, YulOpenResult.bind] using hOpen
                        have hTailClosed :
                            EvmYul.Yul.execSeq fuel' rest codeOverride
                                (.Ok shared store) =
                              result :=
                          execSeq_done_eq_closed hTailOpen hNoOverride
                        simpa [EvmYul.Yul.execSeq, hHeadClosed]
                          using hTailClosed
                    | OutOfFuel =>
                        simp [execSeq, EvmYul.Yul.execSeq, hHead, hHeadClosed,
                          YulOpenResult.bind, YulOpenResult.ok] at hOpen ⊢
                        exact hOpen
                    | Checkpoint jump =>
                        simp [execSeq, EvmYul.Yul.execSeq, hHead, hHeadClosed,
                          YulOpenResult.bind, YulOpenResult.ok] at hOpen ⊢
                        exact hOpen
            | call call =>
                simp [execSeq, YulOpenResult.bind, hHead] at hOpen

  theorem exec_done_eq_closed
      {fuel : Nat} {stmt : Stmt} {codeOverride : Option Contract}
      {state : State} {result : Except Exception State}
      (hOpen :
        exec fuel stmt codeOverride state = .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.exec fuel stmt codeOverride state = result := by
    cases fuel with
    | zero =>
        simpa [exec, EvmYul.Yul.exec, YulOpenResult.error] using hOpen
    | succ fuel' =>
        cases stmt with
        | Block stmts =>
            cases hSeq : execSeq fuel' stmts codeOverride state with
            | done seqResult =>
                have hSeqClosed :
                    EvmYul.Yul.execSeq fuel' stmts codeOverride state =
                      seqResult :=
                  execSeq_done_eq_closed hSeq hNoOverride
                cases seqResult with
                | error err =>
                    simp [exec, EvmYul.Yul.exec, hSeq, hSeqClosed,
                      YulOpenResult.bind] at hOpen ⊢
                    exact hOpen
                | ok stateAfter =>
                    simp [exec, EvmYul.Yul.exec, hSeq, hSeqClosed,
                      YulOpenResult.bind, YulOpenResult.ok] at hOpen ⊢
                    exact hOpen
            | call call =>
                simp [exec, YulOpenResult.bind, hSeq] at hOpen
        | Let vars exprOption =>
            cases hCheck : EvmYul.Yul.checkDeclaration state vars with
            | error err =>
                have hOpen' : Except.error err = result := by
                  rw [exec.eq_def] at hOpen
                  simpa [hCheck, YulOpenResult.error] using hOpen
                have hClosed :
                    EvmYul.Yul.exec fuel'.succ (.Let vars exprOption)
                        codeOverride state =
                      Except.error err := by
                  cases exprOption with
                  | none =>
                      rw [EvmYul.Yul.exec.eq_def]
                      simp [hCheck]
                  | some expr =>
                      cases expr with
                      | Lit value =>
                          rw [EvmYul.Yul.exec.eq_def]
                          simp [hCheck]
                      | Var id =>
                          rw [EvmYul.Yul.exec.eq_def]
                          simp [hCheck]
                      | Call callee args =>
                          cases callee with
                          | inl prim =>
                              rw [EvmYul.Yul.exec.eq_def]
                              simp [hCheck]
                          | inr functionName =>
                              rw [EvmYul.Yul.exec.eq_def]
                              simp [hCheck]
                exact hClosed.trans hOpen'
            | ok unit =>
                cases exprOption with
                | none =>
                    simpa [exec, EvmYul.Yul.exec, hCheck, YulOpenResult.ok]
                      using hOpen
                | some expr =>
                    cases hValues : evalValues fuel' expr codeOverride state with
                    | done valuesResult =>
                        have hValuesClosed :
                            EvmYul.Yul.evalValues fuel' expr codeOverride state =
                              valuesResult :=
                          evalValues_done_eq_closed hValues hNoOverride
                        cases valuesResult with
                        | error err =>
                            simp [exec, EvmYul.Yul.exec, hCheck, hValues,
                              hValuesClosed, YulOpenResult.bind] at hOpen ⊢
                            exact hOpen
                        | ok valuesPair =>
                            rcases valuesPair with ⟨stateAfter, values⟩
                            simp [exec, EvmYul.Yul.exec, hCheck, hValues,
                              hValuesClosed, YulOpenResult.bind] at hOpen ⊢
                            exact hOpen
                    | call call =>
                        simp [exec, hCheck, hValues, YulOpenResult.bind]
                          at hOpen
        | Assign vars expr =>
            cases hCheck : EvmYul.Yul.checkAssignment state vars with
            | error err =>
                have hOpen' : Except.error err = result := by
                  simpa [exec, hCheck, YulOpenResult.error] using hOpen
                have hClosed :
                    EvmYul.Yul.exec fuel'.succ (.Assign vars expr)
                        codeOverride state =
                      Except.error err := by
                  rw [EvmYul.Yul.exec.eq_def]
                  simp [hCheck]
                exact hClosed.trans hOpen'
            | ok unit =>
                cases hValues : evalValues fuel' expr codeOverride state with
                | done valuesResult =>
                    have hValuesClosed :
                        EvmYul.Yul.evalValues fuel' expr codeOverride state =
                          valuesResult :=
                      evalValues_done_eq_closed hValues hNoOverride
                    cases valuesResult with
                    | error err =>
                        simp [exec, EvmYul.Yul.exec, hCheck, hValues,
                          hValuesClosed, YulOpenResult.bind] at hOpen ⊢
                        exact hOpen
                    | ok valuesPair =>
                        rcases valuesPair with ⟨stateAfter, values⟩
                        simp [exec, EvmYul.Yul.exec, hCheck, hValues,
                          hValuesClosed, YulOpenResult.bind] at hOpen ⊢
                        exact hOpen
                | call call =>
                    simp [exec, hCheck, hValues, YulOpenResult.bind] at hOpen
        | ExprStmtCall expr =>
            cases expr with
            | Lit value =>
                simpa [exec, EvmYul.Yul.exec, YulOpenResult.error] using hOpen
            | Var id =>
                simpa [exec, EvmYul.Yul.exec, YulOpenResult.error] using hOpen
            | Call callee args =>
                cases callee with
                | inl prim =>
                    cases hArgs :
                        reverseResult
                          (evalArgs fuel' args.reverse codeOverride state) with
                    | done closedArgs =>
                        have hArgsClosed :
                            EvmYul.Yul.reverse'
                              (EvmYul.Yul.evalArgs fuel' args.reverse
                                codeOverride state) =
                              closedArgs :=
                          by
                            simp [reverseResult, YulOpenResult.map]
                              at hArgs ⊢
                            cases hEvalArgs :
                                evalArgs fuel' args.reverse codeOverride
                                  state with
                            | done argsResult =>
                                have hEvalArgsClosed :
                                    EvmYul.Yul.evalArgs fuel' args.reverse
                                        codeOverride state =
                                      argsResult :=
                                  evalArgs_done_eq_closed hEvalArgs
                                    hNoOverride
                                cases argsResult with
                                | error err =>
                                    simp [hEvalArgs, hEvalArgsClosed,
                                      YulOpenResult.bind, EvmYul.Yul.reverse']
                                      at hArgs ⊢
                                    exact hArgs
                                | ok argsPair =>
                                    rcases argsPair with
                                      ⟨stateAfterArgs, values⟩
                                    simp [hEvalArgs, hEvalArgsClosed,
                                      YulOpenResult.bind, YulOpenResult.ok,
                                      EvmYul.Yul.reverse'] at hArgs ⊢
                                    exact hArgs
                            | call call =>
                                simp [hEvalArgs, YulOpenResult.bind] at hArgs
                        have hExecPrim :
                            EvmYul.Yul.execPrimCall fuel' prim [] closedArgs =
                              result :=
                          execPrimCall_done_eq_closed
                            (hArgs := hArgs)
                            (hOpen := by
                              simpa [exec, hArgs] using hOpen)
                        simpa [exec, EvmYul.Yul.exec, hArgsClosed]
                          using hExecPrim
                    | call call =>
                        simp [exec, execPrimCall, hArgs, YulOpenResult.bind]
                          at hOpen
                | inr functionName =>
                    cases hArgs :
                        reverseResult
                          (evalArgs fuel' args.reverse codeOverride state) with
                    | done closedArgs =>
                        have hArgsClosed :
                            EvmYul.Yul.reverse'
                              (EvmYul.Yul.evalArgs fuel' args.reverse
                                codeOverride state) =
                              closedArgs :=
                          by
                            simp [reverseResult, YulOpenResult.map]
                              at hArgs ⊢
                            cases hEvalArgs :
                                evalArgs fuel' args.reverse codeOverride
                                  state with
                            | done argsResult =>
                                have hEvalArgsClosed :
                                    EvmYul.Yul.evalArgs fuel' args.reverse
                                        codeOverride state =
                                      argsResult :=
                                  evalArgs_done_eq_closed hEvalArgs
                                    hNoOverride
                                cases argsResult with
                                | error err =>
                                    simp [hEvalArgs, hEvalArgsClosed,
                                      YulOpenResult.bind, EvmYul.Yul.reverse']
                                      at hArgs ⊢
                                    exact hArgs
                                | ok argsPair =>
                                    rcases argsPair with
                                      ⟨stateAfterArgs, values⟩
                                    simp [hEvalArgs, hEvalArgsClosed,
                                      YulOpenResult.bind, YulOpenResult.ok,
                                      EvmYul.Yul.reverse'] at hArgs ⊢
                                    exact hArgs
                            | call call =>
                                simp [hEvalArgs, YulOpenResult.bind] at hArgs
                        have hExecCall :
                            EvmYul.Yul.execCall fuel' functionName []
                                codeOverride closedArgs =
                              result :=
                          execCall_done_eq_closed
                            (hArgs := hArgs)
                            (hOpen := by
                              simpa [exec, hArgs] using hOpen)
                            hNoOverride
                        simpa [exec, EvmYul.Yul.exec, hArgsClosed]
                          using hExecCall
                    | call call =>
                        simp [exec, execCall, hArgs, YulOpenResult.bind]
                          at hOpen
        | Switch cond cases defaultBody =>
            cases hCond : eval fuel' cond codeOverride state with
            | done condResult =>
                have hCondClosed :
                    EvmYul.Yul.eval fuel' cond codeOverride state =
                      condResult :=
                  eval_done_eq_closed hCond hNoOverride
                cases condResult with
                | error err =>
                    simp [exec, EvmYul.Yul.exec, hCond, hCondClosed,
                      YulOpenResult.bind] at hOpen ⊢
                    exact hOpen
                | ok condPair =>
                    rcases condPair with ⟨stateAfterCond, value⟩
                    cases hBody :
                        exec fuel'
                          (.Block
                            (EvmYul.Yul.selectSwitchCase value defaultBody
                              cases))
                          codeOverride stateAfterCond with
                    | done bodyResult =>
                        have hBodyClosed :
                            EvmYul.Yul.exec fuel'
                              (.Block
                                (EvmYul.Yul.selectSwitchCase value defaultBody
                                  cases))
                              codeOverride stateAfterCond =
                              bodyResult :=
                          exec_done_eq_closed hBody hNoOverride
                        simp [exec, EvmYul.Yul.exec, hCond, hCondClosed,
                          hBody, hBodyClosed, YulOpenResult.bind] at hOpen ⊢
                        exact hOpen
                    | call call =>
                        simp [exec, hCond, hBody, YulOpenResult.bind] at hOpen
            | call call =>
                simp [exec, hCond, YulOpenResult.bind] at hOpen
        | For cond post body =>
            have hLoopClosed :
                EvmYul.Yul.loop fuel' cond post body codeOverride state =
                  result :=
              loop_done_eq_closed
                (fuel := fuel') (cond := cond) (post := post) (body := body)
                (codeOverride := codeOverride) (state := state)
                (by simpa [exec] using hOpen) hNoOverride
            rw [EvmYul.Yul.exec.eq_def]
            exact hLoopClosed
        | If cond body =>
            cases hCond : eval fuel' cond codeOverride state with
            | done condResult =>
                have hCondClosed :
                    EvmYul.Yul.eval fuel' cond codeOverride state =
                      condResult :=
                  eval_done_eq_closed hCond hNoOverride
                cases condResult with
                | error err =>
                    simp [exec, EvmYul.Yul.exec, hCond, hCondClosed,
                      YulOpenResult.bind] at hOpen ⊢
                    exact hOpen
                | ok condPair =>
                    rcases condPair with ⟨stateAfterCond, value⟩
                    by_cases hZero : value = EvmYul.UInt256.ofNat 0
                    · simp [exec, EvmYul.Yul.exec, hCond, hCondClosed, hZero,
                        YulOpenResult.bind, YulOpenResult.ok] at hOpen ⊢
                      exact hOpen
                    · have hNonzero :
                          value ≠ EvmYul.UInt256.ofNat 0 := hZero
                      have hZeroStruct :
                          value ≠ ({ val := 0 } : Word) := by
                        simpa [EvmYul.UInt256.ofNat] using hZero
                      cases hBody :
                          exec fuel' (.Block body) codeOverride
                            stateAfterCond with
                      | done bodyResult =>
                          have hBodyClosed :
                              EvmYul.Yul.exec fuel' (.Block body) codeOverride
                                  stateAfterCond =
                                bodyResult :=
                            exec_done_eq_closed hBody
                              hNoOverride
                          simp [exec, EvmYul.Yul.exec, hCond, hCondClosed,
                            hZero, hNonzero, hZeroStruct, hBody, hBodyClosed,
                            YulOpenResult.bind] at hOpen ⊢
                          exact hOpen
                      | call call =>
                          simp [exec, hCond, hZero, hNonzero, hZeroStruct,
                            hBody,
                            YulOpenResult.bind] at hOpen
            | call call =>
                simp [exec, hCond, YulOpenResult.bind] at hOpen
        | Continue =>
            simpa [exec, EvmYul.Yul.exec, YulOpenResult.ok] using hOpen
        | Break =>
            simpa [exec, EvmYul.Yul.exec, YulOpenResult.ok] using hOpen
        | Leave =>
            simpa [exec, EvmYul.Yul.exec, YulOpenResult.ok] using hOpen

  theorem loop_done_eq_closed
      {fuel : Nat} {cond : Expr} {post body : List Stmt}
      {codeOverride : Option Contract} {state : State}
      {result : Except Exception State}
      (hOpen :
        loop fuel cond post body codeOverride state = .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.loop fuel cond post body codeOverride state = result := by
    cases fuel with
    | zero =>
        simpa [loop, EvmYul.Yul.loop, YulOpenResult.error] using hOpen
    | succ fuel₁ =>
        cases fuel₁ with
        | zero =>
            simpa [loop, EvmYul.Yul.loop, YulOpenResult.error] using hOpen
        | succ fuel' =>
            cases hCond :
                eval fuel' cond codeOverride
                  (EvmYul.Yul.State.mkOk state) with
            | done condResult =>
                have hCondClosed :
                    EvmYul.Yul.eval fuel' cond codeOverride
                        (EvmYul.Yul.State.mkOk state) =
                      condResult :=
                  eval_done_eq_closed hCond
                    hNoOverride
                cases condResult with
                | error err =>
                    simp [loop, EvmYul.Yul.loop, hCond, hCondClosed,
                      YulOpenResult.bind] at hOpen ⊢
                    exact hOpen
                | ok condPair =>
                    rcases condPair with ⟨stateAfterCond, value⟩
                    by_cases hZero : value = EvmYul.UInt256.ofNat 0
                    · simp [loop, EvmYul.Yul.loop, hCond, hCondClosed, hZero,
                        YulOpenResult.bind, YulOpenResult.ok] at hOpen ⊢
                      exact hOpen
                    · have hZeroStruct :
                          value ≠ ({ val := 0 } : Word) := by
                        simpa [EvmYul.UInt256.ofNat] using hZero
                      cases hBody :
                          exec fuel' (.Block body) codeOverride
                            stateAfterCond with
                      | done bodyResult =>
                          have hBodyClosed :
                              EvmYul.Yul.exec fuel' (.Block body) codeOverride
                                  stateAfterCond =
                                bodyResult :=
                            exec_done_eq_closed hBody
                              hNoOverride
                          cases bodyResult with
                          | error err =>
                              simp [loop, EvmYul.Yul.loop, hCond, hCondClosed,
                                hZero, hZeroStruct, hBody, hBodyClosed,
                                YulOpenResult.bind] at hOpen ⊢
                              exact hOpen
                          | ok bodyState =>
                              cases bodyState with
                              | OutOfFuel =>
                                  simp [loop, EvmYul.Yul.loop, hCond,
                                    hCondClosed, hZero, hZeroStruct, hBody,
                                    hBodyClosed, YulOpenResult.bind,
                                    YulOpenResult.ok] at hOpen ⊢
                                  exact hOpen
                              | Checkpoint jump =>
                                  cases jump with
                                  | Break shared store =>
                                      simp [loop, EvmYul.Yul.loop, hCond,
                                        hCondClosed, hZero, hZeroStruct, hBody,
                                        hBodyClosed, YulOpenResult.bind,
                                        YulOpenResult.ok] at hOpen ⊢
                                      exact hOpen
                                  | Leave shared store =>
                                      simp [loop, EvmYul.Yul.loop, hCond,
                                        hCondClosed, hZero, hZeroStruct, hBody,
                                        hBodyClosed, YulOpenResult.bind,
                                        YulOpenResult.ok] at hOpen ⊢
                                      exact hOpen
                                  | Continue shared store =>
                                      cases hPost :
                                          exec fuel' (.Block post) codeOverride
                                            (EvmYul.Yul.State.reviveJump
                                              (.Checkpoint
                                                (.Continue shared store))) with
                                      | done postResult =>
                                          have hPostClosed :
                                              EvmYul.Yul.exec fuel'
                                                  (.Block post) codeOverride
                                                  (EvmYul.Yul.State.reviveJump
                                                    (.Checkpoint
                                                      (.Continue shared store))) =
                                                postResult :=
                                            exec_done_eq_closed
                                              (fuel := fuel')
                                              (stmt := .Block post)
                                              (codeOverride := codeOverride)
                                              (state :=
                                                EvmYul.Yul.State.reviveJump
                                                  (.Checkpoint
                                                    (.Continue shared store)))
                                              (result := postResult)
                                              hPost hNoOverride
                                          cases postResult with
                                          | error err =>
                                              simp [loop, EvmYul.Yul.loop,
                                                hCond, hCondClosed, hZero,
                                                hZeroStruct, hBody,
                                                hBodyClosed, hPost,
                                                hPostClosed,
                                                YulOpenResult.bind]
                                                at hOpen ⊢
                                              exact hOpen
                                          | ok postState =>
                                              let stateAfterPost :=
                                                EvmYul.Yul.State.overwrite?
                                                  postState state
                                              cases postState with
                                              | OutOfFuel =>
                                                  simp [loop, EvmYul.Yul.loop,
                                                    hCond, hCondClosed, hZero,
                                                    hZeroStruct, hBody,
                                                    hBodyClosed, hPost,
                                                    hPostClosed,
                                                    YulOpenResult.bind,
                                                    YulOpenResult.ok]
                                                    at hOpen ⊢
                                                  exact hOpen
                                              | Checkpoint postJump =>
                                                  cases postJump with
                                                  | Leave ps pv =>
                                                      simp [loop,
                                                        EvmYul.Yul.loop,
                                                        hCond, hCondClosed,
                                                        hZero, hZeroStruct,
                                                        hBody, hBodyClosed,
                                                        hPost, hPostClosed,
                                                        YulOpenResult.bind,
                                                        YulOpenResult.ok]
                                                        at hOpen ⊢
                                                      exact hOpen
                                                  | Break ps pv =>
                                                      cases hLoop :
                                                          exec fuel'
                                                            (.For cond post body)
                                                            codeOverride
                                                            stateAfterPost with
                                                      | done loopResult =>
                                                          have hLoopClosed :
                                                              EvmYul.Yul.exec fuel'
                                                                  (.For cond post body)
                                                                  codeOverride
                                                                  stateAfterPost =
                                                                loopResult :=
                                                            exec_done_eq_closed hLoop
                                                              hNoOverride
                                                          simp [loop,
                                                            EvmYul.Yul.loop,
                                                            hCond, hCondClosed,
                                                            hZero, hZeroStruct,
                                                            hBody, hBodyClosed,
                                                            hPost, hPostClosed,
                                                            hLoop, hLoopClosed,
                                                            stateAfterPost,
                                                            YulOpenResult.bind,
                                                            YulOpenResult.ok]
                                                            at hOpen ⊢
                                                          exact
                                                            by
                                                              simpa [overwriteLoopResult] using
                                                                bind_done_overwrite_result_eq_closed
                                                                  hOpen
                                                      | call call =>
                                                          simp [loop, hCond,
                                                            hZero, hZeroStruct,
                                                            hBody, hPost, hLoop,
                                                            stateAfterPost,
                                                            YulOpenResult.bind]
                                                            at hOpen
                                                  | Continue ps pv =>
                                                      cases hLoop :
                                                          exec fuel'
                                                            (.For cond post body)
                                                            codeOverride
                                                            stateAfterPost with
                                                      | done loopResult =>
                                                          have hLoopClosed :
                                                              EvmYul.Yul.exec fuel'
                                                                  (.For cond post body)
                                                                  codeOverride
                                                                  stateAfterPost =
                                                                loopResult :=
                                                            exec_done_eq_closed hLoop
                                                              hNoOverride
                                                          simp [loop,
                                                            EvmYul.Yul.loop,
                                                            hCond, hCondClosed,
                                                            hZero, hZeroStruct,
                                                            hBody, hBodyClosed,
                                                            hPost, hPostClosed,
                                                            hLoop, hLoopClosed,
                                                            stateAfterPost,
                                                            YulOpenResult.bind,
                                                            YulOpenResult.ok]
                                                            at hOpen ⊢
                                                          exact
                                                            by
                                                              simpa [overwriteLoopResult] using
                                                                bind_done_overwrite_result_eq_closed
                                                                  hOpen
                                                      | call call =>
                                                          simp [loop, hCond,
                                                            hZero, hZeroStruct,
                                                            hBody, hPost, hLoop,
                                                            stateAfterPost,
                                                            YulOpenResult.bind]
                                                            at hOpen
                                              | Ok ps pv =>
                                                  cases hLoop :
                                                      exec fuel'
                                                        (.For cond post body)
                                                        codeOverride
                                                        stateAfterPost with
                                                  | done loopResult =>
                                                      have hLoopClosed :
                                                          EvmYul.Yul.exec fuel'
                                                              (.For cond post body)
                                                              codeOverride
                                                              stateAfterPost =
                                                            loopResult :=
                                                        exec_done_eq_closed hLoop
                                                          hNoOverride
                                                      simp [loop,
                                                        EvmYul.Yul.loop,
                                                        hCond, hCondClosed,
                                                        hZero, hZeroStruct,
                                                        hBody, hBodyClosed,
                                                        hPost, hPostClosed,
                                                        hLoop, hLoopClosed,
                                                        stateAfterPost,
                                                        YulOpenResult.bind,
                                                        YulOpenResult.ok]
                                                        at hOpen ⊢
                                                      exact
                                                        by
                                                          simpa [overwriteLoopResult] using
                                                            bind_done_overwrite_result_eq_closed
                                                              hOpen
                                                  | call call =>
                                                      simp [loop, hCond, hZero,
                                                        hZeroStruct, hBody,
                                                        hPost, hLoop,
                                                        stateAfterPost,
                                                        YulOpenResult.bind]
                                                        at hOpen
                                      | call call =>
                                          simp [loop, hCond, hZero,
                                            hZeroStruct, hBody, hPost,
                                            YulOpenResult.bind] at hOpen
                              | Ok shared store =>
                                  cases hPost :
                                      exec fuel' (.Block post) codeOverride
                                        (EvmYul.Yul.State.reviveJump
                                          (.Ok shared store)) with
                                  | done postResult =>
                                      have hPostClosed :
                                          EvmYul.Yul.exec fuel' (.Block post)
                                              codeOverride
                                              (EvmYul.Yul.State.reviveJump
                                                (.Ok shared store)) =
                                            postResult :=
                                        exec_done_eq_closed hPost
                                          hNoOverride
                                      cases postResult with
                                      | error err =>
                                          simp [loop, EvmYul.Yul.loop, hCond,
                                            hCondClosed, hZero, hZeroStruct,
                                            hBody, hBodyClosed, hPost,
                                            hPostClosed, YulOpenResult.bind]
                                            at hOpen ⊢
                                          exact hOpen
                                      | ok postState =>
                                          let stateAfterPost :=
                                            EvmYul.Yul.State.overwrite?
                                              postState state
                                          cases postState with
                                          | OutOfFuel =>
                                              simp [loop, EvmYul.Yul.loop,
                                                hCond, hCondClosed, hZero,
                                                hZeroStruct, hBody,
                                                hBodyClosed, hPost,
                                                hPostClosed,
                                                YulOpenResult.bind,
                                                YulOpenResult.ok] at hOpen ⊢
                                              exact hOpen
                                          | Checkpoint postJump =>
                                              cases postJump with
                                              | Leave ps pv =>
                                                  simp [loop, EvmYul.Yul.loop,
                                                    hCond, hCondClosed, hZero,
                                                    hZeroStruct, hBody,
                                                    hBodyClosed, hPost,
                                                    hPostClosed,
                                                    YulOpenResult.bind,
                                                    YulOpenResult.ok]
                                                    at hOpen ⊢
                                                  exact hOpen
                                              | Break ps pv =>
                                                  cases hLoop :
                                                      exec fuel'
                                                        (.For cond post body)
                                                        codeOverride
                                                        stateAfterPost with
                                                  | done loopResult =>
                                                      have hLoopClosed :
                                                          EvmYul.Yul.exec fuel'
                                                              (.For cond post body)
                                                              codeOverride
                                                              stateAfterPost =
                                                            loopResult :=
                                                        exec_done_eq_closed hLoop
                                                          hNoOverride
                                                      simp [loop,
                                                        EvmYul.Yul.loop,
                                                        hCond, hCondClosed,
                                                        hZero, hZeroStruct,
                                                        hBody, hBodyClosed,
                                                        hPost, hPostClosed,
                                                        hLoop, hLoopClosed,
                                                        stateAfterPost,
                                                        YulOpenResult.bind,
                                                        YulOpenResult.ok]
                                                        at hOpen ⊢
                                                      exact
                                                        by
                                                          simpa [overwriteLoopResult] using
                                                            bind_done_overwrite_result_eq_closed
                                                              hOpen
                                                  | call call =>
                                                      simp [loop, hCond, hZero,
                                                        hZeroStruct, hBody,
                                                        hPost, hLoop,
                                                        stateAfterPost,
                                                        YulOpenResult.bind]
                                                        at hOpen
                                              | Continue ps pv =>
                                                  cases hLoop :
                                                      exec fuel'
                                                        (.For cond post body)
                                                        codeOverride
                                                        stateAfterPost with
                                                  | done loopResult =>
                                                      have hLoopClosed :
                                                          EvmYul.Yul.exec fuel'
                                                              (.For cond post body)
                                                              codeOverride
                                                              stateAfterPost =
                                                            loopResult :=
                                                        exec_done_eq_closed hLoop
                                                          hNoOverride
                                                      simp [loop,
                                                        EvmYul.Yul.loop,
                                                        hCond, hCondClosed,
                                                        hZero, hZeroStruct,
                                                        hBody, hBodyClosed,
                                                        hPost, hPostClosed,
                                                        hLoop, hLoopClosed,
                                                        stateAfterPost,
                                                        YulOpenResult.bind,
                                                        YulOpenResult.ok]
                                                        at hOpen ⊢
                                                      exact
                                                        by
                                                          simpa [overwriteLoopResult] using
                                                            bind_done_overwrite_result_eq_closed
                                                              hOpen
                                                  | call call =>
                                                      simp [loop, hCond, hZero,
                                                        hZeroStruct, hBody,
                                                        hPost, hLoop,
                                                        stateAfterPost,
                                                        YulOpenResult.bind]
                                                        at hOpen
                                          | Ok ps pv =>
                                              cases hLoop :
                                                  exec fuel'
                                                    (.For cond post body)
                                                    codeOverride
                                                    stateAfterPost with
                                              | done loopResult =>
                                                  have hLoopClosed :
                                                      EvmYul.Yul.exec fuel'
                                                          (.For cond post body)
                                                          codeOverride
                                                          stateAfterPost =
                                                        loopResult :=
                                                    exec_done_eq_closed hLoop
                                                      hNoOverride
                                                  simp [loop, EvmYul.Yul.loop,
                                                    hCond, hCondClosed, hZero,
                                                    hZeroStruct, hBody,
                                                    hBodyClosed, hPost,
                                                    hPostClosed, hLoop,
                                                    stateAfterPost,
                                                    hLoopClosed,
                                                    YulOpenResult.bind,
                                                    YulOpenResult.ok]
                                                    at hOpen ⊢
                                                  exact
                                                    by
                                                      simpa [overwriteLoopResult] using
                                                        bind_done_overwrite_result_eq_closed
                                                          hOpen
                                              | call call =>
                                                  simp [loop, hCond, hZero,
                                                    hZeroStruct, hBody, hPost,
                                                    hLoop, stateAfterPost,
                                                    YulOpenResult.bind]
                                                    at hOpen
                                  | call call =>
                                      simp [loop, hCond, hZero, hZeroStruct,
                                        hBody, hPost, YulOpenResult.bind]
                                        at hOpen
                      | call call =>
                          simp [loop, hCond, hZero, hZeroStruct, hBody,
                            YulOpenResult.bind] at hOpen
            | call call =>
                simp [loop, hCond, YulOpenResult.bind] at hOpen
  theorem call_done_eq_closed
      {fuel : Nat} {args : List Word}
      {functionName? : Option EvmYul.Yul.Ast.YulFunctionName}
      {codeOverride : Option Contract} {state : State}
      {result : Except Exception (State × List Word)}
      (hOpen :
        call fuel args functionName? codeOverride state = .done result)
      (hNoOverride : codeOverride = none) :
      EvmYul.Yul.call fuel args functionName? codeOverride state = result := by
    subst codeOverride
    cases fuel with
    | zero =>
        simpa [call, EvmYul.Yul.call, YulOpenResult.error] using hOpen
    | succ fuel' =>
        cases hFind :
            state.sharedState.accountMap.find? state.executionEnv.codeOwner with
        | none =>
            simpa [call, EvmYul.Yul.call, callFunction?, hFind,
              YulOpenResult.error] using hOpen
        | some yulContract =>
            cases functionName? with
            | none =>
                let f : EvmYul.Yul.Ast.FunctionDefinition :=
                  EvmYul.Yul.Ast.FunctionDefinition.Def [] []
                    [yulContract.code.dispatcher]
                cases hBody :
                    exec fuel' (.Block f.body) none
                      (EvmYul.Yul.State.mkOk
                        (EvmYul.Yul.State.initcall f.params f.rets args state)) with
                | done bodyResult =>
                    have hBodyClosed :
                        EvmYul.Yul.exec fuel' (.Block f.body) none
                            (EvmYul.Yul.State.mkOk
                              (EvmYul.Yul.State.initcall f.params f.rets args
                                state)) =
                          bodyResult :=
                      exec_done_eq_closed hBody rfl
                    cases bodyResult with
                    | error err =>
                        simp [call, EvmYul.Yul.call, callFunction?, hFind, f,
                          hBody, hBodyClosed, YulOpenResult.bind] at hOpen ⊢
                        exact hOpen
                    | ok stateAfterBody =>
                        simp [call, EvmYul.Yul.call, callFunction?, hFind, f,
                          hBody, hBodyClosed, YulOpenResult.bind,
                          YulOpenResult.ok] at hOpen ⊢
                        exact hOpen
                | call externalCall =>
                    simp [call, callFunction?, hFind, f, hBody,
                      YulOpenResult.bind] at hOpen
            | some functionName =>
                cases hFunction :
                    yulContract.code.functions.lookup
                      functionName with
                | none =>
                    simpa [call, EvmYul.Yul.call, callFunction?, hFind,
                      hFunction, YulOpenResult.error] using hOpen
                | some f =>
                    cases hBody :
                        exec fuel' (.Block f.body) none
                          (EvmYul.Yul.State.mkOk
                            (EvmYul.Yul.State.initcall f.params f.rets args
                              state)) with
                    | done bodyResult =>
                        have hBodyClosed :
                            EvmYul.Yul.exec fuel' (.Block f.body) none
                                (EvmYul.Yul.State.mkOk
                                  (EvmYul.Yul.State.initcall f.params f.rets
                                    args state)) =
                              bodyResult :=
                          exec_done_eq_closed hBody rfl
                        cases bodyResult with
                        | error err =>
                            simp [call, EvmYul.Yul.call, callFunction?, hFind,
                              hFunction, hBody, hBodyClosed, YulOpenResult.bind]
                              at hOpen ⊢
                            exact hOpen
                        | ok stateAfterBody =>
                            simp [call, EvmYul.Yul.call, callFunction?, hFind,
                              hFunction, hBody, hBodyClosed, YulOpenResult.bind,
                              YulOpenResult.ok] at hOpen ⊢
                            exact hOpen
                    | call externalCall =>
                        simp [call, callFunction?, hFind, hFunction, hBody,
                          YulOpenResult.bind] at hOpen

end

theorem reverseResult_evalArgs_done_eq_closed
    {fuel : Nat} {args : List Expr} {codeOverride : Option Contract}
    {state : State}
    {result : Except Exception (State × List Word)}
    (hOpen :
      reverseResult (evalArgs fuel args codeOverride state) =
        .done result)
    (hNoOverride : codeOverride = none) :
    EvmYul.Yul.reverse'
        (EvmYul.Yul.evalArgs fuel args codeOverride state) =
      result := by
  simp [reverseResult, YulOpenResult.map] at hOpen ⊢
  cases hArgs : evalArgs fuel args codeOverride state with
  | done argsResult =>
      have hArgsClosed :
          EvmYul.Yul.evalArgs fuel args codeOverride state = argsResult :=
        evalArgs_done_eq_closed hArgs hNoOverride
      cases argsResult with
      | error err =>
          simp [hArgs, hArgsClosed, YulOpenResult.bind,
            EvmYul.Yul.reverse'] at hOpen ⊢
          exact hOpen
      | ok argsPair =>
          rcases argsPair with ⟨stateAfterArgs, values⟩
          simp [hArgs, hArgsClosed, YulOpenResult.bind,
            YulOpenResult.ok, EvmYul.Yul.reverse'] at hOpen ⊢
          exact hOpen
  | call call =>
      simp [hArgs, YulOpenResult.bind] at hOpen

end YulOpen

namespace CallKind

@[simp] theorem primitiveSharedOpenCall?_args_reverse
    (shared : EvmYul.SharedState .EVM)
    (kind : CallKind) (operands : CallOperands) :
    primitiveSharedOpenCall? shared kind
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
    (state : EvmYul.EVM.State)
    (kind : CallKind) (operands : CallOperands) (baseStack : Stack) :
    evmOpenCall?
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
related. This is the universal quantification over arbitrary external-call
responses. The `responseRel` premise says which arbitrary internal mutations
are admissible for this particular source/target boundary; for the compiler
proof this is where reentrant mutations are required to preserve the state
relation.
-/
structure OpenCallRel
    {SourceState : Type v} {TargetState : Type w}
    (responseRel : CallResponse → Prop)
    (stateRel : SourceState → TargetState → Prop)
    (source : OpenCall SourceState)
    (target : OpenCall TargetState) : Prop where
  sameSite : source.site = target.site
  preservesAllResponses :
    ∀ response, responseRel response →
      stateRel (source.resume response) (target.resume response)

namespace OpenCallRel

theorem preserves_response
    {SourceState : Type v} {TargetState : Type w}
    {responseRel : CallResponse → Prop}
    {stateRel : SourceState → TargetState → Prop}
    {source : OpenCall SourceState}
    {target : OpenCall TargetState}
    (hRel : OpenCallRel responseRel stateRel source target)
    (response : CallResponse) (hResponse : responseRel response) :
    stateRel (source.resume response) (target.resume response) :=
  hRel.preservesAllResponses response hResponse

theorem trans
    {LeftState : Type v} {MidState : Type w}
    {RightState : Type}
    {leftResponseRel rightResponseRel : CallResponse → Prop}
    {leftRel : LeftState → MidState → Prop}
    {rightRel : MidState → RightState → Prop}
    {left : OpenCall LeftState}
    {mid : OpenCall MidState}
    {right : OpenCall RightState}
    (hLeft : OpenCallRel leftResponseRel leftRel left mid)
    (hRight : OpenCallRel rightResponseRel rightRel mid right) :
    OpenCallRel
      (fun response => leftResponseRel response ∧ rightResponseRel response)
      (fun leftResult rightResult =>
        ∃ midResult, leftRel leftResult midResult ∧
          rightRel midResult rightResult)
      left right where
  sameSite := hLeft.sameSite.trans hRight.sameSite
  preservesAllResponses := by
    intro response hResponse
    exact
      ⟨mid.resume response,
        hLeft.preservesAllResponses response hResponse.1,
        hRight.preservesAllResponses response hResponse.2⟩

end OpenCallRel

/--
Pointwise relation between two open results.

The `call` branch is intentionally visible: a proof cannot relate suspended
computations without same-site equality and a continuation proof for every
admissible shared response. The admissible-response predicate is allowed to
depend on the two suspended calls, since the external response relation for
stateful calls is usually determined by the source/target pre-call states
captured by those continuations.
-/
inductive OpenResultRel
    {ε₁ : Type u} {ε₂ : Type v} {α : Type w} {β : Type}
    (callResponseRel :
      OpenCall (OpenResult ε₁ α) →
        OpenCall (OpenResult ε₂ β) → CallResponse → Prop)
    (doneRel : Except ε₁ α → Except ε₂ β → Prop) :
    OpenResult ε₁ α → OpenResult ε₂ β → Prop where
  | done {sourceDone : Except ε₁ α} {targetDone : Except ε₂ β} :
      doneRel sourceDone targetDone →
      OpenResultRel callResponseRel doneRel
        (.done sourceDone) (.done targetDone)
  | call
      {sourceCall : OpenCall (OpenResult ε₁ α)}
      {targetCall : OpenCall (OpenResult ε₂ β)} :
      sourceCall.site = targetCall.site →
      (∀ response, callResponseRel sourceCall targetCall response →
        OpenResultRel callResponseRel doneRel
          (sourceCall.resume response) (targetCall.resume response)) →
      OpenResultRel callResponseRel doneRel
        (.call sourceCall) (.call targetCall)

namespace OpenResultRel

theorem bind
    {ε₁ : Type u} {ε₂ : Type v}
    {α : Type w} {β : Type} {γ : Type} {δ : Type}
    {callResponseRel :
      OpenCall (OpenResult ε₁ α) →
        OpenCall (OpenResult ε₂ β) → CallResponse → Prop}
    {doneRel : Except ε₁ α → Except ε₂ β → Prop}
    {callResponseRel' :
      OpenCall (OpenResult ε₁ γ) →
        OpenCall (OpenResult ε₂ δ) → CallResponse → Prop}
    {doneRel' : Except ε₁ γ → Except ε₂ δ → Prop}
    {source : OpenResult ε₁ α} {target : OpenResult ε₂ β}
    {sourceNext : α → OpenResult ε₁ γ}
    {targetNext : β → OpenResult ε₂ δ}
    (hRel : OpenResultRel callResponseRel doneRel source target)
    (hDone :
      ∀ {sourceDone targetDone},
        doneRel sourceDone targetDone →
          OpenResultRel callResponseRel' doneRel'
            (match sourceDone with
            | .ok value => sourceNext value
            | .error err => .done (.error err))
            (match targetDone with
            | .ok value => targetNext value
            | .error err => .done (.error err)))
    (hCallResponse :
      ∀ {sourceCall targetCall response},
        callResponseRel'
          { site := sourceCall.site
            resume := fun response =>
              OpenResult.bind (sourceCall.resume response) sourceNext }
          { site := targetCall.site
            resume := fun response =>
              OpenResult.bind (targetCall.resume response) targetNext }
          response →
        callResponseRel sourceCall targetCall response) :
    OpenResultRel callResponseRel' doneRel'
      (OpenResult.bind source sourceNext)
      (OpenResult.bind target targetNext) := by
  induction hRel with
  | @done sourceDone targetDone hDoneRel =>
      cases sourceDone <;> cases targetDone <;>
        exact hDone hDoneRel
  | call hSite _hResume ih =>
      simp [OpenResult.bind]
      exact OpenResultRel.call hSite (by
        intro response hResponse
        exact ih response (hCallResponse hResponse))

end OpenResultRel

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
    {shared : EvmYul.SharedState .EVM}
    (state : EvmYul.EVM.State)
    (hShared : state.toSharedState = shared)
    (kind : CallKind) (operands : CallOperands) (baseStack : Stack) :
    ∃ primitiveCall :
        OpenCall (EvmYul.SharedState .EVM × List Word),
    ∃ evmCall : OpenCall EvmYul.EVM.State,
      primitiveSharedOpenCall? shared kind
          (kind.args operands).reverse =
        some primitiveCall ∧
      evmOpenCall?
          ({ state with stack := kind.args operands ++ baseStack }
            : EvmYul.EVM.State) kind =
        some evmCall ∧
      OpenCallRel (fun _ => True) (PrimitiveEVMResultRel baseStack)
        primitiveCall evmCall := by
  subst shared
  let site :=
    (CallContext.ofEVMState state).callSite kind
      (kind.canonicalOperands operands)
  let primitiveCall :
      OpenCall (EvmYul.SharedState .EVM × List Word) :=
    { site := site
      resume := fun response =>
        (site.finishShared state.toSharedState response,
          [response.statusWord]) }
  let evmCall : OpenCall EvmYul.EVM.State :=
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
    · intro response _hResponse
      simp [primitiveCall, evmCall, PrimitiveEVMResultRel]

end CallKind

end OpenExternal

end Yul
end EvmCompiler
