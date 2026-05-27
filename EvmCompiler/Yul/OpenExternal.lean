import EvmCompiler.Yul.PrimSemantics

namespace EvmCompiler
namespace Yul

namespace OpenExternal

universe u

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

/--
The request that is visible to the external environment.

`recipient` is the account whose balance/call frame is targeted, while
`codeAddress` is the account whose code is executed. These differ for
`CALLCODE` and `DELEGATECALL`.
-/
structure CallRequest where
  kind : CallKind
  requestedGas : EvmYul.UInt256
  callGas : EvmYul.UInt256
  caller : EvmYul.AccountAddress
  recipient : EvmYul.AccountAddress
  codeAddress : EvmYul.AccountAddress
  transferValue : EvmYul.UInt256
  apparentValue : EvmYul.UInt256
  calldata : ByteArray
  permission : Bool

/--
Local continuation data for applying an external response.

These offsets are not part of the call made to the outside world, but both
interpreters must agree on them before consuming the same response.
-/
structure ReturnWindow where
  inOffset : EvmYul.UInt256
  inSize : EvmYul.UInt256
  outOffset : EvmYul.UInt256
  outSize : EvmYul.UInt256

/-- A complete open call site: external request plus local return-copy window. -/
structure CallSite where
  request : CallRequest
  returnWindow : ReturnWindow

/--
An arbitrary response from the outside world.

`Effect` is intentionally abstract. It can later be instantiated with a concrete
post-world delta, an account-map transformer, a trace token, or `PUnit` for
tests that only care about status/gas/return data. The compiler theorem should
quantify over this response rather than proving facts about one chosen world.
-/
structure CallResponse (Effect : Type u) where
  success : Bool
  gasRemaining : EvmYul.UInt256
  returnData : ByteArray
  effect : Effect

/--
The new external boundary: both sides issue the same call site and receive the
same response. There are no semantic constraints on the response itself.
-/
structure MatchedCall (Effect : Type u) where
  site : CallSite
  response : CallResponse Effect

theorem MatchedCall.same_site {Effect : Type u}
    (matched : MatchedCall Effect) :
    matched.site = matched.site :=
  rfl

theorem MatchedCall.same_response {Effect : Type u}
    (matched : MatchedCall Effect) :
    matched.response = matched.response :=
  rfl

end OpenExternal

end Yul
end EvmCompiler
