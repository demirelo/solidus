import EvmCompiler.VerityBridge.ExecAgreesCases

/-!
# W4 / W5 — the entry adapter and the Phase-5-facing endpoint

`callDispatcher_agrees` lifts the mutual family's `call_agrees` to the dispatcher
entry point, via the reduction `native callDispatcher (some contract) s = native
call [] none (some contract) s` (both build the same
`FunctionDefinition.Def [] [] [contract.dispatcher]` wrapper once the harness
installs `s.executionEnv.code = contract` and the owner account is present).

`native_run_to_interaction_run` is the W5 endpoint Phase 5 composition consumes:
`DoneAgrees` between the native dispatcher run and our
`InteractionSemantics.Program.openRun` (which is, definitionally,
`call [] none (some contract)`).
-/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

open EvmYul.Yul.Ast
open InteractionSemantics

/-- Native `callDispatcher (some contract)` and native `call [] none (some
contract)` coincide when the harness installs `executionEnv.code = contract` and
the owner account is present: both resolve the body to
`[contract.dispatcher]` and run it with identical caller-frame bookkeeping. -/
theorem native_callDispatcher_eq_call (n : Nat) (contract : YulContract) (s : State)
    (hInstall : s.executionEnv.code = contract) (hCB : CodeBridge s) :
    EvmYul.Yul.callDispatcher n (some contract) s =
      EvmYul.Yul.call n [] none (some contract) s := by
  cases n with
  | zero => rw [Native.callDispatcher_zero, Native.call_zero]
  | succ fuel =>
      rw [Native.callDispatcher_succ, Native.call_succ]
      cases hf : s.sharedState.accountMap.find? s.executionEnv.codeOwner with
      | none => exact absurd hf hCB
      | some yc => simp only [Option.getD_some, hInstall]

/-- Our dispatcher run is, definitionally, the `call [] none (some contract)`
entry (no account-map lookup participates). -/
theorem openRun_eq_call (m : Nat) (contract : YulContract) (s : State) :
    InteractionSemantics.Program.openRun m contract s =
      call m [] none (some contract) s := rfl

/-- W4 — the dispatcher agreement, as a corollary of `call_agrees`. -/
theorem callDispatcher_agrees (n : Nat) (contract : YulContract) (s : State)
    (hContract : BridgeContract contract) (hInstall : s.executionEnv.code = contract)
    (hCB : CodeBridge s) :
    ∃ m, DoneAgrees (EvmYul.Yul.callDispatcher n (some contract) s)
      (call m [] none (some contract) s) := by
  rw [native_callDispatcher_eq_call n contract s hInstall hCB]
  exact call_agrees n [] none (some contract) s ⟨contract, rfl, hContract⟩ hCB

/-- W5 — the Phase-5-facing endpoint: `DoneAgrees` between the native dispatcher
run and our `InteractionSemantics.Program.openRun`. Hypotheses are the bridge
contract, the harness installation `executionEnv.code = contract`, and owner-account
presence (`CodeBridge`). -/
theorem native_run_to_interaction_run (n : Nat) (contract : YulContract) (s : State)
    (hContract : BridgeContract contract) (hInstall : s.executionEnv.code = contract)
    (hCB : CodeBridge s) :
    ∃ m, DoneAgrees (EvmYul.Yul.callDispatcher n (some contract) s)
      (InteractionSemantics.Program.openRun m contract s) := by
  obtain ⟨m, hm⟩ := callDispatcher_agrees n contract s hContract hInstall hCB
  exact ⟨m, by rw [openRun_eq_call]; exact hm⟩

end VerityBridge
end Yul
end EvmCompiler
