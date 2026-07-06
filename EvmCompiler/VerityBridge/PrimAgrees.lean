import EvmCompiler.VerityBridge.RequestFree

/-!
# W2 — the primitive layer of the Verity interpreter-equivalence bridge

For a `BridgeOp`, our `InteractionSemantics.Primitive.openEval` degenerates to a native-agreeing
`.done` leaf:

* `closedEval_agrees` — `closedEval` is native `primCall` wrapped through `toResult`
  (the `EXTCODEHASH` override is excluded by `BridgeOp`);
* `openEval_agrees` — `openEval (fuel+1)` burns one tick and delegates to
  `closedEval fuel` (external/GAS/MSIZE branches excluded by `BridgeOp`);
* `primCall_fuel_insensitive` — the W0 same-fuel lemma: native `primCall` uses its
  fuel only for the external call recursions (out of fragment), so on a `BridgeOp`
  it is constant above 1;
* `doneAgrees_openEval_shift` / `doneAgrees_openEval` — the boundary corollaries
  the W3 mutual induction consumes.
-/

namespace EvmCompiler
namespace Yul
namespace VerityBridge

open EvmYul (Operation)

/-- Native error payloads gain the site-local bookkeeping `Failure` carries. -/
def toResult (s : InteractionSemantics.State) :
    Except EvmYul.Yul.Exception (InteractionSemantics.State × List Word) →
      Except InteractionSemantics.Failure (InteractionSemantics.State × List Word)
  | .ok v => .ok v
  | .error e => .error { exception := e, state := s.afterException e }

/-- `toResult` always agrees with the native result it wraps. -/
theorem resultAgrees_toResult (s : InteractionSemantics.State)
    (r : Except EvmYul.Yul.Exception (InteractionSemantics.State × List Word)) :
    ResultAgrees r (toResult s r) := by
  cases r with
  | ok v => exact rfl
  | error e => exact rfl

/-! ## `closedEval` is native `primCall` wrapped -/

theorem closedEval_agrees {op : Operation .Yul} (hOp : BridgeOp op)
    (fuel : Nat) (s : InteractionSemantics.State) (args : List Word) :
    InteractionSemantics.Primitive.closedEval fuel s op args =
      .done (toResult s (EvmYul.Yul.primCall fuel s op args)) := by
  have hHash : op ≠ .Env .EXTCODEHASH := hOp.2.2.2
  unfold InteractionSemantics.Primitive.closedEval
  -- The `op, fuel` match hits the default arm (op ≠ EXTCODEHASH).
  split
  · exact absurd rfl hHash
  · exact absurd rfl hHash
  · -- default arm: `match primCall … with | .ok … | .error …`
    cases h : EvmYul.Yul.primCall fuel s op args with
    | ok v => rfl
    | error e => rfl

/-! ## `openEval (fuel+1)` delegates to `closedEval fuel` -/

theorem openEval_agrees {op : Operation .Yul} (hOp : BridgeOp op)
    (fuel : Nat) (s : InteractionSemantics.State) (args : List Word) :
    InteractionSemantics.Primitive.openEval (fuel + 1) s op args =
      InteractionSemantics.Primitive.closedEval fuel s op args := by
  have hExt : Simulation.ExternalKind.ofYulOperation? op = none := hOp.1
  have hGas : op ≠ .StackMemFlow .GAS := hOp.2.1
  have hMsize : op ≠ .StackMemFlow .MSIZE := hOp.2.2.1
  unfold InteractionSemantics.Primitive.openEval
  rw [hExt]
  -- `match op with | GAS | MSIZE | _ => closedEval fuel …`
  split <;> first | rfl | (rename_i heq; simp_all)

/-! ## W0 fuel-insensitivity (same-fuel decision)

Native `primCall` consumes its fuel only inside the CALL/CALLCODE/DELEGATECALL/
STATICCALL arms (the concrete external-call recursion). `BridgeOp` excludes every
one of those, so `primCall` is constant in fuel above `1`. -/

private theorem callKind_none_of_bridge {op : Operation .Yul} (hOp : BridgeOp op) :
    Simulation.CallKind.ofYulOperation? op = none := by
  have hExt : Simulation.ExternalKind.ofYulOperation? op = none := hOp.1
  unfold Simulation.ExternalKind.ofYulOperation? at hExt
  cases hc : Simulation.CallKind.ofYulOperation? op with
  | none => rfl
  | some k => rw [hc] at hExt; simp at hExt

theorem primCall_fuel_insensitive {op : Operation .Yul} (hOp : BridgeOp op)
    (n m : Nat) (s : InteractionSemantics.State) (args : List Word) :
    EvmYul.Yul.primCall (n + 1) s op args =
      EvmYul.Yul.primCall (m + 1) s op args := by
  have hCall : Simulation.CallKind.ofYulOperation? op = none :=
    callKind_none_of_bridge hOp
  cases op with
  | System sop =>
      cases sop <;>
        first
          | (rw [EvmYul.Yul.primCall.eq_def, EvmYul.Yul.primCall.eq_def]; done)
          | exact absurd hCall (by simp [Simulation.CallKind.ofYulOperation?])
  | _ => rw [EvmYul.Yul.primCall.eq_def, EvmYul.Yul.primCall.eq_def]

/-! ## `CodeBridge` preservation boundary lemma (Part B leaf)

Native `call` demands presence of the `codeOwner` account. For the mutual bridge
family this presence must be preserved through primitive leaves. This is the one
place `primCall` is opened for state reasoning (the ratified boundary). A
`BridgeOp` `primCall` on `.ok` never changes `executionEnv.codeOwner` and never
drops the `codeOwner` account key: it delegates to native `step`, whose only
account-map mutators (SSTORE/TSTORE) `insert` the `codeOwner` key. -/

section Preservation

open EvmYul (State)

/-- `sstore` never touches `executionEnv` and preserves presence of the executing
account (`codeOwner`): on the present branch it `insert`s that key. -/
private theorem sstore_preserves (self : EvmYul.State .Yul) (a b : Word) :
    (EvmYul.State.sstore self a b).executionEnv = self.executionEnv ∧
      (self.accountMap.find? self.executionEnv.codeOwner ≠ none →
        (EvmYul.State.sstore self a b).accountMap.find?
          self.executionEnv.codeOwner ≠ none) := by
  simp only [EvmYul.State.sstore, EvmYul.State.lookupAccount]
  cases hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => exact ⟨rfl, by simp⟩
  | some acc =>
      refine ⟨?_, ?_⟩
      · simp only [Option.option, EvmYul.State.setAccount,
          EvmYul.State.addAccessedStorageKey]
      · intro _
        simp only [Option.option, EvmYul.State.setAccount,
          EvmYul.State.addAccessedStorageKey]
        rw [Batteries.RBMap.find?_insert_of_eq _ (Std.ReflCmp.compare_self)]
        simp

/-- `tstore` never touches `executionEnv` and preserves presence of `codeOwner`. -/
private theorem tstore_preserves (self : EvmYul.State .Yul) (a b : Word) :
    (EvmYul.State.tstore self a b).executionEnv = self.executionEnv ∧
      (self.accountMap.find? self.executionEnv.codeOwner ≠ none →
        (EvmYul.State.tstore self a b).accountMap.find?
          self.executionEnv.codeOwner ≠ none) := by
  simp only [EvmYul.State.tstore, EvmYul.State.lookupAccount]
  cases hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => exact ⟨rfl, by simp⟩
  | some acc =>
      refine ⟨?_, ?_⟩
      · simp only [Option.option, EvmYul.State.updateAccount]
      · intro _
        simp only [Option.option, EvmYul.State.updateAccount]
        rw [Batteries.RBMap.find?_insert_of_eq _ (Std.ReflCmp.compare_self)]
        simp

/-! ### `step`-result preservation, per combinator

`StepPres s s'` is the boundary invariant: `s'` keeps `s`'s `codeOwner` and its
account entry (if present). Each native `step` combinator preserves it; a uniform
`first`-block then discharges every Yul op (the private dispatchers are matched by
defeq, so `exact <combinator>_pres h` accepts the raw `step`-reduced hypothesis). -/

/-- The boundary invariant a `.ok` `step`/`primCall` result must satisfy. -/
def StepPres (s s' : EvmYul.Yul.State) : Prop :=
  s'.executionEnv.codeOwner = s.executionEnv.codeOwner ∧
    (s.sharedState.accountMap.find? s.executionEnv.codeOwner ≠ none →
      s'.sharedState.accountMap.find? s'.executionEnv.codeOwner ≠ none)

private theorem StepPres.rfl' (s : EvmYul.Yul.State) : StepPres s s :=
  ⟨rfl, fun x => x⟩

private theorem StepPres.of_eq {s s' : EvmYul.Yul.State}
    (he : s'.executionEnv = s.executionEnv)
    (ha : s'.sharedState.accountMap = s.sharedState.accountMap) : StepPres s s' := by
  refine ⟨by rw [he], fun hp => ?_⟩
  rw [he, ha]; exact hp

section Combinators

open EvmYul.Yul (State)

variable {s s' : EvmYul.Yul.State} {l : Option Word} {args : List Word}

/-! Unchanged-state combinators: the result is the input state. -/

private theorem execUnOp_pres {f} (h : EvmYul.Yul.execUnOp f s args = .ok (s', l)) :
    StepPres s s' := by
  unfold EvmYul.Yul.execUnOp at h
  split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s

private theorem execBinOp_pres {f} (h : EvmYul.Yul.execBinOp f s args = .ok (s', l)) :
    StepPres s s' := by
  unfold EvmYul.Yul.execBinOp at h
  split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s

private theorem execTriOp_pres {f} (h : EvmYul.Yul.execTriOp f s args = .ok (s', l)) :
    StepPres s s' := by
  unfold EvmYul.Yul.execTriOp at h
  split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s

private theorem execQuadOp_pres {f} (h : EvmYul.Yul.execQuadOp f s args = .ok (s', l)) :
    StepPres s s' := by
  unfold EvmYul.Yul.execQuadOp at h
  split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s

private theorem executionEnvOp_pres {f} (h : EvmYul.Yul.executionEnvOp f s args = .ok (s', l)) :
    StepPres s s' := by
  unfold EvmYul.Yul.executionEnvOp at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s

private theorem unaryExecutionEnvOp_pres {f}
    (h : EvmYul.Yul.unaryExecutionEnvOp f s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.unaryExecutionEnvOp at h
  split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s

private theorem machineStateOp_pres {f} (h : EvmYul.Yul.machineStateOp f s args = .ok (s', l)) :
    StepPres s s' := by
  unfold EvmYul.Yul.machineStateOp at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s

private theorem stateOp_pres {f} (h : EvmYul.Yul.stateOp f s args = .ok (s', l)) :
    StepPres s s' := by
  unfold EvmYul.Yul.stateOp at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s

/-! Machine-state combinators: the result is `setMachineState _`. -/

private theorem setMachineState_pres (m : EvmYul.MachineState) (s : EvmYul.Yul.State) :
    StepPres s (s.setMachineState m) := by
  cases s <;> exact ⟨rfl, fun x => x⟩

private theorem binaryMachineStateOp_pres {f}
    (h : EvmYul.Yul.binaryMachineStateOp f s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.binaryMachineStateOp at h
  split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, _⟩ := h; exact setMachineState_pres _ s

private theorem binaryMachineStateOp'_pres {f}
    (h : EvmYul.Yul.binaryMachineStateOp' f s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.binaryMachineStateOp' at h
  split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, _⟩ := h; exact setMachineState_pres _ s

private theorem ternaryMachineStateOp_pres {f}
    (h : EvmYul.Yul.ternaryMachineStateOp f s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.ternaryMachineStateOp at h
  split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, _⟩ := h; exact setMachineState_pres _ s

/-! Shared-state combinators: the result is `setSharedState _`, where the
underlying `State`/`SharedState` op preserves `executionEnv` and `accountMap`. -/

private theorem unaryStateOp_pres {f}
    (hop : ∀ (st : EvmYul.State .Yul) (v : Word),
      (f st v).1.executionEnv = st.executionEnv ∧ (f st v).1.accountMap = st.accountMap)
    (h : EvmYul.Yul.unaryStateOp f s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.unaryStateOp at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    refine StepPres.of_eq ?_ ?_ <;> cases s <;>
      simp only [EvmYul.Yul.State.setSharedState, EvmYul.Yul.State.sharedState,
        EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toSharedState,
        EvmYul.Yul.State.toState, hop]
  · simp only [reduceCtorEq] at h

private theorem ternaryCopyOp_pres {f}
    (hop : ∀ (sh : EvmYul.SharedState .Yul) (a b c : Word),
      (f sh a b c).executionEnv = sh.executionEnv ∧ (f sh a b c).accountMap = sh.accountMap)
    (h : EvmYul.Yul.ternaryCopyOp f s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.ternaryCopyOp at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    refine StepPres.of_eq ?_ ?_ <;> cases s <;>
      simp only [EvmYul.Yul.State.setSharedState, EvmYul.Yul.State.sharedState,
        EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toSharedState,
        EvmYul.Yul.State.toState, hop]
  · simp only [reduceCtorEq] at h

private theorem quaternaryCopyOp_pres {f}
    (hop : ∀ (sh : EvmYul.SharedState .Yul) (a b c d : Word),
      (f sh a b c d).executionEnv = sh.executionEnv ∧ (f sh a b c d).accountMap = sh.accountMap)
    (h : EvmYul.Yul.quaternaryCopyOp f s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.quaternaryCopyOp at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    refine StepPres.of_eq ?_ ?_ <;> cases s <;>
      simp only [EvmYul.Yul.State.setSharedState, EvmYul.Yul.State.sharedState,
        EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toSharedState,
        EvmYul.Yul.State.toState, hop]
  · simp only [reduceCtorEq] at h

/-! Storage combinators: SSTORE/TSTORE `insert` the `codeOwner` key. -/

private theorem binaryStateOp_sstore_pres
    (h : EvmYul.Yul.binaryStateOp EvmYul.State.sstore s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.binaryStateOp at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rename_i a b _
    cases s with
    | OutOfFuel => exact StepPres.rfl' _
    | Checkpoint j => exact StepPres.rfl' _
    | Ok sh store =>
        obtain ⟨he, hp⟩ := sstore_preserves sh.toState a b
        refine ⟨?_, fun hpres => ?_⟩
        · simp only [EvmYul.Yul.State.setState, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.toState, he]
        · simp only [EvmYul.Yul.State.setState, EvmYul.Yul.State.sharedState,
            EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toState] at hpres ⊢
          rw [he]; exact hp hpres
  · simp only [reduceCtorEq] at h

private theorem binaryStateOp_tstore_pres
    (h : EvmYul.Yul.binaryStateOp EvmYul.State.tstore s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.binaryStateOp at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rename_i a b _
    cases s with
    | OutOfFuel => exact StepPres.rfl' _
    | Checkpoint j => exact StepPres.rfl' _
    | Ok sh store =>
        obtain ⟨he, hp⟩ := tstore_preserves sh.toState a b
        refine ⟨?_, fun hpres => ?_⟩
        · simp only [EvmYul.Yul.State.setState, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.toState, he]
        · simp only [EvmYul.Yul.State.setState, EvmYul.Yul.State.sharedState,
            EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toState] at hpres ⊢
          rw [he]; exact hp hpres
  · simp only [reduceCtorEq] at h

/-! Log combinators: the result is `setSharedState (logOp …)`, which only edits
the substate and machine words. -/

private theorem logOp_of_eq {s : EvmYul.Yul.State} (a b : Word) (t : Array Word) :
    StepPres s (s.setSharedState (EvmYul.SharedState.logOp a b t s.toSharedState)) := by
  refine StepPres.of_eq ?_ ?_ <;> cases s <;>
    simp only [EvmYul.Yul.State.setSharedState, EvmYul.Yul.State.sharedState,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toSharedState, EvmYul.SharedState.logOp]

private theorem log0Op_pres (h : EvmYul.Yul.log0Op s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.log0Op at h
  split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h)
  · exact logOp_of_eq _ _ _
  · exact StepPres.rfl' s

private theorem log1Op_pres (h : EvmYul.Yul.log1Op s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.log1Op at h
  split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h)
  · exact logOp_of_eq _ _ _
  · exact StepPres.rfl' s

private theorem log2Op_pres (h : EvmYul.Yul.log2Op s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.log2Op at h
  split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h)
  · exact logOp_of_eq _ _ _
  · exact StepPres.rfl' s

private theorem log3Op_pres (h : EvmYul.Yul.log3Op s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.log3Op at h
  split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h)
  · exact logOp_of_eq _ _ _
  · exact StepPres.rfl' s

private theorem log4Op_pres (h : EvmYul.Yul.log4Op s args = .ok (s', l)) : StepPres s s' := by
  unfold EvmYul.Yul.log4Op at h
  split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h)
  · exact logOp_of_eq _ _ _
  · exact StepPres.rfl' s

end Combinators

/-! ### The `step` boundary lemma (all non-external Yul ops)

Every Yul op with `ExternalKind.ofYulOperation? = none` that native `step`
answers with `.ok` preserves `StepPres`. The proof reduces `step` for the concrete
op to its private dispatcher (`unfold`/`Id.run`) and a uniform `first`-block picks
the matching combinator lemma (accepted through the private dispatcher by defeq),
closes terminal ops as vacuous errors, and closes the (external/create) default
arm by `hExt`. -/

open EvmYul (Operation)

set_option maxHeartbeats 1000000 in
theorem step_yul_ok_preserves {op : Operation .Yul}
    (hExt : Simulation.ExternalKind.ofYulOperation? op = none)
    (hHash : op ≠ .Env .EXTCODEHASH)
    {s : EvmYul.Yul.State} {args : List Word} {s' : EvmYul.Yul.State} {l : Option Word}
    (h : EvmYul.step (τ := .Yul) op .none s args = .ok (s', l)) : StepPres s s' := by
  cases op <;> rename_i o <;> cases o <;>
    (unfold EvmYul.step at h; simp only [Id.run] at h) <;>
    first
      -- combinators whose lemma has no implicit op function (defeq matches directly)
      | exact execUnOp_pres (args := args) h
      | exact execBinOp_pres (args := args) h
      | exact execTriOp_pres (args := args) h
      | exact execQuadOp_pres (args := args) h
      | exact executionEnvOp_pres (args := args) h
      | exact unaryExecutionEnvOp_pres (args := args) h
      | exact machineStateOp_pres (args := args) h
      | exact stateOp_pres (args := args) h
      | exact binaryMachineStateOp_pres (args := args) h
      | exact ternaryMachineStateOp_pres (args := args) h
      | exact binaryStateOp_sstore_pres (args := args) h
      | exact binaryStateOp_tstore_pres (args := args) h
      | exact log0Op_pres (args := args) h
      | exact log1Op_pres (args := args) h
      | exact log2Op_pres (args := args) h
      | exact log3Op_pres (args := args) h
      | exact log4Op_pres (args := args) h
      -- combinators whose lemma has an implicit `{f}`: supply it so isDefEq can
      -- unfold the private dispatcher (no metavar to get stuck on)
      | exact binaryMachineStateOp'_pres (f := EvmYul.MachineState.keccak256) (args := args) h
      | exact unaryStateOp_pres (f := EvmYul.State.balance) (args := args)
          (fun _ _ => ⟨rfl, rfl⟩) h
      | exact unaryStateOp_pres (f := EvmYul.State.sload) (args := args)
          (fun _ _ => ⟨rfl, rfl⟩) h
      | exact unaryStateOp_pres (f := EvmYul.State.tload) (args := args)
          (fun _ _ => ⟨rfl, rfl⟩) h
      | exact unaryStateOp_pres (f := EvmYul.State.extCodeSize) (args := args)
          (fun _ _ => ⟨rfl, rfl⟩) h
      | exact absurd rfl hHash    -- EXTCODEHASH (excluded by `hHash`; overridden in W2)
      | exact unaryStateOp_pres (f := fun st v => (st, EvmYul.State.calldataload st v))
          (args := args) (fun _ _ => ⟨rfl, rfl⟩) h
      | exact unaryStateOp_pres (f := fun st v => (st, EvmYul.State.blockHash st v))
          (args := args) (fun _ _ => ⟨rfl, rfl⟩) h
      | exact ternaryCopyOp_pres (f := EvmYul.SharedState.calldatacopy) (args := args)
          (fun _ _ _ _ => ⟨rfl, rfl⟩) h
      | exact ternaryCopyOp_pres (f := EvmYul.SharedState.codeBytesCopy) (args := args)
          (fun _ _ _ _ => ⟨rfl, rfl⟩) h
      | exact quaternaryCopyOp_pres (f := EvmYul.SharedState.extCodeCopy') (args := args)
          (fun _ _ _ _ _ => ⟨rfl, rfl⟩) h
      -- POP: `.ok (s, none)` directly
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, _⟩ := h; exact StepPres.rfl' s)
      -- external / create ops: excluded by `hExt`
      | exact absurd hExt (by decide)
      -- remaining ops: terminal errors and bespoke `.Yul` MLOAD/RETURNDATACOPY.
      -- `simp only [reduceCtorEq] at h` is a *clean-failing* error closer (it shuts a
      -- syntactic `.error = .ok`, and simply fails on anything else — so a
      -- mis-fired alternative never leaves a dangling goal that poisons `first`).
      | (first
          -- STOP / INVALID: a private transformer ignoring lits, `whnf`s to error
          | (change (Except.error _ :
                Except EvmYul.Yul.Exception (EvmYul.Yul.State × Option Word)) =
                Except.ok (s', l) at h
             simp only [reduceCtorEq] at h)
          -- RETURN / REVERT / SELFDESTRUCT: a match whose every arm is an error
          | (split at h <;> simp only [reduceCtorEq] at h)
          -- MLOAD / RETURNDATACOPY (`setMachineState`) and any residual error arm:
          -- resolve the argument list, break the remaining match/`if`, normalise the
          -- `do`-block, then close each leaf as an error or a preserved machine store
          | (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _⟩⟩⟩⟩ <;>
              (repeat' split at h) <;>
              simp only [Except.ok.injEq, reduceCtorEq, Prod.mk.injEq, bind, Except.bind,
                pure, Except.pure, Pure.pure, Bind.bind] at h <;>
              (obtain ⟨rfl, _⟩ := h; exact setMachineState_pres _ s)))

/-! ### The ratified `primCall` boundary lemma

A `BridgeOp` `primCall` that returns `.ok` preserves the executing account's
presence and never changes `codeOwner`. It reduces (for a non-external op) to the
`step` default arm, whose preservation is `step_yul_ok_preserves`. -/

/-- For an op with no `CallKind`, positive-fuel `primCall` is the static-mode guard
followed by the `step` default arm (the four external-call arms are excluded). The
statement keeps `op` abstract, so callers can compose without losing its name. -/
private theorem primCall_succ_default {op : Operation .Yul}
    (hCall : Simulation.CallKind.ofYulOperation? op = none)
    (k : Nat) (s : EvmYul.Yul.State) (args : List Word) :
    EvmYul.Yul.primCall (k + 1) s op args =
      (if ¬s.executionEnv.perm ∧ op ∈ ([.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT,
            .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] : List (Operation .Yul)) then
        .error .StaticModeViolation
      else
        (match EvmYul.step (τ := .Yul) op .none s args with
         | .ok (st, lit) => .ok (st, lit.toList)
         | .error e => .error e)) := by
  cases op with
  | System sop =>
      cases sop <;>
        first
          | (rw [EvmYul.Yul.primCall.eq_def]; rfl)
          | exact absurd hCall (by simp [Simulation.CallKind.ofYulOperation?])
  | _ => rw [EvmYul.Yul.primCall.eq_def]; rfl

private theorem primCall_bridge_ok {op : Operation .Yul} (hOp : BridgeOp op)
    {k : Nat} {s : EvmYul.Yul.State} {args : List Word}
    {s' : EvmYul.Yul.State} {out : List Word}
    (h : EvmYul.Yul.primCall (k + 1) s op args = .ok (s', out)) :
    ∃ l, EvmYul.step (τ := .Yul) op .none s args = .ok (s', l) := by
  rw [primCall_succ_default (callKind_none_of_bridge hOp)] at h
  split at h
  · exact absurd h (by simp)
  · cases hstep : EvmYul.step (τ := .Yul) op .none s args with
    | error e => rw [hstep] at h; exact absurd h (by simp)
    | ok stl =>
        obtain ⟨st, l⟩ := stl
        rw [hstep] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact ⟨l, rfl⟩

theorem primCall_preserves_codeBridge {op : Operation .Yul} (hOp : BridgeOp op)
    (fuel : Nat) (s : InteractionSemantics.State) (args : List Word)
    (s' : InteractionSemantics.State) (out : List Word)
    (h : EvmYul.Yul.primCall fuel s op args = .ok (s', out)) :
    s'.executionEnv.codeOwner = s.executionEnv.codeOwner ∧
      (s.sharedState.accountMap.find? s.executionEnv.codeOwner ≠ none →
        s'.sharedState.accountMap.find? s'.executionEnv.codeOwner ≠ none) := by
  show StepPres s s'
  cases fuel with
  | zero => rw [EvmYul.Yul.primCall] at h; exact absurd h (by simp)
  | succ k =>
      obtain ⟨l, hstep⟩ := primCall_bridge_ok hOp h
      exact step_yul_ok_preserves hOp.1 hOp.2.2.2 hstep

end Preservation

/-! ## Boundary corollaries for the W3 mutual induction -/

/-- Off-by-one form (definitional, holds at every fuel): our `openEval (n+1)`
agrees with native `primCall n`. -/
theorem doneAgrees_openEval_shift {op : Operation .Yul} (hOp : BridgeOp op)
    (n : Nat) (s : InteractionSemantics.State) (args : List Word) :
    DoneAgrees (EvmYul.Yul.primCall n s op args)
      (InteractionSemantics.Primitive.openEval (n + 1) s op args) := by
  rw [openEval_agrees hOp, closedEval_agrees hOp]
  exact DoneAgrees.mk (resultAgrees_toResult s _)

/-- Same-fuel form (requires `2 ≤ fuel`, the residue of the primitive off-by-one):
native `primCall (n+2)` agrees with our `openEval (n+2)`. This is the shape the W3
induction consumes at expression/statement primitive sites. -/
theorem doneAgrees_openEval {op : Operation .Yul} (hOp : BridgeOp op)
    (n : Nat) (s : InteractionSemantics.State) (args : List Word) :
    DoneAgrees (EvmYul.Yul.primCall (n + 2) s op args)
      (InteractionSemantics.Primitive.openEval (n + 2) s op args) := by
  have hFuel : EvmYul.Yul.primCall (n + 2) s op args =
      EvmYul.Yul.primCall (n + 1) s op args :=
    primCall_fuel_insensitive hOp (n + 1) n s args
  rw [hFuel]
  exact doneAgrees_openEval_shift hOp (n + 1) s args

end VerityBridge
end Yul
end EvmCompiler
