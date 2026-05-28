import Batteries.Data.RBMap.Lemmas
import EvmCompiler.Yul.NoCallRuntime

namespace EvmCompiler
namespace Yul
namespace ConcreteStateRel

abbrev AccountMapYul := EvmYul.AccountMap .Yul
abbrev AccountMapEVM := EvmYul.AccountMap .EVM

/--
Concrete account agreement for the current no-CALL observation theorem.

The typed source code field is intentionally omitted: Yul source contracts and
EVM bytecode live in different representations. The executable code image is
related separately by `ExecutionEnvRel.codeBytes` and
`RecursiveBridgeInitialCodeImageRel`.
-/
def AccountRel (source : EvmYul.Account .Yul)
    (target : EvmYul.Account .EVM) : Prop :=
  source.nonce = target.nonce ∧
    source.balance = target.balance ∧
    source.storage = target.storage ∧
      source.codeBytes = target.codeBytes ∧
      source.tstorage = target.tstorage

def AccountMapRel (source : AccountMapYul) (target : AccountMapEVM) :
    Prop :=
  ∀ address,
    match source.find? address, target.find? address with
    | none, none => True
    | some sourceAccount, some targetAccount =>
        AccountRel sourceAccount targetAccount
    | _, _ => False

def AccountStorage? {τ : EvmYul.OperationType}
    (accounts : EvmYul.AccountMap τ)
    (address : EvmYul.AccountAddress) : Option EvmYul.Storage :=
  (accounts.find? address).map (fun account => account.storage)

def AccountTransientStorage? {τ : EvmYul.OperationType}
    (accounts : EvmYul.AccountMap τ)
    (address : EvmYul.AccountAddress) : Option EvmYul.Storage :=
  (accounts.find? address).map (fun account => account.tstorage)

def AccountNonce? {τ : EvmYul.OperationType}
    (accounts : EvmYul.AccountMap τ)
    (address : EvmYul.AccountAddress) : Option EvmYul.UInt256 :=
  (accounts.find? address).map (fun account => account.nonce)

def AccountCodeBytes? {τ : EvmYul.OperationType}
    (accounts : EvmYul.AccountMap τ)
    (address : EvmYul.AccountAddress) : Option ByteArray :=
  (accounts.find? address).map (fun account => account.codeBytes)

def StorageImageRel {τ₁ τ₂ : EvmYul.OperationType}
    (source : EvmYul.AccountMap τ₁) (target : EvmYul.AccountMap τ₂) :
    Prop :=
  ∀ address, AccountStorage? source address = AccountStorage? target address

def TransientStorageImageRel {τ₁ τ₂ : EvmYul.OperationType}
    (source : EvmYul.AccountMap τ₁) (target : EvmYul.AccountMap τ₂) :
    Prop :=
  ∀ address,
    AccountTransientStorage? source address =
      AccountTransientStorage? target address

def NonceImageRel {τ₁ τ₂ : EvmYul.OperationType}
    (source : EvmYul.AccountMap τ₁) (target : EvmYul.AccountMap τ₂) :
    Prop :=
  ∀ address, AccountNonce? source address = AccountNonce? target address

def CodeBytesImageRel {τ₁ τ₂ : EvmYul.OperationType}
    (source : EvmYul.AccountMap τ₁) (target : EvmYul.AccountMap τ₂) :
    Prop :=
  ∀ address,
    AccountCodeBytes? source address = AccountCodeBytes? target address

namespace AccountRel

theorem updateStorage {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM} {slot value : Word}
    (hRel : AccountRel source target) :
    AccountRel
      (source.updateStorage slot value)
      (target.updateStorage slot value) := by
  rcases hRel with ⟨hNonce, hBalance, hStorage, hCodeBytes, hTStorage⟩
  by_cases hZero : value == default <;>
    simp [AccountRel, EvmYul.Account.updateStorage, hZero, hBalance,
      hStorage, hTStorage, hNonce, hCodeBytes]

theorem updateTransientStorage {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM} {slot value : Word}
    (hRel : AccountRel source target) :
    AccountRel
      (source.updateTransientStorage slot value)
      (target.updateTransientStorage slot value) := by
  rcases hRel with ⟨hNonce, hBalance, hStorage, hCodeBytes, hTStorage⟩
  by_cases hZero : value == default <;>
    simp [AccountRel, EvmYul.Account.updateTransientStorage, hZero,
      hBalance, hStorage, hTStorage, hNonce, hCodeBytes]

end AccountRel

namespace AccountMapRel

theorem balance {source : AccountMapYul} {target : AccountMapEVM}
    (hRel : AccountMapRel source target) (address : EvmYul.AccountAddress) :
    (source.find? address |>.elim (EvmYul.UInt256.ofNat 0) (·.balance)) =
      (target.find? address |>.elim (EvmYul.UInt256.ofNat 0)
        (·.balance)) := by
  have hAddress := hRel address
  cases hSource : source.find? address <;>
    cases hTarget : target.find? address <;>
      simp [hSource, hTarget, AccountRel] at hAddress ⊢
  exact hAddress.2.1

theorem storageLookup {source : AccountMapYul} {target : AccountMapEVM}
    (hRel : AccountMapRel source target) (address : EvmYul.AccountAddress)
    (slot : Word) :
    (source.find? address |>.option (EvmYul.UInt256.ofNat 0)
        (EvmYul.Account.lookupStorage (k := slot))) =
      (target.find? address |>.option (EvmYul.UInt256.ofNat 0)
        (EvmYul.Account.lookupStorage (k := slot))) := by
  have hAddress := hRel address
  cases hSource : source.find? address with
  | none =>
      cases hTarget : target.find? address with
      | none => rfl
      | some targetAccount =>
          simp [hSource, hTarget] at hAddress
  | some sourceAccount =>
      cases hTarget : target.find? address with
      | none =>
          simp [hSource, hTarget] at hAddress
      | some targetAccount =>
          simp [hSource, hTarget, AccountRel] at hAddress
          simpa [hSource, hTarget, EvmYul.Account.lookupStorage] using
            congrArg
              (fun storage =>
                storage.findD slot (EvmYul.UInt256.ofNat 0))
              hAddress.2.2.1

theorem storageImage {source : AccountMapYul} {target : AccountMapEVM}
    (hRel : AccountMapRel source target) :
    StorageImageRel source target := by
  intro address
  have hAddress := hRel address
  cases hSource : source.find? address with
  | none =>
      cases hTarget : target.find? address with
      | none => simp [AccountStorage?, hSource, hTarget]
      | some targetAccount =>
          simp [hSource, hTarget] at hAddress
  | some sourceAccount =>
      cases hTarget : target.find? address with
      | none =>
          simp [hSource, hTarget] at hAddress
      | some targetAccount =>
          simp [hSource, hTarget, AccountRel] at hAddress
          simpa [AccountStorage?, hSource, hTarget] using hAddress.2.2.1

theorem transientStorageLookup {source : AccountMapYul}
    {target : AccountMapEVM}
    (hRel : AccountMapRel source target) (address : EvmYul.AccountAddress)
    (slot : Word) :
    (source.find? address |>.option (EvmYul.UInt256.ofNat 0)
        (EvmYul.Account.lookupTransientStorage (k := slot))) =
      (target.find? address |>.option (EvmYul.UInt256.ofNat 0)
        (EvmYul.Account.lookupTransientStorage (k := slot))) := by
  have hAddress := hRel address
  cases hSource : source.find? address with
  | none =>
      cases hTarget : target.find? address with
      | none => rfl
      | some targetAccount =>
          simp [hSource, hTarget] at hAddress
  | some sourceAccount =>
      cases hTarget : target.find? address with
      | none =>
          simp [hSource, hTarget] at hAddress
      | some targetAccount =>
          simp [hSource, hTarget, AccountRel] at hAddress
          simpa [hSource, hTarget,
            EvmYul.Account.lookupTransientStorage] using
            congrArg
              (fun storage =>
                storage.findD slot (EvmYul.UInt256.ofNat 0))
              hAddress.2.2.2.2

theorem transientStorageImage {source : AccountMapYul}
    {target : AccountMapEVM}
    (hRel : AccountMapRel source target) :
    TransientStorageImageRel source target := by
  intro address
  have hAddress := hRel address
  cases hSource : source.find? address with
  | none =>
      cases hTarget : target.find? address with
      | none => simp [AccountTransientStorage?, hSource, hTarget]
      | some targetAccount =>
          simp [hSource, hTarget] at hAddress
  | some sourceAccount =>
      cases hTarget : target.find? address with
      | none =>
          simp [hSource, hTarget] at hAddress
      | some targetAccount =>
          simp [hSource, hTarget, AccountRel] at hAddress
          simpa [AccountTransientStorage?, hSource, hTarget] using
            hAddress.2.2.2.2

theorem nonceImage {source : AccountMapYul} {target : AccountMapEVM}
    (hRel : AccountMapRel source target) :
    NonceImageRel source target := by
  intro address
  have hAddress := hRel address
  cases hSource : source.find? address with
  | none =>
      cases hTarget : target.find? address with
      | none => simp [AccountNonce?, hSource, hTarget]
      | some targetAccount =>
          simp [hSource, hTarget] at hAddress
  | some sourceAccount =>
      cases hTarget : target.find? address with
      | none =>
          simp [hSource, hTarget] at hAddress
      | some targetAccount =>
          simp [hSource, hTarget, AccountRel] at hAddress
          simpa [AccountNonce?, hSource, hTarget] using hAddress.1

theorem codeBytesImage {source : AccountMapYul} {target : AccountMapEVM}
    (hRel : AccountMapRel source target) :
    CodeBytesImageRel source target := by
  intro address
  have hAddress := hRel address
  cases hSource : source.find? address with
  | none =>
      cases hTarget : target.find? address with
      | none => simp [AccountCodeBytes?, hSource, hTarget]
      | some targetAccount =>
          simp [hSource, hTarget] at hAddress
  | some sourceAccount =>
      cases hTarget : target.find? address with
      | none =>
          simp [hSource, hTarget] at hAddress
      | some targetAccount =>
          simp [hSource, hTarget, AccountRel] at hAddress
          simpa [AccountCodeBytes?, hSource, hTarget] using
            hAddress.2.2.2.1

theorem insert {source : AccountMapYul} {target : AccountMapEVM}
    {address : EvmYul.AccountAddress}
    {sourceAccount : EvmYul.Account .Yul}
    {targetAccount : EvmYul.Account .EVM}
    (hRel : AccountMapRel source target)
    (hAccount : AccountRel sourceAccount targetAccount) :
    AccountMapRel (source.insert address sourceAccount)
      (target.insert address targetAccount) := by
  intro query
  by_cases hEq : compare query address = .eq
  · simp [
      Batteries.RBMap.find?_insert_of_eq (t := source)
        (k := address) (v := sourceAccount) hEq,
      Batteries.RBMap.find?_insert_of_eq (t := target)
        (k := address) (v := targetAccount) hEq,
      hAccount]
  · simpa [AccountMapRel,
      Batteries.RBMap.find?_insert_of_ne (t := source)
        (k := address) (v := sourceAccount) hEq,
      Batteries.RBMap.find?_insert_of_ne (t := target)
        (k := address) (v := targetAccount) hEq] using hRel query

theorem selfdestructAccountMap {source : AccountMapYul}
    {target : AccountMapEVM} {sourceAddress targetAddress : EvmYul.AccountAddress}
    {created : Bool}
    (hRel : AccountMapRel source target) :
    AccountMapRel
      (EvmYul.selfdestructAccountMap source sourceAddress targetAddress
        created)
      (EvmYul.selfdestructAccountMap target sourceAddress targetAddress
        created) := by
  have hSourceAddress := hRel sourceAddress
  cases hSource : source.find? sourceAddress with
  | none =>
      cases hTarget : target.find? sourceAddress with
      | none =>
          simpa [EvmYul.selfdestructAccountMap, hSource, hTarget] using hRel
      | some targetSource =>
          simp [hSource, hTarget] at hSourceAddress
  | some sourceAccount =>
      cases hTarget : target.find? sourceAddress with
      | none =>
          simp [hSource, hTarget] at hSourceAddress
      | some targetSource =>
          have hSourceAccount : AccountRel sourceAccount targetSource := by
            simpa [hSource, hTarget] using hSourceAddress
          have hBalance : sourceAccount.balance = targetSource.balance :=
            hSourceAccount.2.1
          have hTargetAddress := hRel targetAddress
          cases hSourceTarget : source.find? targetAddress with
          | none =>
              cases hTargetTarget : target.find? targetAddress with
              | none =>
                  by_cases hZero : targetSource.balance == (⟨0⟩ : Word)
                  · simpa [EvmYul.selfdestructAccountMap, hSource, hTarget,
                      hSourceTarget, hTargetTarget, hZero, hBalance] using
                      hRel
                  · have hNewTarget : AccountRel
                        { (default : EvmYul.Account .Yul) with
                          balance := sourceAccount.balance }
                        { (default : EvmYul.Account .EVM) with
                          balance := targetSource.balance } := by
                      exact ⟨rfl, hBalance, rfl, rfl, rfl⟩
                    have hZeroSource : AccountRel
                        { sourceAccount with balance := (⟨0⟩ : Word) }
                        { targetSource with balance := (⟨0⟩ : Word) } := by
                      rcases hSourceAccount with
                        ⟨hNonce, _hBalance, hStorage, hCodeBytes,
                          hTStorage⟩
                      simp [AccountRel, hNonce, hStorage, hCodeBytes,
                        hTStorage]
                    simpa [EvmYul.selfdestructAccountMap, hSource, hTarget,
                      hSourceTarget, hTargetTarget, hZero, hBalance] using
                      (AccountMapRel.insert (address := sourceAddress)
                        (AccountMapRel.insert (address := targetAddress)
                          hRel hNewTarget)
                        hZeroSource)
              | some targetAccount =>
                  simp [hSourceTarget, hTargetTarget] at hTargetAddress
          | some sourceTarget =>
              cases hTargetTarget : target.find? targetAddress with
              | none =>
                  simp [hSourceTarget, hTargetTarget] at hTargetAddress
              | some targetTarget =>
                  have hTargetAccount :
                      AccountRel sourceTarget targetTarget := by
                    simpa [hSourceTarget, hTargetTarget] using hTargetAddress
                  by_cases hDifferent : targetAddress ≠ sourceAddress
                  · have hUpdatedTarget : AccountRel
                        { sourceTarget with
                          balance :=
                            sourceTarget.balance + sourceAccount.balance }
                        { targetTarget with
                          balance :=
                            targetTarget.balance + targetSource.balance } := by
                      rcases hTargetAccount with
                        ⟨hNonce, hTargetBalance, hStorage, hCodeBytes,
                          hTStorage⟩
                      simp [AccountRel, hNonce, hTargetBalance, hBalance,
                        hStorage, hCodeBytes, hTStorage]
                    have hZeroSource : AccountRel
                        { sourceAccount with balance := (⟨0⟩ : Word) }
                        { targetSource with balance := (⟨0⟩ : Word) } := by
                      rcases hSourceAccount with
                        ⟨hNonce, _hBalance, hStorage, hCodeBytes,
                          hTStorage⟩
                      simp [AccountRel, hNonce, hStorage, hCodeBytes,
                        hTStorage]
                    simpa [EvmYul.selfdestructAccountMap, hSource, hTarget,
                      hSourceTarget, hTargetTarget, hDifferent] using
                      (AccountMapRel.insert (address := sourceAddress)
                        (AccountMapRel.insert (address := targetAddress)
                          hRel hUpdatedTarget)
                        hZeroSource)
                  · have hSame : targetAddress = sourceAddress :=
                      Classical.not_not.mp hDifferent
                    subst targetAddress
                    rw [hSource] at hSourceTarget
                    injection hSourceTarget with hSourceTargetEq
                    subst sourceTarget
                    rw [hTarget] at hTargetTarget
                    injection hTargetTarget with hTargetTargetEq
                    subst targetTarget
                    by_cases hCreated : created
                    · have hZeroTarget : AccountRel
                          { sourceAccount with balance := (⟨0⟩ : Word) }
                          { targetSource with balance := (⟨0⟩ : Word) } := by
                        rcases hSourceAccount with
                          ⟨hNonce, _hBalance, hStorage, hCodeBytes,
                            hTStorage⟩
                        simp [AccountRel, hNonce, hStorage, hCodeBytes,
                          hTStorage]
                      have hZeroSource : AccountRel
                          { sourceAccount with balance := (⟨0⟩ : Word) }
                          { targetSource with balance := (⟨0⟩ : Word) } := by
                        rcases hSourceAccount with
                          ⟨hNonce, _hBalance, hStorage, hCodeBytes,
                            hTStorage⟩
                        simp [AccountRel, hNonce, hStorage, hCodeBytes,
                          hTStorage]
                      simpa [EvmYul.selfdestructAccountMap, hSource,
                        hTarget, hCreated]
                        using
                          (AccountMapRel.insert (address := sourceAddress)
                            (AccountMapRel.insert (address := sourceAddress)
                              hRel hZeroTarget)
                            hZeroSource)
                    · simpa [EvmYul.selfdestructAccountMap, hSource,
                        hTarget, hCreated]
                        using hRel

end AccountMapRel

theorem selfbalanceRel
    {source : EvmYul.State .Yul} {target : EvmYul.State .EVM}
    (hAccountMap : AccountMapRel source.accountMap target.accountMap)
    (hOwner : source.executionEnv.codeOwner = target.executionEnv.codeOwner) :
    EvmYul.State.selfbalance source =
      EvmYul.State.selfbalance target := by
  unfold EvmYul.State.selfbalance
  rw [← hOwner]
  exact AccountMapRel.balance hAccountMap source.executionEnv.codeOwner

theorem balanceRel
    {source : EvmYul.State .Yul} {target : EvmYul.State .EVM}
    {address : Word}
    (hAccountMap : AccountMapRel source.accountMap target.accountMap) :
    (EvmYul.State.balance source address).2 =
      (EvmYul.State.balance target address).2 := by
  simpa [EvmYul.State.balance] using
    AccountMapRel.balance hAccountMap
      (EvmYul.AccountAddress.ofUInt256 address)

theorem sloadRel
    {source : EvmYul.State .Yul} {target : EvmYul.State .EVM}
    {slot : Word}
    (hAccountMap : AccountMapRel source.accountMap target.accountMap)
    (hOwner : source.executionEnv.codeOwner = target.executionEnv.codeOwner) :
    (EvmYul.State.sload source slot).2 =
      (EvmYul.State.sload target slot).2 := by
  simp [EvmYul.State.sload, EvmYul.State.lookupAccount]
  rw [← hOwner]
  exact AccountMapRel.storageLookup hAccountMap
    source.executionEnv.codeOwner slot

theorem tloadRel
    {source : EvmYul.State .Yul} {target : EvmYul.State .EVM}
    {slot : Word}
    (hAccountMap : AccountMapRel source.accountMap target.accountMap)
    (hOwner : source.executionEnv.codeOwner = target.executionEnv.codeOwner) :
    (EvmYul.State.tload source slot).2 =
      (EvmYul.State.tload target slot).2 := by
  simp [EvmYul.State.tload, EvmYul.State.lookupAccount]
  rw [← hOwner]
  exact AccountMapRel.transientStorageLookup hAccountMap
    source.executionEnv.codeOwner slot

theorem sstoreAccountMapRel
    {source : EvmYul.State .Yul} {target : EvmYul.State .EVM}
    {slot value : Word}
    (hAccountMap : AccountMapRel source.accountMap target.accountMap)
    (hSigma : source.σ₀ = target.σ₀)
    (hOwner : source.executionEnv.codeOwner = target.executionEnv.codeOwner)
    (hSubstate : source.substate = target.substate) :
    AccountMapRel
      (EvmYul.State.sstore source slot value).accountMap
      (EvmYul.State.sstore target slot value).accountMap := by
  classical
  let owner := source.executionEnv.codeOwner
  have hTargetOwner : target.executionEnv.codeOwner = owner := hOwner.symm
  have hOwnerRel := hAccountMap owner
  cases hSource : source.accountMap.find? owner with
  | none =>
      cases hTarget : target.accountMap.find? owner with
      | none =>
          simpa [EvmYul.State.sstore, EvmYul.State.lookupAccount,
            Option.option, owner, hTargetOwner, hSource, hTarget, hSigma,
            hSubstate] using hAccountMap
      | some targetAccount =>
          simp [hSource, hTarget] at hOwnerRel
  | some sourceAccount =>
      cases hTarget : target.accountMap.find? owner with
      | none =>
          simp [hSource, hTarget] at hOwnerRel
      | some targetAccount =>
          simp [hSource, hTarget] at hOwnerRel
          have hUpdated :
              AccountRel (sourceAccount.updateStorage slot value)
                (targetAccount.updateStorage slot value) :=
            AccountRel.updateStorage hOwnerRel
          have hInserted :
              AccountMapRel
                (source.accountMap.insert owner
                  (sourceAccount.updateStorage slot value))
                (target.accountMap.insert owner
                  (targetAccount.updateStorage slot value)) :=
            AccountMapRel.insert hAccountMap hUpdated
          simpa [EvmYul.State.sstore, EvmYul.State.lookupAccount,
            EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
            Option.option, owner, hTargetOwner, hSource, hTarget, hSigma,
            hSubstate] using hInserted

theorem sstoreSubstateRel
    {source : EvmYul.State .Yul} {target : EvmYul.State .EVM}
    {slot value : Word}
    (hAccountMap : AccountMapRel source.accountMap target.accountMap)
    (hSigma : source.σ₀ = target.σ₀)
    (hOwner : source.executionEnv.codeOwner = target.executionEnv.codeOwner)
    (hSubstate : source.substate = target.substate) :
    (EvmYul.State.sstore source slot value).substate =
      (EvmYul.State.sstore target slot value).substate := by
  classical
  let owner := source.executionEnv.codeOwner
  have hTargetOwner : target.executionEnv.codeOwner = owner := hOwner.symm
  have hOwnerRel := hAccountMap owner
  cases hSource : source.accountMap.find? owner with
  | none =>
      cases hTarget : target.accountMap.find? owner with
      | none =>
          simp [EvmYul.State.sstore, EvmYul.State.lookupAccount,
            Option.option, owner, hTargetOwner, hSource, hTarget, hSubstate]
      | some targetAccount =>
          simp [hSource, hTarget] at hOwnerRel
  | some sourceAccount =>
      cases hTarget : target.accountMap.find? owner with
      | none =>
          simp [hSource, hTarget] at hOwnerRel
      | some targetAccount =>
          simp [hSource, hTarget] at hOwnerRel
          rcases hOwnerRel with
            ⟨_hNonce, _hBalance, hStorage, _hCodeBytes, _hTStorage⟩
          simp [EvmYul.State.sstore, EvmYul.State.lookupAccount,
            EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
            EvmYul.Substate.addAccessedStorageKey, Batteries.RBMap.find!,
            Option.option, owner, hTargetOwner, hSource, hTarget, hSigma,
            hSubstate, hStorage]

theorem tstoreAccountMapRel
    {source : EvmYul.State .Yul} {target : EvmYul.State .EVM}
    {slot value : Word}
    (hAccountMap : AccountMapRel source.accountMap target.accountMap)
    (hOwner : source.executionEnv.codeOwner = target.executionEnv.codeOwner) :
    AccountMapRel
      (EvmYul.State.tstore source slot value).accountMap
      (EvmYul.State.tstore target slot value).accountMap := by
  let owner := source.executionEnv.codeOwner
  have hTargetOwner : target.executionEnv.codeOwner = owner := hOwner.symm
  have hOwnerRel := hAccountMap owner
  cases hSource : source.accountMap.find? owner with
  | none =>
      cases hTarget : target.accountMap.find? owner with
      | none =>
          simpa [EvmYul.State.tstore, EvmYul.State.lookupAccount,
            Option.option, owner, hTargetOwner, hSource, hTarget] using
            hAccountMap
      | some targetAccount =>
          simp [hSource, hTarget] at hOwnerRel
  | some sourceAccount =>
      cases hTarget : target.accountMap.find? owner with
      | none =>
          simp [hSource, hTarget] at hOwnerRel
      | some targetAccount =>
          simp [hSource, hTarget] at hOwnerRel
          have hUpdated :
              AccountRel (sourceAccount.updateTransientStorage slot value)
                (targetAccount.updateTransientStorage slot value) :=
            AccountRel.updateTransientStorage hOwnerRel
          have hInserted :
              AccountMapRel
                (source.accountMap.insert owner
                  (sourceAccount.updateTransientStorage slot value))
                (target.accountMap.insert owner
                  (targetAccount.updateTransientStorage slot value)) :=
            AccountMapRel.insert hAccountMap hUpdated
          simpa [EvmYul.State.tstore, EvmYul.State.lookupAccount,
            EvmYul.State.updateAccount, EvmYul.State.setAccount,
            Option.option, owner, hTargetOwner, hSource, hTarget] using
            hInserted

def config : Reference.StateRelConfig where
  accountMapRel := AccountMapRel
  selfbalanceRel := selfbalanceRel
  balanceRel := balanceRel
  sloadRel := sloadRel
  sstoreAccountMapRel := sstoreAccountMapRel
  sstoreSubstateRel := sstoreSubstateRel
  tloadRel := tloadRel
  tstoreAccountMapRel := tstoreAccountMapRel
  codeRel := fun _ _ => True
  varStackRel := Reference.VarStackRel.exact
  terminalRel := fun _ _ _ _ => True
  revertRel := fun _ _ => True
  gasAvailableRel := Eq
  gasValueRel := by
    intro yul evm hGas
    simpa [EvmYul.MachineState.gas] using hGas
  totalGasRel := Eq

theorem sharedStateRel_accountMapRel
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : Reference.SharedStateRel config source target) :
    AccountMapRel source.toState.accountMap target.toState.accountMap :=
  hRel.chain.accountMap

theorem sharedStateRel_createdAccounts
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : Reference.SharedStateRel config source target) :
    source.toState.createdAccounts = target.toState.createdAccounts :=
  hRel.chain.createdAccounts

theorem sharedStateRel_selfdestructAccountMapRel
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : Reference.SharedStateRel config source target)
    (recipient : Word) :
    AccountMapRel
      (EvmYul.selfdestructAccountMap source.toState.accountMap
        source.executionEnv.codeOwner
        (EvmYul.AccountAddress.ofUInt256 recipient)
        (source.toState.createdAccounts.contains
          source.executionEnv.codeOwner))
      (EvmYul.selfdestructAccountMap target.toState.accountMap
        target.executionEnv.codeOwner
        (EvmYul.AccountAddress.ofUInt256 recipient)
        (target.toState.createdAccounts.contains
          target.executionEnv.codeOwner)) := by
  have hOwner :
      source.executionEnv.codeOwner = target.executionEnv.codeOwner :=
    hRel.chain.executionEnv.codeOwner
  have hCreated :
      source.toState.createdAccounts.contains target.executionEnv.codeOwner =
        target.toState.createdAccounts.contains
          target.executionEnv.codeOwner := by
    rw [← hOwner, hRel.chain.createdAccounts]
  simpa [hOwner, hCreated] using
    AccountMapRel.selfdestructAccountMap
      (sourceAddress := target.executionEnv.codeOwner)
      (targetAddress := EvmYul.AccountAddress.ofUInt256 recipient)
      (created :=
        source.toState.createdAccounts.contains
          target.executionEnv.codeOwner)
      (sharedStateRel_accountMapRel hRel)

theorem sharedStateRel_storageImageRel
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : Reference.SharedStateRel config source target) :
    StorageImageRel source.toState.accountMap target.toState.accountMap :=
  AccountMapRel.storageImage (sharedStateRel_accountMapRel hRel)

theorem sourceStateRel_accountMapRel
    {layout : List Name} {source : Reference.State}
    {target : Objects.Source.State}
    (hRel :
      Reference.SourceBridgeFacts.SourceStateRel config layout source target) :
    ∃ shared store,
      source = .Ok shared store ∧
        AccountMapRel shared.toState.accountMap
          target.shared.toState.accountMap := by
  cases hRel with
  | ok hShared _hVars =>
      exact ⟨_, _, rfl, sharedStateRel_accountMapRel hShared⟩

theorem sourceStateRel_storageImageRel
    {layout : List Name} {source : Reference.State}
    {target : Objects.Source.State}
    (hRel :
      Reference.SourceBridgeFacts.SourceStateRel config layout source target) :
    ∃ shared store,
      source = .Ok shared store ∧
        StorageImageRel shared.toState.accountMap
          target.shared.toState.accountMap := by
  rcases sourceStateRel_accountMapRel hRel with
    ⟨shared, store, hSource, hAccountMap⟩
  exact ⟨shared, store, hSource, AccountMapRel.storageImage hAccountMap⟩

def successfulResultAccountMapRel
    (referenceResult : Reference.Result) (evmFinal : Assembly.EVMState) :
    Prop :=
  match referenceResult with
  | .regular final =>
      AccountMapRel final.toState.accountMap evmFinal.accountMap
  | .yulHalt haltState _ =>
      AccountMapRel haltState.toState.accountMap evmFinal.accountMap
  | .revert _ => False

theorem frameStateRel_accountMap
    {source : Structured.RunState} {target : Assembly.EVMState}
    {tokens : List Word}
    (hRel :
      Structured.Preservation.Frame.StateRel source target tokens) :
    target.accountMap = source.evm.accountMap := by
  have hData :=
    congrArg (fun state : Assembly.EVMState => state.accountMap)
      hRel.dataRel
  simpa [Structured.Preservation.eraseControl, Assembly.eraseGas] using hData

theorem wholeProgramOutcomeRel_regular_accountMap
    {compiler : Objects.Source.State} {targetOutcome : Assembly.StepResult}
    (hWhole : SourceLowered.WholeProgramOutcomeRel
      (Functions.Source.Outcome.regular compiler) targetOutcome) :
    (Assembly.GasAware.StepResult.finalState targetOutcome).accountMap =
      compiler.shared.toState.accountMap := by
  rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.Source.Outcome.regular, Locals.Source.Outcome.regular,
          Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
      cases targetOutcome with
      | running state =>
          simp [Structured.Preservation.WholeProgramOutcomeRel,
            Assembly.GasAware.StepResult.finalState] at hStructured ⊢
          have hTarget :
              state.accountMap = directState.evm.accountMap := by
            have hAccount :=
              congrArg (fun state : Assembly.EVMState => state.accountMap)
                hStructured
            simpa [Structured.Preservation.eraseControl, Assembly.eraseGas]
              using hAccount.symm
          have hCompiler :
              directState.evm.accountMap =
                compiler.shared.toState.accountMap := by
            simpa using
              congrArg (fun shared => shared.toState.accountMap)
                hSourceDirect.1.1
          exact hTarget.trans hCompiler
      | halted halt =>
          simp [Structured.Preservation.WholeProgramOutcomeRel] at hStructured

theorem wholeProgramOutcomeRel_halt_accountMap
    {kind : Assembly.HaltKind} {compiler : Objects.Source.State}
    {targetOutcome : Assembly.StepResult}
    (hWhole : SourceLowered.WholeProgramOutcomeRel
      (Functions.Source.Outcome.halt kind compiler) targetOutcome) :
    (Assembly.GasAware.StepResult.finalState targetOutcome).accountMap =
      compiler.shared.toState.accountMap := by
  rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.Source.Outcome.halt, Locals.Source.Outcome.halt,
          Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
      rename_i directKind
      rcases hSourceDirect with ⟨hKind, hShared⟩
      subst hKind
      cases targetOutcome with
      | running state =>
          simp [Structured.Preservation.WholeProgramOutcomeRel] at hStructured
      | halted halt =>
          simp [Structured.Preservation.WholeProgramOutcomeRel,
            Assembly.GasAware.StepResult.finalState] at hStructured ⊢
          rcases hStructured with ⟨hKind', tokens, hFrame⟩
          subst hKind'
          have hTarget :
              halt.state.accountMap = directState.evm.accountMap :=
            frameStateRel_accountMap hFrame
          have hCompiler :
              directState.evm.accountMap =
                compiler.shared.toState.accountMap := by
            have hAccount :=
              congrArg (fun shared => shared.toState.accountMap) hShared
            simpa using hAccount.symm
          exact hTarget.trans hCompiler

def resultOutput : Reference.Result → ByteArray
  | .regular _ => ByteArray.empty
  | .yulHalt state _ => state.toMachineState.H_return
  | .revert state => state.toMachineState.H_return

def sharedHaltOutput (kind : Assembly.HaltKind)
    (shared : EvmYul.SharedState .EVM) : ByteArray :=
  match kind with
  | .return | .revert => shared.toMachineState.H_return
  | .stop | .selfdestruct => ByteArray.empty

theorem canonicalTerminalRel_output {kind : Assembly.HaltKind}
    {value : Word} {haltState : Reference.State}
    {compiler : Objects.Source.State}
    (hRel :
      Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
        config kind value haltState compiler) :
    resultOutput (.yulHalt haltState value) =
      sharedHaltOutput kind compiler.shared := by
  cases kind with
  | stop =>
      have hEmpty :=
        Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_nonreturn_H_return_empty
          hRel (by simp)
      simpa [resultOutput, sharedHaltOutput] using hEmpty
  | «return» =>
      rcases
        Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_ok_shape
          hRel with ⟨shared, store, hOk⟩
      have hRel' :
          Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
            config .return value (.Ok shared store) compiler := by
        simpa [hOk] using hRel
      have hReturn :=
        Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_H_return
          hRel'
      simpa [resultOutput, sharedHaltOutput, hOk] using hReturn
  | revert =>
      exact False.elim
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_nonrevert
          hRel rfl)
  | selfdestruct =>
      have hEmpty :=
        Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_nonreturn_H_return_empty
          hRel (by simp)
      simpa [resultOutput, sharedHaltOutput] using hEmpty

theorem canonicalTerminalRel_accountMap
    {kind : Assembly.HaltKind} {value : Word}
    {haltState : Reference.State} {compiler : Objects.Source.State}
    (hRel :
      Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
        config kind value haltState compiler) :
    ∃ shared store,
      haltState = .Ok shared store ∧
        AccountMapRel shared.toState.accountMap
          compiler.shared.toState.accountMap := by
  rcases
      Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_ok_shape
        hRel with
    ⟨yulChild, childStore, hOk⟩
  have hRel' :
      Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
        config kind value (.Ok yulChild childStore) compiler := by
    simpa [hOk] using hRel
  have hNonRevert : kind ≠ .revert :=
    Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel_nonrevert
      hRel'
  rcases hRel' with
    ⟨yulPrim, argFuel, source, sourceAfterArgs, sourceValues, args, rest,
      codeOverride, compilerAfterArgs, sharedAfter, layout, hTerminal,
      hExecSeq, hEvalArgs, hArgsRel, hStruct, hCompiler⟩
  cases hArgsRel with
  | @ok sourceShared sourceStore compilerAfterArgs hShared hVars =>
      let sourceAfterArgs : Reference.State := .Ok sourceShared sourceStore
      have hBase :
          AccountMapRel sourceShared.toState.accountMap
            compilerAfterArgs.shared.toState.accountMap :=
        sharedStateRel_accountMapRel hShared
      cases yulPrim <;> simp [Prim.terminal?] at hTerminal
      case StopArith op =>
        cases op <;> simp at hTerminal
        cases hTerminal
        cases argFuel with
        | zero => simp [EvmYul.Yul.evalArgs] at hEvalArgs
        | succ fuel =>
            let stopState : Reference.State :=
              sourceAfterArgs.setMachineState
                (sourceAfterArgs.toMachineState.setHReturn ByteArray.empty)
            have hPrim :
                EvmYul.Yul.primCall fuel.succ sourceAfterArgs
                    ((.StopArith .STOP : EvmYul.Operation .Yul))
                    sourceValues =
                  .error (.YulHalt stopState (EvmYul.UInt256.ofNat 0)) := by
              simpa [stopState, sourceAfterArgs] using
                PrimSemantics.primCall_stop_eq fuel sourceAfterArgs
                  sourceValues
            have hResult :=
              Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                (sourceFuel := fuel.succ) (source := source)
                (sourceAfterArgs := sourceAfterArgs)
                (yulPrim := (.StopArith .STOP : EvmYul.Operation .Yul))
                (args := args) (rest := rest)
                (codeOverride := codeOverride) (argValues := sourceValues)
                (err := .YulHalt stopState (EvmYul.UInt256.ofNat 0))
                (sourceResult :=
                  .error (.YulHalt (.Ok yulChild childStore) value))
                hEvalArgs hPrim hExecSeq
            injection hResult with hErr
            injection hErr with hState _hValue
            have hChild :
                yulChild.toState.accountMap =
                  sourceShared.toState.accountMap := by
              have hStateOk :
                  (.Ok yulChild childStore : Reference.State) =
                    .Ok
                      { sourceShared with
                        toMachineState :=
                          sourceShared.toMachineState.setHReturn
                            ByteArray.empty }
                      sourceStore := by
                simpa [stopState, sourceAfterArgs,
                  EvmYul.Yul.State.setMachineState] using hState
              injection hStateOk with hSharedEq _hStoreEq
              cases hSharedEq
              rfl
            have hSharedAfter :
                sharedAfter.toState.accountMap =
                  compilerAfterArgs.shared.toState.accountMap := by
              let iso : EVMState :=
                { toSharedState := compilerAfterArgs.shared,
                  pc := EvmYul.UInt256.ofNat 0,
                  stack := sourceValues,
                  execLength := 0 }
              have hStep :
                  Structured.Terminal.step .stop iso =
                    .ok
                      { iso with
                        toMachineState :=
                          (iso.toMachineState.setReturnData
                            ByteArray.empty).setHReturn ByteArray.empty } := by
                simp [iso, Structured.Terminal.step,
                  Assembly.Target.stepInstr, Assembly.HaltKind.toPrimOp,
                  Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
                  Assembly.PrimOp.toEVM]
                rfl
              have hSharedAfterEq :
                  sharedAfter =
                    { compilerAfterArgs.shared with
                      toMachineState :=
                        (compilerAfterArgs.shared.toMachineState.setReturnData
                          ByteArray.empty).setHReturn ByteArray.empty } := by
                simpa [Locals.Source.PrimitiveSemantics.structured, iso,
                  hStep, EvmYul.EVM.State.toSharedState] using hStruct.symm
              cases hSharedAfterEq
              rfl
            cases hCompiler
            refine ⟨yulChild, childStore, hOk, ?_⟩
            simpa [Locals.Source.State.withShared, hChild, hSharedAfter] using
              hBase
      case System op =>
        cases op <;> simp at hTerminal
        · -- RETURN
          cases hTerminal
          cases argFuel with
          | zero => simp [EvmYul.Yul.evalArgs] at hEvalArgs
          | succ fuel =>
              cases sourceValues with
              | nil =>
                  have hPrim :=
                    PrimSemantics.primCall_return_nil_eq fuel sourceAfterArgs
                  have hResult :=
                    Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                      (sourceFuel := fuel.succ) (source := source)
                      (sourceAfterArgs := sourceAfterArgs)
                      (yulPrim :=
                        (.System .RETURN : EvmYul.Operation .Yul))
                      (args := args) (rest := rest)
                      (codeOverride := codeOverride) (argValues := [])
                      (err := .InvalidArguments)
                      (sourceResult :=
                        .error (.YulHalt (.Ok yulChild childStore) value))
                      hEvalArgs hPrim hExecSeq
                  cases hResult
              | cons offset restValues =>
                  cases restValues with
                  | nil =>
                      have hPrim :=
                        PrimSemantics.primCall_return_singleton_eq fuel
                          sourceAfterArgs offset
                      have hResult :=
                        Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                          (sourceFuel := fuel.succ) (source := source)
                          (sourceAfterArgs := sourceAfterArgs)
                          (yulPrim :=
                            (.System .RETURN : EvmYul.Operation .Yul))
                          (args := args) (rest := rest)
                          (codeOverride := codeOverride)
                          (argValues := [offset])
                          (err := .InvalidArguments)
                          (sourceResult :=
                            .error
                              (.YulHalt (.Ok yulChild childStore) value))
                          hEvalArgs hPrim hExecSeq
                      cases hResult
                  | cons size more =>
                      cases more with
                      | nil =>
                          have hPrimEq :
                              EvmYul.Yul.primCall fuel.succ sourceAfterArgs
                                  ((.System .RETURN :
                                    EvmYul.Operation .Yul)) [offset, size] =
                                .error
                                  (.YulHalt
                                    (sourceAfterArgs.setMachineState
                                      (sourceAfterArgs.toMachineState.evmReturn
                                        offset size))
                                    ((Option.none : Option Word).getD
                                      ⟨1⟩)) := by
                            simp [EvmYul.Yul.primCall]
                            have hStep :
                                EvmYul.step
                                    ((.System .RETURN :
                                      EvmYul.Operation .Yul)) none =
                                  (fun yulState lits =>
                                    match
                                      EvmYul.Yul.binaryMachineStateOp
                                        EvmYul.MachineState.evmReturn
                                        yulState lits with
                                    | .error e => .error e
                                    | .ok (s, v) =>
                                        .error
                                          (EvmYul.Yul.Exception.YulHalt s
                                            (v.getD ⟨1⟩))) := by
                              rfl
                            rw [hStep]
                            rfl
                          have hResult :=
                            Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                              (sourceFuel := fuel.succ) (source := source)
                              (sourceAfterArgs := sourceAfterArgs)
                              (yulPrim :=
                                (.System .RETURN :
                                  EvmYul.Operation .Yul))
                              (args := args) (rest := rest)
                              (codeOverride := codeOverride)
                              (argValues := [offset, size])
                              (err :=
                                .YulHalt
                                  (sourceAfterArgs.setMachineState
                                    (sourceAfterArgs.toMachineState.evmReturn
                                      offset size))
                                  ((Option.none : Option Word).getD ⟨1⟩))
                              (sourceResult :=
                                .error
                                  (.YulHalt (.Ok yulChild childStore) value))
                              hEvalArgs hPrimEq hExecSeq
                          injection hResult with hErr
                          injection hErr with hState _hValue
                          have hChild :
                              yulChild.toState.accountMap =
                                sourceShared.toState.accountMap := by
                            have hStateOk :
                                (.Ok yulChild childStore :
                                  Reference.State) =
                                  .Ok
                                    { sourceShared with
                                      toMachineState :=
                                        sourceShared.toMachineState.evmReturn
                                          offset size }
                                    sourceStore := by
                              simpa [sourceAfterArgs,
                                EvmYul.Yul.State.setMachineState] using
                                hState
                            injection hStateOk with hSharedEq _hStoreEq
                            cases hSharedEq
                            rfl
                          have hSharedAfter :
                              sharedAfter.toState.accountMap =
                                compilerAfterArgs.shared.toState.accountMap := by
                            have hSharedAfterOk :
                                (Except.ok sharedAfter :
                                  Except EVMException
                                    (EvmYul.SharedState .EVM)) =
                                  .ok
                                    { compilerAfterArgs.shared with
                                      toMachineState :=
                                        compilerAfterArgs.shared.toMachineState.evmReturn
                                          offset size } := by
                              simpa [Locals.Source.PrimitiveSemantics.structured,
                                Structured.Terminal.step,
                                Assembly.Target.stepInstr,
                                Assembly.PrimOp.step,
                                Assembly.PrimOp.continuingStep?,
                                Assembly.HaltKind.toPrimOp,
                                Assembly.PrimOp.toEVM,
                                Locals.SourceLowering.PrimitiveSemantics.evm_step_return_eq_binaryMachineStateOp,
                                EvmYul.EVM.binaryMachineStateOp,
                                EvmYul.Stack.pop2,
                                EvmYul.EVM.State.replaceStackAndIncrPC,
                                EvmYul.EVM.State.incrPC,
                                EvmYul.EVM.State.toSharedState,
                                Id.run] using hStruct.symm
                            injection hSharedAfterOk with hSharedAfterEq
                            cases hSharedAfterEq
                            rfl
                          cases hCompiler
                          refine ⟨yulChild, childStore, hOk, ?_⟩
                          simpa [Locals.Source.State.withShared, hChild,
                            hSharedAfter] using hBase
                      | cons extra extras =>
                          have hPrim :=
                            PrimSemantics.primCall_return_cons_cons_cons_eq
                              fuel sourceAfterArgs offset size extra extras
                          have hResult :=
                            Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                              (sourceFuel := fuel.succ) (source := source)
                              (sourceAfterArgs := sourceAfterArgs)
                              (yulPrim :=
                                (.System .RETURN :
                                  EvmYul.Operation .Yul))
                              (args := args) (rest := rest)
                              (codeOverride := codeOverride)
                              (argValues := offset :: size :: extra :: extras)
                              (err := .InvalidArguments)
                              (sourceResult :=
                                .error
                                  (.YulHalt (.Ok yulChild childStore) value))
                              hEvalArgs hPrim hExecSeq
                          cases hResult
        · -- REVERT
          cases hTerminal
          exact False.elim (hNonRevert rfl)
        · -- SELFDESTRUCT
          cases hTerminal
          cases argFuel with
          | zero => simp [EvmYul.Yul.evalArgs] at hEvalArgs
          | succ fuel =>
              by_cases hStatic : sourceAfterArgs.executionEnv.perm = false
              · have hPrim :=
                  PrimSemantics.primCall_selfdestruct_static_eq fuel
                    sourceAfterArgs sourceValues hStatic
                have hResult :=
                  Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                    (sourceFuel := fuel.succ) (source := source)
                    (sourceAfterArgs := sourceAfterArgs)
                    (yulPrim :=
                      (.System .SELFDESTRUCT : EvmYul.Operation .Yul))
                    (args := args) (rest := rest)
                    (codeOverride := codeOverride) (argValues := sourceValues)
                    (err := .StaticModeViolation)
                    (sourceResult :=
                      .error (.YulHalt (.Ok yulChild childStore) value))
                    hEvalArgs hPrim hExecSeq
                cases hResult
              · cases sourceValues with
                | nil =>
                    have hPrim :=
                      PrimSemantics.primCall_selfdestruct_nil_eq fuel
                        sourceAfterArgs hStatic
                    have hResult :=
                      Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                        (sourceFuel := fuel.succ) (source := source)
                        (sourceAfterArgs := sourceAfterArgs)
                        (yulPrim :=
                          (.System .SELFDESTRUCT :
                            EvmYul.Operation .Yul))
                        (args := args) (rest := rest)
                        (codeOverride := codeOverride) (argValues := [])
                        (err := .InvalidArguments)
                        (sourceResult :=
                          .error (.YulHalt (.Ok yulChild childStore) value))
                        hEvalArgs hPrim hExecSeq
                    cases hResult
                | cons recipient more =>
                    cases more with
                    | nil =>
                        have hPrim :
                            EvmYul.Yul.primCall fuel.succ sourceAfterArgs
                                ((.System .SELFDESTRUCT :
                                  EvmYul.Operation .Yul))
                                [recipient] =
                              .error
                                (.YulHalt
                                  (PrimSemantics.selfdestructState
                                    sourceAfterArgs recipient)
                                  (EvmYul.UInt256.ofNat 0)) := by
                          simp [EvmYul.Yul.primCall, hStatic,
                            PrimSemantics.step_selfdestruct_lit_eq]
                        have hResult :=
                          Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                            (sourceFuel := fuel.succ) (source := source)
                            (sourceAfterArgs := sourceAfterArgs)
                            (yulPrim :=
                              (.System .SELFDESTRUCT :
                                EvmYul.Operation .Yul))
                            (args := args) (rest := rest)
                            (codeOverride := codeOverride)
                            (argValues := [recipient])
                            (err :=
                              .YulHalt
                                (PrimSemantics.selfdestructState
                                  sourceAfterArgs recipient)
                                (EvmYul.UInt256.ofNat 0))
                            (sourceResult :=
                              .error
                                (.YulHalt (.Ok yulChild childStore) value))
                            hEvalArgs hPrim hExecSeq
                        injection hResult with hErr
                        injection hErr with hState _hValue
                        have hChild :
                            yulChild.toState.accountMap =
                              (EvmYul.selfdestructAccountMap
                                sourceShared.toState.accountMap
                                sourceShared.executionEnv.codeOwner
                                (EvmYul.AccountAddress.ofUInt256 recipient)
                                (sourceShared.toState.createdAccounts.contains
                                  sourceShared.executionEnv.codeOwner)) := by
                          have hStateOk :
                              (.Ok yulChild childStore : Reference.State) =
                                PrimSemantics.selfdestructState
                                  sourceAfterArgs recipient := by
                            exact hState
                          simpa [PrimSemantics.selfdestructState,
                            EvmYul.Yul.selfdestructState, sourceAfterArgs,
                            EvmYul.Yul.State.setState,
                            EvmYul.Yul.State.setMachineState] using
                            congrArg
                              (fun state : Reference.State =>
                                state.toState.accountMap)
                              hStateOk
                        have hSharedAfter :
                            sharedAfter.toState.accountMap =
                              (EvmYul.selfdestructAccountMap
                                compilerAfterArgs.shared.toState.accountMap
                                compilerAfterArgs.shared.executionEnv.codeOwner
                                (EvmYul.AccountAddress.ofUInt256 recipient)
                                (compilerAfterArgs.shared.toState.createdAccounts.contains
                                  compilerAfterArgs.shared.executionEnv.codeOwner)) := by
                          let iso : EVMState :=
                            { toSharedState := compilerAfterArgs.shared,
                              pc := EvmYul.UInt256.ofNat 0,
                              stack := [recipient],
                              execLength := 0 }
                          have hStep :
                              Structured.Terminal.step .selfdestruct iso =
                                .ok
                                  (Locals.SourceLowering.PrimitiveSemantics.selfdestructTerminalState
                                    iso recipient []) := by
                            apply
                              Locals.SourceLowering.PrimitiveSemantics.structured_terminal_step_selfdestruct_of_stack
                            simp [iso]
                          have hSharedAfterEq :
                              sharedAfter =
                                (Locals.SourceLowering.PrimitiveSemantics.selfdestructTerminalState
                                  iso recipient []).toSharedState := by
                            simpa [Locals.Source.PrimitiveSemantics.structured,
                              iso, hStep] using hStruct.symm
                          cases hSharedAfterEq
                          simp [Locals.SourceLowering.PrimitiveSemantics.selfdestructTerminalState,
                            EvmYul.EVM.selfdestructState,
                            EvmYul.EVM.State.replaceStackAndIncrPC,
                            EvmYul.EVM.State.incrPC, iso]
                        cases hCompiler
                        refine ⟨yulChild, childStore, hOk, ?_⟩
                        simpa [Locals.Source.State.withShared, hChild,
                          hSharedAfter] using
                            sharedStateRel_selfdestructAccountMapRel hShared
                              recipient
                    | cons extra extras =>
                        have hPrim :=
                          PrimSemantics.primCall_selfdestruct_cons_cons_eq
                            fuel sourceAfterArgs recipient extra extras
                            hStatic
                        have hResult :=
                          Reference.SourceBridgeFacts.execSeq_expr_prim_call_error_of_evalArgs_ok_primCall_error
                            (sourceFuel := fuel.succ) (source := source)
                            (sourceAfterArgs := sourceAfterArgs)
                            (yulPrim :=
                              (.System .SELFDESTRUCT :
                                EvmYul.Operation .Yul))
                            (args := args) (rest := rest)
                            (codeOverride := codeOverride)
                            (argValues := recipient :: extra :: extras)
                            (err := .InvalidArguments)
                            (sourceResult :=
                              .error
                                (.YulHalt (.Ok yulChild childStore) value))
                            hEvalArgs hPrim hExecSeq
                        cases hResult

theorem canonicalRevertRel_output {revertState : Reference.State}
    {compiler : Objects.Source.State}
    (hRel :
      Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
        config revertState compiler) :
    resultOutput (.revert revertState) =
      sharedHaltOutput .revert compiler.shared := by
  rcases
    Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel_ok_shape
      hRel with ⟨shared, store, hOk⟩
  have hRel' :
      Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
        config (.Ok shared store) compiler := by
    simpa [hOk] using hRel
  have hShared :=
    Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel_shared
      hRel'
  simpa [resultOutput, sharedHaltOutput, hOk] using hShared.machine.H_return

theorem wholeProgramOutcomeRel_regular_output
    {compiler : Objects.Source.State} {targetOutcome : Assembly.StepResult}
    (hWhole : SourceLowered.WholeProgramOutcomeRel
      (Functions.Source.Outcome.regular compiler) targetOutcome) :
    Assembly.GasAware.StepResult.output targetOutcome = ByteArray.empty := by
  rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.Source.Outcome.regular, Locals.Source.Outcome.regular,
          Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
      cases targetOutcome <;>
        simp [Assembly.GasAware.StepResult.output,
          Structured.Preservation.WholeProgramOutcomeRel] at hStructured ⊢

theorem wholeProgramOutcomeRel_halt_output
    {kind : Assembly.HaltKind} {compiler : Objects.Source.State}
    {targetOutcome : Assembly.StepResult}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {initial : Assembly.EVMState}
    (hWhole : SourceLowered.WholeProgramOutcomeRel
      (Functions.Source.Outcome.halt kind compiler) targetOutcome)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target fuel initial
        targetOutcome) :
    Assembly.GasAware.StepResult.output targetOutcome =
      sharedHaltOutput kind compiler.shared := by
  rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
  cases direct with
  | mk directState directMode =>
      cases directMode <;>
        simp [Functions.Source.Outcome.halt, Locals.Source.Outcome.halt,
          Functions.SourceDirect.BlockScopedOutcomeRel,
          Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
      rename_i directKind
      rcases hSourceDirect with ⟨hKind, hShared⟩
      subst hKind
      cases targetOutcome with
      | running state =>
          simp [Structured.Preservation.WholeProgramOutcomeRel] at hStructured
      | halted halt =>
          simp [Structured.Preservation.WholeProgramOutcomeRel] at hStructured
          rcases hStructured with ⟨hKind', tokens, hFrame⟩
          subst hKind'
          have hOutput :=
            Assembly.Preservation.BlockTraceResult.halted_output hTrace
          have hHReturn :
              halt.state.toMachineState.H_return =
                compiler.shared.toMachineState.H_return := by
            rcases hFrame with ⟨_hStack, hData⟩
            have hState :=
              congrArg
                (fun state : Assembly.EVMState =>
                  state.toMachineState.H_return)
                hData
            simp [Structured.Preservation.eraseControl, Assembly.eraseGas]
              at hState
            have hSharedH :
                compiler.shared.toMachineState.H_return =
                  directState.evm.toMachineState.H_return := by
              simpa using
                congrArg (fun shared => shared.toMachineState.H_return)
                  hShared
            exact hState.trans hSharedH.symm
          cases hKind : halt.kind <;>
            simp [Assembly.GasAware.StepResult.output,
              Assembly.HaltKind.output, sharedHaltOutput, hOutput, hHReturn,
              hKind]

theorem dispatcherOutcomeRel_output
    {program : Program} {referenceInitial : Reference.State}
    {referenceResult : Reference.Result}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {fuel : Nat} {initial : Assembly.EVMState}
    (hDispatcher :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel config
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          config)
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          config)
        program referenceInitial referenceResult sourceOutcome)
    (hWhole : SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hTrace :
      Assembly.Preservation.BlockTraceResult asm target fuel initial
        targetOutcome) :
    resultOutput referenceResult =
      Assembly.GasAware.StepResult.output targetOutcome := by
  cases referenceResult with
  | regular final =>
      rcases hDispatcher with ⟨bodyState, hFinal, hSourceOk⟩
      cases hSourceOk with
      | regular hRel =>
          exact (wholeProgramOutcomeRel_regular_output hWhole).symm
      | brk hRel =>
          rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
          cases direct with
          | mk directState directMode =>
              cases directMode <;>
                simp [Functions.Source.Outcome.brk,
                  Locals.Source.Outcome.brk,
                  Functions.SourceDirect.BlockScopedOutcomeRel,
                  Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
              cases targetOutcome <;>
                simp [Structured.Preservation.WholeProgramOutcomeRel]
                  at hStructured
      | cont hRel =>
          rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
          cases direct with
          | mk directState directMode =>
              cases directMode <;>
                simp [Functions.Source.Outcome.cont,
                  Locals.Source.Outcome.cont,
                  Functions.SourceDirect.BlockScopedOutcomeRel,
                  Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
              cases targetOutcome <;>
                simp [Structured.Preservation.WholeProgramOutcomeRel]
                  at hStructured
      | leave hRel =>
          rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
          cases direct with
          | mk directState directMode =>
              cases directMode <;>
                simp [Functions.Source.Outcome.leave,
                  Locals.Source.Outcome.leave,
                  Functions.SourceDirect.BlockScopedOutcomeRel,
                  Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
              cases targetOutcome <;>
                simp [Structured.Preservation.WholeProgramOutcomeRel]
                  at hStructured
  | yulHalt haltState value =>
      rcases hDispatcher with ⟨kind, compiler, hTerminal, hSourceOutcome⟩
      subst hSourceOutcome
      calc
        resultOutput (.yulHalt haltState value)
            = sharedHaltOutput kind compiler.shared :=
          canonicalTerminalRel_output hTerminal
        _ = Assembly.GasAware.StepResult.output targetOutcome :=
          (wholeProgramOutcomeRel_halt_output hWhole hTrace).symm
  | revert revertState =>
      rcases hDispatcher with ⟨compiler, hRevert, hSourceOutcome⟩
      subst hSourceOutcome
      calc
        resultOutput (.revert revertState)
            = sharedHaltOutput .revert compiler.shared :=
          canonicalRevertRel_output hRevert
        _ = Assembly.GasAware.StepResult.output targetOutcome :=
          (wholeProgramOutcomeRel_halt_output hWhole hTrace).symm

theorem dispatcherOutcomeRel_success_accountMap
    {program : Program} {referenceInitial : Reference.State}
    {referenceResult : Reference.Result}
    {sourceOutcome : Objects.Source.Outcome}
    {targetOutcome : Assembly.StepResult}
    {evmFinal : Assembly.EVMState} {output : ByteArray}
    (hReferenceInitialOk :
      ∃ shared store, referenceInitial = .Ok shared store)
    (hDispatcher :
      Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel config
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          config)
        (Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          config)
        program referenceInitial referenceResult sourceOutcome)
    (hWhole : SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome)
    (hAgrees :
      Assembly.GasAware.XResultAgrees targetOutcome
        (.success evmFinal output)) :
    successfulResultAccountMapRel referenceResult evmFinal := by
  rcases hReferenceInitialOk with ⟨referenceShared, referenceStore, hInitial⟩
  subst hInitial
  have hEVMAccount :
      evmFinal.accountMap =
        (Assembly.GasAware.StepResult.finalState targetOutcome).accountMap :=
    Assembly.GasAware.XResultAgrees.success_accountMap hAgrees
  cases referenceResult with
  | regular final =>
      rcases hDispatcher with ⟨bodyState, hFinal, hSourceOk⟩
      cases hSourceOk with
      | regular hRel =>
          rcases sourceStateRel_accountMapRel hRel with
            ⟨bodyShared, bodyStore, hBody, hAccountMap⟩
          have hFinalAccount :
              final.toState.accountMap = bodyShared.toState.accountMap := by
            simp [hFinal, hBody, Program.installContract,
              EvmYul.Yul.State.setStore, EvmYul.Yul.State.overwrite?,
              EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.toState]
          have hTargetAccount :=
            wholeProgramOutcomeRel_regular_accountMap hWhole
          have hEVMCompiler := hEVMAccount.trans hTargetAccount
          simpa [successfulResultAccountMapRel, hFinalAccount, hEVMCompiler]
            using hAccountMap
      | brk hRel =>
          rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
          cases direct with
          | mk directState directMode =>
              cases directMode <;>
                simp [Functions.Source.Outcome.brk,
                  Locals.Source.Outcome.brk,
                  Functions.SourceDirect.BlockScopedOutcomeRel,
                  Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
              cases targetOutcome <;>
                simp [Structured.Preservation.WholeProgramOutcomeRel]
                  at hStructured
      | cont hRel =>
          rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
          cases direct with
          | mk directState directMode =>
              cases directMode <;>
                simp [Functions.Source.Outcome.cont,
                  Locals.Source.Outcome.cont,
                  Functions.SourceDirect.BlockScopedOutcomeRel,
                  Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
              cases targetOutcome <;>
                simp [Structured.Preservation.WholeProgramOutcomeRel]
                  at hStructured
      | leave hRel =>
          rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
          cases direct with
          | mk directState directMode =>
              cases directMode <;>
                simp [Functions.Source.Outcome.leave,
                  Locals.Source.Outcome.leave,
                  Functions.SourceDirect.BlockScopedOutcomeRel,
                  Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
              cases targetOutcome <;>
                simp [Structured.Preservation.WholeProgramOutcomeRel]
                  at hStructured
  | yulHalt haltState value =>
      rcases hDispatcher with ⟨kind, compiler, hTerminal, hSourceOutcome⟩
      subst hSourceOutcome
      rcases canonicalTerminalRel_accountMap hTerminal with
        ⟨haltShared, haltStore, hHaltState, hAccountMap⟩
      have hTargetAccount :=
        wholeProgramOutcomeRel_halt_accountMap hWhole
      have hEVMCompiler :
          evmFinal.accountMap = compiler.shared.toState.accountMap :=
        hEVMAccount.trans hTargetAccount
      simpa [successfulResultAccountMapRel, hHaltState, hEVMCompiler]
        using hAccountMap
  | revert revertState =>
      rcases hDispatcher with ⟨compiler, hRevert, hSourceOutcome⟩
      subst hSourceOutcome
      rcases hWhole with ⟨direct, hSourceDirect, hStructured⟩
      cases direct with
      | mk directState directMode =>
          cases directMode <;>
            simp [Functions.Source.Outcome.halt, Locals.Source.Outcome.halt,
              Functions.SourceDirect.BlockScopedOutcomeRel,
              Functions.SourceDirect.StmtOutcomeRel] at hSourceDirect
          rename_i directKind
          rcases hSourceDirect with ⟨hKind, hShared⟩
          subst hKind
          cases targetOutcome with
          | running state =>
              simp [Structured.Preservation.WholeProgramOutcomeRel]
                at hStructured
          | halted halt =>
              simp [Structured.Preservation.WholeProgramOutcomeRel]
                at hStructured
              rcases hStructured with ⟨hKind', tokens, hFrame⟩
              exact hAgrees.1 hKind'.symm

end ConcreteStateRel
end Yul
end EvmCompiler
