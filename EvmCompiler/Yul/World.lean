import EvmCompiler.Yul.RecursiveBridgeSupport
import Batteries.Data.RBMap.Lemmas

namespace EvmCompiler
namespace Yul

namespace World

/--
Concrete code-image relation for external worlds.

The relation is intentionally below the current feature-coverage checker: an
external account may contain CALL-family code while we are proving the
CALL-family bridge.  It still requires checked lowering, frame resources, and
bytecode bridge facts for the emitted EVM code.
-/
noncomputable def CompiledCodeRel (contract : AstContract)
    (bytes : ByteArray) : Prop :=
  (∃ (program : Program) (asm : Assembly.Program)
      (target : Assembly.TargetProgram),
    program.contract = contract ∧
      Program.compileCheckedAssemblyTargetBytecodeResources? program =
        some (asm, target) ∧
      bytes = Assembly.Bytecode.encodeTarget target) ∨
    (contract = default ∧ bytes = default)

theorem CompiledCodeRel.of_checked
    {program : Program} {asm : Assembly.Program}
    {target : Assembly.TargetProgram}
    (hCompile :
      Program.compileCheckedAssemblyTargetBytecodeResources? program =
        some (asm, target)) :
    CompiledCodeRel program.contract
      (Assembly.Bytecode.encodeTarget target) := by
  exact Or.inl ⟨program, asm, target, rfl, hCompile, rfl⟩

theorem CompiledCodeRel.empty :
    CompiledCodeRel (default : AstContract) (default : ByteArray) := by
  exact Or.inr ⟨rfl, rfl⟩

theorem CompiledCodeRel.checked_or_empty
    {contract : AstContract} {bytes : ByteArray}
    (hCode : CompiledCodeRel contract bytes) :
    (∃ (program : Program) (asm : Assembly.Program)
        (target : Assembly.TargetProgram),
      program.contract = contract ∧
        Program.compileCheckedAssemblyTargetBytecodeResources? program =
          some (asm, target) ∧
        bytes = Assembly.Bytecode.encodeTarget target) ∨
      (contract = default ∧ bytes = default) :=
  hCode

noncomputable def codeImageRel : Reference.CodeImageRel :=
  CompiledCodeRel

structure CompiledAccountRel (yul : EvmYul.Account .Yul)
    (evm : EvmYul.Account .EVM) : Prop where
  nonce : yul.nonce = evm.nonce
  balance : yul.balance = evm.balance
  storage : yul.storage = evm.storage
  tstorage : yul.tstorage = evm.tstorage
  code : CompiledCodeRel yul.code evm.code

theorem CompiledAccountRel.codeRel
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm) :
    codeImageRel yul.code evm.code :=
  hAccount.code

theorem CompiledAccountRel.with_balance
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (balance : EvmYul.UInt256) :
    CompiledAccountRel
      { yul with balance := balance }
      { evm with balance := balance } := by
  exact
    { nonce := hAccount.nonce
      balance := rfl
      storage := hAccount.storage
      tstorage := hAccount.tstorage
      code := hAccount.code }

theorem CompiledAccountRel.update_storage
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (slot value : EvmYul.UInt256) :
    CompiledAccountRel
      (EvmYul.Account.updateStorage yul slot value)
      (EvmYul.Account.updateStorage evm slot value) := by
  unfold EvmYul.Account.updateStorage
  by_cases hZero : (value == default) = true
  · simp [hZero]
    exact
      { nonce := hAccount.nonce
        balance := hAccount.balance
        storage := by simp [hAccount.storage]
        tstorage := hAccount.tstorage
        code := hAccount.code }
  · simp [hZero]
    exact
      { nonce := hAccount.nonce
        balance := hAccount.balance
        storage := by simp [hAccount.storage]
        tstorage := hAccount.tstorage
        code := hAccount.code }

theorem CompiledAccountRel.update_transientStorage
    {yul : EvmYul.Account .Yul} {evm : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yul evm)
    (slot value : EvmYul.UInt256) :
    CompiledAccountRel
      (EvmYul.Account.updateTransientStorage yul slot value)
      (EvmYul.Account.updateTransientStorage evm slot value) := by
  unfold EvmYul.Account.updateTransientStorage
  by_cases hZero : (value == default) = true
  · simp [hZero]
    exact
      { nonce := hAccount.nonce
        balance := hAccount.balance
        storage := hAccount.storage
        tstorage := by simp [hAccount.tstorage]
        code := hAccount.code }
  · simp [hZero]
    exact
      { nonce := hAccount.nonce
        balance := hAccount.balance
        storage := hAccount.storage
        tstorage := by simp [hAccount.tstorage]
        code := hAccount.code }

theorem CompiledAccountRel.default_with_balance
    (balance : EvmYul.UInt256) :
    CompiledAccountRel
      { (default : EvmYul.Account .Yul) with balance := balance }
      { (default : EvmYul.Account .EVM) with balance := balance } := by
  exact
    { nonce := rfl
      balance := rfl
      storage := rfl
      tstorage := rfl
      code := CompiledCodeRel.empty }

inductive CompiledToExecuteRel :
    EvmYul.ToExecute .Yul → EvmYul.ToExecute .EVM → Prop
  | precompiled (addr : EvmYul.AccountAddress) :
      CompiledToExecuteRel
        (EvmYul.ToExecute.Precompiled addr)
        (EvmYul.ToExecute.Precompiled addr)
  | code {contract : AstContract} {bytes : ByteArray}
      (hCode : CompiledCodeRel contract bytes) :
      CompiledToExecuteRel
        (EvmYul.ToExecute.Code contract)
        (EvmYul.ToExecute.Code bytes)

structure CompiledAccountMapRel (yul : EvmYul.AccountMap .Yul)
    (evm : EvmYul.AccountMap .EVM) : Prop where
  yul_to_evm :
    ∀ addr yulAccount,
      yul.find? addr = some yulAccount →
        ∃ evmAccount,
          evm.find? addr = some evmAccount ∧
            CompiledAccountRel yulAccount evmAccount
  evm_to_yul :
    ∀ addr evmAccount,
      evm.find? addr = some evmAccount →
        ∃ yulAccount,
          yul.find? addr = some yulAccount ∧
            CompiledAccountRel yulAccount evmAccount

def accountMapRel : Reference.AccountMapRel :=
  CompiledAccountMapRel

theorem CompiledAccountMapRel.find_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {yulAccount : EvmYul.Account .Yul}
    (hFind : yul.find? addr = some yulAccount) :
    ∃ evmAccount,
      evm.find? addr = some evmAccount ∧
        CompiledAccountRel yulAccount evmAccount :=
  hWorld.yul_to_evm addr yulAccount hFind

theorem CompiledAccountMapRel.find_evm
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {evmAccount : EvmYul.Account .EVM}
    (hFind : evm.find? addr = some evmAccount) :
    ∃ yulAccount,
      yul.find? addr = some yulAccount ∧
        CompiledAccountRel yulAccount evmAccount :=
  hWorld.evm_to_yul addr evmAccount hFind

theorem CompiledAccountMapRel.not_find_yul_of_not_find_evm
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress}
    (hFind : evm.find? addr = none) :
    yul.find? addr = none := by
  cases hYul : yul.find? addr with
  | none => rfl
  | some yulAccount =>
      rcases hWorld.find_yul hYul with ⟨evmAccount, hEvm, _⟩
      simp [hFind] at hEvm

theorem CompiledAccountMapRel.not_find_evm_of_not_find_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress}
    (hFind : yul.find? addr = none) :
    evm.find? addr = none := by
  cases hEvm : evm.find? addr with
  | none => rfl
  | some evmAccount =>
      rcases hWorld.find_evm hEvm with ⟨yulAccount, hYul, _⟩
      simp [hFind] at hYul

theorem CompiledAccountMapRel.balance_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) :
    (yul.find? addr |>.elim ⟨0⟩ (·.balance)) =
      (evm.find? addr |>.elim ⟨0⟩ (·.balance)) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [hEvm]
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      simp [hEvm, hAccount.balance]

theorem CompiledAccountMapRel.storage_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (slot : EvmYul.UInt256) :
    (yul.find? addr |>.option ⟨0⟩
        (EvmYul.Account.lookupStorage (k := slot))) =
      (evm.find? addr |>.option ⟨0⟩
        (EvmYul.Account.lookupStorage (k := slot))) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      rw [hEvm]
      rfl
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      rw [hEvm]
      exact
        congrArg (fun storage =>
          Batteries.RBMap.findD storage slot (⟨0⟩ : EvmYul.UInt256))
          hAccount.storage

theorem CompiledAccountMapRel.transientStorage_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (slot : EvmYul.UInt256) :
    (yul.find? addr |>.option ⟨0⟩
        (EvmYul.Account.lookupTransientStorage (k := slot))) =
      (evm.find? addr |>.option ⟨0⟩
        (EvmYul.Account.lookupTransientStorage (k := slot))) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      rw [hEvm]
      rfl
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      rw [hEvm]
      exact
        congrArg (fun storage =>
          Batteries.RBMap.findD storage slot (⟨0⟩ : EvmYul.UInt256))
          hAccount.tstorage

theorem CompiledAccountMapRel.insert
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress)
    {yulAccount : EvmYul.Account .Yul} {evmAccount : EvmYul.Account .EVM}
    (hAccount : CompiledAccountRel yulAccount evmAccount) :
    CompiledAccountMapRel
      (yul.insert addr yulAccount)
      (evm.insert addr evmAccount) := by
  refine
    { yul_to_evm := ?_
      evm_to_yul := ?_ }
  · intro query foundYul hFind
    rw [Batteries.RBMap.find?_insert] at hFind ⊢
    split at hFind <;> rename_i hCmp
    · cases hFind
      exact ⟨evmAccount, by simp [hCmp], hAccount⟩
    · rcases hWorld.find_yul hFind with
        ⟨foundEvm, hFoundEvm, hFoundAccount⟩
      exact ⟨foundEvm, by simp [hCmp, hFoundEvm], hFoundAccount⟩
  · intro query foundEvm hFind
    rw [Batteries.RBMap.find?_insert] at hFind ⊢
    split at hFind <;> rename_i hCmp
    · cases hFind
      exact ⟨yulAccount, by simp [hCmp], hAccount⟩
    · rcases hWorld.find_evm hFind with
        ⟨foundYul, hFoundYul, hFoundAccount⟩
      exact ⟨foundYul, by simp [hCmp, hFoundYul], hFoundAccount⟩

theorem CompiledAccountMapRel.increaseBalance
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (amount : EvmYul.UInt256) :
    CompiledAccountMapRel
      (EvmYul.AccountMap.increaseBalance .Yul yul addr amount)
      (EvmYul.AccountMap.increaseBalance .EVM evm addr amount) := by
  unfold EvmYul.AccountMap.increaseBalance
  cases hYul : yul.find? addr with
  | none =>
      cases hEvm : evm.find? addr with
      | none =>
          exact hWorld.insert addr
            (CompiledAccountRel.default_with_balance amount)
      | some evmAccount =>
          rcases hWorld.find_evm hEvm with ⟨_, hYulFound, _⟩
          simp [hYul] at hYulFound
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvmFound, hAccount⟩
      cases hEvm : evm.find? addr with
      | none =>
          simp [hEvm] at hEvmFound
      | some evmAccount' =>
          have hSame : evmAccount = evmAccount' :=
            Option.some.inj (hEvmFound.symm.trans hEvm)
          subst evmAccount'
          have hIncreased :
              CompiledAccountRel
                { yulAccount with balance := yulAccount.balance + amount }
                { evmAccount with balance := evmAccount.balance + amount } := by
            rw [← hAccount.balance]
            exact hAccount.with_balance (yulAccount.balance + amount)
          exact hWorld.insert addr hIncreased

theorem CompiledAccountMapRel.updateStorage_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (slot value : EvmYul.UInt256) :
    CompiledAccountMapRel
      (match yul.find? addr with
      | none => yul
      | some account =>
          yul.insert addr (EvmYul.Account.updateStorage account slot value))
      (match evm.find? addr with
      | none => evm
      | some account =>
          evm.insert addr (EvmYul.Account.updateStorage account slot value)) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [hEvm, hWorld]
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      simp [hEvm]
      exact hWorld.insert addr (hAccount.update_storage slot value)

theorem CompiledAccountMapRel.updateTransientStorage_at
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) (slot value : EvmYul.UInt256) :
    CompiledAccountMapRel
      (match yul.find? addr with
      | none => yul
      | some account =>
          yul.insert addr
            (EvmYul.Account.updateTransientStorage account slot value))
      (match evm.find? addr with
      | none => evm
      | some account =>
          evm.insert addr
            (EvmYul.Account.updateTransientStorage account slot value)) := by
  cases hYul : yul.find? addr with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [hEvm, hWorld]
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvm, hAccount⟩
      simp [hEvm]
      exact hWorld.insert addr (hAccount.update_transientStorage slot value)

theorem CompiledAccountMapRel.decreaseBalance_of_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {amount : EvmYul.UInt256}
    {yulAfter : EvmYul.AccountMap .Yul}
    (hDecrease :
      EvmYul.AccountMap.decreaseBalance .Yul yul addr amount =
        some yulAfter) :
    ∃ evmAfter,
      EvmYul.AccountMap.decreaseBalance .EVM evm addr amount =
          some evmAfter ∧
        CompiledAccountMapRel yulAfter evmAfter := by
  unfold EvmYul.AccountMap.decreaseBalance at hDecrease ⊢
  cases hYul : yul.find? addr with
  | none =>
      simp [hYul] at hDecrease
  | some yulAccount =>
      rcases hWorld.find_yul hYul with
        ⟨evmAccount, hEvmFound, hAccount⟩
      simp [hYul] at hDecrease
      by_cases hTooSmall : yulAccount.balance < amount
      · simp [hTooSmall] at hDecrease
      · have hEvmEnough : ¬ evmAccount.balance < amount := by
          simpa [← hAccount.balance] using hTooSmall
        refine
          ⟨evm.insert addr
              { evmAccount with balance := evmAccount.balance - amount },
            ?_, ?_⟩
        · simp [hEvmFound, hEvmEnough]
        · simp [hTooSmall] at hDecrease
          subst yulAfter
          have hDecreased :
              CompiledAccountRel
                { yulAccount with balance := yulAccount.balance - amount }
                { evmAccount with balance := evmAccount.balance - amount } := by
            rw [← hAccount.balance]
            exact hAccount.with_balance (yulAccount.balance - amount)
          exact hWorld.insert addr hDecreased

theorem CompiledAccountMapRel.transferBalance_of_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {fromAddr toAddr : EvmYul.AccountAddress} {amount : EvmYul.UInt256}
    {yulAfter : EvmYul.AccountMap .Yul}
    (hTransfer :
      EvmYul.AccountMap.transferBalance .Yul yul fromAddr toAddr amount =
        some yulAfter) :
    ∃ evmAfter,
      EvmYul.AccountMap.transferBalance .EVM evm fromAddr toAddr amount =
          some evmAfter ∧
        CompiledAccountMapRel yulAfter evmAfter := by
  unfold EvmYul.AccountMap.transferBalance at hTransfer ⊢
  cases hYulDecrease :
      EvmYul.AccountMap.decreaseBalance .Yul yul fromAddr amount with
  | none =>
      simp [hYulDecrease] at hTransfer
  | some yulDecreased =>
      simp [hYulDecrease] at hTransfer
      subst yulAfter
      rcases hWorld.decreaseBalance_of_yul hYulDecrease with
        ⟨evmDecreased, hEvmDecrease, hDecreasedWorld⟩
      refine
        ⟨EvmYul.AccountMap.increaseBalance .EVM evmDecreased toAddr amount,
          ?_, ?_⟩
      · simp [hEvmDecrease]
      · exact hDecreasedWorld.increaseBalance toAddr amount

theorem CompiledAccountMapRel.selfbalance
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner) :
    EvmYul.State.selfbalance yul = EvmYul.State.selfbalance evm := by
  unfold EvmYul.State.selfbalance
  rw [hOwner]
  exact hWorld.balance_at evm.executionEnv.codeOwner

theorem CompiledAccountMapRel.balance
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {address : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap) :
    (EvmYul.State.balance yul address).2 =
      (EvmYul.State.balance evm address).2 := by
  simpa [EvmYul.State.balance] using
    hWorld.balance_at (EvmYul.AccountAddress.ofUInt256 address)

theorem CompiledAccountMapRel.sload
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner) :
    (EvmYul.State.sload yul slot).2 =
      (EvmYul.State.sload evm slot).2 := by
  unfold EvmYul.State.sload EvmYul.State.lookupAccount
  rw [hOwner]
  exact hWorld.storage_at evm.executionEnv.codeOwner slot

theorem CompiledAccountMapRel.sstore_accountMap
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot value : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (_hSigma : yul.σ₀ = evm.σ₀)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner)
    (_hSubstate : yul.substate = evm.substate) :
    CompiledAccountMapRel
      (EvmYul.State.sstore yul slot value).accountMap
      (EvmYul.State.sstore evm slot value).accountMap := by
  unfold EvmYul.State.sstore EvmYul.State.lookupAccount
    EvmYul.State.setAccount EvmYul.State.addAccessedStorageKey
  rw [hOwner]
  cases hYul : yul.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [Option.option, hYul, hEvm]
      exact hWorld
  | some yulAccount =>
      rcases hWorld.find_yul hYul with ⟨evmAccount, hEvm, hAccount⟩
      simp [Option.option, hYul, hEvm]
      exact hWorld.insert evm.executionEnv.codeOwner
        (hAccount.update_storage slot value)

theorem CompiledAccountMapRel.sstore_substate
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot value : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hSigma : yul.σ₀ = evm.σ₀)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner)
    (hSubstate : yul.substate = evm.substate) :
    (EvmYul.State.sstore yul slot value).substate =
      (EvmYul.State.sstore evm slot value).substate := by
  unfold EvmYul.State.sstore EvmYul.State.lookupAccount
    EvmYul.State.setAccount EvmYul.State.addAccessedStorageKey
  rw [hOwner]
  cases hYul : yul.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [Option.option, hYul, hEvm, hSubstate]
  | some yulAccount =>
      rcases hWorld.find_yul hYul with ⟨evmAccount, hEvm, hAccount⟩
      simp [Option.option, Batteries.RBMap.find!, hYul, hEvm, hSigma,
        hSubstate, hAccount.storage]

theorem CompiledAccountMapRel.tload
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner) :
    (EvmYul.State.tload yul slot).2 =
      (EvmYul.State.tload evm slot).2 := by
  unfold EvmYul.State.tload EvmYul.State.lookupAccount
  rw [hOwner]
  exact hWorld.transientStorage_at evm.executionEnv.codeOwner slot

theorem CompiledAccountMapRel.tstore_accountMap
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    {slot value : Word}
    (hWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hOwner : yul.executionEnv.codeOwner = evm.executionEnv.codeOwner) :
    CompiledAccountMapRel
      (EvmYul.State.tstore yul slot value).accountMap
      (EvmYul.State.tstore evm slot value).accountMap := by
  unfold EvmYul.State.tstore EvmYul.State.lookupAccount EvmYul.State.updateAccount
  rw [hOwner]
  cases hYul : yul.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
      have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
      simp [Option.option, hYul, hEvm]
      exact hWorld
  | some yulAccount =>
      rcases hWorld.find_yul hYul with ⟨evmAccount, hEvm, hAccount⟩
      simp [Option.option, hYul, hEvm]
      exact hWorld.insert evm.executionEnv.codeOwner
        (hAccount.update_transientStorage slot value)

noncomputable def stateRelConfig
    (varStackRel : Reference.VarStackRel)
    (terminalRel :
      Assembly.HaltKind → Word → Reference.State → EVMState → Prop)
    (revertRel : Reference.State → EVMState → Prop)
    (gasAvailableRel : Word → Word → Prop)
    (gasValueRel :
      ∀ {yul evm : EvmYul.MachineState},
        gasAvailableRel yul.gasAvailable evm.gasAvailable →
          EvmYul.MachineState.gas yul = EvmYul.MachineState.gas evm)
    (totalGasRel : Nat → Nat → Prop) :
    Reference.StateRelConfig where
  accountMapRel := accountMapRel
  selfbalanceRel := by
    intro yul evm hWorld hOwner
    exact hWorld.selfbalance hOwner
  balanceRel := by
    intro yul evm address hWorld
    exact hWorld.balance
  sloadRel := by
    intro yul evm slot hWorld hOwner
    exact hWorld.sload hOwner
  sstoreAccountMapRel := by
    intro yul evm slot value hWorld hSigma hOwner hSubstate
    exact hWorld.sstore_accountMap hSigma hOwner hSubstate
  sstoreSubstateRel := by
    intro yul evm slot value hWorld hSigma hOwner hSubstate
    exact hWorld.sstore_substate hSigma hOwner hSubstate
  tloadRel := by
    intro yul evm slot hWorld hOwner
    exact hWorld.tload hOwner
  tstoreAccountMapRel := by
    intro yul evm slot value hWorld hOwner
    exact hWorld.tstore_accountMap hOwner
  codeRel := codeImageRel
  varStackRel := varStackRel
  terminalRel := terminalRel
  revertRel := revertRel
  gasAvailableRel := gasAvailableRel
  gasValueRel := gasValueRel
  totalGasRel := totalGasRel

theorem CompiledAccountMapRel.toExecute_precompiled
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    {addr : EvmYul.AccountAddress}
    (hPrecompile : addr ∈ EvmYul.π) :
    CompiledToExecuteRel
      (EvmYul.toExecute .Yul yul addr)
      (EvmYul.toExecute .EVM evm addr) := by
  simp [EvmYul.toExecute, hPrecompile,
    CompiledToExecuteRel.precompiled]

theorem CompiledAccountMapRel.toExecute_code_of_find_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {yulAccount : EvmYul.Account .Yul}
    (hNotPrecompile : addr ∉ EvmYul.π)
    (hFind : yul.find? addr = some yulAccount) :
    ∃ evmAccount,
      evm.find? addr = some evmAccount ∧
        CompiledToExecuteRel
          (EvmYul.ToExecute.Code yulAccount.code)
          (EvmYul.toExecute .EVM evm addr) := by
  rcases hWorld.find_yul hFind with
    ⟨evmAccount, hEvmFind, hAccount⟩
  refine ⟨evmAccount, hEvmFind, ?_⟩
  simp [EvmYul.toExecute, hNotPrecompile, hEvmFind]
  exact CompiledToExecuteRel.code hAccount.code

end World

end Yul
end EvmCompiler
