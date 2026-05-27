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

theorem CompiledCodeRel.checkedBytecodeResources_or_empty
    {contract : AstContract} {bytes : ByteArray}
    (hCode : CompiledCodeRel contract bytes) :
    (∃ (program : Program) (asm : Assembly.Program)
        (target : Assembly.TargetProgram),
      program.contract = contract ∧
        Program.compileCheckedAssemblyTargetBytecodeResources? program =
          some (asm, target) ∧
        Program.compileCheckedAssemblyTargetBytecode? program =
          some (asm, target) ∧
        _root_.EvmCompiler.Yul.Program.RecursiveBridgeCompileResources program ∧
        Assembly.Bytecode.TargetFitsDecodeWindow target ∧
        Assembly.Bytecode.JumpdestCorrect target ∧
        bytes = Assembly.Bytecode.encodeTarget target) ∨
      (contract = default ∧ bytes = default) := by
  rcases hCode with hChecked | hEmpty
  · rcases hChecked with
      ⟨program, asm, target, hContract, hCompile, hBytes⟩
    rcases
        Program.compileCheckedAssemblyTargetBytecodeResources?_eq_some
          hCompile with
      ⟨hBytecode, hResources⟩
    rcases Program.compileCheckedAssemblyTargetBytecode?_eq_some
        hBytecode with
      ⟨_hTarget, hDecode, hJumpdest⟩
    exact Or.inl
      ⟨program, asm, target, hContract, hCompile, hBytecode,
        hResources, hDecode, hJumpdest, hBytes⟩
  · exact Or.inr hEmpty

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
  | precompiled (precompiled : EvmYul.PrecompiledContract) :
      CompiledToExecuteRel
        (EvmYul.ToExecute.Precompiled precompiled)
        (EvmYul.ToExecute.Precompiled precompiled)
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

theorem CompiledAccountMapRel.empty :
    CompiledAccountMapRel
      (∅ : EvmYul.AccountMap .Yul)
      (∅ : EvmYul.AccountMap .EVM) := by
  refine
    { yul_to_evm := ?_
      evm_to_yul := ?_ }
  · intro _addr _yulAccount hFind
    rcases Batteries.RBMap.find?_some_mem_toList hFind with
      ⟨_, hMem, _⟩
    simp at hMem
  · intro _addr _evmAccount hFind
    rcases Batteries.RBMap.find?_some_mem_toList hFind with
      ⟨_, hMem, _⟩
    simp at hMem

theorem accountMap_isEmpty_false_of_find?
    {τ : EvmYul.OperationType}
    {accountMap : EvmYul.AccountMap τ}
    {addr : EvmYul.AccountAddress} {account : EvmYul.Account τ}
    (hFind : accountMap.find? addr = some account) :
    accountMap.isEmpty = false := by
  cases hEmpty : accountMap.isEmpty
  · rfl
  · have hListEmpty : accountMap.toList = [] := by
      simpa [Batteries.RBMap.isEmpty] using
        (Batteries.RBSet.isEmpty_iff_toList_eq_nil
          (t := (accountMap : Batteries.RBSet _ _))).mp hEmpty
    rcases Batteries.RBMap.find?_some_mem_toList hFind with
      ⟨_, hMem, _⟩
    simp [hListEmpty] at hMem

theorem accountMap_exists_find?_of_isEmpty_false
    {τ : EvmYul.OperationType}
    {accountMap : EvmYul.AccountMap τ}
    (hEmpty : accountMap.isEmpty = false) :
    ∃ addr account, accountMap.find? addr = some account := by
  have hListNe : accountMap.toList ≠ [] := by
    intro hNil
    have hEmptyTrue : accountMap.isEmpty = true := by
      simpa [Batteries.RBMap.isEmpty] using
        (Batteries.RBSet.isEmpty_iff_toList_eq_nil
          (t := (accountMap : Batteries.RBSet _ _))).mpr hNil
    simp [hEmpty] at hEmptyTrue
  cases hList : accountMap.toList with
  | nil => exact False.elim (hListNe hList)
  | cons entry _tail =>
      rcases entry with ⟨addr, account⟩
      refine ⟨addr, account, ?_⟩
      rw [Batteries.RBMap.find?_some]
      exact ⟨addr, by simp [hList], by simp⟩

theorem CompiledAccountMapRel.isEmpty_eq
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm) :
    yul.isEmpty = evm.isEmpty := by
  cases hYul : yul.isEmpty
  · cases hEvm : evm.isEmpty
    · rfl
    · rcases accountMap_exists_find?_of_isEmpty_false hYul with
        ⟨addr, yulAccount, hFindYul⟩
      rcases hWorld.find_yul hFindYul with
        ⟨evmAccount, hFindEvm, _hAccount⟩
      have hEvmFalse :=
        accountMap_isEmpty_false_of_find? hFindEvm
      simp [hEvm] at hEvmFalse
  · cases hEvm : evm.isEmpty
    · rcases accountMap_exists_find?_of_isEmpty_false hEvm with
        ⟨addr, evmAccount, hFindEvm⟩
      rcases hWorld.find_evm hFindEvm with
        ⟨yulAccount, hFindYul, _hAccount⟩
      have hYulFalse :=
        accountMap_isEmpty_false_of_find? hFindYul
      simp [hYul] at hYulFalse
    · rfl

theorem CompiledAccountMapRel.if_empty_parent
    {yulParent yulChild : EvmYul.AccountMap .Yul}
    {evmParent evmChild : EvmYul.AccountMap .EVM}
    (hParent : CompiledAccountMapRel yulParent evmParent)
    (hChild : CompiledAccountMapRel yulChild evmChild)
    (hEmpty : yulChild.isEmpty = evmChild.isEmpty) :
    CompiledAccountMapRel
      (if yulChild.isEmpty then
        yulParent
      else
        yulChild)
      (if evmChild.isEmpty then
        evmParent
      else
        evmChild) := by
  cases hEvm : evmChild.isEmpty
  · have hYul : yulChild.isEmpty = false := by
      simpa [hEvm] using hEmpty
    simp [hYul]
    exact hChild
  · have hYul : yulChild.isEmpty = true := by
      simpa [hEvm] using hEmpty
    simp [hYul]
    exact hParent

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

theorem accountAddress_eq_of_compare_eq {a b : EvmYul.AccountAddress}
    (h : compare a b = Ordering.eq) : a = b := by
  apply Fin.ext
  change compare a.val b.val = Ordering.eq at h
  exact compare_eq_iff_eq.1 h

theorem CompiledAccountMapRel.insert_insert_distinct_comm
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {a b : EvmYul.AccountAddress}
    (hAB : compare a b ≠ Ordering.eq)
    (hBA : compare b a ≠ Ordering.eq)
    {yulA : EvmYul.Account .Yul} {evmA : EvmYul.Account .EVM}
    {yulB : EvmYul.Account .Yul} {evmB : EvmYul.Account .EVM}
    (hA : CompiledAccountRel yulA evmA)
    (hB : CompiledAccountRel yulB evmB) :
    CompiledAccountMapRel
      ((yul.insert a yulA).insert b yulB)
      ((evm.insert b evmB).insert a evmA) := by
  refine
    { yul_to_evm := ?_
      evm_to_yul := ?_ }
  · intro query foundYul hFind
    rw [Batteries.RBMap.find?_insert] at hFind
    split at hFind <;> rename_i hQueryB
    · have hQueryEq : query = b := accountAddress_eq_of_compare_eq hQueryB
      subst query
      cases hFind
      refine ⟨evmB, ?_, hB⟩
      rw [Batteries.RBMap.find?_insert]
      simp [hBA, Batteries.RBMap.find?_insert]
    · rw [Batteries.RBMap.find?_insert] at hFind
      split at hFind <;> rename_i hQueryA
      · have hQueryEq : query = a := accountAddress_eq_of_compare_eq hQueryA
        subst query
        cases hFind
        refine ⟨evmA, ?_, hA⟩
        rw [Batteries.RBMap.find?_insert]
        simp
      · rcases hWorld.find_yul hFind with
          ⟨foundEvm, hFoundEvm, hFoundAccount⟩
        refine ⟨foundEvm, ?_, hFoundAccount⟩
        rw [Batteries.RBMap.find?_insert]
        simp [hQueryA, Batteries.RBMap.find?_insert, hQueryB, hFoundEvm]
  · intro query foundEvm hFind
    rw [Batteries.RBMap.find?_insert] at hFind
    split at hFind <;> rename_i hQueryA
    · have hQueryEq : query = a := accountAddress_eq_of_compare_eq hQueryA
      subst query
      cases hFind
      refine ⟨yulA, ?_, hA⟩
      rw [Batteries.RBMap.find?_insert]
      simp [hAB, Batteries.RBMap.find?_insert]
    · rw [Batteries.RBMap.find?_insert] at hFind
      split at hFind <;> rename_i hQueryB
      · have hQueryEq : query = b := accountAddress_eq_of_compare_eq hQueryB
        subst query
        cases hFind
        refine ⟨yulB, ?_, hB⟩
        rw [Batteries.RBMap.find?_insert]
        simp
      · rcases hWorld.find_evm hFind with
          ⟨foundYul, hFoundYul, hFoundAccount⟩
        refine ⟨foundYul, ?_, hFoundAccount⟩
        rw [Batteries.RBMap.find?_insert]
        simp [hQueryB, Batteries.RBMap.find?_insert, hQueryA, hFoundYul]

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

/--
Account-map part of the EVM `Θ` CALL prelude.

This deliberately mirrors EVM order instead of `AccountMap.transferBalance`:
the recipient is credited/materialized first, missing recipients are
materialized only for nonzero value, and the sender is debited afterward.
-/
abbrev callRecipientCredit {τ : EvmYul.OperationType}
    (accountMap : EvmYul.AccountMap τ)
    (recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) : EvmYul.AccountMap τ :=
  EvmYul.Yul.callRecipientCredit accountMap recipient value

abbrev callSourceDebit {τ : EvmYul.OperationType}
    (accountMap : EvmYul.AccountMap τ)
    (source : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) : EvmYul.AccountMap τ :=
  EvmYul.Yul.callSourceDebit accountMap source value

abbrev callTransferUnchecked {τ : EvmYul.OperationType}
    (accountMap : EvmYul.AccountMap τ)
    (source recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) : EvmYul.AccountMap τ :=
  EvmYul.Yul.callTransferUnchecked accountMap source recipient value

def evmCallTransfer (evm : EvmYul.AccountMap .EVM)
    (source recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) : EvmYul.AccountMap .EVM :=
  callTransferUnchecked evm source recipient value

theorem CompiledAccountMapRel.callTransferUnchecked_preserve
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (source recipient : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) :
    CompiledAccountMapRel
      (callTransferUnchecked yul source recipient value)
      (callTransferUnchecked evm source recipient value) := by
  have hRecipientIncreased :
      CompiledAccountMapRel
        (callRecipientCredit yul recipient value)
        (callRecipientCredit evm recipient value) := by
    unfold callRecipientCredit EvmYul.Yul.callRecipientCredit
    cases hRecipientYul : yul.find? recipient with
    | none =>
        have hRecipientEvm :=
          hWorld.not_find_evm_of_not_find_yul hRecipientYul
        by_cases hValue :
            (value != (⟨0⟩ : EvmYul.UInt256)) = true
        · simp [hRecipientEvm, hValue]
          exact hWorld.insert recipient
            (CompiledAccountRel.default_with_balance value)
        · simp [hRecipientEvm, hValue]
          exact hWorld
    | some yulRecipientAccount =>
        rcases hWorld.find_yul hRecipientYul with
          ⟨evmRecipientAccount, hRecipientEvm, hRecipientRel⟩
        simp [hRecipientEvm]
        have hIncreased :
            CompiledAccountRel
              { yulRecipientAccount with
                balance := yulRecipientAccount.balance + value }
              { evmRecipientAccount with
                balance := evmRecipientAccount.balance + value } := by
          rw [← hRecipientRel.balance]
          exact hRecipientRel.with_balance
            (yulRecipientAccount.balance + value)
        exact hWorld.insert recipient hIncreased
  change
    CompiledAccountMapRel
      (callSourceDebit (callRecipientCredit yul recipient value) source value)
      (callSourceDebit (callRecipientCredit evm recipient value) source value)
  unfold callSourceDebit EvmYul.Yul.callSourceDebit
  cases hSourceYul :
      (callRecipientCredit yul recipient value).find? source with
  | none =>
      have hSourceEvm :=
        hRecipientIncreased.not_find_evm_of_not_find_yul hSourceYul
      rw [hSourceEvm]
      exact hRecipientIncreased
  | some yulSourceAccount =>
      rcases hRecipientIncreased.find_yul hSourceYul with
        ⟨evmSourceAccount, hSourceEvm, hSourceRel⟩
      rw [hSourceEvm]
      have hDecreased :
          CompiledAccountRel
            { yulSourceAccount with
              balance := yulSourceAccount.balance - value }
            { evmSourceAccount with
              balance := evmSourceAccount.balance - value } := by
        rw [← hSourceRel.balance]
        exact hSourceRel.with_balance
          (yulSourceAccount.balance - value)
      exact hRecipientIncreased.insert source hDecreased

theorem CompiledAccountMapRel.callTransferAccountMap?_of_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    {yulAfter : EvmYul.AccountMap .Yul}
    (hTransfer :
      EvmYul.Yul.callTransferAccountMap? yul source recipient value =
        some yulAfter) :
    CompiledAccountMapRel yulAfter
      (evmCallTransfer evm source recipient value) := by
  by_cases hEnough :
      value ≤ (yul.find? source |>.option ⟨0⟩ (·.balance))
  · have hUnchecked :
        EvmYul.Yul.callTransferAccountMap? yul source recipient value =
          some (World.callTransferUnchecked yul source recipient value) := by
      simp [EvmYul.Yul.callTransferAccountMap?, hEnough,
        World.callTransferUnchecked]
    rw [hTransfer] at hUnchecked
    cases hUnchecked
    simpa [evmCallTransfer] using
      hWorld.callTransferUnchecked_preserve source recipient value
  · simp [EvmYul.Yul.callTransferAccountMap?, hEnough] at hTransfer

theorem CompiledAccountMapRel.callTransferEnough_iff
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (source : EvmYul.AccountAddress)
    (value : EvmYul.UInt256) :
    (value ≤ (yul.find? source |>.option ⟨0⟩ (·.balance))) ↔
      value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance)) := by
  have hBalance :
      (yul.find? source |>.option ⟨0⟩ (·.balance)) =
        (evm.find? source |>.option ⟨0⟩ (·.balance)) := by
    cases hYul : yul.find? source with
    | none =>
        have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
        simp [Option.option, hEvm]
    | some yulAccount =>
        rcases hWorld.find_yul hYul with
          ⟨evmAccount, hEvm, hAccount⟩
        simp [Option.option, hEvm, hAccount.balance]
  rw [hBalance]

theorem CompiledAccountMapRel.callTransferAccountMap?_of_evm_enough
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    (hEnough :
      value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance))) :
    ∃ yulAfter,
      EvmYul.Yul.callTransferAccountMap? yul source recipient value =
          some yulAfter ∧
        CompiledAccountMapRel yulAfter
          (evmCallTransfer evm source recipient value) := by
  have hYulEnough :
      value ≤ (yul.find? source |>.option ⟨0⟩ (·.balance)) :=
    (hWorld.callTransferEnough_iff source value).mpr hEnough
  refine
    ⟨callTransferUnchecked yul source recipient value, ?_, ?_⟩
  · simp [EvmYul.Yul.callTransferAccountMap?, hYulEnough,
      callTransferUnchecked]
  · simpa [evmCallTransfer] using
      hWorld.callTransferUnchecked_preserve source recipient value

theorem CompiledAccountMapRel.callTransferAccountMap?_none_of_evm_not_enough
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256}
    (hNotEnough :
      ¬ value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance))) :
    EvmYul.Yul.callTransferAccountMap? yul source recipient value = none := by
  have hYulNotEnough :
      ¬ value ≤ (yul.find? source |>.option ⟨0⟩ (·.balance)) := by
    intro hYulEnough
    exact hNotEnough
      ((hWorld.callTransferEnough_iff source value).mp hYulEnough)
  simp [EvmYul.Yul.callTransferAccountMap?, hYulNotEnough]

theorem CompiledAccountMapRel.callTransferAccountMap?_none_iff_evm_not_enough
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {source recipient : EvmYul.AccountAddress}
    {value : EvmYul.UInt256} :
    EvmYul.Yul.callTransferAccountMap? yul source recipient value = none ↔
      ¬ value ≤ (evm.find? source |>.option ⟨0⟩ (·.balance)) := by
  constructor
  · intro hNone hEnough
    rcases hWorld.callTransferAccountMap?_of_evm_enough
        (source := source) (recipient := recipient) hEnough with
      ⟨yulAfter, hSome, _hRel⟩
    simp [hNone] at hSome
  · intro hNotEnough
    exact hWorld.callTransferAccountMap?_none_of_evm_not_enough hNotEnough

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

theorem executionEnvRel_callFrame
    {cfg : Reference.StateRelConfig}
    {yulCode : AstContract} {evmCode : ByteArray}
    (hCode : cfg.codeRel yulCode evmCode)
    (codeOwner sender source : EvmYul.AccountAddress)
    (weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (gasPrice depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool)
    (blobVersionedHashes : List ByteArray) :
    Reference.ExecutionEnvRel cfg
      { codeOwner := codeOwner
        sender := sender
        source := source
        weiValue := weiValue
        calldata := calldata
        code := yulCode
        gasPrice := gasPrice
        header := header
        depth := depth
        perm := perm
        blobVersionedHashes := blobVersionedHashes }
      { codeOwner := codeOwner
        sender := sender
        source := source
        weiValue := weiValue
        calldata := calldata
        code := evmCode
        gasPrice := gasPrice
        header := header
        depth := depth
        perm := perm
        blobVersionedHashes := blobVersionedHashes } := by
  exact
    { codeOwner := rfl
      sender := rfl
      source := rfl
      weiValue := rfl
      calldata := rfl
      code := hCode
      gasPrice := rfl
      header := rfl
      depth := rfl
      perm := rfl
      blobVersionedHashes := rfl }

theorem CompiledToExecuteRel.executionEnvRel_callFrame
    {cfg : Reference.StateRelConfig}
    {yulExec : EvmYul.ToExecute .Yul}
    {evmExec : EvmYul.ToExecute .EVM}
    (hExec : CompiledToExecuteRel yulExec evmExec)
    (hCodeRel :
      ∀ {yulCode : AstContract} {evmCode : ByteArray},
        CompiledCodeRel yulCode evmCode →
          cfg.codeRel yulCode evmCode)
    (codeOwner sender source : EvmYul.AccountAddress)
    (weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (gasPrice depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool)
    (blobVersionedHashes : List ByteArray) :
    Reference.ExecutionEnvRel cfg
      { codeOwner := codeOwner
        sender := sender
        source := source
        weiValue := weiValue
        calldata := calldata
        code :=
          match yulExec with
          | EvmYul.ToExecute.Precompiled _ => default
          | EvmYul.ToExecute.Code yulCode => yulCode
        gasPrice := gasPrice
        header := header
        depth := depth
        perm := perm
        blobVersionedHashes := blobVersionedHashes }
      { codeOwner := codeOwner
        sender := sender
        source := source
        weiValue := weiValue
        calldata := calldata
        code :=
          match evmExec with
          | EvmYul.ToExecute.Precompiled _ => default
          | EvmYul.ToExecute.Code evmCode => evmCode
        gasPrice := gasPrice
        header := header
        depth := depth
        perm := perm
        blobVersionedHashes := blobVersionedHashes } := by
  cases hExec with
  | precompiled precompiled =>
      simpa using
        World.executionEnvRel_callFrame
          (hCodeRel CompiledCodeRel.empty)
          codeOwner sender source weiValue calldata gasPrice depth
          header perm blobVersionedHashes
  | code hCode =>
      simpa using
        World.executionEnvRel_callFrame
          (hCodeRel hCode)
          codeOwner sender source weiValue calldata gasPrice depth
          header perm blobVersionedHashes

theorem chainStateRel_addAccessedAccount
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.State .Yul} {evm : EvmYul.State .EVM}
    (hChain : Reference.ChainStateRel cfg yul evm)
    (addr : EvmYul.AccountAddress) :
    Reference.ChainStateRel cfg
      (EvmYul.State.addAccessedAccount yul addr)
      (EvmYul.State.addAccessedAccount evm addr) := by
  rcases hChain with
    ⟨hAccountMap, hSigma, hTotal, hReceipts, hSubstate, hEnv,
      hBlocks, hGenesis, hCreated⟩
  constructor
  · simpa [EvmYul.State.addAccessedAccount] using hAccountMap
  · simpa [EvmYul.State.addAccessedAccount] using hSigma
  · simpa [EvmYul.State.addAccessedAccount] using hTotal
  · simpa [EvmYul.State.addAccessedAccount] using hReceipts
  · simp [EvmYul.State.addAccessedAccount, EvmYul.Substate.addAccessedAccount,
      hSubstate]
  · simpa [EvmYul.State.addAccessedAccount] using hEnv
  · simpa [EvmYul.State.addAccessedAccount] using hBlocks
  · simpa [EvmYul.State.addAccessedAccount] using hGenesis
  · simpa [EvmYul.State.addAccessedAccount] using hCreated

theorem sharedStateRel_addAccessedAccount
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (addr : EvmYul.AccountAddress) :
    Reference.SharedStateRel cfg
      { yul with toState := EvmYul.State.addAccessedAccount yul.toState addr }
      { evm with toState := EvmYul.State.addAccessedAccount evm.toState addr } := by
  rcases hShared with ⟨hChain, hMachine⟩
  constructor
  · exact chainStateRel_addAccessedAccount hChain addr
  · simpa [EvmYul.State.addAccessedAccount] using hMachine

theorem machineStateRel_finishExternalCall
    {cfg : Reference.StateRelConfig}
    {yul evm : EvmYul.MachineState}
    (hMachine : Reference.MachineStateRel cfg yul evm)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256) :
    Reference.MachineStateRel cfg
      (yul.finishExternalCall returnData inOffset inSize outOffset outSize)
      (evm.finishExternalCall returnData inOffset inSize outOffset outSize) := by
  rcases hMachine with ⟨hGas, hActive, hMemory, _hReturn, _hHReturn⟩
  constructor
  · simpa [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes] using
      hGas
  · simp [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes,
      hActive]
  · simp [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes,
      hMemory]
  · simp [EvmYul.MachineState.finishExternalCall]
  · simp [EvmYul.MachineState.finishExternalCall]

theorem machineStateRel_finishExternalCallWithTargetGas
    {cfg : Reference.StateRelConfig}
    {yul evm : EvmYul.MachineState}
    (hMachine : Reference.MachineStateRel cfg yul evm)
    {targetGas : EvmYul.UInt256}
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.finishExternalCall returnData inOffset inSize
          outOffset outSize).gasAvailable
        targetGas) :
    Reference.MachineStateRel cfg
      (yul.finishExternalCall returnData inOffset inSize outOffset outSize)
      { evm.finishExternalCall returnData inOffset inSize outOffset outSize with
        gasAvailable := targetGas } := by
  rcases hMachine with ⟨_hGas, hActive, hMemory, _hReturn, _hHReturn⟩
  constructor
  · exact hGas
  · simp [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes,
      hActive]
  · simp [EvmYul.MachineState.finishExternalCall, EvmYul.writeBytes,
      hMemory]
  · simp [EvmYul.MachineState.finishExternalCall]
  · simp [EvmYul.MachineState.finishExternalCall]

theorem machineStateRel_gasAvailable_eq
    {cfg : Reference.StateRelConfig}
    {yul evm : EvmYul.MachineState}
    (hMachine : Reference.MachineStateRel cfg yul evm) :
    yul.gasAvailable = evm.gasAvailable := by
  simpa [EvmYul.MachineState.gas] using
    cfg.gasValueRel hMachine.gasAvailable

theorem machineStateRel_freshExternalCall
    {cfg : Reference.StateRelConfig}
    {yulGas evmGas : EvmYul.UInt256}
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.MachineStateRel cfg
      (EvmYul.MachineState.freshExternalCall yulGas)
      (EvmYul.MachineState.freshExternalCall evmGas) := by
  constructor
  · simpa [EvmYul.MachineState.freshExternalCall] using hGas
  · simp [EvmYul.MachineState.freshExternalCall]
  · simp [EvmYul.MachineState.freshExternalCall]
  · simp [EvmYul.MachineState.freshExternalCall]
  · simp [EvmYul.MachineState.freshExternalCall]

theorem sharedStateRel_freshExternalCall
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulGas evmGas : EvmYul.UInt256}
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas }
      { evm with
        toMachineState := EvmYul.MachineState.freshExternalCall evmGas } := by
  rcases hShared with ⟨hChain, _hMachine⟩
  exact ⟨hChain, machineStateRel_freshExternalCall hGas⟩

theorem sharedStateRel_finishExternalCall
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize }
      { evm with
        toMachineState :=
          evm.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize } := by
  rcases hShared with ⟨hChain, hMachine⟩
  exact
    ⟨hChain,
      machineStateRel_finishExternalCall hMachine returnData
        inOffset inSize outOffset outSize⟩

theorem sharedStateRel_finishExternalCallWithTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {targetGas : EvmYul.UInt256}
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas } } := by
  rcases hShared with ⟨hChain, hMachine⟩
  exact
    ⟨hChain,
      machineStateRel_finishExternalCallWithTargetGas hMachine
        returnData inOffset inSize outOffset outSize hGas⟩

theorem sharedStateRel_finishExternalCallAfterAccessWithTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (addr : EvmYul.AccountAddress)
    {targetGas : EvmYul.UInt256}
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toState := EvmYul.State.addAccessedAccount yul.toState addr
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize }
      { evm with
        toState := EvmYul.State.addAccessedAccount evm.toState addr
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas } } := by
  simpa using
    sharedStateRel_finishExternalCallWithTargetGas
      (sharedStateRel_addAccessedAccount hShared addr)
      returnData inOffset inSize outOffset outSize hGas

theorem sharedStateRel_finishExternalCallWithWorld
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hCreated : yulCreated = evmCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          evm.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := evmAccountMap
        substate := evmSubstate
        createdAccounts := evmCreated } := by
  rcases hShared with ⟨hChain, hMachine⟩
  rcases hChain with
    ⟨_hAccountMap, hSigma, hTotal, hReceipts, _hSubstate, hEnv,
      hBlocks, hGenesis, _hCreated⟩
  constructor
  · constructor
    · exact hAccountMap
    · simpa using hSigma
    · simpa using hTotal
    · simpa using hReceipts
    · exact hSubstate
    · simpa using hEnv
    · simpa using hBlocks
    · simpa using hGenesis
    · exact hCreated
  · exact
      machineStateRel_finishExternalCall hMachine returnData
        inOffset inSize outOffset outSize

theorem sharedStateRel_finishExternalCallWithWorldAndTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hCreated : yulCreated = evmCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap := evmAccountMap
        substate := evmSubstate
        createdAccounts := evmCreated } := by
  rcases hShared with ⟨hChain, hMachine⟩
  rcases hChain with
    ⟨_hAccountMap, hSigma, hTotal, hReceipts, _hSubstate, hEnv,
      hBlocks, hGenesis, _hCreated⟩
  constructor
  · exact
      { accountMap := hAccountMap
        σ₀ := by simpa using hSigma
        totalGasUsedInBlock := by simpa using hTotal
        transactionReceipts := by simpa using hReceipts
        substate := hSubstate
        executionEnv := by simpa using hEnv
        blocks := by simpa using hBlocks
        genesisBlockHeader := by simpa using hGenesis
        createdAccounts := hCreated }
  · exact
      machineStateRel_finishExternalCallWithTargetGas hMachine
        returnData inOffset inSize outOffset outSize hGas

theorem sharedStateRel_finishExternalCallAfterAccessWithWorldAndTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (addr : EvmYul.AccountAddress)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hCreated : yulCreated = evmCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := (EvmYul.State.addAccessedAccount yul.toState addr).substate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap := evmAccountMap
        substate := (EvmYul.State.addAccessedAccount evm.toState addr).substate
        createdAccounts := evmCreated } := by
  have hSubstate :
      (EvmYul.State.addAccessedAccount yul.toState addr).substate =
        (EvmYul.State.addAccessedAccount evm.toState addr).substate := by
    rcases hShared with ⟨hChain, _hMachine⟩
    rcases hChain with
      ⟨_hAccountMap, _hSigma, _hTotal, _hReceipts, hSubstate,
        _hEnv, _hBlocks, _hGenesis, _hCreated⟩
    simp [EvmYul.State.addAccessedAccount, EvmYul.Substate.addAccessedAccount,
      hSubstate]
  simpa [EvmYul.State.addAccessedAccount] using
    sharedStateRel_finishExternalCallWithWorldAndTargetGas
      (sharedStateRel_addAccessedAccount hShared addr)
      hAccountMap hSubstate hCreated returnData
      inOffset inSize outOffset outSize hGas

theorem buildContractCallEmptyReturnState_none_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {targetGas : EvmYul.UInt256}
    (inOffset inSize outOffset outSize value : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildContractCallEmptyReturnState
          (.Ok yul store) none
          inOffset inSize outOffset outSize value =
        .ok (.Ok yulAfter store, [value]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas } } := by
  refine
    ⟨{ yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize },
      ?_, ?_⟩
  · simp [EvmYul.Yul.buildContractCallEmptyReturnState,
      EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.toMachineState]
  · exact
      sharedStateRel_finishExternalCallWithTargetGas hShared
        ByteArray.empty inOffset inSize outOffset outSize hGas

theorem buildContractCallEmptyReturnState_afterAccess_some_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (inOffset inSize outOffset outSize value : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildContractCallEmptyReturnState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) addr)
          (some yulAccountMap)
          inOffset inSize outOffset outSize value =
        .ok (.Ok yulAfter store, [value]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evmAccountMap
          substate := (EvmYul.State.addAccessedAccount evm.toState addr).substate } := by
  have hCreated : yul.createdAccounts = evm.createdAccounts := by
    rcases hShared with ⟨hChain, _hMachine⟩
    exact hChain.createdAccounts
  refine
    ⟨{ yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := (EvmYul.State.addAccessedAccount yul.toState addr).substate },
      ?_, ?_⟩
  · simp [EvmYul.Yul.buildContractCallEmptyReturnState,
      EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.Yul.State.toSharedState,
      EvmYul.Yul.State.toMachineState, EvmYul.State.addAccessedAccount]
  · simpa [EvmYul.State.addAccessedAccount] using
      sharedStateRel_finishExternalCallAfterAccessWithWorldAndTargetGas
        hShared addr hAccountMap hCreated ByteArray.empty
        inOffset inSize outOffset outSize hGas

theorem buildContractCallEmptyReturnState_afterAccess_none_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {targetGas : EvmYul.UInt256}
    (inOffset inSize outOffset outSize value : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildContractCallEmptyReturnState
          (EvmYul.Yul.addAccessedAccount
            (.Ok yul store) addr)
          none
          inOffset inSize outOffset outSize value =
        .ok (.Ok yulAfter store, [value]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          substate := (EvmYul.State.addAccessedAccount evm.toState addr).substate } := by
  refine
    ⟨{ yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall ByteArray.empty
            inOffset inSize outOffset outSize
        substate := (EvmYul.State.addAccessedAccount yul.toState addr).substate },
      ?_, ?_⟩
  · simp [EvmYul.Yul.buildContractCallEmptyReturnState,
      EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.Yul.State.toSharedState,
      EvmYul.Yul.State.toMachineState, EvmYul.State.addAccessedAccount]
  · simpa [EvmYul.State.addAccessedAccount] using
      sharedStateRel_finishExternalCallAfterAccessWithTargetGas
        hShared addr ByteArray.empty inOffset inSize outOffset outSize hGas

theorem buildContractCallReturnState_ok_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize value : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildContractCallReturnState
          (.Ok yul store) yulAccountMap yulSubstate returnData
          inOffset inSize outOffset outSize value =
        .ok (.Ok yulAfter store, [value]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evmAccountMap
          substate := evmSubstate } := by
  have hCreated : yul.createdAccounts = evm.createdAccounts := by
    rcases hShared with ⟨hChain, _hMachine⟩
    exact hChain.createdAccounts
  refine
    ⟨{ yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate },
      ?_, ?_⟩
  · simp [EvmYul.Yul.buildContractCallReturnState,
      EvmYul.Yul.State.toMachineState]
  · exact
      sharedStateRel_finishExternalCallWithWorldAndTargetGas
        hShared hAccountMap hSubstate hCreated returnData
        inOffset inSize outOffset outSize hGas

theorem buildPrecompiledContractCallState_success_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {yulAccountMap yulAccountMapAfter : EvmYul.AccountMap .Yul}
    {evmAccountMapAfter : EvmYul.AccountMap .EVM}
    {yulSubstateAfter evmSubstateAfter : EvmYul.Substate}
    {targetGas yulReturnedGas : EvmYul.UInt256}
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256)
    (yulEnv : EvmYul.ExecutionEnv .Yul)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hRun :
      runPrecompiledContract precompiled yulAccountMap gas yul.substate yulEnv =
        (true, yulAccountMapAfter, yulReturnedGas,
          yulSubstateAfter, returnData))
    (hAccountMap :
      cfg.accountMapRel
        (if yulAccountMapAfter.isEmpty then
          yul.accountMap
        else
          yulAccountMapAfter)
        evmAccountMapAfter)
    (hSubstate : yulSubstateAfter = evmSubstateAfter)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildPrecompiledContractCallState
          (.Ok yul store) yulAccountMap precompiled gas yulEnv
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap := evmAccountMapAfter
          substate := evmSubstateAfter } := by
  rcases
    buildContractCallReturnState_ok_rel
      hShared store hAccountMap hSubstate returnData
      inOffset inSize outOffset outSize ⟨1⟩ hGas with
    ⟨yulAfter, hBuild, hRel⟩
  refine ⟨yulAfter, ?_, hRel⟩
  simp [EvmYul.Yul.buildPrecompiledContractCallState,
    EvmYul.Yul.State.toState, EvmYul.Yul.State.toSharedState,
    hRun, hBuild]

theorem buildPrecompiledContractCallState_failure_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {yulAccountMap yulAccountMapAfter : EvmYul.AccountMap .Yul}
    {yulSubstateAfter : EvmYul.Substate}
    {targetGas yulReturnedGas : EvmYul.UInt256}
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256)
    (yulEnv : EvmYul.ExecutionEnv .Yul)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hRun :
      runPrecompiledContract precompiled yulAccountMap gas yul.substate yulEnv =
        (false, yulAccountMapAfter, yulReturnedGas,
          yulSubstateAfter, returnData))
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildPrecompiledContractCallState
          (.Ok yul store) yulAccountMap precompiled gas yulEnv
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨0⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas } } := by
  rcases
    buildContractCallEmptyReturnState_none_rel
      hShared store inOffset inSize outOffset outSize ⟨0⟩ hGas with
    ⟨yulAfter, hBuild, hRel⟩
  refine ⟨yulAfter, ?_, hRel⟩
  simp [EvmYul.Yul.buildPrecompiledContractCallState,
    EvmYul.Yul.State.toState, hRun, hBuild]

theorem sharedStateRel_callResultMergeWithTargetGas
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap :
      cfg.accountMapRel yulAccountMap
        (if evmAccountMap.isEmpty then
          evm.accountMap
        else
          evmAccountMap))
    (hSubstate :
      yulSubstate =
        if evmAccountMap.isEmpty then
          evm.substate
        else
          evmSubstate)
    (hCreated : yulCreated = evmCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if evmAccountMap.isEmpty then
            evm.accountMap
          else
            evmAccountMap
        substate :=
          if evmAccountMap.isEmpty then
            evm.substate
          else
            evmSubstate
        createdAccounts := evmCreated } := by
  exact
    sharedStateRel_finishExternalCallWithWorldAndTargetGas hShared
      hAccountMap hSubstate hCreated returnData inOffset inSize
      outOffset outSize hGas

theorem sharedStateRel_callSuccessMergeWithTargetGasOfEvmNonempty
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hCreated : yulCreated = evmCreated)
    (hEvmAccountMapNonempty :
      (evmAccountMap.isEmpty) = false)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState :=
          yul.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulAccountMap
        substate := yulSubstate
        createdAccounts := yulCreated }
      { evm with
        toMachineState :=
          { evm.toMachineState.finishExternalCall returnData
              inOffset inSize outOffset outSize with
            gasAvailable := targetGas }
        accountMap :=
          if evmAccountMap.isEmpty then
            evm.accountMap
          else
            evmAccountMap
        substate :=
          if evmAccountMap.isEmpty then
            evm.substate
          else
            evmSubstate
        createdAccounts := evmCreated } := by
  simpa [hEvmAccountMapNonempty] using
    sharedStateRel_callResultMergeWithTargetGas hShared
      (yulAccountMap := yulAccountMap)
      (evmAccountMap := evmAccountMap)
      (yulSubstate := yulSubstate)
      (evmSubstate := evmSubstate)
      (yulCreated := yulCreated)
      (evmCreated := evmCreated)
      (targetGas := targetGas)
      (by simpa [hEvmAccountMapNonempty] using hAccountMap)
      (by simpa [hEvmAccountMapNonempty] using hSubstate)
      hCreated returnData inOffset inSize
      outOffset outSize hGas

theorem restoreSuccessfulContractCallState_ok_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {evmChildAccountMap : EvmYul.AccountMap .EVM}
    {evmChildSubstate : EvmYul.Substate}
    {evmChildCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {targetGas : EvmYul.UInt256}
    (hAccountMap :
      cfg.accountMapRel yulChild.accountMap
        (if evmChildAccountMap.isEmpty then
          evmParent.accountMap
        else
          evmChildAccountMap))
    (hSubstate :
      yulChild.substate =
        if evmChildAccountMap.isEmpty then
          evmParent.substate
        else
          evmChildSubstate)
    (hCreated : yulChild.createdAccounts = evmChildCreated)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreSuccessfulContractCallState
          (.Ok yulParent parentStore)
          (.Ok yulChild childStore)
          restoreStore returnData inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChildAccountMap.isEmpty then
              evmParent.accountMap
            else
              evmChildAccountMap
          substate :=
            if evmChildAccountMap.isEmpty then
              evmParent.substate
            else
              evmChildSubstate
          createdAccounts := evmChildCreated } := by
  refine
    ⟨{ yulParent with
        toMachineState :=
          yulParent.toMachineState.finishExternalCall returnData
            inOffset inSize outOffset outSize
        accountMap := yulChild.accountMap
        substate := yulChild.substate
        createdAccounts := yulChild.createdAccounts },
      ?_, ?_⟩
  · simp [EvmYul.Yul.restoreSuccessfulContractCallState,
      EvmYul.Yul.State.toMachineState]
  · exact
      sharedStateRel_callResultMergeWithTargetGas hParent
        hAccountMap hSubstate hCreated returnData
        inOffset inSize outOffset outSize hGas

theorem restoreRevertedContractCallState_afterAccess_ok_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore : EvmYul.Yul.VarStore)
    (addr : EvmYul.AccountAddress)
    {yulChild : EvmYul.SharedState .Yul}
    {targetGas : EvmYul.UInt256}
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall
          yulChild.toMachineState.H_return
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreRevertedContractCallState
          (EvmYul.Yul.addAccessedAccount (.Ok yulParent parentStore) addr)
          (.Ok yulChild childStore)
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter parentStore, [⟨0⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall
                yulChild.toMachineState.H_return
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          substate :=
            (EvmYul.State.addAccessedAccount evmParent.toState addr).substate } := by
  refine
    ⟨{ yulParent with
        toMachineState :=
          yulParent.toMachineState.finishExternalCall
            yulChild.toMachineState.H_return
            inOffset inSize outOffset outSize
        substate :=
          (EvmYul.State.addAccessedAccount yulParent.toState addr).substate },
      ?_, ?_⟩
  · simp [EvmYul.Yul.restoreRevertedContractCallState,
      EvmYul.Yul.addAccessedAccount, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.toState,
      EvmYul.State.addAccessedAccount]
  · simpa [EvmYul.State.addAccessedAccount] using
      sharedStateRel_finishExternalCallAfterAccessWithTargetGas
        hParent addr yulChild.toMachineState.H_return
        inOffset inSize outOffset outSize hGas

theorem sharedStateRel_of_eraseGas_eq
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {evm target : EVMState}
    (hShared : Reference.SharedStateRel cfg yul target.toSharedState)
    (hErase : Assembly.eraseGas evm = Assembly.eraseGas target)
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        evm.gasAvailable) :
    Reference.SharedStateRel cfg yul evm.toSharedState := by
  have hAccountMap : evm.accountMap = target.accountMap := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.accountMap) hErase
  have hSigma : evm.σ₀ = target.σ₀ := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.σ₀) hErase
  have hTotal :
      evm.totalGasUsedInBlock = target.totalGasUsedInBlock := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.totalGasUsedInBlock) hErase
  have hReceipts :
      evm.transactionReceipts = target.transactionReceipts := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.transactionReceipts) hErase
  have hSubstate : evm.substate = target.substate := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.substate) hErase
  have hEnv : evm.executionEnv = target.executionEnv := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.executionEnv) hErase
  have hBlocks : evm.blocks = target.blocks := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.blocks) hErase
  have hGenesis : evm.genesisBlockHeader = target.genesisBlockHeader := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.genesisBlockHeader) hErase
  have hCreated : evm.createdAccounts = target.createdAccounts := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.createdAccounts) hErase
  have hActiveWords :
      evm.toMachineState.activeWords =
        target.toMachineState.activeWords := by
    simpa [Assembly.eraseGas] using
      congrArg
        (fun state : EVMState => state.toMachineState.activeWords) hErase
  have hMemory :
      evm.toMachineState.memory = target.toMachineState.memory := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.toMachineState.memory) hErase
  have hReturnData :
      evm.toMachineState.returnData =
        target.toMachineState.returnData := by
    simpa [Assembly.eraseGas] using
      congrArg
        (fun state : EVMState => state.toMachineState.returnData) hErase
  have hHReturn :
      evm.toMachineState.H_return =
        target.toMachineState.H_return := by
    simpa [Assembly.eraseGas] using
      congrArg (fun state : EVMState => state.toMachineState.H_return) hErase
  rcases hShared with ⟨hChain, hMachine⟩
  constructor
  · constructor
    · simpa [hAccountMap] using hChain.accountMap
    · simpa [hSigma] using hChain.σ₀
    · simpa [hTotal] using hChain.totalGasUsedInBlock
    · simpa [hReceipts] using hChain.transactionReceipts
    · simpa [hSubstate] using hChain.substate
    · simpa [hEnv] using hChain.executionEnv
    · simpa [hBlocks] using hChain.blocks
    · simpa [hGenesis] using hChain.genesisBlockHeader
    · simpa [hCreated] using hChain.createdAccounts
  · constructor
    · exact hGas
    · simpa [hActiveWords] using hMachine.activeWords
    · simpa [hMemory] using hMachine.memory
    · simpa [hReturnData] using hMachine.returnData
    · simpa [hHReturn] using hMachine.H_return

theorem sharedStateRel_of_XResultAgrees_running_success
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {target evm : EVMState}
    {output : ByteArray}
    (hShared : Reference.SharedStateRel cfg yul target.toSharedState)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.running target)
        (.success evm output))
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        evm.gasAvailable) :
    Reference.SharedStateRel cfg yul evm.toSharedState :=
  sharedStateRel_of_eraseGas_eq hShared hAgree hGas

theorem sharedStateRel_of_XResultAgrees_halted_success
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evm : EVMState}
    {output : ByteArray}
    (hShared : Reference.SharedStateRel cfg yul halt.state.toSharedState)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evm output))
    (hGas :
      cfg.gasAvailableRel yul.toMachineState.gasAvailable
        evm.gasAvailable) :
    halt.kind ≠ .revert ∧
      Reference.SharedStateRel cfg yul evm.toSharedState ∧
        output = halt.output := by
  rcases hAgree with ⟨hNotRevert, hErase, hOutput⟩
  exact
    ⟨hNotRevert, sharedStateRel_of_eraseGas_eq hShared hErase hGas,
      hOutput⟩

theorem XResultAgrees_halted_revert
    {halt : Assembly.Halt}
    {returnedGas : EvmYul.UInt256}
    {output : ByteArray}
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.revert returnedGas output)) :
    halt.kind = .revert ∧ output = halt.output := by
  simpa [Assembly.GasAware.XResultAgrees] using hAgree

theorem restoreSuccessfulContractCallState_childEvm_nonempty_rel
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {evmChild : EVMState}
    (hChild :
      Reference.SharedStateRel cfg yulChild evmChild.toSharedState)
    (hNonempty : evmChild.accountMap.isEmpty = false)
    (returnData : ByteArray)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreSuccessfulContractCallState
          (.Ok yulParent parentStore)
          (.Ok yulChild childStore)
          restoreStore returnData inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then
              evmParent.accountMap
            else
              evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              evmParent.substate
            else
              evmChild.substate
          createdAccounts := evmChild.createdAccounts } := by
  rcases hChild with ⟨hChildChain, _hChildMachine⟩
  exact
    restoreSuccessfulContractCallState_ok_rel
      hParent parentStore childStore restoreStore
      (yulChild := yulChild)
      (evmChildAccountMap := evmChild.accountMap)
      (evmChildSubstate := evmChild.substate)
      (evmChildCreated := evmChild.createdAccounts)
      (targetGas := targetGas)
      (by simpa [hNonempty] using hChildChain.accountMap)
      (by simpa [hNonempty] using hChildChain.substate)
      hChildChain.createdAccounts
      returnData inOffset inSize outOffset outSize hGas

theorem restoreSuccessfulContractCallState_of_XResultAgrees_running_success_nonempty
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {targetChild evmChild : EVMState}
    {returnData : ByteArray}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild targetChild.toSharedState)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.running targetChild)
        (.success evmChild returnData))
    (hChildGas :
      cfg.gasAvailableRel yulChild.toMachineState.gasAvailable
        evmChild.gasAvailable)
    (hNonempty : evmChild.accountMap.isEmpty = false)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.restoreSuccessfulContractCallState
          (.Ok yulParent parentStore)
          (.Ok yulChild childStore)
          restoreStore returnData inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evmParent with
          toMachineState :=
            { evmParent.toMachineState.finishExternalCall returnData
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if evmChild.accountMap.isEmpty then
              evmParent.accountMap
            else
              evmChild.accountMap
          substate :=
            if evmChild.accountMap.isEmpty then
              evmParent.substate
            else
              evmChild.substate
          createdAccounts := evmChild.createdAccounts } := by
  exact
    restoreSuccessfulContractCallState_childEvm_nonempty_rel
      hParent parentStore childStore restoreStore
      (sharedStateRel_of_XResultAgrees_running_success
        hTargetChild hAgree hChildGas)
      hNonempty returnData inOffset inSize outOffset outSize hGas

theorem restoreSuccessfulContractCallState_of_XResultAgrees_halted_success_nonempty
    {cfg : Reference.StateRelConfig}
    {yulParent : EvmYul.SharedState .Yul}
    {evmParent : EvmYul.SharedState .EVM}
    (hParent : Reference.SharedStateRel cfg yulParent evmParent)
    (parentStore childStore restoreStore : EvmYul.Yul.VarStore)
    {yulChild : EvmYul.SharedState .Yul}
    {halt : Assembly.Halt}
    {evmChild : EVMState}
    {returnData : ByteArray}
    (hTargetChild :
      Reference.SharedStateRel cfg yulChild halt.state.toSharedState)
    (hAgree :
      Assembly.GasAware.XResultAgrees (.halted halt)
        (.success evmChild returnData))
    (hChildGas :
      cfg.gasAvailableRel yulChild.toMachineState.gasAvailable
        evmChild.gasAvailable)
    (hNonempty : evmChild.accountMap.isEmpty = false)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hGas :
      cfg.gasAvailableRel
        (yulParent.toMachineState.finishExternalCall returnData
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    halt.kind ≠ .revert ∧
      ∃ yulAfter,
        EvmYul.Yul.restoreSuccessfulContractCallState
            (.Ok yulParent parentStore)
            (.Ok yulChild childStore)
            restoreStore returnData inOffset inSize outOffset outSize =
          .ok (.Ok yulAfter restoreStore, [⟨1⟩]) ∧
        Reference.SharedStateRel cfg yulAfter
          { evmParent with
            toMachineState :=
              { evmParent.toMachineState.finishExternalCall returnData
                  inOffset inSize outOffset outSize with
                gasAvailable := targetGas }
            accountMap :=
              if evmChild.accountMap.isEmpty then
                evmParent.accountMap
              else
                evmChild.accountMap
            substate :=
              if evmChild.accountMap.isEmpty then
                evmParent.substate
              else
                evmChild.substate
            createdAccounts := evmChild.createdAccounts } := by
  rcases
    sharedStateRel_of_XResultAgrees_halted_success
      hTargetChild hAgree hChildGas with
    ⟨hNotRevert, hChild, _hOutput⟩
  exact
    ⟨hNotRevert,
      restoreSuccessfulContractCallState_childEvm_nonempty_rel
        hParent parentStore childStore restoreStore hChild hNonempty
        returnData inOffset inSize outOffset outSize hGas⟩

theorem sharedStateRel_freshExternalCallWithWorld
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas evmGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hExecutionEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (hCreated : yulCreated = evmCreated)
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv := yulEnv
        createdAccounts := yulCreated }
      { evm with
        toMachineState := EvmYul.MachineState.freshExternalCall evmGas
        accountMap := evmAccountMap
        substate := evmSubstate
        executionEnv := evmEnv
        createdAccounts := evmCreated } := by
  rcases hShared with ⟨hChain, _hMachine⟩
  rcases hChain with
    ⟨_hAccountMap, hSigma, hTotal, hReceipts, _hSubstate, _hEnv,
      hBlocks, hGenesis, _hCreated⟩
  constructor
  · constructor
    · exact hAccountMap
    · simpa using hSigma
    · simpa using hTotal
    · simpa using hReceipts
    · exact hSubstate
    · exact hExecutionEnv
    · simpa using hBlocks
    · simpa using hGenesis
    · exact hCreated
  · exact machineStateRel_freshExternalCall hGas

theorem sharedStateRel_freshExternalCallWithWorldFromFreshEvmFrame
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas evmGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hExecutionEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (hCreated : yulCreated = evmCreated)
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv := yulEnv
        createdAccounts := yulCreated }
      ({ (default : EvmYul.EVM.State) with
        accountMap := evmAccountMap
        σ₀ := evm.σ₀
        totalGasUsedInBlock := evm.totalGasUsedInBlock
        transactionReceipts := evm.transactionReceipts
        substate := evmSubstate
        executionEnv := evmEnv
        blocks := evm.blocks
        genesisBlockHeader := evm.genesisBlockHeader
        createdAccounts := evmCreated
        toMachineState := EvmYul.MachineState.freshExternalCall evmGas }
        : EvmYul.EVM.State).toSharedState := by
  rcases hShared with ⟨hChain, _hMachine⟩
  rcases hChain with
    ⟨_hAccountMap, hSigma, hTotal, hReceipts, _hSubstate, _hEnv,
      hBlocks, hGenesis, _hCreated⟩
  constructor
  · constructor
    · exact hAccountMap
    · simpa using hSigma
    · simpa using hTotal
    · simpa using hReceipts
    · exact hSubstate
    · exact hExecutionEnv
    · simpa using hBlocks
    · simpa using hGenesis
    · exact hCreated
  · exact machineStateRel_freshExternalCall hGas

theorem sharedStateRel_callFrameFromFreshEvmFrame
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas evmGas : EvmYul.UInt256}
    {yulCode : AstContract} {evmCode : ByteArray}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hCode : cfg.codeRel yulCode evmCode)
    (hCreated : yulCreated = evmCreated)
    (hGas : cfg.gasAvailableRel yulGas evmGas)
    (codeOwner sender source : EvmYul.AccountAddress)
    (weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (gasPrice depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool)
    (blobVersionedHashes : List ByteArray) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv :=
          { codeOwner := codeOwner
            sender := sender
            source := source
            weiValue := weiValue
            calldata := calldata
            code := yulCode
            gasPrice := gasPrice
            header := header
            depth := depth
            perm := perm
            blobVersionedHashes := blobVersionedHashes }
        createdAccounts := yulCreated }
      ({ (default : EvmYul.EVM.State) with
        accountMap := evmAccountMap
        σ₀ := evm.σ₀
        totalGasUsedInBlock := evm.totalGasUsedInBlock
        transactionReceipts := evm.transactionReceipts
        substate := evmSubstate
        executionEnv :=
          { codeOwner := codeOwner
            sender := sender
            source := source
            weiValue := weiValue
            calldata := calldata
            code := evmCode
            gasPrice := gasPrice
            header := header
            depth := depth
            perm := perm
            blobVersionedHashes := blobVersionedHashes }
        blocks := evm.blocks
        genesisBlockHeader := evm.genesisBlockHeader
        createdAccounts := evmCreated
        toMachineState := EvmYul.MachineState.freshExternalCall evmGas }
        : EvmYul.EVM.State).toSharedState := by
  exact
    sharedStateRel_freshExternalCallWithWorldFromFreshEvmFrame hShared
      hAccountMap hSubstate
      (executionEnvRel_callFrame hCode codeOwner sender source weiValue
        calldata gasPrice depth header perm blobVersionedHashes)
      hCreated hGas

def xiInitialState
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM) : EVMState :=
  { (default : EVMState) with
    accountMap := accountMap
    σ₀ := sigma0
    totalGasUsedInBlock := chainContext.totalGasUsedInBlock
    transactionReceipts := chainContext.transactionReceipts
    executionEnv := env
    substate := substate
    createdAccounts := createdAccounts
    gasAvailable := gas
    blocks := blocks
    genesisBlockHeader := genesisBlockHeader }

theorem xiInitialState_toSharedState_eq_freshExternalCall
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM) :
    (xiInitialState createdAccounts genesisBlockHeader blocks accountMap sigma0
        chainContext gas substate env).toSharedState =
      ({ (default : EVMState) with
        accountMap := accountMap
        σ₀ := sigma0
        totalGasUsedInBlock := chainContext.totalGasUsedInBlock
        transactionReceipts := chainContext.transactionReceipts
        substate := substate
        executionEnv := env
        blocks := blocks
        genesisBlockHeader := genesisBlockHeader
        createdAccounts := createdAccounts
        toMachineState := EvmYul.MachineState.freshExternalCall gas }
        : EVMState).toSharedState := by
  simp [xiInitialState, EvmYul.MachineState.freshExternalCall]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem sharedStateRel_freshExternalCallWithWorldFromXiInitialState
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    {yulCreated evmCreated : Batteries.RBSet EvmYul.AccountAddress compare}
    {yulGas evmGas : EvmYul.UInt256}
    (hAccountMap : cfg.accountMapRel yulAccountMap evmAccountMap)
    (hSubstate : yulSubstate = evmSubstate)
    (hExecutionEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (hCreated : yulCreated = evmCreated)
    (hGas : cfg.gasAvailableRel yulGas evmGas) :
    Reference.SharedStateRel cfg
      { yul with
        toMachineState := EvmYul.MachineState.freshExternalCall yulGas
        accountMap := yulAccountMap
        substate := yulSubstate
        executionEnv := yulEnv
        createdAccounts := yulCreated }
      (xiInitialState evmCreated evm.genesisBlockHeader evm.blocks
        evmAccountMap evm.σ₀
        { totalGasUsedInBlock := evm.totalGasUsedInBlock
          transactionReceipts := evm.transactionReceipts }
        evmGas evmSubstate evmEnv).toSharedState := by
  rw [xiInitialState_toSharedState_eq_freshExternalCall]
  exact
    sharedStateRel_freshExternalCallWithWorldFromFreshEvmFrame hShared
      hAccountMap hSubstate hExecutionEnv hCreated hGas

theorem Xi_succ_eq_X
    (fuel : Nat)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM) :
    EvmYul.EVM.Ξ fuel.succ createdAccounts genesisBlockHeader blocks
        accountMap sigma0 chainContext gas substate env =
      match EvmYul.EVM.X fuel (EvmYul.EVM.D_J env.code ⟨0⟩)
          (xiInitialState createdAccounts genesisBlockHeader blocks
            accountMap sigma0 chainContext gas substate env) with
      | .error err => .error err
      | .ok (.success evmState' output) =>
          .ok (.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.gasAvailable, evmState'.substate) output)
      | .ok (.revert returnedGas output) =>
          .ok (.revert returnedGas output) := by
  simp only [EvmYul.EVM.Ξ]
  change
    (do
      let result ← EvmYul.EVM.X fuel (EvmYul.EVM.D_J env.code ⟨0⟩)
        (xiInitialState createdAccounts genesisBlockHeader blocks
          accountMap sigma0 chainContext gas substate env)
      match result with
      | EvmYul.EVM.ExecutionResult.success evmState' output =>
          .ok (EvmYul.EVM.ExecutionResult.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.gasAvailable, evmState'.substate) output)
      | EvmYul.EVM.ExecutionResult.revert returnedGas output =>
          .ok (EvmYul.EVM.ExecutionResult.revert returnedGas output)) =
    _
  cases EvmYul.EVM.X fuel (EvmYul.EVM.D_J env.code ⟨0⟩)
      (xiInitialState createdAccounts genesisBlockHeader blocks
        accountMap sigma0 chainContext gas substate env) with
  | error err => rfl
  | ok result =>
      cases result <;> rfl

theorem xiInitialState_eq_installCodeAndGas
    (target : Assembly.TargetProgram) (gasNat : Nat)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (initialGas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM) :
    xiInitialState createdAccounts genesisBlockHeader blocks accountMap sigma0
        chainContext (EvmYul.UInt256.ofNat gasNat) substate
        { env with code := Assembly.Bytecode.encodeTarget target } =
      Assembly.GasAware.installCodeAndGas target gasNat
        { xiInitialState createdAccounts genesisBlockHeader blocks accountMap
            sigma0 chainContext initialGas substate env with
          pc := Assembly.Program.pcAfter []
          stack := [] } := by
  simp [xiInitialState, Assembly.GasAware.installCodeAndGas,
    Assembly.Program.pcAfter]
  constructor <;> rfl

theorem Xi_succ_eq_X_installedCode
    (fuel gasNat : Nat)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (initialGas : EvmYul.UInt256) (substate : EvmYul.Substate)
    (env : EvmYul.ExecutionEnv .EVM)
    (target : Assembly.TargetProgram) :
    EvmYul.EVM.Ξ fuel.succ createdAccounts genesisBlockHeader blocks
        accountMap sigma0 chainContext (EvmYul.UInt256.ofNat gasNat) substate
        { env with code := Assembly.Bytecode.encodeTarget target } =
      match EvmYul.EVM.X fuel (Assembly.GasAware.validJumps target)
          (Assembly.GasAware.installCodeAndGas target gasNat
            { xiInitialState createdAccounts genesisBlockHeader blocks
                accountMap sigma0 chainContext initialGas substate env with
              pc := Assembly.Program.pcAfter []
              stack := [] }) with
      | .error err => .error err
      | .ok (.success evmState' output) =>
          .ok (.success
            (evmState'.createdAccounts, evmState'.accountMap,
              evmState'.gasAvailable, evmState'.substate) output)
      | .ok (.revert returnedGas output) =>
          .ok (.revert returnedGas output) := by
  rw [Xi_succ_eq_X]
  rw [xiInitialState_eq_installCodeAndGas (initialGas := initialGas)]
  have hZero : (⟨0⟩ : EvmYul.UInt256) = EvmYul.UInt256.ofNat 0 := rfl
  simp [Assembly.GasAware.validJumps, hZero]

theorem Theta_code_succ_eq_Xi
    (fuel : Nat)
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (accountMap sigma0 : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (substate : EvmYul.Substate)
    (source origin recipient : EvmYul.AccountAddress)
    (code : ByteArray)
    (gas gasPrice value weiValue : EvmYul.UInt256)
    (calldata : ByteArray)
    (depth : Nat)
    (header : EvmYul.BlockHeader)
    (perm : Bool) :
    EvmYul.EVM.Θ fuel.succ blobVersionedHashes createdAccounts
        genesisBlockHeader blocks accountMap sigma0 chainContext substate
        source origin recipient (.Code code) gas gasPrice value weiValue
        calldata depth header perm =
      match EvmYul.EVM.Ξ fuel createdAccounts genesisBlockHeader blocks
          (EvmYul.EVM.thetaCallTransfer accountMap source recipient value)
          sigma0 chainContext gas substate
          (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source origin
            recipient (.Code code) gasPrice weiValue calldata depth header
            perm) with
      | .error err =>
          if err == EvmYul.EVM.ExecutionException.OutOfFuel then
            .error EvmYul.EVM.ExecutionException.OutOfFuel
          else
            .ok (createdAccounts, accountMap, ⟨0⟩, substate, false,
              ByteArray.empty)
      | .ok (.revert returnedGas output) =>
          .ok (createdAccounts, accountMap, returnedGas, substate, false,
            output)
      | .ok (.success (createdAccounts', accountMap', returnedGas,
          substate') output) =>
          .ok (createdAccounts',
            if accountMap'.isEmpty then accountMap else accountMap',
            returnedGas,
            if accountMap'.isEmpty then substate else substate',
            true, output) := by
  simp only [EvmYul.EVM.Θ]
  generalize hChild :
    EvmYul.EVM.Ξ fuel createdAccounts genesisBlockHeader blocks
      (EvmYul.EVM.thetaCallTransfer accountMap source recipient value)
      sigma0 chainContext gas substate
      (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source origin
        recipient (EvmYul.ToExecute.Code code) gasPrice weiValue calldata
        depth header perm) = child
  cases child with
  | error err =>
      by_cases hErr : err == EvmYul.EVM.ExecutionException.OutOfFuel
      · simp [hErr]
        rfl
      · simp [hErr]
  | ok result =>
      cases result with
      | success data output =>
          rcases data with
            ⟨createdAccounts', accountMap', returnedGas, substate'⟩
          simp
      | revert returnedGas output =>
          simp

theorem Ccallgas_eq_of_dead_eq
    {τ υ : EvmYul.OperationType}
    {yulAccountMap : EvmYul.AccountMap τ}
    {evmAccountMap : EvmYul.AccountMap υ}
    {yulMachine evmMachine : EvmYul.MachineState}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {target recipient : EvmYul.AccountAddress}
    {value gas : EvmYul.UInt256}
    (hGas : yulMachine.gasAvailable = evmMachine.gasAvailable)
    (hSubstate : yulSubstate = evmSubstate)
    (hDead :
      EvmYul.State.dead yulAccountMap recipient =
        EvmYul.State.dead evmAccountMap recipient) :
    EvmYul.EVM.Ccallgas target recipient value gas
        yulAccountMap yulMachine yulSubstate =
      EvmYul.EVM.Ccallgas target recipient value gas
        evmAccountMap evmMachine evmSubstate := by
  subst evmSubstate
  cases value
  simp [EvmYul.EVM.Ccallgas, EvmYul.EVM.Cgascap,
    EvmYul.EVM.Cextra, EvmYul.EVM.Cnew, hGas, hDead]

theorem CompiledAccountMapRel.dead_eq_of_missing
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress}
    (hMissing : yul.find? addr = none) :
    EvmYul.State.dead yul addr = EvmYul.State.dead evm addr := by
  have hEvmMissing := hWorld.not_find_evm_of_not_find_yul hMissing
  unfold EvmYul.State.dead
  rw [hMissing, hEvmMissing]
  rfl

theorem CompiledAccountMapRel.Ccallgas_eq_of_missing_recipient
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yulMachine evmMachine : EvmYul.MachineState}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {target recipient : EvmYul.AccountAddress}
    {value gas : EvmYul.UInt256}
    (hGas : yulMachine.gasAvailable = evmMachine.gasAvailable)
    (hSubstate : yulSubstate = evmSubstate)
    (hMissing : yul.find? recipient = none) :
    EvmYul.EVM.Ccallgas target recipient value gas
        yul yulMachine yulSubstate =
      EvmYul.EVM.Ccallgas target recipient value gas
        evm evmMachine evmSubstate := by
  exact
    Ccallgas_eq_of_dead_eq hGas hSubstate
      (hWorld.dead_eq_of_missing hMissing)

theorem CompiledAccountMapRel.toExecute_precompiled
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    {addr : EvmYul.AccountAddress}
    {precompiled : EvmYul.PrecompiledContract}
    (hPrecompile :
      EvmYul.PrecompiledContract.ofAddress? addr = some precompiled) :
    CompiledToExecuteRel
      (EvmYul.toExecute .Yul yul addr)
      (EvmYul.toExecute .EVM evm addr) := by
  simp [EvmYul.toExecute, hPrecompile,
    CompiledToExecuteRel.precompiled]

theorem CompiledAccountMapRel.toExecute_code_of_find_yul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {addr : EvmYul.AccountAddress} {yulAccount : EvmYul.Account .Yul}
    (hNotPrecompile :
      EvmYul.PrecompiledContract.ofAddress? addr = none)
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

theorem CompiledAccountMapRel.toExecute
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (addr : EvmYul.AccountAddress) :
    CompiledToExecuteRel
      (EvmYul.toExecute .Yul yul addr)
      (EvmYul.toExecute .EVM evm addr) := by
  cases hPrecompile : EvmYul.PrecompiledContract.ofAddress? addr with
  | some precompiled =>
      exact CompiledAccountMapRel.toExecute_precompiled hPrecompile
  | none =>
      simp [EvmYul.toExecute, hPrecompile]
      cases hYul : yul.find? addr with
      | none =>
          have hEvm := hWorld.not_find_evm_of_not_find_yul hYul
          simp [hEvm]
          exact CompiledToExecuteRel.code CompiledCodeRel.empty
      | some yulAccount =>
          rcases hWorld.find_yul hYul with
            ⟨evmAccount, hEvmFind, hAccount⟩
          simp [hEvmFind]
          exact CompiledToExecuteRel.code hAccount.code

structure CompiledPrecompileResultRel
    (yulRes :
      Bool × EvmYul.AccountMap .Yul × EvmYul.UInt256 ×
        EvmYul.Substate × ByteArray)
    (evmRes :
      Bool × EvmYul.AccountMap .EVM × EvmYul.UInt256 ×
        EvmYul.Substate × ByteArray) : Prop where
  success : yulRes.1 = evmRes.1
  accountMap : CompiledAccountMapRel yulRes.2.1 evmRes.2.1
  gas : yulRes.2.2.1 = evmRes.2.2.1
  substate : yulRes.2.2.2.1 = evmRes.2.2.2.1
  output : yulRes.2.2.2.2 = evmRes.2.2.2.2

theorem CompiledPrecompileResultRel.same
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    (success : Bool) (gas : EvmYul.UInt256)
    (substate : EvmYul.Substate) (output : ByteArray) :
    CompiledPrecompileResultRel
      (success, yul, gas, substate, output)
      (success, evm, gas, substate, output) :=
  ⟨rfl, hWorld, rfl, rfl, rfl⟩

theorem CompiledPrecompileResultRel.empty
    (success : Bool) (gas : EvmYul.UInt256)
    (substate : EvmYul.Substate) (output : ByteArray) :
    CompiledPrecompileResultRel
      (success, (∅ : EvmYul.AccountMap .Yul), gas, substate, output)
      (success, (∅ : EvmYul.AccountMap .EVM), gas, substate, output) :=
  ⟨rfl, CompiledAccountMapRel.empty, rfl, rfl, rfl⟩

theorem CompiledPrecompileResultRel.accountMap_merge
    {yulParent : EvmYul.AccountMap .Yul}
    {evmParent : EvmYul.AccountMap .EVM}
    {yulRes :
      Bool × EvmYul.AccountMap .Yul × EvmYul.UInt256 ×
        EvmYul.Substate × ByteArray}
    {evmRes :
      Bool × EvmYul.AccountMap .EVM × EvmYul.UInt256 ×
        EvmYul.Substate × ByteArray}
    (hParent : CompiledAccountMapRel yulParent evmParent)
    (hResult : CompiledPrecompileResultRel yulRes evmRes) :
    CompiledAccountMapRel
      (if yulRes.2.1.isEmpty then yulParent else yulRes.2.1)
      (if evmRes.2.1.isEmpty then evmParent else evmRes.2.1) := by
  exact
    CompiledAccountMapRel.if_empty_parent
      hParent hResult.accountMap hResult.accountMap.isEmpty_eq

theorem runPrecompiledContract_substate
    {τ : EvmYul.OperationType} (precompiled : EvmYul.PrecompiledContract)
    (accountMap : EvmYul.AccountMap τ) (gas : EvmYul.UInt256)
    (substate : EvmYul.Substate) (env : EvmYul.ExecutionEnv τ) :
    (runPrecompiledContract precompiled accountMap gas substate env).2.2.2.1 =
      substate := by
  cases precompiled
  · by_cases hGas : gas.toNat < 3000
    · simp [runPrecompiledContract, Ξ_ECREC, hGas]
    · simp [runPrecompiledContract, Ξ_ECREC, hGas]
  · by_cases hGas :
        gas.toNat < 60 + 12 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_SHA256, hGas]
    · simp [runPrecompiledContract, Ξ_SHA256, hGas, dbgTrace]
  · by_cases hGas :
        gas.toNat < 600 + 120 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_RIP160, hGas]
    · simp [runPrecompiledContract, Ξ_RIP160, hGas, dbgTrace]
  · by_cases hGas :
        gas.toNat < 15 + 3 * ((env.calldata.size + 31) / 32)
    · simp [runPrecompiledContract, Ξ_ID, hGas]
    · simp [runPrecompiledContract, Ξ_ID, hGas]
  · by_cases hGas : gas.toNat < Ξ_EXPMOD_gasCost env.calldata
    · simp [runPrecompiledContract, Ξ_EXPMOD, hGas]
    · simp [runPrecompiledContract, Ξ_EXPMOD, hGas]
  · by_cases hGas : gas.toNat < 150
    · simp [runPrecompiledContract, Ξ_BN_ADD, hGas]
    · simp [runPrecompiledContract, Ξ_BN_ADD, hGas]
      cases hBN : BN_ADD (env.calldata.readBytes 0 32)
          (env.calldata.readBytes 32 32)
          (env.calldata.readBytes 64 32)
          (env.calldata.readBytes 96 32) with
      | ok output => simp
      | error err => simp [dbgTrace]
  · by_cases hGas : gas.toNat < 6000
    · simp [runPrecompiledContract, Ξ_BN_MUL, hGas]
    · simp [runPrecompiledContract, Ξ_BN_MUL, hGas]
      cases hBN : BN_MUL (env.calldata.readBytes 0 32)
          (env.calldata.readBytes 32 32)
          (env.calldata.readBytes 64 32) with
      | ok output => simp
      | error err => simp [dbgTrace]
  · by_cases hGas :
        gas.toNat < 34000 * (env.calldata.size / 192) + 45000
    · simp [runPrecompiledContract, Ξ_SNARKV, hGas]
    · simp [runPrecompiledContract, Ξ_SNARKV, hGas]
      cases hSNARK : SNARKV env.calldata with
      | ok output => simp
      | error err => simp [dbgTrace]
  · by_cases hGas :
        gas.toNat <
          EvmYul.fromByteArrayBigEndian (env.calldata.extract 0 4)
    · simp [runPrecompiledContract, Ξ_BLAKE2_F, hGas, dbgTrace]
    · simp [runPrecompiledContract, Ξ_BLAKE2_F, hGas]
      cases hBLAKE : ffi.BLAKE2 env.calldata with
      | ok output => simp
      | error err => simp [dbgTrace]
  · by_cases hGas : gas.toNat < 50000
    · simp [runPrecompiledContract, Ξ_PointEval, hGas]
    · simp [runPrecompiledContract, Ξ_PointEval, hGas]
      cases hPoint : PointEval env.calldata with
      | ok output => simp
      | error err => simp [dbgTrace]

theorem runPrecompiledContract_substate_merge_of_eq
    {precompiled : EvmYul.PrecompiledContract}
    {yulAccountMap : EvmYul.AccountMap .Yul}
    {evmAccountMap : EvmYul.AccountMap .EVM}
    {yulSubstate evmSubstate : EvmYul.Substate}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    (gas : EvmYul.UInt256)
    (hSubstate : yulSubstate = evmSubstate) :
    (runPrecompiledContract precompiled yulAccountMap gas
        yulSubstate yulEnv).2.2.2.1 =
      if (runPrecompiledContract precompiled evmAccountMap gas
          evmSubstate evmEnv).2.1.isEmpty then
        evmSubstate
      else
        (runPrecompiledContract precompiled evmAccountMap gas
          evmSubstate evmEnv).2.2.2.1 := by
  rw [runPrecompiledContract_substate]
  by_cases hEmpty :
      (runPrecompiledContract precompiled evmAccountMap gas
        evmSubstate evmEnv).2.1.isEmpty
  · simp [hEmpty, hSubstate]
  · rw [runPrecompiledContract_substate]
    simp [hEmpty, hSubstate]

theorem CompiledAccountMapRel.precompile_ecrec
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_ECREC yul gas substate yI)
      (Ξ_ECREC evm gas substate eI) := by
  by_cases hGas : gas.toNat < 3000
  · simp [Ξ_ECREC, hGas]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_ECREC, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas - EvmYul.UInt256.ofNat 3000) substate _

theorem CompiledAccountMapRel.precompile_sha256
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_SHA256 yul gas substate yI)
      (Ξ_SHA256 evm gas substate eI) := by
  by_cases hGas : gas.toNat < 60 + 12 * ((eI.calldata.size + 31) / 32)
  · simp [Ξ_SHA256, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_SHA256, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas -
          EvmYul.UInt256.ofNat (60 + 12 * ((eI.calldata.size + 31) / 32)))
        substate _

theorem CompiledAccountMapRel.precompile_rip160
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_RIP160 yul gas substate yI)
      (Ξ_RIP160 evm gas substate eI) := by
  by_cases hGas : gas.toNat < 600 + 120 * ((eI.calldata.size + 31) / 32)
  · simp [Ξ_RIP160, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_RIP160, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas -
          EvmYul.UInt256.ofNat
            (600 + 120 * ((eI.calldata.size + 31) / 32)))
        substate _

theorem CompiledAccountMapRel.precompile_id
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_ID yul gas substate yI)
      (Ξ_ID evm gas substate eI) := by
  by_cases hGas : gas.toNat < 15 + 3 * ((eI.calldata.size + 31) / 32)
  · simp [Ξ_ID, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_ID, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas -
          EvmYul.UInt256.ofNat (15 + 3 * ((eI.calldata.size + 31) / 32)))
        substate eI.calldata

theorem CompiledAccountMapRel.precompile_expmod
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_EXPMOD yul gas substate yI)
      (Ξ_EXPMOD evm gas substate eI) := by
  by_cases hGas : gas.toNat < Ξ_EXPMOD_gasCost eI.calldata
  · simp [Ξ_EXPMOD, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_EXPMOD, hGas, hCalldata]
    exact
      CompiledPrecompileResultRel.same hWorld true
        (gas -
          EvmYul.UInt256.ofNat (Ξ_EXPMOD_gasCost eI.calldata))
        substate (Ξ_EXPMOD_output eI.calldata)

theorem CompiledAccountMapRel.precompile_bn_add
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_BN_ADD yul gas substate yI)
      (Ξ_BN_ADD evm gas substate eI) := by
  by_cases hGas : gas.toNat < 150
  · simp [Ξ_BN_ADD, hGas]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_BN_ADD, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas - EvmYul.UInt256.ofNat 150) substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.precompile_bn_mul
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_BN_MUL yul gas substate yI)
      (Ξ_BN_MUL evm gas substate eI) := by
  by_cases hGas : gas.toNat < 6000
  · simp [Ξ_BN_MUL, hGas]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_BN_MUL, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas - EvmYul.UInt256.ofNat 6000) substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.precompile_snarkv
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_SNARKV yul gas substate yI)
      (Ξ_SNARKV evm gas substate eI) := by
  by_cases hGas : gas.toNat < 34000 * (eI.calldata.size / 192) + 45000
  · simp [Ξ_SNARKV, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_SNARKV, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas -
            EvmYul.UInt256.ofNat
              (34000 * (eI.calldata.size / 192) + 45000))
          substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.precompile_blake2_f
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_BLAKE2_F yul gas substate yI)
      (Ξ_BLAKE2_F evm gas substate eI) := by
  by_cases hGas :
      gas.toNat < EvmYul.fromByteArrayBigEndian (eI.calldata.extract 0 4)
  · simp [Ξ_BLAKE2_F, hGas, hCalldata]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_BLAKE2_F, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas -
            EvmYul.UInt256.ofNat
              (EvmYul.fromByteArrayBigEndian (eI.calldata.extract 0 4)))
          substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.precompile_point_eval
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hCalldata : yI.calldata = eI.calldata)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (Ξ_PointEval yul gas substate yI)
      (Ξ_PointEval evm gas substate eI) := by
  by_cases hGas : gas.toNat < 50000
  · simp [Ξ_PointEval, hGas]
    exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty
  · simp [Ξ_PointEval, hGas, hCalldata]
    split
    · exact
        CompiledPrecompileResultRel.same hWorld true
          (gas - EvmYul.UInt256.ofNat 50000) substate _
    · exact CompiledPrecompileResultRel.empty false ⟨0⟩ substate .empty

theorem CompiledAccountMapRel.runPrecompiledContract_preserve
    {yul : EvmYul.AccountMap .Yul} {evm : EvmYul.AccountMap .EVM}
    (hWorld : CompiledAccountMapRel yul evm)
    {cfg : Reference.StateRelConfig}
    {yI : EvmYul.ExecutionEnv .Yul} {eI : EvmYul.ExecutionEnv .EVM}
    (hEnv : Reference.ExecutionEnvRel cfg yI eI)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledPrecompileResultRel
      (runPrecompiledContract precompiled yul gas substate yI)
      (runPrecompiledContract precompiled evm gas substate eI) := by
  cases precompiled
  · exact hWorld.precompile_ecrec hEnv.calldata gas substate
  · exact hWorld.precompile_sha256 hEnv.calldata gas substate
  · exact hWorld.precompile_rip160 hEnv.calldata gas substate
  · exact hWorld.precompile_id hEnv.calldata gas substate
  · exact hWorld.precompile_expmod hEnv.calldata gas substate
  · exact hWorld.precompile_bn_add hEnv.calldata gas substate
  · exact hWorld.precompile_bn_mul hEnv.calldata gas substate
  · exact hWorld.precompile_snarkv hEnv.calldata gas substate
  · exact hWorld.precompile_blake2_f hEnv.calldata gas substate
  · exact hWorld.precompile_point_eval hEnv.calldata gas substate

theorem CompiledAccountMapRel.runPrecompiledContract_accountMap_merge
    {yulParent : EvmYul.AccountMap .Yul}
    {evmParent : EvmYul.AccountMap .EVM}
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmCallMap : EvmYul.AccountMap .EVM}
    (hParent : CompiledAccountMapRel yulParent evmParent)
    (hCallMap : CompiledAccountMapRel yulCallMap evmCallMap)
    {cfg : Reference.StateRelConfig}
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    (hEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256) (substate : EvmYul.Substate) :
    CompiledAccountMapRel
      (if (runPrecompiledContract precompiled yulCallMap gas
          substate yulEnv).2.1.isEmpty then
        yulParent
      else
        (runPrecompiledContract precompiled yulCallMap gas
          substate yulEnv).2.1)
      (if (runPrecompiledContract precompiled evmCallMap gas
          substate evmEnv).2.1.isEmpty then
        evmParent
      else
        (runPrecompiledContract precompiled evmCallMap gas
          substate evmEnv).2.1) := by
  exact
    CompiledPrecompileResultRel.accountMap_merge hParent
      (hCallMap.runPrecompiledContract_preserve hEnv precompiled gas substate)

theorem buildPrecompiledContractCallState_success_of_evm_run_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (hParentWorld : CompiledAccountMapRel yul.accountMap evm.accountMap)
    (hCfgAccountMap :
      ∀ {yulMap : EvmYul.AccountMap .Yul}
        {evmMap : EvmYul.AccountMap .EVM},
        CompiledAccountMapRel yulMap evmMap →
          cfg.accountMapRel yulMap evmMap)
    (store : EvmYul.Yul.VarStore)
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmCallMap : EvmYul.AccountMap .EVM}
    (hCallMap : CompiledAccountMapRel yulCallMap evmCallMap)
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    (hEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hSuccess :
      (runPrecompiledContract precompiled evmCallMap gas
        evm.substate evmEnv).1 = true)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall
          (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildPrecompiledContractCallState
          (.Ok yul store) yulCallMap precompiled gas yulEnv
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨1⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall
                (runPrecompiledContract precompiled evmCallMap gas
                  evm.substate evmEnv).2.2.2.2
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas }
          accountMap :=
            if (runPrecompiledContract precompiled evmCallMap gas
                evm.substate evmEnv).2.1.isEmpty then
              evm.accountMap
            else
              (runPrecompiledContract precompiled evmCallMap gas
                evm.substate evmEnv).2.1
          substate :=
            if (runPrecompiledContract precompiled evmCallMap gas
                evm.substate evmEnv).2.1.isEmpty then
              evm.substate
            else
              (runPrecompiledContract precompiled evmCallMap gas
                evm.substate evmEnv).2.2.2.1 } := by
  have hParentSubstate : yul.substate = evm.substate := by
    rcases hShared with ⟨hChain, _hMachine⟩
    exact hChain.substate
  have hResult :
      CompiledPrecompileResultRel
        (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv)
        (runPrecompiledContract precompiled evmCallMap gas
          evm.substate evmEnv) := by
    simpa [hParentSubstate] using
      hCallMap.runPrecompiledContract_preserve
        hEnv precompiled gas yul.substate
  have hYulSuccess :
      (runPrecompiledContract precompiled yulCallMap gas
        yul.substate yulEnv).1 = true :=
    hResult.success.trans hSuccess
  have hYulRun :
      runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv =
        (true,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.2) := by
    simpa [hYulSuccess] using
      (show
        runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv =
          ((runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.2.2) from rfl)
  have hAccountMap :
      cfg.accountMapRel
        (if (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.1.isEmpty then
          yul.accountMap
        else
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.1)
        (if (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.1.isEmpty then
          evm.accountMap
        else
          (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.1) :=
    hCfgAccountMap <| by
      simpa [hParentSubstate] using
        hParentWorld.runPrecompiledContract_accountMap_merge
          hCallMap hEnv precompiled gas yul.substate
  have hSubstate :
      (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv).2.2.2.1 =
        if (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.1.isEmpty then
          evm.substate
        else
          (runPrecompiledContract precompiled evmCallMap gas
            evm.substate evmEnv).2.2.2.1 := by
    simpa [hParentSubstate] using
      (runPrecompiledContract_substate_merge_of_eq
        (precompiled := precompiled)
        (yulAccountMap := yulCallMap)
        (evmAccountMap := evmCallMap)
        (yulSubstate := yul.substate)
        (evmSubstate := evm.substate)
        (yulEnv := yulEnv)
        (evmEnv := evmEnv)
        gas hParentSubstate)
  have hOutput :
      (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv).2.2.2.2 =
        (runPrecompiledContract precompiled evmCallMap gas
          evm.substate evmEnv).2.2.2.2 :=
    hResult.output
  have hGasYul :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.2
          inOffset inSize outOffset outSize).gasAvailable
        targetGas := by
    simpa [hOutput] using hGas
  rcases
    buildPrecompiledContractCallState_success_rel
      hShared store
      (precompiled := precompiled)
      (gas := gas)
      (yulEnv := yulEnv)
      (returnData :=
        (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv).2.2.2.2)
      (inOffset := inOffset)
      (inSize := inSize)
      (outOffset := outOffset)
      (outSize := outSize)
      hYulRun hAccountMap hSubstate hGasYul with
    ⟨yulAfter, hBuild, hRel⟩
  refine ⟨yulAfter, hBuild, ?_⟩
  simpa [hOutput] using hRel

theorem buildPrecompiledContractCallState_failure_of_evm_run_rel
    {cfg : Reference.StateRelConfig}
    {yul : EvmYul.SharedState .Yul} {evm : EvmYul.SharedState .EVM}
    (hShared : Reference.SharedStateRel cfg yul evm)
    (store : EvmYul.Yul.VarStore)
    {yulCallMap : EvmYul.AccountMap .Yul}
    {evmCallMap : EvmYul.AccountMap .EVM}
    (hCallMap : CompiledAccountMapRel yulCallMap evmCallMap)
    {yulEnv : EvmYul.ExecutionEnv .Yul}
    {evmEnv : EvmYul.ExecutionEnv .EVM}
    (hEnv : Reference.ExecutionEnvRel cfg yulEnv evmEnv)
    (precompiled : EvmYul.PrecompiledContract)
    (gas : EvmYul.UInt256)
    (inOffset inSize outOffset outSize : EvmYul.UInt256)
    {targetGas : EvmYul.UInt256}
    (hFailure :
      (runPrecompiledContract precompiled evmCallMap gas
        evm.substate evmEnv).1 = false)
    (hGas :
      cfg.gasAvailableRel
        (yul.toMachineState.finishExternalCall ByteArray.empty
          inOffset inSize outOffset outSize).gasAvailable
        targetGas) :
    ∃ yulAfter,
      EvmYul.Yul.buildPrecompiledContractCallState
          (.Ok yul store) yulCallMap precompiled gas yulEnv
          inOffset inSize outOffset outSize =
        .ok (.Ok yulAfter store, [⟨0⟩]) ∧
      Reference.SharedStateRel cfg yulAfter
        { evm with
          toMachineState :=
            { evm.toMachineState.finishExternalCall ByteArray.empty
                inOffset inSize outOffset outSize with
              gasAvailable := targetGas } } := by
  have hParentSubstate : yul.substate = evm.substate := by
    rcases hShared with ⟨hChain, _hMachine⟩
    exact hChain.substate
  have hResult :
      CompiledPrecompileResultRel
        (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv)
        (runPrecompiledContract precompiled evmCallMap gas
          evm.substate evmEnv) := by
    simpa [hParentSubstate] using
      hCallMap.runPrecompiledContract_preserve
        hEnv precompiled gas yul.substate
  have hYulFailure :
      (runPrecompiledContract precompiled yulCallMap gas
        yul.substate yulEnv).1 = false :=
    hResult.success.trans hFailure
  have hYulRun :
      runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv =
        (false,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.1,
          (runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv).2.2.2.2) := by
    simpa [hYulFailure] using
      (show
        runPrecompiledContract precompiled yulCallMap gas
            yul.substate yulEnv =
          ((runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.2.1,
            (runPrecompiledContract precompiled yulCallMap gas
              yul.substate yulEnv).2.2.2.2) from rfl)
  exact
    buildPrecompiledContractCallState_failure_rel
      hShared store
      (precompiled := precompiled)
      (gas := gas)
      (yulEnv := yulEnv)
      (returnData :=
        (runPrecompiledContract precompiled yulCallMap gas
          yul.substate yulEnv).2.2.2.2)
      (inOffset := inOffset)
      (inSize := inSize)
      (outOffset := outOffset)
      (outSize := outSize)
      hYulRun hGas

end World

end Yul
end EvmCompiler
