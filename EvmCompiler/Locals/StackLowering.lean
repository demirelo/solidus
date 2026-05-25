import EvmCompiler.Locals.Syntax

namespace EvmCompiler
namespace Locals

namespace StackLowering

theorem getElem?_append_right_add {α : Type} (left right : List α)
    (idx : Nat) :
    (left ++ right)[left.length + idx]? = right[idx]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem list_eq_take_getElem?_drop {α : Type} {xs : List α}
    {idx : Nat} {value : α}
    (hGet : xs[idx]? = some value) :
    xs = xs.take idx ++ value :: xs.drop (idx + 1) := by
  rcases List.getElem?_eq_some_iff.mp hGet with ⟨hLt, hValue⟩
  have hDrop :
      xs.drop idx = value :: xs.drop (idx + 1) := by
    rw [List.drop_eq_getElem_cons hLt, hValue]
  calc
    xs = xs.take idx ++ xs.drop idx := by
      exact (List.take_append_drop idx xs).symm
    _ = xs.take idx ++ value :: xs.drop (idx + 1) := by
      rw [hDrop]

theorem getElem?_replace_same {α : Type} {xs : List α}
    {idx : Nat} {old value : α}
    (hGet : xs[idx]? = some old) :
    (xs.take idx ++ value :: xs.drop (idx + 1))[idx]? =
      some value := by
  rcases List.getElem?_eq_some_iff.mp hGet with ⟨hLt, _hValue⟩
  have hSet := List.set_eq_take_cons_drop value hLt
  rw [← hSet]
  rw [List.getElem?_set]
  simp [hLt]

theorem getElem?_replace_ne {α : Type} {xs : List α}
    {idx j : Nat} {old value atValue : α}
    (hGetIdx : xs[idx]? = some old)
    (hGetJ : xs[j]? = some atValue)
    (hNe : j ≠ idx) :
    (xs.take idx ++ value :: xs.drop (idx + 1))[j]? =
      some atValue := by
  rcases List.getElem?_eq_some_iff.mp hGetIdx with ⟨hLt, _hValue⟩
  have hSet := List.set_eq_take_cons_drop value hLt
  have hNe' : idx ≠ j := by
    intro hEq
    exact hNe hEq.symm
  rw [← hSet]
  rw [List.getElem?_set]
  simp [hNe', hGetJ]

theorem getElem?_eq_index_of_nodup {α : Type} {xs : List α}
    {i j : Nat} {value : α}
    (hNoDup : xs.Nodup)
    (hi : xs[i]? = some value)
    (hj : xs[j]? = some value) :
    i = j := by
  rcases List.getElem?_eq_some_iff.mp hi with ⟨hiLt, hiValue⟩
  rcases List.getElem?_eq_some_iff.mp hj with ⟨hjLt, hjValue⟩
  exact
    (List.Nodup.getElem_inj_iff hNoDup).mp
      (by rw [hiValue, hjValue])

/--
Source-visible variables embedded in a full compiler stack layout.

This relation belongs to the locals-to-stack lowering proof, not to the pure
locals source semantics.  The source environment is represented only by a
lookup function, so foreign frontends can adapt their own variable stores at
the reference boundary while this module owns the target stack-slot shape.
-/
def VisibleLookupSlotRel (sourceLayout fullLayout : List Name)
    (lookup : Name → Option Word) (stack : EvmYul.Stack Word) : Prop :=
  ∀ {sourceIdx : Nat} {name : Name},
    sourceLayout[sourceIdx]? = some name →
      ∃ fullIdx : Nat, ∃ value : Word,
        fullLayout[fullIdx]? = some name ∧
        stack[fullIdx]? = some value ∧
        lookup name = some value

namespace VisibleLookupSlotRel

theorem cons_source_insert {sourceLayout fullLayout : List Name}
    {lookup lookup' : Name → Option Word} {stack : EvmYul.Stack Word}
    {name : Name} {value : Word}
    (hNew : lookup' name = some value)
    (hPreserve :
      ∀ {sourceName : Name},
        sourceName ∈ sourceLayout → lookup' sourceName = lookup sourceName)
    (hRel : VisibleLookupSlotRel sourceLayout fullLayout lookup stack) :
    VisibleLookupSlotRel (name :: sourceLayout) (name :: fullLayout)
      lookup' (value :: stack) := by
  intro sourceIdx sourceName hSourceName
  cases sourceIdx with
  | zero =>
      simp at hSourceName
      subst sourceName
      exact ⟨0, value, by simp, by simp, hNew⟩
  | succ sourceIdx =>
      have hTailName : sourceLayout[sourceIdx]? = some sourceName := by
        simpa using hSourceName
      rcases hRel hTailName with
        ⟨fullIdx, oldValue, hFullName, hStack, hLookup⟩
      refine ⟨fullIdx + 1, oldValue, ?hFull, ?hStack, ?hLookup⟩
      · simpa using hFullName
      · simpa using hStack
      · rw [hPreserve (List.mem_of_getElem? hTailName)]
        exact hLookup

theorem cons_hidden {sourceLayout fullLayout : List Name}
    {lookup : Name → Option Word} {stack : EvmYul.Stack Word}
    {hiddenName : Name} {hiddenValue : Word}
    (hRel : VisibleLookupSlotRel sourceLayout fullLayout lookup stack) :
    VisibleLookupSlotRel sourceLayout (hiddenName :: fullLayout) lookup
      (hiddenValue :: stack) := by
  intro sourceIdx sourceName hSourceName
  rcases hRel hSourceName with
    ⟨fullIdx, value, hFullName, hStack, hLookup⟩
  exact ⟨fullIdx + 1, value, by simpa using hFullName,
    by simpa using hStack, hLookup⟩

theorem prefix_hidden {sourceLayout fullLayout hiddenLayout : List Name}
    {lookup : Name → Option Word}
    {stack hiddenValues : EvmYul.Stack Word}
    (hHiddenLength : hiddenValues.length = hiddenLayout.length)
    (hRel : VisibleLookupSlotRel sourceLayout fullLayout lookup stack) :
    VisibleLookupSlotRel sourceLayout (hiddenLayout ++ fullLayout) lookup
      (hiddenValues ++ stack) := by
  intro sourceIdx sourceName hSourceName
  rcases hRel hSourceName with
    ⟨fullIdx, value, hFullName, hStack, hLookup⟩
  refine ⟨hiddenLayout.length + fullIdx, value, ?hFull, ?hStackAt,
    hLookup⟩
  · simpa using
      (getElem?_append_right_add hiddenLayout fullLayout fullIdx).trans
        hFullName
  · rw [List.getElem?_append_right]
    · have hSub :
          hiddenLayout.length + fullIdx - hiddenValues.length = fullIdx := by
          omega
      rw [hSub]
      exact hStack
    · simp [hHiddenLength]

theorem assign {sourceLayout fullLayout : List Name}
    {lookup lookup' : Name → Option Word} {stack : EvmYul.Stack Word}
    {name : Name} {value : Word} {sourceIdx targetFullIdx : Nat}
    (hNoDupFull : fullLayout.Nodup)
    (hTargetSource : sourceLayout[sourceIdx]? = some name)
    (hTargetFull : fullLayout[targetFullIdx]? = some name)
    (hLookupTarget : lookup' name = some value)
    (hLookupPreserve :
      ∀ {sourceName : Name},
        sourceName ∈ sourceLayout → sourceName ≠ name →
          lookup' sourceName = lookup sourceName)
    (hRel : VisibleLookupSlotRel sourceLayout fullLayout lookup stack) :
    VisibleLookupSlotRel sourceLayout fullLayout lookup'
      (stack.take targetFullIdx ++ value :: stack.drop (targetFullIdx + 1)) := by
  rcases hRel hTargetSource with
    ⟨targetWitnessIdx, oldTarget, hTargetWitnessFull,
      hTargetWitnessStack, _hTargetLookup⟩
  have hTargetWitnessEq : targetWitnessIdx = targetFullIdx :=
    getElem?_eq_index_of_nodup hNoDupFull hTargetWitnessFull hTargetFull
  subst targetWitnessIdx
  intro sourceIdx' sourceName hSourceName
  by_cases hSame : sourceName = name
  · subst sourceName
    refine
      ⟨targetFullIdx, value, hTargetFull, ?hStack, hLookupTarget⟩
    exact getElem?_replace_same hTargetWitnessStack
  · rcases hRel hSourceName with
      ⟨fullIdx, slotValue, hFullName, hStackAt, hLookup⟩
    have hNeIdx : fullIdx ≠ targetFullIdx := by
      intro hEq
      subst fullIdx
      have hNameEq : sourceName = name := by
        rw [hTargetFull] at hFullName
        cases hFullName
        rfl
      exact hSame hNameEq
    refine ⟨fullIdx, slotValue, hFullName, ?hStackAt, ?hLookup⟩
    · exact getElem?_replace_ne hTargetWitnessStack hStackAt hNeIdx
    · rw [hLookupPreserve (List.mem_of_getElem? hSourceName) hSame]
      exact hLookup

end VisibleLookupSlotRel

end StackLowering

end Locals
end EvmCompiler
