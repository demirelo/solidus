import EvmCompiler.Yul.Compiler
import EvmCompiler.Locals.Preservation

namespace EvmCompiler
namespace Yul

namespace ArgSlots

/--
A named value at a concrete compiler-layout slot.

This is target-side evidence for compiler-generated temporaries and ordinary
locals. It deliberately does not mention imported Yul source states.
-/
def LayoutSlotValue (fullLayout : List Name) (stack : EvmYul.Stack Word)
    (name : Name) (value : Word) : Prop :=
  ∃ idx : Nat, fullLayout[idx]? = some name ∧ stack[idx]? = some value

/--
Source-order argument values stored in compiler locals.

Every expression is a generated/readable local variable whose declared layout
slot contains the corresponding source-order value. Imported-Yul argument
scheduling is proved in `Yul.Reference`; target stack replay from this evidence
is lower and independent of the reference interpreter.
-/
inductive Values (layout : List Name) (stack : EvmYul.Stack Word) :
    List (Locals.Expr 1) → List Word → Prop where
  | nil : Values layout stack [] []
  | cons_var {name : Name} {rest : List (Locals.Expr 1)}
      {value : Word} {values : List Word}
      (hSlot : LayoutSlotValue layout stack name value)
      (hTail : Values layout stack rest values) :
      Values layout stack (.var name :: rest) (value :: values)

namespace Values

theorem varSlotValuesAt_seqCast
    {layout : List Name} {stack : EvmYul.Stack Word}
    {m n offset : Nat} {seq : Locals.ExprSeq m} {values : List Word}
    (h : m = n)
    (hValues :
      Locals.ExprSeq.VarSlotValuesAt layout stack offset seq values) :
    Locals.ExprSeq.VarSlotValuesAt layout stack offset
      (Expr.seqCast h seq) values := by
  cases h
  simpa [Expr.seqCast] using hValues

theorem map_layout {layout layout' : List Name}
    {stack stack' : EvmYul.Stack Word}
    {exprs : List (Locals.Expr 1)} {values : List Word}
    (hMap :
      ∀ {name value},
        LayoutSlotValue layout stack name value →
          LayoutSlotValue layout' stack' name value)
    (hArgs : Values layout stack exprs values) :
    Values layout' stack' exprs values := by
  induction hArgs with
  | nil =>
      exact Values.nil
  | cons_var hSlot _hTail ih =>
      exact Values.cons_var (hMap hSlot) ih

theorem length_eq {layout : List Name}
    {stack : EvmYul.Stack Word}
    {exprs : List (Locals.Expr 1)} {values : List Word}
    (hArgs : Values layout stack exprs values) :
    exprs.length = values.length := by
  induction hArgs with
  | nil =>
      rfl
  | cons_var _hSlot _hTail ih =>
      simp [ih]

theorem all_vars {layout : List Name}
    {stack : EvmYul.Stack Word}
    {exprs : List (Locals.Expr 1)} {values : List Word}
    (hArgs : Values layout stack exprs values) :
    ∀ {expr : Locals.Expr 1},
      expr ∈ exprs → ∃ name : Name, expr = .var name := by
  intro expr hMem
  induction hArgs with
  | nil =>
      simp at hMem
  | @cons_var name rest value values hSlot hTail ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst expr
          exact ⟨name, rfl⟩
      | inr hTailMem =>
          exact ih hTailMem

theorem singleton {layout : List Name}
    {stack : EvmYul.Stack Word} {name : Name} {value : Word}
    (hSlot : LayoutSlotValue layout stack name value) :
    Values layout stack [.var name] [value] :=
  Values.cons_var hSlot Values.nil

theorem append {layout : List Name}
    {stack : EvmYul.Stack Word}
    {left right : List (Locals.Expr 1)}
    {leftValues rightValues : List Word}
    (hLeft : Values layout stack left leftValues)
    (hRight : Values layout stack right rightValues) :
    Values layout stack (left ++ right)
      (leftValues ++ rightValues) := by
  induction hLeft with
  | nil =>
      simpa using hRight
  | cons_var hSlot _hTail ih =>
      simpa using Values.cons_var hSlot ih

theorem reverse {layout : List Name}
    {stack : EvmYul.Stack Word}
    {exprs : List (Locals.Expr 1)} {values : List Word}
    (hArgs : Values layout stack exprs values) :
    Values layout stack exprs.reverse values.reverse := by
  induction hArgs with
  | nil =>
      exact Values.nil
  | cons_var hSlot _hTail ih =>
      simpa [List.reverse_cons] using
        Values.append ih (Values.singleton hSlot)

theorem toVarSlotValuesAt_of_toSeq?
    {layout : List Name} {stack : EvmYul.Stack Word}
    {exprs : List (Locals.Expr 1)} {values : List Word}
    {offset results : Nat} {seq : Locals.ExprSeq results}
    (hSlots : Values layout stack exprs values)
    (hSeq : Expr.List.toSeq? exprs results = some seq)
    (hBound :
      ∀ {pos : Nat} {name : Name} {idx : Nat},
        exprs[pos]? = some (.var name) →
          layout[idx]? = some name →
            offset + pos + idx + 1 ≤ 16) :
    Locals.ExprSeq.VarSlotValuesAt layout stack offset seq values := by
  induction hSlots generalizing offset results seq with
  | nil =>
      cases results with
      | zero =>
          simp [Expr.List.toSeq?] at hSeq
          cases hSeq
          exact Locals.ExprSeq.VarSlotValuesAt.nil
      | succ results =>
          simp [Expr.List.toSeq?] at hSeq
  | @cons_var name rest value values hSlot hTail ih =>
      cases results with
      | zero =>
          simp [Expr.List.toSeq?] at hSeq
      | succ results =>
          cases hTailSeq : Expr.List.toSeq? rest results with
          | none =>
              simp [Expr.List.toSeq?, hTailSeq] at hSeq
          | some tailSeq =>
              simp [Expr.List.toSeq?, hTailSeq, Expr.seqCast] at hSeq
              cases hSeq
              rcases hSlot with ⟨idx, hName, hStack⟩
              have hHeadBound : offset + idx + 1 ≤ 16 := by
                simpa [Nat.add_assoc] using
                  (hBound (pos := 0) (idx := idx) (by simp) hName)
              have hTailBound :
                  ∀ {pos : Nat} {tailName : Name} {tailIdx : Nat},
                    rest[pos]? = some (.var tailName) →
                      layout[tailIdx]? = some tailName →
                        offset + 1 + pos + tailIdx + 1 ≤ 16 := by
                intro pos tailName tailIdx hExpr hLayout
                have hBound' :=
                  hBound (pos := pos + 1) (idx := tailIdx)
                    (by simpa using hExpr) hLayout
                omega
              exact
                varSlotValuesAt_seqCast
                  (by simp [Nat.add_comm])
                  (Locals.ExprSeq.VarSlotValuesAt.cons_var hName hStack
                    hHeadBound
                    (ih (offset := offset + 1) (results := results)
                      (seq := tailSeq) hTailSeq hTailBound))

theorem runCode_toSeq
    (ctx : Locals.Ctx) (baseState currentState : EVMState)
    (layout : List Name) (offset : Nat) (pushed : List Word)
    {exprs : List (Locals.Expr 1)} {values : List Word}
    {results : Nat} {seq : Locals.ExprSeq results}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hCurrentStack : currentState.stack = pushed ++ baseState.stack)
    (hPushedLen : pushed.length = offset)
    (hSlots : Values layout baseState.stack exprs values)
    (hSeq : Expr.List.toSeq? exprs results = some seq)
    (hBound :
      ∀ {pos : Nat} {name : Name} {idx : Nat},
        exprs[pos]? = some (.var name) →
          layout[idx]? = some name →
            offset + pos + idx + 1 ≤ 16) :
    ∃ finalState : EVMState,
      Locals.Direct.Expr.ExprSeq.runCode ctx offset seq currentState =
        .ok finalState ∧
      finalState.stack = values.reverse ++ pushed ++ baseState.stack ∧
      finalState.toSharedState = currentState.toSharedState := by
  exact
    Locals.Direct.Expr.ExprSeq.runCode_of_varSlotValuesAt ctx baseState
      currentState layout offset pushed hCtxLayout hNoDup hCurrentStack
      hPushedLen
      (Values.toVarSlotValuesAt_of_toSeq? hSlots hSeq hBound)

theorem runCode_toStackSeq
    (ctx : Locals.Ctx) (baseState currentState : EVMState)
    (layout : List Name) (offset : Nat) (pushed : List Word)
    {exprs : List (Locals.Expr 1)} {values : List Word}
    {results : Nat} {seq : Locals.ExprSeq results}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hCurrentStack : currentState.stack = pushed ++ baseState.stack)
    (hPushedLen : pushed.length = offset)
    (hSlots : Values layout baseState.stack exprs values)
    (hSeq : Expr.List.toStackSeq? exprs results = some seq)
    (hBound :
      ∀ {pos : Nat} {name : Name} {idx : Nat},
        exprs.reverse[pos]? = some (.var name) →
          layout[idx]? = some name →
            offset + pos + idx + 1 ≤ 16) :
    ∃ finalState : EVMState,
      Locals.Direct.Expr.ExprSeq.runCode ctx offset seq currentState =
        .ok finalState ∧
      finalState.stack = values ++ pushed ++ baseState.stack ∧
      finalState.toSharedState = currentState.toSharedState := by
  have hSeq' : Expr.List.toSeq? exprs.reverse results = some seq := by
    simpa [Expr.List.toStackSeq?] using hSeq
  rcases
      Values.runCode_toSeq ctx baseState currentState layout offset pushed
        hCtxLayout hNoDup hCurrentStack hPushedLen
        (Values.reverse hSlots) hSeq' hBound with
    ⟨finalState, hRun, hStack, hShared⟩
  exact
    ⟨finalState, hRun, by simpa using hStack, hShared⟩

end Values

end ArgSlots

end Yul
end EvmCompiler
