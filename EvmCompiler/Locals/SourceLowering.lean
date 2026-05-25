import EvmCompiler.Locals.SourceSemantics
import EvmCompiler.Locals.Semantics
import EvmCompiler.Locals.StackLowering
import EvmCompiler.Locals.Preservation

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace EvmCompiler
namespace Locals

/-
Source-to-backend relation for the locals abstraction.

This file is deliberately about the lowering boundary.  The stack-free
`Locals.Source` interpreter above does not mention stack slots or cleanup
depths; this module owns the facts that relate those source notions to the
existing stack-shaped `Locals.Direct` backend.
-/
namespace SourceLowering

def CtxRel (source : Source.Ctx) (target : Ctx) : Prop :=
  target.layout = source.scope ∧
    target.breakDepth? = source.breakScope?.map List.length ∧
    target.continueDepth? = source.continueScope?.map List.length ∧
    target.leaveDepth? = source.leaveScope?.map List.length ∧
    target.leaveRetc = 0

namespace CtxRel

theorem initial :
    CtxRel Source.Ctx.initial Ctx.initial := by
  simp [CtxRel, Source.Ctx.initial, Ctx.initial]

theorem withoutLoopControl {source : Source.Ctx} {target : Ctx}
    (hRel : CtxRel source target) :
    CtxRel source.withoutLoopControl target.withoutLoopControl := by
  rcases hRel with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  simp [CtxRel, Source.Ctx.withoutLoopControl, Ctx.withoutLoopControl,
    hLayout, hBreak, hContinue, hLeave, hRetc]

theorem withLoopControl_self {source : Source.Ctx} {target : Ctx}
    (hRel : CtxRel source target) :
    CtxRel (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) := by
  rcases hRel with ⟨hLayout, _hBreak, _hContinue, hLeave, hRetc⟩
  simp [CtxRel, Source.Ctx.withLoopControl, Ctx.withLoopControl, hLayout,
    hLeave, hRetc]

theorem withLeaveScope_self {source : Source.Ctx} {target : Ctx}
    (hRel : CtxRel source target) :
    CtxRel (source.withLeaveScope source.scope)
      { target with leaveDepth? := some target.layout.length } := by
  rcases hRel with ⟨hLayout, hBreak, hContinue, _hLeave, hRetc⟩
  simp [CtxRel, Source.Ctx.withLeaveScope, hLayout, hBreak, hContinue, hRetc]

theorem withScopeCons {source : Source.Ctx} {target : Ctx}
    {name : Name}
    (hRel : CtxRel source target) :
    CtxRel { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) := by
  rcases hRel with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  simp [CtxRel, Ctx.withLayout, hLayout, hBreak, hContinue, hLeave, hRetc]

end CtxRel

/--
The exact concrete suffix retained by cleaning a target layout down to a source
handler scope.  This is lower-proof evidence: source semantics only mentions
the handler scope, while the direct backend realizes it by popping stack slots.
-/
def CleanupScopeRel (layout scope : List Name) : Prop :=
  layout.drop (layout.length - scope.length) = scope

namespace CleanupScopeRel

theorem refl (layout : List Name) :
    CleanupScopeRel layout layout := by
  simp [CleanupScopeRel]

theorem cons {layout scope : List Name} {name : Name}
    (hRel : CleanupScopeRel layout scope) :
    CleanupScopeRel (name :: layout) scope := by
  have hLen : scope.length ≤ layout.length := by
    have hLength := congrArg List.length hRel
    simp [CleanupScopeRel] at hLength
    omega
  have hDrop :
      (name :: layout).drop ((name :: layout).length - scope.length) =
        layout.drop (layout.length - scope.length) := by
    have hSub :
        (name :: layout).length - scope.length =
          (layout.length - scope.length) + 1 := by
      simp
      omega
    rw [hSub]
    simp
  rw [CleanupScopeRel, hDrop]
  exact hRel

theorem depth_le {layout scope : List Name}
    (hRel : CleanupScopeRel layout scope) :
    scope.length ≤ layout.length := by
  have hLength := congrArg List.length hRel
  simp [CleanupScopeRel] at hLength
  omega

theorem trans {outer middle inner : List Name}
    (hOuter : CleanupScopeRel outer middle)
    (hMiddle : CleanupScopeRel middle inner) :
    CleanupScopeRel outer inner := by
  have hMiddleLen : inner.length ≤ middle.length :=
    CleanupScopeRel.depth_le hMiddle
  have hOuterLen : middle.length ≤ outer.length :=
    CleanupScopeRel.depth_le hOuter
  have hSum :
      outer.length - inner.length =
        (outer.length - middle.length) + (middle.length - inner.length) := by
    omega
  unfold CleanupScopeRel at hOuter hMiddle ⊢
  rw [hSum, ← List.drop_drop, hOuter, hMiddle]

end CleanupScopeRel

namespace Scope

theorem stmt_outEnv_cleanupScopeRel (env : List Name) (stmt : Stmt) :
    CleanupScopeRel (Scope.Stmt.outEnv env stmt) env := by
  cases stmt <;> simp [Scope.Stmt.outEnv]
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.cons (CleanupScopeRel.refl env)
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env
  · exact CleanupScopeRel.refl env

theorem stmtList_outEnv_cleanupScopeRel :
    ∀ (env : List Name) (stmts : List Stmt),
      CleanupScopeRel (Scope.StmtList.outEnv env stmts) env
  | env, [] => by
      simp [Scope.StmtList.outEnv, CleanupScopeRel.refl]
  | env, stmt :: rest => by
      exact
        CleanupScopeRel.trans
          (stmtList_outEnv_cleanupScopeRel (Scope.Stmt.outEnv env stmt) rest)
          (stmt_outEnv_cleanupScopeRel env stmt)

theorem block_outEnv_cleanupScopeRel (env : List Name) (block : Block) :
    CleanupScopeRel (Scope.Block.outEnv env block) env := by
  cases block with
  | mk stmts =>
      exact stmtList_outEnv_cleanupScopeRel env stmts

end Scope

/--
Lowering-side handler invariant for source contexts.

`CtxRel` records the numeric cleanup depths used by the direct backend.
`CtxHandlersRel` records the stronger fact needed by preservation: cleaning to
those depths keeps exactly the source handler scopes.  Keeping this separate
lets the source semantics stay a named-scope semantics.
-/
def CtxHandlersRel (source : Source.Ctx) (target : Ctx) : Prop :=
  (∀ scope, source.breakScope? = some scope →
    CleanupScopeRel target.layout scope) ∧
  (∀ scope, source.continueScope? = some scope →
    CleanupScopeRel target.layout scope) ∧
  (∀ scope, source.leaveScope? = some scope →
    CleanupScopeRel target.layout scope)

namespace CtxHandlersRel

theorem initial :
    CtxHandlersRel Source.Ctx.initial Ctx.initial := by
  simp [CtxHandlersRel, Source.Ctx.initial]

theorem withoutLoopControl {source : Source.Ctx} {target : Ctx}
    (hRel : CtxHandlersRel source target) :
    CtxHandlersRel source.withoutLoopControl target.withoutLoopControl := by
  rcases hRel with ⟨_hBreak, _hContinue, hLeave⟩
  refine ⟨?_, ?_, ?_⟩
  · intro scope h
    simp [Source.Ctx.withoutLoopControl] at h
  · intro scope h
    simp [Source.Ctx.withoutLoopControl] at h
  · intro scope h
    exact hLeave scope (by simpa [Source.Ctx.withoutLoopControl] using h)

theorem withLoopControl_self {source : Source.Ctx} {target : Ctx}
    (hCtx : CtxRel source target)
    (hRel : CtxHandlersRel source target) :
    CtxHandlersRel (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) := by
  rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
  rcases hRel with ⟨_hBreakRel, _hContinueRel, hLeaveRel⟩
  refine ⟨?_, ?_, ?_⟩
  · intro scope h
    simp [Source.Ctx.withLoopControl] at h
    subst scope
    simpa [hLayout, Ctx.withLoopControl] using
      (CleanupScopeRel.refl target.layout)
  · intro scope h
    simp [Source.Ctx.withLoopControl] at h
    subst scope
    simpa [hLayout, Ctx.withLoopControl] using
      (CleanupScopeRel.refl target.layout)
  · intro scope h
    exact hLeaveRel scope
      (by simpa [Source.Ctx.withLoopControl] using h)

theorem withScopeCons {source : Source.Ctx} {target : Ctx}
    {name : Name}
    (hRel : CtxHandlersRel source target) :
    CtxHandlersRel { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) := by
  rcases hRel with ⟨hBreak, hContinue, hLeave⟩
  refine ⟨?_, ?_, ?_⟩
  · intro scope h
    exact CleanupScopeRel.cons
      (hBreak scope (by simpa [Ctx.withLayout] using h))
  · intro scope h
    exact CleanupScopeRel.cons
      (hContinue scope (by simpa [Ctx.withLayout] using h))
  · intro scope h
    exact CleanupScopeRel.cons
      (hLeave scope (by simpa [Ctx.withLayout] using h))

end CtxHandlersRel

structure CtxInv (source : Source.Ctx) (target : Ctx) : Prop where
  rel : CtxRel source target
  handlers : CtxHandlersRel source target
  nodup : source.scope.Nodup

def StackStoreRel (layout : List Name) (store : Source.Store)
    (stack : EvmYul.Stack Word) : Prop :=
  stack.length = layout.length ∧
    ∀ {idx : Nat} {name : Name},
      layout[idx]? = some name → stack[idx]? = store name

namespace StackStoreRel

theorem nil :
    StackStoreRel [] Source.Store.empty [] := by
  simp [StackStoreRel]

theorem cons_insert {layout : List Name} {store : Source.Store}
    {stack : EvmYul.Stack Word} {name : Name} {value : Word}
    (hFresh : name ∉ layout)
    (hRel : StackStoreRel layout store stack) :
    StackStoreRel (name :: layout) (Source.Store.insert store name value)
      (value :: stack) := by
  rcases hRel with ⟨hLen, hLookup⟩
  constructor
  · simp [hLen]
  · intro idx sourceName hLayout
    cases idx with
    | zero =>
        simp at hLayout
        subst sourceName
        simp [Source.Store.insert]
    | succ idx =>
        have hTail : layout[idx]? = some sourceName := by
          simpa using hLayout
        have hNe : sourceName ≠ name := by
          intro hEq
          subst sourceName
          exact hFresh (List.mem_of_getElem? hTail)
        simp [hLookup hTail, Source.Store.insert, hNe]

theorem restrictTo_suffix {pre scope : List Name}
    {store : Source.Store} {stack : EvmYul.Stack Word}
    (hRel : StackStoreRel (pre ++ scope) store stack) :
    StackStoreRel scope (Source.Store.restrictTo scope store)
      (stack.drop pre.length) := by
  rcases hRel with ⟨hLen, hLookup⟩
  constructor
  · simp [List.length_drop, hLen]
  · intro idx name hLayout
    have hCombined :
        (pre ++ scope)[pre.length + idx]? = some name := by
      exact (StackLowering.getElem?_append_right_add pre scope idx).trans
        hLayout
    have hStack := hLookup hCombined
    rw [List.getElem?_drop]
    simpa [Source.Store.restrictTo, List.mem_of_getElem? hLayout] using hStack

theorem restrictTo_self {layout : List Name}
    {store : Source.Store} {stack : EvmYul.Stack Word}
    (hRel : StackStoreRel layout store stack) :
    StackStoreRel layout (Source.Store.restrictTo layout store) stack := by
  rcases hRel with ⟨hLen, hLookup⟩
  constructor
  · exact hLen
  · intro idx name hLayout
    have hMem : name ∈ layout :=
      List.mem_of_getElem? hLayout
    simpa [Source.Store.restrictTo, hMem] using hLookup hLayout

theorem lookup_value {layout : List Name} {store : Source.Store}
    {stack : EvmYul.Stack Word} {idx : Nat} {name : Name}
    (hRel : StackStoreRel layout store stack)
    (hName : layout[idx]? = some name) :
    ∃ value : Word, stack[idx]? = some value ∧ store name = some value := by
  rcases hRel with ⟨hLen, hLookup⟩
  rcases List.getElem?_eq_some_iff.mp hName with ⟨hIdxLtLayout, _hName⟩
  have hIdxLtStack : idx < stack.length := by
    omega
  cases hStackAt : stack[idx]? with
  | none =>
      have hNone := List.getElem?_eq_none_iff.mp hStackAt
      omega
  | some value =>
      have hLookupAt := hLookup hName
      rw [hStackAt] at hLookupAt
      exact ⟨value, rfl, hLookupAt.symm⟩

theorem contains_of_layout {layout : List Name} {store : Source.Store}
    {stack : EvmYul.Stack Word} {idx : Nat} {name : Name}
    (hRel : StackStoreRel layout store stack)
    (hName : layout[idx]? = some name) :
    store.contains name = true := by
  rcases lookup_value hRel hName with ⟨value, _hStack, hStore⟩
  simp [Source.Store.contains, hStore]

theorem assign {layout : List Name} {store : Source.Store}
    {stack : EvmYul.Stack Word} {name : Name} {value : Word}
    {idx : Nat}
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hRel : StackStoreRel layout store stack) :
    StackStoreRel layout (Source.Store.insert store name value)
      (stack.take idx ++ value :: stack.drop (idx + 1)) := by
  rcases hRel with ⟨hLen, hLookup⟩
  rcases lookup_value ⟨hLen, hLookup⟩ hName with
    ⟨old, hStackOld, _hStoreOld⟩
  constructor
  · rcases List.getElem?_eq_some_iff.mp hStackOld with ⟨hLt, _hOld⟩
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hLt), hLen]
    omega
  · intro j sourceName hLayout
    by_cases hSame : sourceName = name
    · subst sourceName
      have hEq : j = idx :=
        StackLowering.getElem?_eq_index_of_nodup hNoDup hLayout hName
      subst j
      simp [Source.Store.insert]
      exact StackLowering.getElem?_replace_same hStackOld
    · rcases lookup_value ⟨hLen, hLookup⟩ hLayout with
        ⟨oldAtJ, hStackAtJ, hStoreAtJ⟩
      have hNeIdx : j ≠ idx := by
        intro hEq
        subst j
        have hNameEq : sourceName = name := by
          rw [hName] at hLayout
          cases hLayout
          rfl
        exact hSame hNameEq
      simpa [Source.Store.insert, hSame, hStoreAtJ] using
        (StackLowering.getElem?_replace_ne (value := value)
          hStackOld hStackAtJ hNeIdx)

end StackStoreRel

namespace Cleanup

theorem run_replicate_pop_exists (state : EVMState) :
    ∀ n, n ≤ state.stack.length →
      ∃ final,
        Structured.Code.run
            (List.replicate n (Structured.BasicInstr.op .pop)) state =
          .ok final ∧
        final.stack = state.stack.drop n ∧
        final.toSharedState = state.toSharedState := by
  intro n
  induction n generalizing state with
  | zero =>
      intro _hLen
      refine ⟨state, ?_, ?_, rfl⟩ <;> simp [Structured.Code.run]
  | succ n ih =>
      intro hLen
      cases state with
      | mk shared pc stack execLength =>
          cases stack with
          | nil =>
              simp at hLen
          | cons top rest =>
              have hTailLen : n ≤ rest.length := by
                simpa using Nat.succ_le_succ_iff.mp hLen
              let state0 : EVMState :=
                { toSharedState := shared, pc := pc, stack := top :: rest,
                  execLength := execLength }
              let stepState : EVMState :=
                state0.replaceStackAndIncrPC rest
              have hStep :
                  Structured.BasicInstr.step (Structured.BasicInstr.op .pop)
                      state0 =
                    .ok stepState := by
                subst stepState
                simp [state0, Structured.BasicInstr.step,
                  Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
                  Assembly.Target.stepInstr, Assembly.PrimOp.step,
                  Assembly.PrimStep.run, Assembly.PrimOp.continuingStep?,
                  EvmYul.Stack.pop]
              rcases ih stepState hTailLen with
                ⟨final, hRun, hFinalStack, hFinalShared⟩
              refine ⟨final, ?_, ?_, ?_⟩
              · simpa [Structured.Code.run, state0, hStep,
                  List.replicate_succ] using hRun
              · simpa [state0, stepState] using hFinalStack
              · simpa [state0, stepState] using hFinalShared

end Cleanup

def StateRel (layout : List Name) (source : Source.State)
    (target : RunState) : Prop :=
  target.evm.toSharedState = source.shared ∧
    StackStoreRel layout source.vars target.evm.stack

structure LoweringStateRel (sourceCtx : Source.Ctx) (targetCtx : Ctx)
    (source : Source.State) (target : RunState) : Prop where
  ctx : CtxInv sourceCtx targetCtx
  state : StateRel sourceCtx.scope source target

namespace StateRel

theorem initial {initial : EVMState} (hStack : initial.stack = []) :
    StateRel [] (Source.Program.initialState initial.toSharedState)
      (Structured.Program.initialState initial) := by
  constructor
  · simp [Source.Program.initialState, Structured.Program.initialState,
      Structured.RunState.initial]
  · constructor
    · simpa [Structured.Program.initialState, Structured.RunState.initial,
        hStack]
    · intro idx name hName
      simp at hName

theorem insert {layout : List Name} {source : Source.State}
    {target : RunState} {name : Name} {value : Word}
    (hFresh : name ∉ layout)
    (hRel : StateRel layout source target) :
    StateRel (name :: layout) (source.insert name value)
      (target.withEVM { target.evm with stack := value :: target.evm.stack }) := by
  rcases hRel with ⟨hShared, hStack⟩
  exact ⟨hShared,
    StackStoreRel.cons_insert hFresh hStack⟩

theorem restrictTo_suffix {pre scope : List Name} {source : Source.State}
    {target cleaned : RunState}
    (hRel : StateRel (pre ++ scope) source target)
    (hShared : cleaned.evm.toSharedState = target.evm.toSharedState)
    (hStack : cleaned.evm.stack = target.evm.stack.drop pre.length) :
    StateRel scope (source.restrictTo scope) cleaned := by
  rcases hRel with ⟨hSharedRel, hStackRel⟩
  constructor
  · simp [Source.State.restrictTo, hShared, hSharedRel]
  · rw [hStack]
    exact StackStoreRel.restrictTo_suffix hStackRel

theorem restrictTo_self {layout : List Name} {source : Source.State}
    {target : RunState}
    (hRel : StateRel layout source target) :
    StateRel layout (source.restrictTo layout) target := by
  rcases hRel with ⟨hShared, hStackRel⟩
  constructor
  · simpa [Source.State.restrictTo] using hShared
  · exact StackStoreRel.restrictTo_self hStackRel

theorem cleanupAll_exists {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target) :
    ∃ cleaned,
      Direct.Ctx.runCleanupAll targetCtx target = .ok cleaned ∧
        cleaned.evm.toSharedState = target.evm.toSharedState ∧
        cleaned.evm.stack = [] ∧
        cleaned.returns = target.returns := by
  rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
  rcases hRel with ⟨_hShared, hStackRel⟩
  have hLen : targetCtx.layout.length ≤ target.evm.stack.length := by
    rcases hStackRel with ⟨hStackLen, _hLookup⟩
    simp [hLayout, hStackLen]
  rcases Cleanup.run_replicate_pop_exists target.evm
      targetCtx.layout.length hLen with
    ⟨evmClean, hRun, hStack, hSharedClean⟩
  refine ⟨target.withEVM evmClean, ?_, ?_, ?_, rfl⟩
  · simp [Direct.Ctx.runCleanupAll, Ctx.cleanupAll, Structured.Code.runState,
      hRun]
  · simpa [Structured.RunState.withEVM] using hSharedClean
  · rcases hStackRel with ⟨hStackLen, _hLookup⟩
    have hDrop : target.evm.stack.drop targetCtx.layout.length = [] := by
      rw [hLayout, ← hStackLen]
      simp
    simpa [Structured.RunState.withEVM, hDrop] using hStack

theorem cleanupTo_scope_exists {ctx : Ctx} {scope : List Name}
    {source : Source.State} {target : RunState}
    (hScope : CleanupScopeRel ctx.layout scope)
    (hRel : StateRel ctx.layout source target) :
    ∃ cleaned,
      Direct.Ctx.runCleanupTo ctx scope.length target = .ok cleaned ∧
        StateRel scope (source.restrictTo scope) cleaned ∧
        cleaned.returns = target.returns := by
  have hDepth : scope.length ≤ ctx.layout.length :=
    CleanupScopeRel.depth_le hScope
  rcases hRel with ⟨hSharedRel, hStackRel⟩
  rcases hStackRel with ⟨hStackLen, hStackLookup⟩
  let n := ctx.layout.length - scope.length
  have hRunLen : n ≤ target.evm.stack.length := by
    dsimp [n]
    omega
  rcases Cleanup.run_replicate_pop_exists target.evm n hRunLen with
    ⟨evmClean, hRun, hCleanStack, hCleanShared⟩
  refine ⟨target.withEVM evmClean, ?_, ?_, rfl⟩
  · unfold Direct.Ctx.runCleanupTo
    unfold Ctx.cleanupTo?
    simp [hDepth, Structured.Code.runState, n, hRun]
  · constructor
    · simpa [Structured.RunState.withEVM, Source.State.restrictTo,
        hCleanShared] using hSharedRel
    · constructor
      · have hScopeN : ctx.layout.drop n = scope := by
          simpa [n] using hScope
        have hScopeLen :
            (ctx.layout.drop n).length = scope.length := by
          rw [hScopeN]
        simpa [Structured.RunState.withEVM, hCleanStack, hStackLen] using
          hScopeLen
      · intro idx name hName
        have hScopeN : ctx.layout.drop n = scope := by
          simpa [n] using hScope
        have hLayoutAt :
            ctx.layout[n + idx]? = some name := by
          have hDropAt :
              (ctx.layout.drop n)[idx]? = some name := by
            rw [hScopeN]
            exact hName
          simpa [List.getElem?_drop] using hDropAt
        have hStackAt := hStackLookup hLayoutAt
        have hNameMem : name ∈ scope :=
          List.mem_of_getElem? hName
        simp [Structured.RunState.withEVM, hCleanStack, List.getElem?_drop,
          Source.State.restrictTo, Source.Store.restrictTo, n, hNameMem,
          hStackAt]

end StateRel

structure PrimitiveSound (prim : Source.PrimitiveSemantics) : Prop where
  eval_step :
    ∀ {op : Structured.BasicOp}
      {shared shared' : EvmYul.SharedState .EVM}
      {values values' : List Word} {evm evm' : EVMState}
      {baseStack : EvmYul.Stack Word},
      prim.eval op shared values = .ok (shared', values') →
      evm.toSharedState = shared →
      evm.stack = values.reverse ++ baseStack →
      Structured.BasicOp.step op evm = .ok evm' →
        evm'.toSharedState = shared' ∧
          evm'.stack = values'.reverse ++ baseStack
  eval_step_exists :
    ∀ {op : Structured.BasicOp}
      {shared shared' : EvmYul.SharedState .EVM}
      {values values' : List Word} {evm : EVMState}
      {baseStack : EvmYul.Stack Word},
      prim.eval op shared values = .ok (shared', values') →
      evm.toSharedState = shared →
      evm.stack = values.reverse ++ baseStack →
        ∃ evm',
          Structured.BasicOp.step op evm = .ok evm' ∧
            evm'.toSharedState = shared' ∧
              evm'.stack = values'.reverse ++ baseStack
  eval_length :
    ∀ {op : Structured.BasicOp}
      {shared shared' : EvmYul.SharedState .EVM}
      {values values' : List Word},
      prim.eval op shared values = .ok (shared', values') →
        values'.length = Expressions.Structured.BasicOp.outputs op
  terminal_step :
    ∀ {kind : Assembly.HaltKind}
      {shared shared' : EvmYul.SharedState .EVM}
      {values : List Word} {evm evm' : EVMState}
      {baseStack : EvmYul.Stack Word},
      prim.terminal kind shared values = .ok shared' →
      evm.toSharedState = shared →
      evm.stack = values.reverse ++ baseStack →
      Structured.Terminal.step kind evm = .ok evm' →
        evm'.toSharedState = shared'
  terminal_step_exists :
    ∀ {kind : Assembly.HaltKind}
      {shared shared' : EvmYul.SharedState .EVM}
      {values : List Word} {evm : EVMState}
      {baseStack : EvmYul.Stack Word},
      prim.terminal kind shared values = .ok shared' →
      evm.toSharedState = shared →
      evm.stack = values.reverse ++ baseStack →
        ∃ evm',
          Structured.Terminal.step kind evm = .ok evm' ∧
            evm'.toSharedState = shared'

namespace PrimitiveSemantics

theorem evm_step_return_eq_binaryMachineStateOp :
    (EvmYul.step (EvmYul.Operation.RETURN : EvmYul.Operation .EVM) none) =
      EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmReturn :=
  rfl

theorem evm_step_revert_eq_binaryMachineStateOp :
    (EvmYul.step (EvmYul.Operation.REVERT : EvmYul.Operation .EVM) none) =
      EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmRevert :=
  rfl

theorem structured_terminal_step_return_of_stack
    (state : EVMState) (offset size : Word) (tail : EvmYul.Stack Word)
    (hStack : state.stack = offset :: size :: tail) :
    Structured.Terminal.step .return state =
      .ok (({ state with
        toMachineState := state.toMachineState.evmReturn offset size
      }).replaceStackAndIncrPC tail) := by
  cases state with
  | mk shared pc stack execLength =>
      simp at hStack
      subst stack
      simp [Structured.Terminal.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
        Assembly.HaltKind.toPrimOp, Assembly.PrimOp.toEVM,
        evm_step_return_eq_binaryMachineStateOp,
        EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
        EvmYul.EVM.State.replaceStackAndIncrPC]
      rfl

theorem structured_terminal_step_revert_of_stack
    (state : EVMState) (offset size : Word) (tail : EvmYul.Stack Word)
    (hStack : state.stack = offset :: size :: tail) :
    Structured.Terminal.step .revert state =
      .ok (({ state with
        toMachineState := state.toMachineState.evmRevert offset size
      }).replaceStackAndIncrPC tail) := by
  cases state with
  | mk shared pc stack execLength =>
      simp at hStack
      subst stack
      simp [Structured.Terminal.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
        Assembly.HaltKind.toPrimOp, Assembly.PrimOp.toEVM,
        evm_step_revert_eq_binaryMachineStateOp,
        EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
        EvmYul.EVM.State.replaceStackAndIncrPC]
      rfl

open EvmYul

def selfdestructShared (shared : EvmYul.SharedState .EVM)
    (recipient : Word) : EvmYul.SharedState .EVM :=
  let source := shared.executionEnv.codeOwner
  let target : AccountAddress := AccountAddress.ofUInt256 recipient
  if shared.createdAccounts.contains source then
    let substate' : Substate :=
      { shared.substate with
        selfDestructSet := shared.substate.selfDestructSet.insert source
        accessedAccounts := shared.substate.accessedAccounts.insert target }
    let accountMap' :=
      match shared.lookupAccount source with
      | none =>
          dbg_trace
            "No 'self' found to be destructed; this should probably not be happening;"
          shared.accountMap
      | some sourceAccount =>
          match shared.lookupAccount target with
          | none =>
              if sourceAccount.balance == ⟨0⟩ then
                shared.accountMap
              else
                shared.accountMap.insert target
                    { (default : Account .EVM) with
                      balance := sourceAccount.balance }
                  |>.insert source { sourceAccount with balance := ⟨0⟩ }
          | some targetAccount =>
              if target = source then
                shared.accountMap.insert target
                    { targetAccount with balance := ⟨0⟩ }
                  |>.insert source { sourceAccount with balance := ⟨0⟩ }
              else
                shared.accountMap.insert target
                    { targetAccount with
                      balance := targetAccount.balance + sourceAccount.balance }
                  |>.insert source { sourceAccount with balance := ⟨0⟩ }
    { shared with accountMap := accountMap', substate := substate' }
  else
    let substate' : Substate :=
      { shared.substate with
        accessedAccounts := shared.substate.accessedAccounts.insert target }
    let accountMap' :=
      match shared.lookupAccount source with
      | none =>
          dbg_trace
            "No 'self' found to be destructed; this should probably not be happening;"
          shared.accountMap
      | some sourceAccount =>
          match shared.lookupAccount target with
          | none =>
              if sourceAccount.balance == ⟨0⟩ then
                shared.accountMap
              else
                shared.accountMap.insert target
                    { (default : Account .EVM) with
                      balance := sourceAccount.balance }
                  |>.insert source { sourceAccount with balance := ⟨0⟩ }
          | some targetAccount =>
              if target = source then
                shared.accountMap
              else
                shared.accountMap.insert target
                    { targetAccount with
                      balance := targetAccount.balance + sourceAccount.balance }
                  |>.insert source { sourceAccount with balance := ⟨0⟩ }
    { shared with accountMap := accountMap', substate := substate' }

theorem structured_terminal_step_selfdestruct_of_stack
    (state : EVMState) (recipient : Word) (tail : EvmYul.Stack Word)
    (hStack : state.stack = recipient :: tail) :
    Structured.Terminal.step .selfdestruct state =
      .ok (({ state with
        toSharedState := selfdestructShared state.toSharedState recipient
      }).replaceStackAndIncrPC tail) := by
  cases state with
  | mk shared pc stack execLength =>
      simp at hStack
      subst stack
      unfold Structured.Terminal.step Assembly.Target.stepInstr
        Assembly.PrimOp.step
      simp [Assembly.PrimOp.continuingStep?, Assembly.HaltKind.toPrimOp,
        Assembly.PrimOp.toEVM]
      unfold EvmYul.step
      unfold Id.run
      simp [selfdestructShared, EvmYul.Stack.pop,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
      split <;> rfl

theorem structured_terminal_step_selfdestruct_nil
    (state : EVMState) (hStack : state.stack = []) :
    Structured.Terminal.step .selfdestruct state = .error .StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
      simp at hStack
      subst stack
      unfold Structured.Terminal.step Assembly.Target.stepInstr
        Assembly.PrimOp.step
      simp [Assembly.PrimOp.continuingStep?, Assembly.HaltKind.toPrimOp,
        Assembly.PrimOp.toEVM]
      unfold EvmYul.step
      unfold Id.run
      simp [EvmYul.Stack.pop]

theorem structured_terminal_stop_step
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm evm' : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal .stop shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack)
    (hStep : Structured.Terminal.step .stop evm = .ok evm') :
    evm'.toSharedState = shared' := by
  simp [Source.PrimitiveSemantics.structured, Structured.Terminal.step,
    Assembly.Target.stepInstr, Assembly.HaltKind.toPrimOp,
    Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
    Assembly.PrimOp.toEVM] at hEval hStep ⊢
  cases hStep
  cases hEval
  simp [hShared]

theorem structured_terminal_stop_step_exists
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal .stop shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack) :
    ∃ evm',
      Structured.Terminal.step .stop evm = .ok evm' ∧
        evm'.toSharedState = shared' := by
  let evm' : EVMState :=
    { evm with
      toMachineState := evm.toMachineState.setReturnData .empty }
  refine ⟨evm', ?_, ?_⟩
  · simp [Structured.Terminal.step, Assembly.Target.stepInstr,
      Assembly.HaltKind.toPrimOp, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimOp.toEVM, evm']
    rfl
  · exact
      structured_terminal_stop_step
        (baseStack := baseStack) hEval hShared hStack (by
          simp [Structured.Terminal.step, Assembly.Target.stepInstr,
            Assembly.HaltKind.toPrimOp, Assembly.PrimOp.step,
            Assembly.PrimOp.continuingStep?, Assembly.PrimOp.toEVM, evm']
          rfl)

theorem structured_terminal_return_step
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm evm' : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal .return shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack)
    (hStep : Structured.Terminal.step .return evm = .ok evm') :
    evm'.toSharedState = shared' := by
  cases hValues : values.reverse with
  | nil =>
      simp [Source.PrimitiveSemantics.structured, Structured.Terminal.step,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.HaltKind.toPrimOp,
        Assembly.PrimOp.toEVM, evm_step_return_eq_binaryMachineStateOp,
        EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2, hValues] at hEval
  | cons offset rest =>
      cases rest with
      | nil =>
          simp [Source.PrimitiveSemantics.structured,
            Structured.Terminal.step, Assembly.Target.stepInstr,
            Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
            Assembly.HaltKind.toPrimOp, Assembly.PrimOp.toEVM,
            evm_step_return_eq_binaryMachineStateOp,
            EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
            hValues] at hEval
      | cons size tail =>
          let iso : EVMState :=
            { toSharedState := shared,
              pc := EvmYul.UInt256.ofNat 0,
              stack := values.reverse,
              execLength := 0 }
          have hIso :
              Structured.Terminal.step .return iso =
                .ok (({ iso with
                  toMachineState := iso.toMachineState.evmReturn offset size
                }).replaceStackAndIncrPC tail) := by
            apply structured_terminal_step_return_of_stack
            simp [iso, hValues]
          simp [Source.PrimitiveSemantics.structured, iso, hIso] at hEval
          have hTargetStack :
              evm.stack = offset :: size :: (tail ++ baseStack) := by
            rw [hStack, hValues]
            simp
          have hTarget :=
            structured_terminal_step_return_of_stack evm offset size
              (tail ++ baseStack) hTargetStack
          rw [hTarget] at hStep
          cases hStep
          cases hEval
          simp [hShared, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]

theorem structured_terminal_return_step_exists
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal .return shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack) :
    ∃ evm',
      Structured.Terminal.step .return evm = .ok evm' ∧
        evm'.toSharedState = shared' := by
  cases hValues : values.reverse with
  | nil =>
      simp [Source.PrimitiveSemantics.structured, Structured.Terminal.step,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.HaltKind.toPrimOp,
        Assembly.PrimOp.toEVM, evm_step_return_eq_binaryMachineStateOp,
        EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2, hValues] at hEval
  | cons offset rest =>
      cases rest with
      | nil =>
          simp [Source.PrimitiveSemantics.structured,
            Structured.Terminal.step, Assembly.Target.stepInstr,
            Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
            Assembly.HaltKind.toPrimOp, Assembly.PrimOp.toEVM,
            evm_step_return_eq_binaryMachineStateOp,
            EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
            hValues] at hEval
      | cons size tail =>
          let evm' : EVMState :=
            ({ evm with
              toMachineState := evm.toMachineState.evmReturn offset size
            }).replaceStackAndIncrPC (tail ++ baseStack)
          refine ⟨evm', ?_, ?_⟩
          · apply structured_terminal_step_return_of_stack
            rw [hStack, hValues]
            simp
          · exact
              structured_terminal_return_step
                (baseStack := baseStack) hEval hShared hStack (by
                  apply structured_terminal_step_return_of_stack
                  rw [hStack, hValues]
                  simp)

theorem structured_terminal_revert_step
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm evm' : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal .revert shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack)
    (hStep : Structured.Terminal.step .revert evm = .ok evm') :
    evm'.toSharedState = shared' := by
  cases hValues : values.reverse with
  | nil =>
      simp [Source.PrimitiveSemantics.structured, Structured.Terminal.step,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.HaltKind.toPrimOp,
        Assembly.PrimOp.toEVM, evm_step_revert_eq_binaryMachineStateOp,
        EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2, hValues] at hEval
  | cons offset rest =>
      cases rest with
      | nil =>
          simp [Source.PrimitiveSemantics.structured,
            Structured.Terminal.step, Assembly.Target.stepInstr,
            Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
            Assembly.HaltKind.toPrimOp, Assembly.PrimOp.toEVM,
            evm_step_revert_eq_binaryMachineStateOp,
            EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
            hValues] at hEval
      | cons size tail =>
          let iso : EVMState :=
            { toSharedState := shared,
              pc := EvmYul.UInt256.ofNat 0,
              stack := values.reverse,
              execLength := 0 }
          have hIso :
              Structured.Terminal.step .revert iso =
                .ok (({ iso with
                  toMachineState := iso.toMachineState.evmRevert offset size
                }).replaceStackAndIncrPC tail) := by
            apply structured_terminal_step_revert_of_stack
            simp [iso, hValues]
          simp [Source.PrimitiveSemantics.structured, iso, hIso] at hEval
          have hTargetStack :
              evm.stack = offset :: size :: (tail ++ baseStack) := by
            rw [hStack, hValues]
            simp
          have hTarget :=
            structured_terminal_step_revert_of_stack evm offset size
              (tail ++ baseStack) hTargetStack
          rw [hTarget] at hStep
          cases hStep
          cases hEval
          simp [hShared, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]

theorem structured_terminal_revert_step_exists
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal .revert shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack) :
    ∃ evm',
      Structured.Terminal.step .revert evm = .ok evm' ∧
        evm'.toSharedState = shared' := by
  cases hValues : values.reverse with
  | nil =>
      simp [Source.PrimitiveSemantics.structured, Structured.Terminal.step,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.HaltKind.toPrimOp,
        Assembly.PrimOp.toEVM, evm_step_revert_eq_binaryMachineStateOp,
        EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2, hValues] at hEval
  | cons offset rest =>
      cases rest with
      | nil =>
          simp [Source.PrimitiveSemantics.structured,
            Structured.Terminal.step, Assembly.Target.stepInstr,
            Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
            Assembly.HaltKind.toPrimOp, Assembly.PrimOp.toEVM,
            evm_step_revert_eq_binaryMachineStateOp,
            EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
            hValues] at hEval
      | cons size tail =>
          let evm' : EVMState :=
            ({ evm with
              toMachineState := evm.toMachineState.evmRevert offset size
            }).replaceStackAndIncrPC (tail ++ baseStack)
          refine ⟨evm', ?_, ?_⟩
          · apply structured_terminal_step_revert_of_stack
            rw [hStack, hValues]
            simp
          · exact
              structured_terminal_revert_step
                (baseStack := baseStack) hEval hShared hStack (by
                  apply structured_terminal_step_revert_of_stack
                  rw [hStack, hValues]
                  simp)

theorem structured_terminal_selfdestruct_step
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm evm' : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal .selfdestruct shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack)
    (hStep : Structured.Terminal.step .selfdestruct evm = .ok evm') :
    evm'.toSharedState = shared' := by
  cases hValues : values.reverse with
  | nil =>
      let iso : EVMState :=
        { toSharedState := shared,
          pc := EvmYul.UInt256.ofNat 0,
          stack := values.reverse,
          execLength := 0 }
      have hIso :
          Structured.Terminal.step .selfdestruct iso =
            .error .StackUnderflow := by
        apply structured_terminal_step_selfdestruct_nil
        simp [iso, hValues]
      simp [Source.PrimitiveSemantics.structured, iso, hIso] at hEval
  | cons recipient tail =>
      let iso : EVMState :=
        { toSharedState := shared,
          pc := EvmYul.UInt256.ofNat 0,
          stack := values.reverse,
          execLength := 0 }
      have hIso :
          Structured.Terminal.step .selfdestruct iso =
            .ok (({ iso with
              toSharedState := selfdestructShared iso.toSharedState recipient
            }).replaceStackAndIncrPC tail) := by
        apply structured_terminal_step_selfdestruct_of_stack
        simp [iso, hValues]
      simp [Source.PrimitiveSemantics.structured, iso, hIso] at hEval
      have hTargetStack : evm.stack = recipient :: (tail ++ baseStack) := by
        rw [hStack, hValues]
        simp
      have hTarget :=
        structured_terminal_step_selfdestruct_of_stack evm recipient
          (tail ++ baseStack) hTargetStack
      rw [hTarget] at hStep
      cases hStep
      cases hEval
      simp [hShared, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem structured_terminal_selfdestruct_step_exists
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal .selfdestruct shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack) :
    ∃ evm',
      Structured.Terminal.step .selfdestruct evm = .ok evm' ∧
        evm'.toSharedState = shared' := by
  cases hValues : values.reverse with
  | nil =>
      let iso : EVMState :=
        { toSharedState := shared,
          pc := EvmYul.UInt256.ofNat 0,
          stack := values.reverse,
          execLength := 0 }
      have hIso :
          Structured.Terminal.step .selfdestruct iso =
            .error .StackUnderflow := by
        apply structured_terminal_step_selfdestruct_nil
        simp [iso, hValues]
      simp [Source.PrimitiveSemantics.structured, iso, hIso] at hEval
  | cons recipient tail =>
      let evm' : EVMState :=
        ({ evm with
          toSharedState := selfdestructShared evm.toSharedState recipient
        }).replaceStackAndIncrPC (tail ++ baseStack)
      refine ⟨evm', ?_, ?_⟩
      · apply structured_terminal_step_selfdestruct_of_stack
        rw [hStack, hValues]
        simp
      · exact
          structured_terminal_selfdestruct_step
            (baseStack := baseStack) hEval hShared hStack (by
              apply structured_terminal_step_selfdestruct_of_stack
              rw [hStack, hValues]
              simp)

theorem structured_terminal_step
    {kind : Assembly.HaltKind}
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm evm' : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal kind shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack)
    (hStep : Structured.Terminal.step kind evm = .ok evm') :
    evm'.toSharedState = shared' := by
  cases kind
  · exact structured_terminal_stop_step hEval hShared hStack hStep
  · exact structured_terminal_return_step hEval hShared hStack hStep
  · exact structured_terminal_revert_step hEval hShared hStack hStep
  · exact structured_terminal_selfdestruct_step hEval hShared hStack hStep

theorem structured_terminal_step_exists
    {kind : Assembly.HaltKind}
    {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word} {evm : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      Source.PrimitiveSemantics.structured.terminal kind shared values =
        .ok shared')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack) :
    ∃ evm',
      Structured.Terminal.step kind evm = .ok evm' ∧
        evm'.toSharedState = shared' := by
  cases kind
  · exact structured_terminal_stop_step_exists hEval hShared hStack
  · exact structured_terminal_return_step_exists hEval hShared hStack
  · exact structured_terminal_revert_step_exists hEval hShared hStack
  · exact structured_terminal_selfdestruct_step_exists hEval hShared hStack

end PrimitiveSemantics

mutual
  def Expr.Accessible {results : Nat} (layout : List Name) (offset : Nat)
      (expr : Expr results) : Prop :=
    match expr with
    | .lit _value => True
    | .var name =>
        ∃ idx, layout[idx]? = some name ∧ offset + idx + 1 ≤ 16
    | .code _code => False
    | .prim _op args => ExprSeq.Accessible layout offset args

  def ExprSeq.Accessible {results : Nat} (layout : List Name) (offset : Nat)
      (exprs : ExprSeq results) : Prop :=
    match exprs with
    | .nil => True
    | .cons (left := left) head tail =>
        Expr.Accessible layout offset head ∧
          ExprSeq.Accessible layout (offset + left) tail
end

namespace Access

mutual
  def exprWidth {results : Nat} : Expr results → Nat
    | .lit _value => 0
    | .var _name => 1
    | .code _code => 0
    | .prim _op args => exprSeqWidth args

  def exprSeqWidth {results : Nat} : ExprSeq results → Nat
    | .nil => 0
    | .cons (left := left) head tail =>
        max (exprWidth head) (left + exprSeqWidth tail)
end

def ExprBound (env : List Name) (offset : Nat) {results : Nat}
    (expr : Expr results) : Prop :=
  offset + env.length + exprWidth expr ≤ 16

def ExprSeqBound (env : List Name) (offset : Nat) {results : Nat}
    (exprs : ExprSeq results) : Prop :=
  offset + env.length + exprSeqWidth exprs ≤ 16

end Access

namespace Scope

mutual
  theorem expr_sourceOwned_of_scoped {env : List Name}
      {results : Nat} {expr : Expr results}
      (hScoped : Scope.ExprScoped env expr) :
      Source.Expr.SourceOwned expr := by
    cases expr with
    | lit _value =>
        simp [Source.Expr.SourceOwned]
    | var _name =>
        simp [Source.Expr.SourceOwned]
    | code _code =>
        exact False.elim hScoped
    | prim _op args =>
        exact exprSeq_sourceOwned_of_scoped hScoped

  theorem exprSeq_sourceOwned_of_scoped {env : List Name}
      {results : Nat} {exprs : ExprSeq results}
      (hScoped : Scope.ExprSeqScoped env exprs) :
      Source.ExprSeq.SourceOwned exprs := by
    cases exprs with
    | nil =>
        simp [Source.ExprSeq.SourceOwned]
    | cons head tail =>
        rcases hScoped with ⟨hHead, hTail⟩
        exact
          ⟨expr_sourceOwned_of_scoped hHead,
            exprSeq_sourceOwned_of_scoped hTail⟩
end

end Scope

namespace CtxRel

mutual
  theorem expr_accessible_of_scoped {offset : Nat}
      {source : Source.Ctx} {target : Ctx}
      {results : Nat} {expr : Expr results}
      (hRel : CtxRel source target)
      (hScoped : Scope.ExprScoped source.scope expr)
      (hBound :
        offset + target.layout.length + Access.exprWidth expr ≤ 16) :
      Expr.Accessible source.scope offset expr := by
    cases expr with
    | lit _value =>
        simp [Expr.Accessible]
    | var name =>
        rcases hRel with
          ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
        rcases List.mem_iff_getElem?.mp hScoped with ⟨idx, hGet⟩
        have hIdxLt : idx < source.scope.length := by
          exact (List.getElem?_eq_some_iff.mp hGet).1
        exact
          ⟨idx, hGet, by
            simp [Access.exprWidth] at hBound
            rw [hLayout] at hBound
            omega⟩
    | code _code =>
        exact False.elim hScoped
    | prim _op args =>
        exact exprSeq_accessible_of_scoped hRel hScoped
          (by simpa [Access.exprWidth] using hBound)

  theorem exprSeq_accessible_of_scoped {offset : Nat}
      {source : Source.Ctx} {target : Ctx}
      {results : Nat} {exprs : ExprSeq results}
      (hRel : CtxRel source target)
      (hScoped : Scope.ExprSeqScoped source.scope exprs)
      (hBound :
        offset + target.layout.length + Access.exprSeqWidth exprs ≤ 16) :
      ExprSeq.Accessible source.scope offset exprs := by
    cases exprs with
    | nil =>
        simp [ExprSeq.Accessible]
    | cons head tail =>
        rename_i left _right
        rcases hScoped with ⟨hHeadScoped, hTailScoped⟩
        have hHeadBound :
            offset + target.layout.length + Access.exprWidth head ≤ 16 := by
          have hLe :
              Access.exprWidth head ≤
                max (Access.exprWidth head)
                  (left + Access.exprSeqWidth tail) :=
            Nat.le_max_left _ _
          simp [Access.exprSeqWidth] at hBound
          omega
        have hTailBound :
            (offset + left) + target.layout.length +
                Access.exprSeqWidth tail ≤ 16 := by
          have hLe :
              left + Access.exprSeqWidth tail ≤
                max (Access.exprWidth head)
                  (left + Access.exprSeqWidth tail) :=
            Nat.le_max_right _ _
          simp [Access.exprSeqWidth] at hBound
          omega
        exact
          ⟨expr_accessible_of_scoped hRel hHeadScoped hHeadBound,
            exprSeq_accessible_of_scoped hRel hTailScoped hTailBound⟩
end

theorem expr_accessible_of_scoped_bound {offset : Nat}
    {source : Source.Ctx} {target : Ctx}
    {results : Nat} {expr : Expr results}
    (hRel : CtxRel source target)
    (hScoped : Scope.ExprScoped source.scope expr)
    (hBound : Access.ExprBound source.scope offset expr) :
    Expr.Accessible source.scope offset expr := by
  apply expr_accessible_of_scoped hRel hScoped
  rcases hRel with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
  simpa [Access.ExprBound, hLayout] using hBound

theorem exprSeq_accessible_of_scoped_bound {offset : Nat}
    {source : Source.Ctx} {target : Ctx}
    {results : Nat} {exprs : ExprSeq results}
    (hRel : CtxRel source target)
    (hScoped : Scope.ExprSeqScoped source.scope exprs)
    (hBound : Access.ExprSeqBound source.scope offset exprs) :
    ExprSeq.Accessible source.scope offset exprs := by
  apply exprSeq_accessible_of_scoped hRel hScoped
  rcases hRel with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
  simpa [Access.ExprSeqBound, hLayout] using hBound

end CtxRel

namespace SourceWF

mutual
  theorem expr_scoped {env : List Name} {results : Nat}
      {expr : Expr results}
      (hWF : Source.Expr.SourceWF env expr) :
      Scope.ExprScoped env expr := by
    rcases hWF with ⟨hOwned, hLexical⟩
    cases expr with
    | lit value =>
        simp [Scope.ExprScoped]
    | var name =>
        simpa [Scope.ExprScoped] using hLexical
    | code code =>
        simp [Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        exact
          exprSeq_scoped
            (env := env) (exprs := args) ⟨hOwned, hLexical⟩

  theorem exprSeq_scoped {env : List Name} {results : Nat}
      {exprs : ExprSeq results}
      (hWF : Source.ExprSeq.SourceWF env exprs) :
      Scope.ExprSeqScoped env exprs := by
    rcases hWF with ⟨hOwned, hLexical⟩
    cases exprs with
    | nil =>
        simp [Scope.ExprSeqScoped]
    | cons head tail =>
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        rcases hLexical with ⟨hHeadLexical, hTailLexical⟩
        exact
          ⟨expr_scoped
              (env := env) (expr := head)
              ⟨hHeadOwned, hHeadLexical⟩,
            exprSeq_scoped
              (env := env) (exprs := tail)
              ⟨hTailOwned, hTailLexical⟩⟩
end

mutual
  theorem block_scoped {env : List Name} {block : Block}
      (hWF : Source.Block.SourceWF env block) :
      Scope.Block.Scoped env block := by
    rcases hWF with ⟨hOwned, hLexical⟩
    cases block with
    | mk stmts =>
        exact
          stmtList_scoped
            (env := env) (stmts := stmts) ⟨hOwned, hLexical⟩

  theorem stmt_scoped {env : List Name} {stmt : Stmt}
      (hWF : Source.Stmt.SourceWF env stmt) :
      Scope.Stmt.Scoped env stmt := by
    rcases hWF with ⟨hOwned, hLexical⟩
    cases stmt with
    | expr expr =>
        exact
          expr_scoped (env := env) (expr := expr)
            ⟨hOwned.2, hLexical⟩
    | exprs exprs =>
        simp [Source.Stmt.SourceOwned] at hOwned
    | let_ name value =>
        exact
          ⟨hLexical.1,
            expr_scoped (env := env) (expr := value)
              ⟨hOwned, hLexical.2⟩⟩
    | assign name value =>
        exact
          ⟨hLexical.1,
            expr_scoped (env := env) (expr := value)
              ⟨hOwned, hLexical.2⟩⟩
    | assignTop name =>
        simp [Source.Stmt.SourceOwned] at hOwned
    | assignTopWithOffset offset name =>
        simp [Source.Stmt.SourceOwned] at hOwned
    | block body =>
        change Source.Block.SourceOwned body at hOwned
        change Lexical.BlockScoped env body at hLexical
        exact
          block_scoped (env := env) (block := body)
            ⟨hOwned, hLexical⟩
    | if_ cond body =>
        change
          Source.Expr.SourceOwned cond ∧ Source.Block.SourceOwned body
          at hOwned
        change
          Lexical.ExprScoped env cond ∧ Lexical.BlockScoped env body
          at hLexical
        exact
          ⟨expr_scoped (env := env) (expr := cond)
              ⟨hOwned.1, hLexical.1⟩,
            block_scoped (env := env) (block := body)
              ⟨hOwned.2, hLexical.2⟩⟩
    | switch scrutinee cases defaultBody =>
        cases defaultBody with
        | none =>
            have hOwned' :
                Source.Expr.SourceOwned scrutinee ∧
                  Source.CaseList.SourceOwned cases ∧ True := by
              simpa [Source.Stmt.SourceOwned] using hOwned
            have hLexical' :
                Lexical.ExprScoped env scrutinee ∧
                  Lexical.CaseListScoped env cases ∧ True := by
              simpa [Lexical.StmtScoped, Lexical.DefaultScoped] using
                hLexical
            exact
              ⟨expr_scoped (env := env) (expr := scrutinee)
                  ⟨hOwned'.1, hLexical'.1⟩,
                caseList_scoped (env := env) (cases := cases)
                  hOwned'.2.1 hLexical'.2.1,
                trivial⟩
        | some body =>
            have hOwned' :
                Source.Expr.SourceOwned scrutinee ∧
                  Source.CaseList.SourceOwned cases ∧
                    Source.Block.SourceOwned body := by
              simpa [Source.Stmt.SourceOwned] using hOwned
            have hLexical' :
                Lexical.ExprScoped env scrutinee ∧
                  Lexical.CaseListScoped env cases ∧
                    Lexical.BlockScoped env body := by
              simpa [Lexical.StmtScoped, Lexical.DefaultScoped] using
                hLexical
            exact
              ⟨expr_scoped (env := env) (expr := scrutinee)
                  ⟨hOwned'.1, hLexical'.1⟩,
                caseList_scoped (env := env) (cases := cases)
                  hOwned'.2.1 hLexical'.2.1,
                block_scoped (env := env) (block := body)
                  ⟨hOwned'.2.2, hLexical'.2.2⟩⟩
    | for_ init cond post body =>
        change
          Source.Block.SourceOwned init ∧ Source.Expr.SourceOwned cond ∧
            Source.Block.SourceOwned post ∧ Source.Block.SourceOwned body
          at hOwned
        change
          Lexical.BlockScoped env init ∧
            Lexical.ExprScoped (Scope.Block.outEnv env init) cond ∧
              Lexical.BlockScoped (Scope.Block.outEnv env init) post ∧
                Lexical.BlockScoped (Scope.Block.outEnv env init) body
          at hLexical
        refine
          ⟨block_scoped (env := env) (block := init)
              ⟨hOwned.1, hLexical.1⟩, ?_, ?_, ?_⟩
        · exact
            expr_scoped
              (env := Scope.Block.outEnv env init) (expr := cond)
              ⟨hOwned.2.1, hLexical.2.1⟩
        · exact
            block_scoped
              (env := Scope.Block.outEnv env init) (block := post)
              ⟨hOwned.2.2.1, hLexical.2.2.1⟩
        · exact
            block_scoped
              (env := Scope.Block.outEnv env init) (block := body)
              ⟨hOwned.2.2.2, hLexical.2.2.2⟩
    | brk =>
        simp [Scope.Stmt.Scoped]
    | cont =>
        simp [Scope.Stmt.Scoped]
    | leave =>
        simp [Scope.Stmt.Scoped]
    | call name =>
        simp [Source.Stmt.SourceOwned] at hOwned
    | terminal kind =>
        simp [Scope.Stmt.Scoped]
    | terminalArgs kind args =>
        exact
          exprSeq_scoped (env := env) (exprs := args)
            ⟨hOwned, hLexical⟩

  theorem stmtList_scoped {env : List Name} {stmts : List Stmt}
      (hWF : Source.StmtList.SourceWF env stmts) :
      Scope.StmtList.Scoped env stmts := by
    rcases hWF with ⟨hOwned, hLexical⟩
    cases stmts with
    | nil =>
        simp [Scope.StmtList.Scoped]
    | cons stmt rest =>
        change
          Source.Stmt.SourceOwned stmt ∧ Source.StmtList.SourceOwned rest
          at hOwned
        change
          Lexical.StmtScoped env stmt ∧
            Lexical.StmtListScoped (Scope.Stmt.outEnv env stmt) rest
          at hLexical
        exact
          ⟨stmt_scoped (env := env) (stmt := stmt)
              ⟨hOwned.1, hLexical.1⟩,
            stmtList_scoped
              (env := Scope.Stmt.outEnv env stmt) (stmts := rest)
              ⟨hOwned.2, hLexical.2⟩⟩

  theorem caseList_scoped {env : List Name}
      {cases : List (Word × Block)}
      (hOwned : Source.CaseList.SourceOwned cases)
      (hLexical : Lexical.CaseListScoped env cases) :
      Scope.CaseList.Scoped env cases := by
    cases cases with
    | nil =>
        simp [Scope.CaseList.Scoped]
    | cons head rest =>
        rcases head with ⟨value, body⟩
        change
          Source.Block.SourceOwned body ∧ Source.CaseList.SourceOwned rest
          at hOwned
        change
          Lexical.BlockScoped env body ∧ Lexical.CaseListScoped env rest
          at hLexical
        exact
          ⟨block_scoped (env := env) (block := body)
              ⟨hOwned.1, hLexical.1⟩,
            caseList_scoped (env := env) (cases := rest)
              hOwned.2 hLexical.2⟩

  theorem default_scoped {env : List Name}
      {defaultBody : Option Block}
      (hOwned :
        match defaultBody with
        | none => True
        | some body => Source.Block.SourceOwned body)
      (hLexical : Lexical.DefaultScoped env defaultBody) :
      Scope.Default.Scoped env defaultBody := by
    cases defaultBody with
    | none =>
        simp [Scope.Default.Scoped]
    | some body =>
        exact
          block_scoped (env := env) (block := body)
            ⟨hOwned, hLexical⟩
end

theorem program_scoped_of_sourceWF {program : Program}
    (hWF : Source.Program.SourceWF program) :
    Program.Scoped program := by
  exact block_scoped (env := []) (block := program.body) hWF.2

theorem program_scoped_of_sourceAccepted {program : Program}
    (hAccepted : Program.SourceAccepted program) :
    Program.Scoped program :=
  program_scoped_of_sourceWF hAccepted.2

end SourceWF

namespace AtomicStmt

/--
Non-recursive source statements whose direct/local-stack proof is discharged by
one statement bridge.

This is a proof-interface classifier, not a source-language restriction for the
whole locals layer.  Compound control forms are handled by recursive block and
statement theorems; stack-only backend forms and procedure calls are outside the
stack-free locals source boundary.
-/
def Holds : Stmt → Prop
  | .expr (results := results) _expr => results = 0
  | .let_ _name _value => True
  | .assign _name _value => True
  | .brk => True
  | .cont => True
  | .terminal _kind => True
  | .terminalArgs _kind _args => True
  | .exprs _exprs => False
  | .assignTop _name => False
  | .assignTopWithOffset _offset _name => False
  | .block _body => False
  | .if_ _cond _body => False
  | .switch _scrutinee _cases _defaultBody => False
  | .for_ _init _cond _post _body => False
  | .leave => False
  | .call _name => False

/--
Stack-access bound needed by the atomic statement bridges.  It is lower-proof
evidence: higher layers should prove source scoping, and this boundary turns
that into concrete DUP/SWAP reachability.
-/
def AccessBound (layoutLength : Nat) : Stmt → Prop
  | .expr expr => layoutLength + Access.exprWidth expr ≤ 16
  | .let_ _name value => layoutLength + Access.exprWidth value ≤ 16
  | .assign _name value => layoutLength + Access.exprWidth value ≤ 16
  | .terminalArgs _kind args =>
      layoutLength + Access.exprSeqWidth args ≤ 16
  | _ => True

def SourceAccessBound (env : List Name) : Stmt → Prop
  | .expr expr => Access.ExprBound env 0 expr
  | .let_ _name value => Access.ExprBound env 0 value
  | .assign _name value => Access.ExprBound env 0 value
  | .terminalArgs _kind args => Access.ExprSeqBound env 0 args
  | _ => True

theorem accessBound_of_sourceAccessBound {source : Source.Ctx}
    {target : Ctx} {stmt : Stmt}
    (hCtx : CtxRel source target)
    (hBound : SourceAccessBound source.scope stmt) :
    AccessBound target.layout.length stmt := by
  rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
  cases stmt <;> simpa [SourceAccessBound, AccessBound,
    Access.ExprBound, Access.ExprSeqBound, hLayout] using hBound

end AtomicStmt

namespace Structural

def AtomicLowerable (env : List Name) (stmt : Stmt) : Prop :=
  AtomicStmt.Holds stmt ∧
    Scope.Stmt.Scoped env stmt ∧
    AtomicStmt.SourceAccessBound env stmt

mutual
  def BlockLowerable (env : List Name) : Block → Prop
    | ⟨stmts⟩ => StmtListLowerable env stmts

  def StmtLowerable (env : List Name) : Stmt → Prop
    | .expr expr => AtomicLowerable env (.expr expr)
    | .exprs _exprs => False
    | .let_ name value => AtomicLowerable env (.let_ name value)
    | .assign name value => AtomicLowerable env (.assign name value)
    | .assignTop _name => False
    | .assignTopWithOffset _offset _name => False
    | .block body => BlockLowerable env body
    | .if_ cond body =>
        Scope.ExprScoped env cond ∧ Access.ExprBound env 0 cond ∧
          BlockLowerable env body
    | .switch scrutinee cases defaultBody =>
        Scope.ExprScoped env scrutinee ∧
          Access.ExprBound env 0 scrutinee ∧
          CaseListLowerable env cases ∧
          DefaultLowerable env defaultBody
    | .for_ init cond post body =>
        BlockLowerable env init ∧
          Scope.ExprScoped (Scope.Block.outEnv env init) cond ∧
          Access.ExprBound (Scope.Block.outEnv env init) 0 cond ∧
          BlockLowerable (Scope.Block.outEnv env init) post ∧
          BlockLowerable (Scope.Block.outEnv env init) body
    | .brk => AtomicLowerable env .brk
    | .cont => AtomicLowerable env .cont
    | .leave => False
    | .call _name => False
    | .terminal kind => AtomicLowerable env (.terminal kind)
    | .terminalArgs kind args => AtomicLowerable env (.terminalArgs kind args)

  def StmtListLowerable (env : List Name) : List Stmt → Prop
    | [] => True
    | stmt :: rest =>
        StmtLowerable env stmt ∧
          StmtListLowerable (Scope.Stmt.outEnv env stmt) rest

  def CaseListLowerable (env : List Name) :
      List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        BlockLowerable env body ∧ CaseListLowerable env rest

  def DefaultLowerable (env : List Name) : Option Block → Prop
    | none => True
    | some body => BlockLowerable env body
end

theorem atomicLowerable_scoped {env : List Name} {stmt : Stmt}
    (hLower : AtomicLowerable env stmt) :
    Scope.Stmt.Scoped env stmt :=
  hLower.2.1

theorem atomicLowerable_sourceAccessBound {env : List Name} {stmt : Stmt}
    (hLower : AtomicLowerable env stmt) :
    AtomicStmt.SourceAccessBound env stmt :=
  hLower.2.2

theorem atomicLowerable_holds {env : List Name} {stmt : Stmt}
    (hLower : AtomicLowerable env stmt) :
    AtomicStmt.Holds stmt :=
  hLower.1

mutual
  theorem blockLowerable_scoped {env : List Name} {block : Block}
      (hLower : BlockLowerable env block) :
      Scope.Block.Scoped env block := by
    cases block with
    | mk stmts =>
        exact stmtListLowerable_scoped (env := env) (stmts := stmts) hLower

  theorem stmtLowerable_scoped {env : List Name} {stmt : Stmt}
      (hLower : StmtLowerable env stmt) :
      Scope.Stmt.Scoped env stmt := by
    cases stmt with
    | expr expr =>
        exact hLower.2.1
    | exprs exprs =>
        cases hLower
    | let_ name value =>
        exact hLower.2.1
    | assign name value =>
        exact hLower.2.1
    | assignTop name =>
        cases hLower
    | assignTopWithOffset offset name =>
        cases hLower
    | block body =>
        exact blockLowerable_scoped hLower
    | if_ cond body =>
        exact ⟨hLower.1, blockLowerable_scoped hLower.2.2⟩
    | switch scrutinee cases defaultBody =>
        exact
          ⟨hLower.1, caseListLowerable_scoped hLower.2.2.1,
            defaultLowerable_scoped hLower.2.2.2⟩
    | for_ init cond post body =>
        rcases hLower with
          ⟨hInitLower, hCondScoped, _hCondAccess, hPostLower, hBodyLower⟩
        exact
          ⟨blockLowerable_scoped hInitLower, hCondScoped,
            blockLowerable_scoped hPostLower,
            blockLowerable_scoped hBodyLower⟩
    | brk =>
        exact hLower.2.1
    | cont =>
        exact hLower.2.1
    | leave =>
        cases hLower
    | call name =>
        cases hLower
    | terminal kind =>
        exact hLower.2.1
    | terminalArgs kind args =>
        exact hLower.2.1

  theorem stmtListLowerable_scoped {env : List Name}
      {stmts : List Stmt}
      (hLower : StmtListLowerable env stmts) :
      Scope.StmtList.Scoped env stmts := by
    cases stmts with
    | nil =>
        simp [StmtListLowerable, Scope.StmtList.Scoped]
    | cons stmt rest =>
        rcases hLower with ⟨hStmt, hRest⟩
        exact
          ⟨stmtLowerable_scoped hStmt,
            stmtListLowerable_scoped
              (env := Scope.Stmt.outEnv env stmt) (stmts := rest) hRest⟩

  theorem caseListLowerable_scoped {env : List Name}
      {cases : List (Word × Block)}
      (hLower : CaseListLowerable env cases) :
      Scope.CaseList.Scoped env cases := by
    cases cases with
    | nil =>
        simp [CaseListLowerable, Scope.CaseList.Scoped]
    | cons head rest =>
        rcases head with ⟨value, body⟩
        rcases hLower with ⟨hBody, hRest⟩
        exact
          ⟨blockLowerable_scoped hBody,
            caseListLowerable_scoped (env := env) (cases := rest) hRest⟩

theorem defaultLowerable_scoped {env : List Name}
      {defaultBody : Option Block}
      (hLower : DefaultLowerable env defaultBody) :
      Scope.Default.Scoped env defaultBody := by
    cases defaultBody with
    | none =>
        simp [DefaultLowerable, Scope.Default.Scoped]
    | some body =>
        exact blockLowerable_scoped hLower
end

mutual
  def BlockMeasure : Block → Nat
    | ⟨stmts⟩ => StmtListMeasure stmts + 1

  def StmtMeasure : Stmt → Nat
    | .block body => BlockMeasure body + 1
    | .if_ _cond body => BlockMeasure body + 1
    | .switch _scrutinee cases defaultBody =>
        CaseListMeasure cases + DefaultMeasure defaultBody + 1
    | .for_ init _cond post body =>
        BlockMeasure init + BlockMeasure post + BlockMeasure body + 1
    | _ => 1

  def StmtListMeasure : List Stmt → Nat
    | [] => 1
    | stmt :: rest => StmtMeasure stmt + StmtListMeasure rest + 1

  def CaseListMeasure : List (Word × Block) → Nat
    | [] => 1
    | (_value, body) :: rest => BlockMeasure body + CaseListMeasure rest + 1

  def DefaultMeasure : Option Block → Nat
    | none => 1
    | some body => BlockMeasure body + 1
end

theorem select_lowerable {env : List Name} {value : Word}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {selected : Block}
    (hCases : CaseListLowerable env cases)
    (hDefault : DefaultLowerable env defaultBody)
    (hSelect : Source.Switch.select value cases defaultBody = some selected) :
    BlockLowerable env selected := by
  induction cases with
  | nil =>
      cases defaultBody with
      | none =>
          simp [Source.Switch.select] at hSelect
      | some body =>
          simp [Source.Switch.select] at hSelect
          cases hSelect
          exact hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      rcases hCases with ⟨hBody, hRest⟩
      by_cases hEq : caseValue = value
      · simp [Source.Switch.select, hEq] at hSelect
        cases hSelect
        exact hBody
      · simp [Source.Switch.select, hEq] at hSelect
        exact ih hRest hSelect

theorem select_blockMeasure_lt {value : Word}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {selected : Block}
    (hSelect : Source.Switch.select value cases defaultBody = some selected) :
    BlockMeasure selected <
      CaseListMeasure cases + DefaultMeasure defaultBody + 1 := by
  induction cases with
  | nil =>
      cases defaultBody with
      | none =>
          simp [Source.Switch.select] at hSelect
      | some body =>
          simp [Source.Switch.select] at hSelect
          cases hSelect
          simp [CaseListMeasure, DefaultMeasure]
          omega
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      by_cases hEq : caseValue = value
      · simp [Source.Switch.select, hEq] at hSelect
        cases hSelect
        simp [CaseListMeasure]
        omega
      · simp [Source.Switch.select, hEq] at hSelect
        have hRestMeasure := ih hSelect
        simp [CaseListMeasure]
        omega

end Structural

namespace Expr

theorem eval_of_evalOne {prim : Source.PrimitiveSemantics}
    {expr : Expr 1} {state state' : Source.State} {value : Word}
    (hOne : Source.Expr.evalOne prim expr state = .ok (state', value)) :
    Source.Expr.eval prim expr state = .ok (state', [value]) := by
  unfold Source.Expr.evalOne at hOne
  cases hEval : Source.Expr.eval prim expr state with
  | error _err =>
      simp [hEval] at hOne
  | ok result =>
      rcases result with ⟨s, values⟩
      simp [hEval] at hOne
      cases values with
      | nil =>
          simp [Source.invalid, invalid, Structured.invalid] at hOne
      | cons head tail =>
          cases tail with
          | nil =>
              simp at hOne
              rcases hOne with ⟨rfl, rfl⟩
              simpa using hEval
          | cons _second _more =>
              simp [Source.invalid, invalid, Structured.invalid] at hOne

mutual
  theorem eval_length_of_sourceOwned {prim : Source.PrimitiveSemantics}
      (hPrim : PrimitiveSound prim) {results : Nat} {expr : Expr results}
      {state state' : Source.State} {values : List Word}
      (hOwned : Source.Expr.SourceOwned expr)
      (hEval : Source.Expr.eval prim expr state = .ok (state', values)) :
      values.length = results := by
    cases expr with
    | lit _value =>
        simp [Source.Expr.eval] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        simp
    | var name =>
        unfold Source.Expr.eval at hEval
        cases hLookup : state.vars name with
        | none =>
            simp [hLookup, Source.invalid, invalid, Structured.invalid] at hEval
        | some value =>
            simp [hLookup] at hEval
            rcases hEval with ⟨rfl, rfl⟩
            simp
    | code _code =>
        simp [Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        unfold Source.Expr.eval at hEval
        cases hArgs : Source.Expr.ExprSeq.eval prim args state with
        | error err =>
            simp [hArgs] at hEval
        | ok argResult =>
            rcases argResult with ⟨stateAfterArgs, argValues⟩
            simp [hArgs] at hEval
            cases hPrimEval :
                prim.eval op stateAfterArgs.shared argValues with
            | error err =>
                simp [hPrimEval] at hEval
            | ok primResult =>
                rcases primResult with ⟨shared', values'⟩
                simp [hPrimEval] at hEval
                rcases hEval with ⟨rfl, rfl⟩
                exact hPrim.eval_length hPrimEval

  theorem evalSeq_length_of_sourceOwned {prim : Source.PrimitiveSemantics}
      (hPrim : PrimitiveSound prim) {results : Nat} {exprs : ExprSeq results}
      {state state' : Source.State} {values : List Word}
      (hOwned : Source.ExprSeq.SourceOwned exprs)
      (hEval :
        Source.Expr.ExprSeq.eval prim exprs state = .ok (state', values)) :
      values.length = results := by
    cases exprs with
    | nil =>
        simp [Source.Expr.ExprSeq.eval] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        simp
    | cons head tail =>
        simp [Source.ExprSeq.SourceOwned] at hOwned
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        unfold Source.Expr.ExprSeq.eval at hEval
        cases hHead : Source.Expr.eval prim head state with
        | error err =>
            simp [hHead] at hEval
        | ok headResult =>
            rcases headResult with ⟨stateAfterHead, headValues⟩
            simp [hHead] at hEval
            cases hTail :
                Source.Expr.ExprSeq.eval prim tail stateAfterHead with
            | error err =>
                simp [hTail] at hEval
            | ok tailResult =>
                rcases tailResult with ⟨stateAfterTail, tailValues⟩
                simp [hTail] at hEval
                rcases hEval with ⟨rfl, rfl⟩
                have hHeadLen :=
                  eval_length_of_sourceOwned hPrim hHeadOwned hHead
                have hTailLen :=
                  evalSeq_length_of_sourceOwned hPrim hTailOwned hTail
                simp [hHeadLen, hTailLen]
end

end Expr

def StackPrefixRel (layout : List Name) (source : Source.State)
    (stackPrefix : List Word) (evm : EVMState) : Prop :=
  evm.toSharedState = source.shared ∧
    ∃ baseStack : EvmYul.Stack Word,
      evm.stack = stackPrefix ++ baseStack ∧
        StackStoreRel layout source.vars baseStack

namespace StackPrefixRel

theorem of_stateRel {layout : List Name} {source : Source.State}
    {target : RunState} (hRel : StateRel layout source target) :
    StackPrefixRel layout source [] target.evm := by
  rcases hRel with ⟨hShared, hStackRel⟩
  exact ⟨hShared, target.evm.stack, by simp, hStackRel⟩

theorem to_stateRel_nil {layout : List Name} {source : Source.State}
    {target : RunState}
    (hRel : StackPrefixRel layout source [] target.evm) :
    StateRel layout source target := by
  rcases hRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  exact ⟨hShared, by simpa [hStack] using hStackRel⟩

end StackPrefixRel

namespace Expr

mutual
  theorem runCode_of_eval_sourceOwned {prim : Source.PrimitiveSemantics}
      (hPrim : PrimitiveSound prim) :
      ∀ {results : Nat} {expr : Expr results}
        {layout : List Name} {ctx : Ctx} {offset : Nat}
        {source source' : Source.State} {values : List Word}
        {evm : EVMState} {stackPrefix : List Word},
        ctx.layout = layout →
        layout.Nodup →
        Source.Expr.SourceOwned expr →
        Expr.Accessible layout offset expr →
        stackPrefix.length = offset →
        StackPrefixRel layout source stackPrefix evm →
        Source.Expr.eval prim expr source = .ok (source', values) →
          ∃ evm',
            Direct.Expr.runCode ctx offset expr evm = .ok evm' ∧
              StackPrefixRel layout source' (values.reverse ++ stackPrefix)
                evm' := by
    intro results expr layout ctx offset source source' values evm stackPrefix
      hCtxLayout hNoDup hOwned hAccess hPrefixLen hRel hEval
    cases expr with
    | lit value =>
        simp [Source.Expr.eval] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        rcases hRel with ⟨hShared, baseStack, hStack, hStackRel⟩
        let evm' :=
          evm.replaceStackAndIncrPC (evm.stack.push value) (pcΔ := 33)
        refine ⟨evm', ?_, ?_⟩
        · simp [Direct.Expr.runCode, Structured.BasicInstr.step,
            Assembly.Target.stepInstr, evm']
        · constructor
          · simpa [evm', EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] using hShared
          · refine ⟨baseStack, ?_, hStackRel⟩
            simp [evm', hStack, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, List.append_assoc]
    | var name =>
        unfold Source.Expr.eval at hEval
        cases hLookup : source.vars name with
        | none =>
            simp [hLookup, Source.invalid, invalid, Structured.invalid] at hEval
        | some value =>
            simp [hLookup] at hEval
            rcases hEval with ⟨rfl, rfl⟩
            rcases hAccess with ⟨idx, hName, hBound⟩
            rcases hRel with ⟨hShared, baseStack, hStack, hStackRel⟩
            have hBaseAt : baseStack[idx]? = some value := by
              have hSlot := hStackRel.2 hName
              simpa [hLookup] using hSlot
            have hStackAt : evm.stack[offset + idx]? = some value := by
              rw [hStack]
              have hOffsetLen : offset = stackPrefix.length := hPrefixLen.symm
              subst offset
              rw [List.getElem?_append_right]
              · simpa using hBaseAt
              · simp
            let evm' := evm.replaceStackAndIncrPC (value :: evm.stack)
            have hRun :
                Direct.Expr.runCode ctx offset (.var name) evm = .ok evm' := by
              simpa [evm'] using
                (Direct.Expr.runCode_var_layout_slot_value ctx evm name layout
                  (idx := idx) (offset := offset) hCtxLayout hNoDup hName
                  hStackAt hBound)
            refine ⟨evm', hRun, ?_⟩
            constructor
            · simpa [evm', EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC] using hShared
            · refine ⟨baseStack, ?_, hStackRel⟩
              simp [evm', hStack, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC, List.append_assoc]
    | code _code =>
        simp [Source.Expr.SourceOwned] at hOwned
    | prim op args =>
        unfold Source.Expr.eval at hEval
        cases hArgs : Source.Expr.ExprSeq.eval prim args source with
        | error err =>
            simp [hArgs] at hEval
        | ok argResult =>
            rcases argResult with ⟨sourceAfterArgs, argValues⟩
            simp [hArgs] at hEval
            cases hPrimEval :
                prim.eval op sourceAfterArgs.shared argValues with
            | error err =>
                simp [hPrimEval] at hEval
            | ok primResult =>
                rcases primResult with ⟨shared', values'⟩
                simp [hPrimEval] at hEval
                rcases hEval with ⟨rfl, rfl⟩
                rcases
                  runSeqCode_of_eval_sourceOwned hPrim
                    (layout := layout) (ctx := ctx) (offset := offset)
                    (source := source) (source' := sourceAfterArgs)
                    (values := argValues) (evm := evm)
                    (stackPrefix := stackPrefix)
                    hCtxLayout hNoDup hOwned hAccess hPrefixLen hRel hArgs with
                  ⟨evmAfterArgs, hRunArgs, hArgsRel⟩
                rcases hArgsRel with
                  ⟨hArgsShared, baseStack, hArgsStack, hArgsStackRel⟩
                rcases hPrim.eval_step_exists
                    (baseStack := stackPrefix ++ baseStack)
                    hPrimEval hArgsShared
                    (by
                      rw [hArgsStack]
                      simp [List.append_assoc]) with
                  ⟨evmAfterPrim, hStep, hStepShared, hStepStack⟩
                refine ⟨evmAfterPrim, ?_, ?_⟩
                · simp [Direct.Expr.runCode, hRunArgs, hStep]
                · constructor
                  · simpa [Source.State.withShared] using hStepShared
                  · refine ⟨baseStack, ?_, ?_⟩
                    · rw [hStepStack]
                      simp [List.append_assoc]
                    · simpa [Source.State.withShared] using hArgsStackRel

  theorem runSeqCode_of_eval_sourceOwned {prim : Source.PrimitiveSemantics}
      (hPrim : PrimitiveSound prim) :
      ∀ {results : Nat} {exprs : ExprSeq results}
        {layout : List Name} {ctx : Ctx} {offset : Nat}
        {source source' : Source.State} {values : List Word}
        {evm : EVMState} {stackPrefix : List Word},
        ctx.layout = layout →
        layout.Nodup →
        Source.ExprSeq.SourceOwned exprs →
        ExprSeq.Accessible layout offset exprs →
        stackPrefix.length = offset →
        StackPrefixRel layout source stackPrefix evm →
        Source.Expr.ExprSeq.eval prim exprs source = .ok (source', values) →
          ∃ evm',
            Direct.Expr.ExprSeq.runCode ctx offset exprs evm = .ok evm' ∧
              StackPrefixRel layout source' (values.reverse ++ stackPrefix)
                evm' := by
    intro results exprs layout ctx offset source source' values evm stackPrefix
      hCtxLayout hNoDup hOwned hAccess hPrefixLen hRel hEval
    cases exprs with
    | nil =>
        simp [Source.Expr.ExprSeq.eval] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        refine ⟨evm, ?_, ?_⟩
        · simp [Direct.Expr.ExprSeq.runCode]
        · simpa using hRel
    | @cons left right head tail =>
        simp [Source.ExprSeq.SourceOwned] at hOwned
        rcases hOwned with ⟨hHeadOwned, hTailOwned⟩
        simp [ExprSeq.Accessible] at hAccess
        rcases hAccess with ⟨hHeadAccess, hTailAccess⟩
        unfold Source.Expr.ExprSeq.eval at hEval
        cases hHead : Source.Expr.eval prim head source with
        | error err =>
            simp [hHead] at hEval
        | ok headResult =>
            rcases headResult with ⟨sourceAfterHead, headValues⟩
            simp [hHead] at hEval
            cases hTail :
                Source.Expr.ExprSeq.eval prim tail sourceAfterHead with
            | error err =>
                simp [hTail] at hEval
            | ok tailResult =>
                rcases tailResult with ⟨sourceAfterTail, tailValues⟩
                simp [hTail] at hEval
                rcases hEval with ⟨rfl, rfl⟩
                rcases
                  runCode_of_eval_sourceOwned hPrim
                    (layout := layout) (ctx := ctx) (offset := offset)
                    (source := source) (source' := sourceAfterHead)
                    (values := headValues) (evm := evm)
                    (stackPrefix := stackPrefix)
                    hCtxLayout hNoDup hHeadOwned hHeadAccess hPrefixLen hRel
                    hHead with
                  ⟨evmAfterHead, hRunHead, hHeadRel⟩
                have hHeadLen :
                    headValues.length = left :=
                  eval_length_of_sourceOwned hPrim hHeadOwned hHead
                have hNextPrefixLen :
                    (headValues.reverse ++ stackPrefix).length =
                      offset + left := by
                  simp [hHeadLen, hPrefixLen, Nat.add_comm]
                rcases
                  runSeqCode_of_eval_sourceOwned hPrim
                    (layout := layout) (ctx := ctx) (offset := offset + left)
                    (source := sourceAfterHead) (source' := sourceAfterTail)
                    (values := tailValues) (evm := evmAfterHead)
                    (stackPrefix := headValues.reverse ++ stackPrefix)
                    hCtxLayout hNoDup hTailOwned hTailAccess hNextPrefixLen
                    hHeadRel hTail with
                  ⟨evmAfterTail, hRunTail, hTailRel⟩
                refine ⟨evmAfterTail, ?_, ?_⟩
                · simp [Direct.Expr.ExprSeq.runCode, hRunHead, hRunTail]
                · simpa [List.reverse_append, List.append_assoc] using hTailRel
end

end Expr

namespace Switch

theorem source_select_eq (scrutinee : Word)
    (cases : List (Word × Block)) (defaultBody : Option Block) :
    Source.Switch.select scrutinee cases defaultBody =
      Direct.Switch.select scrutinee cases defaultBody := by
  induction cases with
  | nil =>
      cases defaultBody <;> rfl
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      by_cases hEq : value = scrutinee
      · simp [Source.Switch.select, Direct.Switch.select, hEq]
      · simp [Source.Switch.select, Direct.Switch.select, hEq, ih]

end Switch

def ExprResultRel (layout : List Name) (source : Source.State)
    (values : List Word) (target : RunState) : Prop :=
  target.evm.toSharedState = source.shared ∧
    ∃ baseStack : EvmYul.Stack Word,
      target.evm.stack = values ++ baseStack ∧
        StackStoreRel layout source.vars baseStack

namespace ExprResultRel

theorem of_stateRel_push {layout : List Name} {source : Source.State}
    {target : RunState} {values : List Word} {evm : EVMState}
    (hRel : StateRel layout source target)
    (hShared : evm.toSharedState = target.evm.toSharedState)
    (hStack : evm.stack = values ++ target.evm.stack) :
    ExprResultRel layout source values (target.withEVM evm) := by
  rcases hRel with ⟨hSharedRel, hStackRel⟩
  exact ⟨by simpa [hSharedRel] using hShared,
    ⟨target.evm.stack, by simpa using hStack, hStackRel⟩⟩

theorem to_stateRel_cons_insert {layout : List Name}
    {source : Source.State} {target : RunState} {name : Name}
    {value : Word}
    (hFresh : name ∉ layout)
    (hRel : ExprResultRel layout source [value] target) :
    StateRel (name :: layout) (source.insert name value) target := by
  rcases hRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  constructor
  · simpa [Source.State.insert] using hShared
  · rw [hStack]
    exact StackStoreRel.cons_insert hFresh hStackRel

end ExprResultRel

namespace Expr

theorem lit_bridge {prim : Source.PrimitiveSemantics} {layout : List Name}
    {source : Source.State} {target : RunState} {ctx : Ctx}
    {value : Word}
    (hRel : StateRel layout source target) :
    Source.Expr.eval prim (Expr.lit value) source = .ok (source, [value]) ∧
      ∃ evm,
        Direct.Expr.runCode ctx 0 (Expr.lit value) target.evm = .ok evm ∧
          ExprResultRel layout source [value] (target.withEVM evm) := by
  constructor
  · rfl
  · let evm :=
      target.evm.replaceStackAndIncrPC (target.evm.stack.push value)
        (pcΔ := 33)
    refine ⟨evm, ?hRun, ?hResult⟩
    · simp [Direct.Expr.runCode, Structured.BasicInstr.step,
        Assembly.Target.stepInstr, evm]
    · exact
        ExprResultRel.of_stateRel_push hRel
          (by simp [evm, EvmYul.Stack.push,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC])
          (by simp [evm, EvmYul.Stack.push,
            EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC])

theorem evalOne_bridge_sourceOwned {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {expr : Expr 1} {layout : List Name} {source source' : Source.State}
    {value : Word} {target : RunState} {ctx : Ctx}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible layout 0 expr)
    (hRel : StateRel layout source target)
    (hEvalOne : Source.Expr.evalOne prim expr source = .ok (source', value)) :
    ∃ evm,
      Direct.Expr.runCode ctx 0 expr target.evm = .ok evm ∧
        ExprResultRel layout source' [value] (target.withEVM evm) := by
  have hEval := eval_of_evalOne hEvalOne
  rcases runCode_of_eval_sourceOwned hPrim
      (layout := layout) (ctx := ctx) (offset := 0)
      (source := source) (source' := source') (values := [value])
      (evm := target.evm) (stackPrefix := [])
      hCtxLayout hNoDup hOwned hAccess rfl
      (StackPrefixRel.of_stateRel hRel) hEval with
    ⟨evm, hRun, hPrefixRel⟩
  have hResult : ExprResultRel layout source' [value] (target.withEVM evm) := by
    rcases hPrefixRel with ⟨hShared, baseStack, hStack, hStackRel⟩
    exact ⟨by simpa [Structured.RunState.withEVM] using hShared,
      baseStack, by simpa [Structured.RunState.withEVM] using hStack,
      hStackRel⟩
  exact ⟨evm, hRun, hResult⟩

theorem evalCondition_bridge_sourceOwned {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {expr : Expr 1} {layout : List Name} {source source' : Source.State}
    {value : Word} {target : RunState} {ctx : Ctx}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible layout 0 expr)
    (hRel : StateRel layout source target)
    (hEvalOne : Source.Expr.evalOne prim expr source = .ok (source', value)) :
    ∃ target',
      Source.Expr.evalCondition prim expr source =
        .ok (source', value != EvmYul.UInt256.ofNat 0) ∧
      Direct.Expr.runCondition ctx expr target =
        .ok (target', value != EvmYul.UInt256.ofNat 0) ∧
      StateRel layout source' target' := by
  rcases evalOne_bridge_sourceOwned hPrim hCtxLayout hNoDup hOwned hAccess
      hRel hEvalOne with
    ⟨evmAfterExpr, hRunExpr, hExprRel⟩
  rcases hExprRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  have hStackEVM : evmAfterExpr.stack = [value] ++ baseStack := by
    simpa [Structured.RunState.withEVM] using hStack
  let evmAfterPop : EVMState := { evmAfterExpr with stack := baseStack }
  let target' : RunState := target.withEVM evmAfterPop
  refine ⟨target', ?hSource, ?hTarget, ?hRel⟩
  · simp [Source.Expr.evalCondition, hEvalOne]
  · simp [Direct.Expr.runCondition, hRunExpr,
      Structured.Code.popCondition, hStackEVM, EvmYul.Stack.pop, target',
      evmAfterPop]
  · exact
      ⟨by simpa [target', evmAfterPop, Structured.RunState.withEVM]
          using hShared,
        by simpa [target', evmAfterPop, Structured.RunState.withEVM]
          using hStackRel⟩

theorem evalOne_pop_bridge_sourceOwned {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {expr : Expr 1} {layout : List Name} {source source' : Source.State}
    {value : Word} {target : RunState} {ctx : Ctx}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible layout 0 expr)
    (hRel : StateRel layout source target)
    (hEvalOne : Source.Expr.evalOne prim expr source = .ok (source', value)) :
    ∃ targetAfterExpr targetAfterPop stackAfterPop,
      Direct.Expr.runState ctx expr target = .ok targetAfterExpr ∧
      targetAfterExpr.evm.stack.pop = some (stackAfterPop, value) ∧
      targetAfterPop =
        targetAfterExpr.withEVM
          { targetAfterExpr.evm with stack := stackAfterPop } ∧
      StateRel layout source' targetAfterPop := by
  rcases evalOne_bridge_sourceOwned hPrim hCtxLayout hNoDup hOwned hAccess
      hRel hEvalOne with
    ⟨evmAfterExpr, hRunExpr, hExprRel⟩
  rcases hExprRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  have hStackEVM : evmAfterExpr.stack = [value] ++ baseStack := by
    simpa [Structured.RunState.withEVM] using hStack
  let targetAfterExpr : RunState := target.withEVM evmAfterExpr
  let targetAfterPop : RunState :=
    targetAfterExpr.withEVM { targetAfterExpr.evm with stack := baseStack }
  refine ⟨targetAfterExpr, targetAfterPop, baseStack, ?hRunState, ?hPop,
    rfl, ?hRel⟩
  · simp [Direct.Expr.runState, hRunExpr, targetAfterExpr]
  · simp [targetAfterExpr, hStackEVM, EvmYul.Stack.pop]
  · exact
      ⟨by simpa [targetAfterPop, targetAfterExpr,
          Structured.RunState.withEVM] using hShared,
        by simpa [targetAfterPop, targetAfterExpr,
          Structured.RunState.withEVM] using hStackRel⟩

theorem var_bridge {prim : Source.PrimitiveSemantics} {layout : List Name}
    {source : Source.State} {target : RunState} {ctx : Ctx}
    {name : Name} {idx : Nat}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hRel : StateRel layout source target) :
    ∃ value evm,
      Source.Expr.eval prim (Expr.var name) source = .ok (source, [value]) ∧
        Direct.Expr.runCode ctx 0 (Expr.var name) target.evm = .ok evm ∧
          ExprResultRel layout source [value] (target.withEVM evm) := by
  rcases hRel with ⟨hShared, hStackRel⟩
  rcases StackStoreRel.lookup_value hStackRel hName with
    ⟨value, hStackAt, hStore⟩
  let evm := target.evm.replaceStackAndIncrPC (value :: target.evm.stack)
  refine ⟨value, evm, ?hSource, ?hTarget, ?hResult⟩
  · simp [Source.Expr.eval, hStore]
  · simpa [evm] using
      (Direct.Expr.runCode_var_layout_slot_value ctx target.evm name layout
        (idx := idx) (offset := 0) hCtxLayout hNoDup hName
        (by simpa using hStackAt) (by simpa using hBound))
  · exact
      ExprResultRel.of_stateRel_push
        (layout := layout) (source := source) (target := target)
        (values := [value]) (evm := evm) ⟨hShared, hStackRel⟩
        (by simp [evm, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC])
        (by simp [evm, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC])

end Expr

namespace Assignment

theorem stackOp_swap?_step_eq_swap {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) (state : EVMState) :
    ∃ op, Locals.StackOp.swap? n = some op ∧
      Structured.BasicOp.step op state = EvmYul.swap n state := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> refine ⟨_, rfl, rfl⟩

theorem evm_swap_assign_get? {state : EVMState}
    {locals : EvmYul.Stack Word} {idx : Nat} {old value : Word}
    (hStack : state.stack = value :: locals)
    (hLocal : locals[idx]? = some old) :
    EvmYul.swap (idx + 1) state =
      .ok (state.replaceStackAndIncrPC
        (old :: locals.take idx ++ [value] ++ locals.drop (idx + 1))) := by
  have hLocals :
      locals = locals.take idx ++ old :: locals.drop (idx + 1) :=
    StackLowering.list_eq_take_getElem?_drop hLocal
  let base : EVMState := { state with stack := locals }
  have hSwap :=
    Structured.Preservation.StackShuffle.swap_snoc
      (state := base) (front := locals.take idx)
      (suffix := locals.drop (idx + 1)) (top := value) (last := old)
  have hLocals' :
      locals = locals.take idx ++ [old] ++ locals.drop (idx + 1) := by
    simpa [List.append_assoc] using hLocals
  have hStart :
      { base with
          stack := value :: locals.take idx ++ [old] ++
            locals.drop (idx + 1) } = state := by
    cases state with
    | mk shared pc stack execLength =>
        dsimp [base] at hStack ⊢
        subst stack
        have hStackEq :
            value :: locals.take idx ++ [old] ++ locals.drop (idx + 1) =
              value :: locals :=
          congrArg (fun xs => value :: xs) hLocals'.symm
        simpa [hStackEq] using hLocals.symm
  have hLt : idx < locals.length := by
    rcases List.getElem?_eq_some_iff.mp hLocal with ⟨hLt, _hValue⟩
    exact hLt
  have hTakeLen : (locals.take idx).length = idx := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hLt)]
  rw [hStart] at hSwap
  simpa [hTakeLen, List.append_assoc] using hSwap

theorem assignTop_stateRel {layout : List Name} {source : Source.State}
    {targetAfterExpr : RunState} {ctx : Ctx} {program : Program}
    {fuel : Nat}
    {name : Name} {idx : Nat} {value : Word}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hExprRel : ExprResultRel layout source [value] targetAfterExpr) :
    ∃ targetAfter,
      Direct.Stmt.run program ctx fuel (.assignTop name)
          targetAfterExpr =
        .ok (Outcome.regular targetAfter, ctx) ∧
      StateRel layout
        (source.withVars (Source.Store.insert source.vars name value))
        targetAfter := by
  rcases hExprRel with ⟨hShared, baseStack, hStack, hStackRel⟩
  rcases StackStoreRel.lookup_value hStackRel hName with
    ⟨old, hOld, _hOldStore⟩
  have hDepth :
      Locals.Layout.lookupDepth? name ctx.layout = some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  rcases stackOp_swap?_step_eq_swap
      (n := idx + 1) (by omega) hBound targetAfterExpr.evm with
    ⟨swapOp, hSwapOp, hSwapStep⟩
  let swappedEVM :=
    targetAfterExpr.evm.replaceStackAndIncrPC
      (old :: baseStack.take idx ++ [value] ++ baseStack.drop (idx + 1))
  let finalStack :=
    baseStack.take idx ++ value :: baseStack.drop (idx + 1)
  let finalEVM := swappedEVM.replaceStackAndIncrPC finalStack
  let targetAfter := targetAfterExpr.withEVM finalEVM
  refine ⟨targetAfter, ?hRun, ?hRel⟩
  · have hSwapRun :
        EvmYul.swap (idx + 1) targetAfterExpr.evm =
          .ok swappedEVM := by
      simpa [swappedEVM] using
        (evm_swap_assign_get? (state := targetAfterExpr.evm)
          (locals := baseStack) (idx := idx) (old := old) (value := value)
          hStack hOld)
    have hSwapRun' : swapOp.step targetAfterExpr.evm = .ok swappedEVM := by
      rw [hSwapStep, hSwapRun]
    have hPop :
        Structured.BasicOp.pop.step swappedEVM = .ok finalEVM := by
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimStep.run, Assembly.PrimOp.continuingStep?,
        EvmYul.Stack.pop, swappedEVM, finalEVM, finalStack,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, List.append_assoc]
    simp [Direct.Stmt.run, hDepth, hSwapOp, hSwapRun', hPop,
      targetAfter, Structured.RunState.withEVM]
  · constructor
    · simpa [targetAfter, finalEVM, swappedEVM, Source.State.withVars,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hShared
    · simpa [targetAfter, finalEVM, swappedEVM, finalStack,
        Source.State.withVars, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using
        (StackStoreRel.assign hNoDup hName hStackRel :
          StackStoreRel layout
            (Source.Store.insert source.vars name value) finalStack)

theorem assign_stateRel_of_runState {layout : List Name}
    {sourceAfterValue : Source.State} {targetBefore targetAfterExpr : RunState}
    {ctx : Ctx} {program : Program} {fuel : Nat}
    {name : Name} {idx : Nat} {value : Word} {valueExpr : Expr 1}
    (hExprRun :
      Direct.Expr.runState ctx valueExpr targetBefore = .ok targetAfterExpr)
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hExprRel :
      ExprResultRel layout sourceAfterValue [value] targetAfterExpr) :
    ∃ targetAfter,
      Direct.Stmt.run program ctx fuel (.assign name valueExpr) targetBefore =
        .ok (Outcome.regular targetAfter, ctx) ∧
      StateRel layout
        (sourceAfterValue.withVars
          (Source.Store.insert sourceAfterValue.vars name value))
        targetAfter := by
  rcases assignTop_stateRel (layout := layout)
      (source := sourceAfterValue) (targetAfterExpr := targetAfterExpr)
      (ctx := ctx) (program := program) (fuel := fuel)
      (name := name) (idx := idx) (value := value)
      hCtxLayout hNoDup hName hBound hExprRel with
    ⟨targetAfter, hTopRun, hRel⟩
  refine ⟨targetAfter, ?hAssignRun, hRel⟩
  unfold Direct.Expr.runState at hExprRun
  cases hRunCode : Direct.Expr.runCode ctx 0 valueExpr targetBefore.evm with
  | error err =>
      simp [hRunCode] at hExprRun
  | ok evmAfterValue =>
      simp [hRunCode] at hExprRun
      cases hExprRun
      simpa [Direct.Stmt.run, hRunCode] using hTopRun

end Assignment

namespace Stmt

theorem expr_bridge {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterExpr : Source.State} {target : RunState} {fuel : Nat}
    {expr : Expr 0} {values : List Word}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hRel : StateRel sourceCtx.scope source target)
    (hEval :
      Source.Expr.eval prim expr source = .ok (sourceAfterExpr, values)) :
    ∃ targetAfter,
      Source.Stmt.run prim program sourceCtx fuel (.expr expr) source =
        .ok (Source.Outcome.regular sourceAfterExpr, sourceCtx) ∧
      Direct.Stmt.run program targetCtx fuel (.expr expr) target =
        .ok (Outcome.regular targetAfter, targetCtx) ∧
      StateRel sourceCtx.scope sourceAfterExpr targetAfter ∧
      CtxRel sourceCtx targetCtx := by
  have hValuesLen : values.length = 0 :=
    Expr.eval_length_of_sourceOwned hPrim hOwned hEval
  have hValuesNil : values = [] := by
    cases values with
    | nil => rfl
    | cons _head _tail =>
        simp at hValuesLen
  rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  rcases Expr.runCode_of_eval_sourceOwned hPrim
      (layout := sourceCtx.scope) (ctx := targetCtx) (offset := 0)
      (source := source) (source' := sourceAfterExpr) (values := values)
      (evm := target.evm) (stackPrefix := [])
      (by simpa [hLayout]) hNoDup hOwned hAccess rfl
      (StackPrefixRel.of_stateRel hRel) hEval with
    ⟨evm, hTargetExpr, hExprRel⟩
  have hTargetRunState :
      Direct.Expr.runState targetCtx expr target = .ok (target.withEVM evm) := by
    simp [Direct.Expr.runState, hTargetExpr]
  have hExprRelNil :
      StackPrefixRel sourceCtx.scope sourceAfterExpr [] evm := by
    simpa [hValuesNil] using hExprRel
  refine ⟨target.withEVM evm, ?_, ?_, ?_, hCtxRel⟩
  · simp [Source.Stmt.run, hEval]
  · simp [Direct.Stmt.run, hTargetRunState]
  · exact StackPrefixRel.to_stateRel_nil
      (target := target.withEVM evm) hExprRelNil

theorem let_lit_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {name : Name} {value : Word}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel : StateRel sourceCtx.scope source target) :
    Source.Stmt.run prim program sourceCtx fuel (.let_ name (.lit value))
        source =
      .ok
        (Source.Outcome.regular (source.insert name value),
          { sourceCtx with scope := name :: sourceCtx.scope }) ∧
      ∃ targetAfter,
        Direct.Stmt.run program targetCtx fuel (.let_ name (.lit value))
            target =
          .ok
            (Outcome.regular targetAfter,
              targetCtx.withLayout (name :: targetCtx.layout)) ∧
        StateRel (name :: sourceCtx.scope) (source.insert name value)
          targetAfter ∧
        CtxRel { sourceCtx with scope := name :: sourceCtx.scope }
          (targetCtx.withLayout (name :: targetCtx.layout)) := by
  rcases Expr.lit_bridge (prim := prim) (layout := sourceCtx.scope)
      (source := source) (target := target) (ctx := targetCtx)
      (value := value) hRel with
    ⟨hSourceExpr, evm, hTargetExpr, hExprRel⟩
  have hSourceEvalOne :
      Source.Expr.evalOne prim (Expr.lit value) source =
        .ok (source, value) := by
    simp [Source.Expr.evalOne, hSourceExpr]
  have hTargetRunState :
      Direct.Expr.runState targetCtx (Expr.lit value) target =
        .ok (target.withEVM evm) := by
    simp [Direct.Expr.runState, hTargetExpr]
  refine ⟨?hSource, target.withEVM evm, ?hTarget, ?hState, ?hCtx⟩
  · simp [Source.Stmt.run, hSourceEvalOne]
  · simp [Direct.Stmt.run, hTargetRunState]
  · exact ExprResultRel.to_stateRel_cons_insert hFresh hExprRel
  · exact CtxRel.withScopeCons hCtx

theorem let_var_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {name readName : Name} {idx : Nat}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hRead : sourceCtx.scope[idx]? = some readName)
    (hBound : idx + 1 ≤ 16)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel : StateRel sourceCtx.scope source target) :
    ∃ value targetAfter,
      Source.Stmt.run prim program sourceCtx fuel (.let_ name (.var readName))
          source =
        .ok
          (Source.Outcome.regular (source.insert name value),
            { sourceCtx with scope := name :: sourceCtx.scope }) ∧
      Direct.Stmt.run program targetCtx fuel (.let_ name (.var readName))
          target =
        .ok
          (Outcome.regular targetAfter,
            targetCtx.withLayout (name :: targetCtx.layout)) ∧
      StateRel (name :: sourceCtx.scope) (source.insert name value)
        targetAfter ∧
      CtxRel { sourceCtx with scope := name :: sourceCtx.scope }
        (targetCtx.withLayout (name :: targetCtx.layout)) := by
  rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  rcases Expr.var_bridge (prim := prim) (layout := sourceCtx.scope)
      (source := source) (target := target) (ctx := targetCtx)
      (name := readName) (idx := idx)
      (by simpa [hLayout]) hNoDup hRead hBound hRel with
    ⟨value, evm, hSourceExpr, hTargetExpr, hExprRel⟩
  have hSourceEvalOne :
      Source.Expr.evalOne prim (Expr.var readName) source =
        .ok (source, value) := by
    simp [Source.Expr.evalOne, hSourceExpr]
  have hTargetRunState :
      Direct.Expr.runState targetCtx (Expr.var readName) target =
        .ok (target.withEVM evm) := by
    simp [Direct.Expr.runState, hTargetExpr]
  refine ⟨value, target.withEVM evm, ?hSource, ?hTarget, ?hState, ?hCtx⟩
  · simp [Source.Stmt.run, hSourceEvalOne]
  · simp [Direct.Stmt.run, hTargetRunState]
  · exact ExprResultRel.to_stateRel_cons_insert hFresh hExprRel
  · exact CtxRel.withScopeCons hCtxRel

theorem let_expr_bridge {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterValue : Source.State} {target : RunState} {fuel : Nat}
    {name : Name} {value : Word} {expr : Expr 1}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalOne :
      Source.Expr.evalOne prim expr source = .ok (sourceAfterValue, value)) :
    ∃ targetAfter,
      Source.Stmt.run prim program sourceCtx fuel (.let_ name expr) source =
        .ok
          (Source.Outcome.regular (sourceAfterValue.insert name value),
            { sourceCtx with scope := name :: sourceCtx.scope }) ∧
      Direct.Stmt.run program targetCtx fuel (.let_ name expr) target =
        .ok
          (Outcome.regular targetAfter,
            targetCtx.withLayout (name :: targetCtx.layout)) ∧
      StateRel (name :: sourceCtx.scope) (sourceAfterValue.insert name value)
        targetAfter ∧
      CtxRel { sourceCtx with scope := name :: sourceCtx.scope }
        (targetCtx.withLayout (name :: targetCtx.layout)) := by
  rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  rcases Expr.evalOne_bridge_sourceOwned hPrim
      (layout := sourceCtx.scope) (source := source)
      (source' := sourceAfterValue) (value := value)
      (target := target) (ctx := targetCtx)
      (by simpa [hLayout]) hNoDup hOwned hAccess hRel hEvalOne with
    ⟨evm, hTargetExpr, hExprRel⟩
  have hTargetRunState :
      Direct.Expr.runState targetCtx expr target = .ok (target.withEVM evm) := by
    simp [Direct.Expr.runState, hTargetExpr]
  refine ⟨target.withEVM evm, ?_, ?_, ?_, ?_⟩
  · simp [Source.Stmt.run, hEvalOne]
  · simp [Direct.Stmt.run, hTargetRunState]
  · exact ExprResultRel.to_stateRel_cons_insert hFresh hExprRel
  · exact CtxRel.withScopeCons hCtxRel

theorem assign_lit_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {name : Name} {idx : Nat} {value : Word}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hName : sourceCtx.scope[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hRel : StateRel sourceCtx.scope source target) :
    ∃ targetAfter,
      Source.Stmt.run prim program sourceCtx fuel
          (.assign name (.lit value)) source =
        .ok
          (Source.Outcome.regular
            (source.withVars (Source.Store.insert source.vars name value)),
            sourceCtx) ∧
      Direct.Stmt.run program targetCtx fuel (.assign name (.lit value))
          target =
        .ok (Outcome.regular targetAfter, targetCtx) ∧
      StateRel sourceCtx.scope
        (source.withVars (Source.Store.insert source.vars name value))
        targetAfter ∧
      CtxRel sourceCtx targetCtx := by
  rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hContains : source.vars.contains name = true :=
    StackStoreRel.contains_of_layout hRel.2 hName
  rcases Expr.lit_bridge (prim := prim) (layout := sourceCtx.scope)
      (source := source) (target := target) (ctx := targetCtx)
      (value := value) hRel with
    ⟨hSourceExpr, evm, hTargetExpr, hExprRel⟩
  have hSourceEvalOne :
      Source.Expr.evalOne prim (Expr.lit value) source =
        .ok (source, value) := by
    simp [Source.Expr.evalOne, hSourceExpr]
  have hTargetRunState :
      Direct.Expr.runState targetCtx (Expr.lit value) target =
        .ok (target.withEVM evm) := by
    simp [Direct.Expr.runState, hTargetExpr]
  rcases Assignment.assign_stateRel_of_runState
      (layout := sourceCtx.scope) (sourceAfterValue := source)
      (targetBefore := target) (targetAfterExpr := target.withEVM evm)
      (ctx := targetCtx) (program := program) (fuel := fuel)
      (name := name) (idx := idx) (value := value)
      (valueExpr := Expr.lit value)
      hTargetRunState (by simpa [hLayout]) hNoDup hName hBound hExprRel with
    ⟨targetAfter, hTarget, hTargetRel⟩
  refine ⟨targetAfter, ?hSource, hTarget, hTargetRel, hCtxRel⟩
  simp [Source.Stmt.run, hContains, hSourceEvalOne]

theorem assign_var_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {name readName : Name} {assignIdx readIdx : Nat}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAssignName : sourceCtx.scope[assignIdx]? = some name)
    (hReadName : sourceCtx.scope[readIdx]? = some readName)
    (hAssignBound : assignIdx + 1 ≤ 16)
    (hReadBound : readIdx + 1 ≤ 16)
    (hRel : StateRel sourceCtx.scope source target) :
    ∃ value targetAfter,
      Source.Stmt.run prim program sourceCtx fuel
          (.assign name (.var readName)) source =
        .ok
          (Source.Outcome.regular
            (source.withVars (Source.Store.insert source.vars name value)),
            sourceCtx) ∧
      Direct.Stmt.run program targetCtx fuel (.assign name (.var readName))
          target =
        .ok (Outcome.regular targetAfter, targetCtx) ∧
      StateRel sourceCtx.scope
        (source.withVars (Source.Store.insert source.vars name value))
        targetAfter ∧
      CtxRel sourceCtx targetCtx := by
  rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hContains : source.vars.contains name = true :=
    StackStoreRel.contains_of_layout hRel.2 hAssignName
  rcases Expr.var_bridge (prim := prim) (layout := sourceCtx.scope)
      (source := source) (target := target) (ctx := targetCtx)
      (name := readName) (idx := readIdx)
      (by simpa [hLayout]) hNoDup hReadName hReadBound hRel with
    ⟨value, evm, hSourceExpr, hTargetExpr, hExprRel⟩
  have hSourceEvalOne :
      Source.Expr.evalOne prim (Expr.var readName) source =
        .ok (source, value) := by
    simp [Source.Expr.evalOne, hSourceExpr]
  have hTargetRunState :
      Direct.Expr.runState targetCtx (Expr.var readName) target =
        .ok (target.withEVM evm) := by
    simp [Direct.Expr.runState, hTargetExpr]
  rcases Assignment.assign_stateRel_of_runState
      (layout := sourceCtx.scope) (sourceAfterValue := source)
      (targetBefore := target) (targetAfterExpr := target.withEVM evm)
      (ctx := targetCtx) (program := program) (fuel := fuel)
      (name := name) (idx := assignIdx) (value := value)
      (valueExpr := Expr.var readName)
      hTargetRunState (by simpa [hLayout]) hNoDup hAssignName hAssignBound
      hExprRel with
    ⟨targetAfter, hTarget, hTargetRel⟩
  refine ⟨value, targetAfter, ?hSource, hTarget, hTargetRel, hCtxRel⟩
  simp [Source.Stmt.run, hContains, hSourceEvalOne]

theorem assign_expr_bridge {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterValue : Source.State} {target : RunState} {fuel : Nat}
    {name : Name} {idx : Nat} {value : Word} {expr : Expr 1}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hName : sourceCtx.scope[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalOne :
      Source.Expr.evalOne prim expr source = .ok (sourceAfterValue, value)) :
    ∃ targetAfter,
      Source.Stmt.run prim program sourceCtx fuel (.assign name expr) source =
        .ok
          (Source.Outcome.regular
            (sourceAfterValue.withVars
              (Source.Store.insert sourceAfterValue.vars name value)),
            sourceCtx) ∧
      Direct.Stmt.run program targetCtx fuel (.assign name expr) target =
        .ok (Outcome.regular targetAfter, targetCtx) ∧
      StateRel sourceCtx.scope
        (sourceAfterValue.withVars
          (Source.Store.insert sourceAfterValue.vars name value))
        targetAfter ∧
      CtxRel sourceCtx targetCtx := by
  rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hContains : source.vars.contains name = true :=
    StackStoreRel.contains_of_layout hRel.2 hName
  rcases Expr.evalOne_bridge_sourceOwned hPrim
      (layout := sourceCtx.scope) (source := source)
      (source' := sourceAfterValue) (value := value)
      (target := target) (ctx := targetCtx)
      (by simpa [hLayout]) hNoDup hOwned hAccess hRel hEvalOne with
    ⟨evm, hTargetExpr, hExprRel⟩
  have hTargetRunState :
      Direct.Expr.runState targetCtx expr target = .ok (target.withEVM evm) := by
    simp [Direct.Expr.runState, hTargetExpr]
  rcases Assignment.assign_stateRel_of_runState
      (layout := sourceCtx.scope) (sourceAfterValue := sourceAfterValue)
      (targetBefore := target) (targetAfterExpr := target.withEVM evm)
      (ctx := targetCtx) (program := program) (fuel := fuel)
      (name := name) (idx := idx) (value := value) (valueExpr := expr)
      hTargetRunState (by simpa [hLayout]) hNoDup hName hBound hExprRel with
    ⟨targetAfter, hTarget, hTargetRel⟩
  refine ⟨targetAfter, ?_, hTarget, hTargetRel, hCtxRel⟩
  · simp [Source.Stmt.run, hContains, hEvalOne]

theorem brk_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {breakScope : List Name}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hBreak : sourceCtx.breakScope? = some breakScope)
    (hRel : StateRel targetCtx.layout source target) :
    ∃ targetAfter,
      Source.Stmt.run prim program sourceCtx fuel .brk source =
        .ok (Source.Outcome.brk (source.restrictTo breakScope), sourceCtx) ∧
      Direct.Stmt.run program targetCtx fuel .brk target =
        .ok (Outcome.brk targetAfter, targetCtx) ∧
      StateRel breakScope (source.restrictTo breakScope) targetAfter ∧
      CtxRel sourceCtx targetCtx ∧
      CtxHandlersRel sourceCtx targetCtx := by
  rcases hCtx with ⟨hLayout, hBreakDepth, hContinue, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreakDepth, hContinue, hLeave, hRetc⟩
  have hTargetDepth : targetCtx.breakDepth? = some breakScope.length := by
    rw [hBreakDepth, hBreak]
    rfl
  have hScope : CleanupScopeRel targetCtx.layout breakScope :=
    hHandlers.1 breakScope hBreak
  rcases StateRel.cleanupTo_scope_exists hScope hRel with
    ⟨targetAfter, hCleanup, hTargetRel, _hReturns⟩
  refine ⟨targetAfter, ?_, ?_, ?_, hCtxRel, hHandlers⟩
  · simp [Source.Stmt.run, hBreak]
  · simp [Direct.Stmt.run, hTargetDepth, hCleanup]
  · exact hTargetRel

theorem cont_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {continueScope : List Name}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hContinue : sourceCtx.continueScope? = some continueScope)
    (hRel : StateRel targetCtx.layout source target) :
    ∃ targetAfter,
      Source.Stmt.run prim program sourceCtx fuel .cont source =
        .ok
          (Source.Outcome.cont (source.restrictTo continueScope),
            sourceCtx) ∧
      Direct.Stmt.run program targetCtx fuel .cont target =
        .ok (Outcome.cont targetAfter, targetCtx) ∧
      StateRel continueScope (source.restrictTo continueScope) targetAfter ∧
      CtxRel sourceCtx targetCtx ∧
      CtxHandlersRel sourceCtx targetCtx := by
  rcases hCtx with ⟨hLayout, hBreak, hContinueDepth, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreak, hContinueDepth, hLeave, hRetc⟩
  have hTargetDepth :
      targetCtx.continueDepth? = some continueScope.length := by
    rw [hContinueDepth, hContinue]
    rfl
  have hScope : CleanupScopeRel targetCtx.layout continueScope :=
    hHandlers.2.1 continueScope hContinue
  rcases StateRel.cleanupTo_scope_exists hScope hRel with
    ⟨targetAfter, hCleanup, hTargetRel, _hReturns⟩
  refine ⟨targetAfter, ?_, ?_, ?_, hCtxRel, hHandlers⟩
  · simp [Source.Stmt.run, hContinue]
  · simp [Direct.Stmt.run, hTargetDepth, hCleanup]
  · exact hTargetRel

end Stmt

def ModeRel : Source.Mode → Structured.Mode → Prop
  | .regular, .regular => True
  | .brk, .brk => True
  | .cont, .cont => True
  | .leave, .leave => True
  | .halt sourceKind, .halt targetKind => sourceKind = targetKind
  | _, _ => False

def OutcomeRel (layout : List Name) (source : Source.Outcome)
    (target : Outcome) : Prop :=
  match source.mode, target.mode with
  | .regular, .regular => StateRel layout source.state target.state
  | .brk, .brk => StateRel layout source.state target.state
  | .cont, .cont => StateRel layout source.state target.state
  | .leave, .leave => StateRel layout source.state target.state
  | .halt sourceKind, .halt targetKind =>
      target.state.evm.toSharedState = source.state.shared ∧
        sourceKind = targetKind
  | _, _ => False

namespace OutcomeRel

theorem regular {layout : List Name} {source : Source.State}
    {target : RunState}
    (hRel : StateRel layout source target) :
    OutcomeRel layout (Source.Outcome.regular source)
      (Outcome.regular target) := by
  exact hRel

theorem brk {layout : List Name} {source : Source.State}
    {target : RunState}
    (hRel : StateRel layout source target) :
    OutcomeRel layout (Source.Outcome.brk source) (Outcome.brk target) := by
  exact hRel

theorem cont {layout : List Name} {source : Source.State}
    {target : RunState}
    (hRel : StateRel layout source target) :
    OutcomeRel layout (Source.Outcome.cont source) (Outcome.cont target) := by
  exact hRel

theorem leave {layout : List Name} {source : Source.State}
    {target : RunState}
    (hRel : StateRel layout source target) :
    OutcomeRel layout (Source.Outcome.leave source) (Outcome.leave target) := by
  exact hRel

theorem halt {layout : List Name} {kind : Assembly.HaltKind}
    {source : Source.State} {target : RunState}
    (hRel : StateRel layout source target) :
    OutcomeRel layout (Source.Outcome.halt kind source)
      (Outcome.halt kind target) := by
  exact ⟨hRel.1, rfl⟩

theorem halt_shared {layout : List Name} {kind : Assembly.HaltKind}
    {source : Source.State} {target : RunState}
    (hShared : target.evm.toSharedState = source.shared) :
    OutcomeRel layout (Source.Outcome.halt kind source)
      (Outcome.halt kind target) := by
  exact ⟨hShared, rfl⟩

end OutcomeRel

namespace Stmt

theorem terminal_bridge {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {kind : Assembly.HaltKind} {shared' : EvmYul.SharedState .EVM}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hTerminal : prim.terminal kind source.shared [] = .ok shared') :
    ∃ sourceAfter targetAfter,
      Source.Stmt.run prim program sourceCtx fuel (.terminal kind) source =
        .ok (Source.Outcome.halt kind sourceAfter, sourceCtx) ∧
      Direct.Stmt.run program targetCtx fuel (.terminal kind) target =
        .ok (Outcome.halt kind targetAfter, targetCtx) ∧
      OutcomeRel sourceCtx.scope (Source.Outcome.halt kind sourceAfter)
        (Outcome.halt kind targetAfter) ∧
      CtxRel sourceCtx targetCtx := by
  rcases hRel with ⟨hInitialShared, hStackRel⟩
  have hRel : StateRel sourceCtx.scope source target :=
    ⟨hInitialShared, hStackRel⟩
  rcases StateRel.cleanupAll_exists hCtx hRel with
    ⟨cleaned, hCleanup, hCleanupShared, hCleanupStack, _hReturns⟩
  have hCleanedShared : cleaned.evm.toSharedState = source.shared :=
    hCleanupShared.trans hInitialShared
  rcases
      hPrim.terminal_step_exists
        (kind := kind) (shared := source.shared) (shared' := shared')
        (values := []) (evm := cleaned.evm) (baseStack := [])
        hTerminal hCleanedShared (by simpa using hCleanupStack) with
    ⟨evm', hStep, hStepShared⟩
  let sourceAfter := source.withShared shared'
  let targetAfter : RunState := cleaned.withEVM evm'
  refine ⟨sourceAfter, targetAfter, ?hSource, ?hTarget, ?hOutcome, hCtx⟩
  · simp [Source.Stmt.run, hTerminal, sourceAfter]
  · unfold Direct.Stmt.run
    simp [hCleanup, hStep, targetAfter]
  · exact OutcomeRel.halt_shared
      (layout := sourceCtx.scope) (kind := kind)
      (source := sourceAfter) (target := targetAfter)
      (by simpa [sourceAfter, targetAfter, Source.State.withShared] using
        hStepShared)

theorem terminalArgs_bridge {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterArgs : Source.State} {target : RunState} {fuel : Nat}
    {kind : Assembly.HaltKind} {args : ExprSeq kind.argCount}
    {values : List Word} {shared' : EvmYul.SharedState .EVM}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.ExprSeq.SourceOwned args)
    (hAccess : ExprSeq.Accessible sourceCtx.scope 0 args)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalArgs :
      Source.Expr.ExprSeq.eval prim args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      prim.terminal kind sourceAfterArgs.shared values = .ok shared') :
    ∃ targetAfter,
      Source.Stmt.run prim program sourceCtx fuel
          (.terminalArgs kind args) source =
        .ok
          (Source.Outcome.halt kind
            (sourceAfterArgs.withShared shared'),
            sourceCtx) ∧
      Direct.Stmt.run program targetCtx fuel (.terminalArgs kind args)
          target =
        .ok (Outcome.halt kind targetAfter, targetCtx) ∧
      OutcomeRel sourceCtx.scope
        (Source.Outcome.halt kind (sourceAfterArgs.withShared shared'))
        (Outcome.halt kind targetAfter) ∧
      CtxRel sourceCtx targetCtx := by
  rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  have hCtxRel : CtxRel sourceCtx targetCtx :=
    ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
  rcases Expr.runSeqCode_of_eval_sourceOwned hPrim
      (layout := sourceCtx.scope) (ctx := targetCtx) (offset := 0)
      (source := source) (source' := sourceAfterArgs) (values := values)
      (evm := target.evm) (stackPrefix := [])
      (by simpa [hLayout]) hNoDup hOwned hAccess rfl
      (StackPrefixRel.of_stateRel hRel) hEvalArgs with
    ⟨evmAfterArgs, hRunArgs, hArgsRel⟩
  rcases hArgsRel with
    ⟨hArgsShared, baseStack, hArgsStack, _hArgsStackRel⟩
  rcases hPrim.terminal_step_exists
      (kind := kind) (shared := sourceAfterArgs.shared)
      (shared' := shared') (values := values)
      (evm := evmAfterArgs) (baseStack := baseStack)
      hTerminal hArgsShared (by simpa using hArgsStack) with
    ⟨evmAfter, hStep, hStepShared⟩
  let targetAfter : RunState := target.withEVM evmAfter
  refine ⟨targetAfter, ?_, ?_, ?_, hCtxRel⟩
  · simp [Source.Stmt.run, hEvalArgs, hTerminal, Source.State.withShared]
  · simp [Direct.Stmt.run, hRunArgs, hStep, targetAfter]
  · exact OutcomeRel.halt_shared
      (layout := sourceCtx.scope) (kind := kind)
      (source := sourceAfterArgs.withShared shared')
      (target := targetAfter)
      (by simpa [targetAfter, Source.State.withShared,
        Structured.RunState.withEVM] using hStepShared)

end Stmt

/--
Result relation for one source/direct statement or open-block step.

Regular fallthrough exposes the next source context and its lowering relation.
Abrupt control only exposes the resulting source/target states at the retained
source scope; the cleanup depth used to get there remains owned by the lowering
proofs that construct this relation.
-/
def RunResultRel (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Outcome × Ctx) : Prop :=
  match sourceResult, targetResult with
  | (sourceOutcome, sourceCtx), (targetOutcome, targetCtx) =>
      match sourceOutcome.mode, targetOutcome.mode with
      | .regular, .regular =>
          StateRel sourceCtx.scope sourceOutcome.state targetOutcome.state ∧
            CtxRel sourceCtx targetCtx ∧
            CtxHandlersRel sourceCtx targetCtx
      | .brk, .brk =>
          ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
      | .cont, .cont =>
          ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
      | .leave, .leave =>
          ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
      | .halt sourceKind, .halt targetKind =>
          targetOutcome.state.evm.toSharedState =
            sourceOutcome.state.shared ∧
          sourceKind = targetKind
      | _, _ => False

def ScopedOutcomeRel (scope : List Name) (sourceOutcome : Source.Outcome)
    (targetOutcome : Outcome) : Prop :=
  match sourceOutcome.mode, targetOutcome.mode with
  | .regular, .regular =>
      StateRel scope sourceOutcome.state targetOutcome.state
  | .brk, .brk =>
      ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
  | .cont, .cont =>
      ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
  | .leave, .leave =>
      ∃ layout, StateRel layout sourceOutcome.state targetOutcome.state
  | .halt sourceKind, .halt targetKind =>
      targetOutcome.state.evm.toSharedState = sourceOutcome.state.shared ∧
          sourceKind = targetKind
      | _, _ => False

def RunResultRelAt (entryCtx : Source.Ctx)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Outcome × Ctx) : Prop :=
  match sourceResult, targetResult with
  | (sourceOutcome, sourceCtx), (targetOutcome, targetCtx) =>
      match sourceOutcome.mode, targetOutcome.mode with
      | .regular, .regular =>
          StateRel sourceCtx.scope sourceOutcome.state targetOutcome.state ∧
            CtxRel sourceCtx targetCtx ∧
            CtxHandlersRel sourceCtx targetCtx
      | .brk, .brk =>
          ∃ scope,
            entryCtx.breakScope? = some scope ∧
              StateRel scope sourceOutcome.state targetOutcome.state
      | .cont, .cont =>
          ∃ scope,
            entryCtx.continueScope? = some scope ∧
              StateRel scope sourceOutcome.state targetOutcome.state
      | .leave, .leave =>
          ∃ scope,
            entryCtx.leaveScope? = some scope ∧
              StateRel scope sourceOutcome.state targetOutcome.state
      | .halt sourceKind, .halt targetKind =>
          targetOutcome.state.evm.toSharedState =
            sourceOutcome.state.shared ∧
          sourceKind = targetKind
      | _, _ => False

def HandlerScopesEq (left right : Source.Ctx) : Prop :=
  left.breakScope? = right.breakScope? ∧
    left.continueScope? = right.continueScope? ∧
    left.leaveScope? = right.leaveScope?

namespace HandlerScopesEq

theorem refl (ctx : Source.Ctx) : HandlerScopesEq ctx ctx := by
  simp [HandlerScopesEq]

theorem symm {left right : Source.Ctx}
    (hEq : HandlerScopesEq left right) :
    HandlerScopesEq right left := by
  rcases hEq with ⟨hBreak, hContinue, hLeave⟩
  exact ⟨hBreak.symm, hContinue.symm, hLeave.symm⟩

theorem trans {left mid right : Source.Ctx}
    (hLeft : HandlerScopesEq left mid)
    (hRight : HandlerScopesEq mid right) :
    HandlerScopesEq left right := by
  rcases hLeft with ⟨hBreakLeft, hContinueLeft, hLeaveLeft⟩
  rcases hRight with ⟨hBreakRight, hContinueRight, hLeaveRight⟩
  exact
    ⟨hBreakLeft.trans hBreakRight, hContinueLeft.trans hContinueRight,
      hLeaveLeft.trans hLeaveRight⟩

end HandlerScopesEq

namespace Structural

theorem stmtLowerable_regular_handlerScopesEq
    {prim : Source.PrimitiveSemantics} {program : Program}
    {sourceCtx sourceCtxAfter : Source.Ctx} {fuel : Nat} {stmt : Stmt}
    {source sourceAfter : Source.State}
    (hLower : StmtLowerable sourceCtx.scope stmt)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel stmt source =
        .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter)) :
    HandlerScopesEq sourceCtx sourceCtxAfter := by
  cases stmt with
  | expr expr =>
      cases hEval : Source.Expr.eval prim expr source with
      | error err =>
          simp [Source.Stmt.run, hEval] at hSourceRun
      | ok result =>
          rcases result with ⟨stateAfterExpr, values⟩
          simp [Source.Stmt.run, hEval] at hSourceRun
          rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
          cases hCtxEq
          exact HandlerScopesEq.refl sourceCtx
  | exprs exprs =>
      cases hLower
  | let_ name value =>
      cases hEval : Source.Expr.evalOne prim value source with
      | error err =>
          simp [Source.Stmt.run, hEval] at hSourceRun
      | ok result =>
          rcases result with ⟨stateAfterValue, value'⟩
          simp [Source.Stmt.run, hEval] at hSourceRun
          rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
          cases hCtxEq
          simp [HandlerScopesEq]
  | assign name value =>
      cases hContains : source.vars.contains name with
      | false =>
          simp [Source.Stmt.run, hContains, Source.invalid,
            Structured.invalid] at hSourceRun
      | true =>
          cases hEval : Source.Expr.evalOne prim value source with
          | error err =>
              simp [Source.Stmt.run, hContains, hEval] at hSourceRun
          | ok result =>
              rcases result with ⟨stateAfterValue, value'⟩
              simp [Source.Stmt.run, hContains, hEval] at hSourceRun
              rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
              cases hCtxEq
              exact HandlerScopesEq.refl sourceCtx
  | assignTop name =>
      cases hLower
  | assignTopWithOffset offset name =>
      cases hLower
  | block body =>
      cases hScoped : Source.Block.runScoped prim program sourceCtx body fuel
          source with
      | error err =>
          simp [Source.Stmt.run, hScoped] at hSourceRun
      | ok outcome =>
          cases outcome with
          | mk blockState mode =>
              cases mode <;> simp [Source.Stmt.run, hScoped,
                Source.Outcome.regular, Source.Outcome.brk,
                Source.Outcome.cont, Source.Outcome.leave,
                Source.Outcome.halt] at hSourceRun
              case regular =>
                rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
                cases hCtxEq
                exact HandlerScopesEq.refl sourceCtx
  | if_ cond body =>
      cases fuel with
      | zero =>
          simp [Source.Stmt.run, Source.invalid, Structured.invalid]
            at hSourceRun
      | succ fuel =>
          cases hCond : Source.Expr.evalCondition prim cond source with
          | error err =>
              simp [Source.Stmt.run, hCond] at hSourceRun
          | ok condResult =>
              rcases condResult with ⟨stateAfterCond, condTrue⟩
              cases condTrue
              · simp [Source.Stmt.run, hCond] at hSourceRun
                rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
                cases hCtxEq
                exact HandlerScopesEq.refl sourceCtx
              · cases hScoped :
                    Source.Block.runScoped prim program sourceCtx body fuel
                      stateAfterCond with
                | error err =>
                    simp [Source.Stmt.run, hCond, hScoped] at hSourceRun
                | ok outcome =>
                    cases outcome with
                    | mk blockState mode =>
                        cases mode <;> simp [Source.Stmt.run, hCond,
                          hScoped, Source.Outcome.regular,
                          Source.Outcome.brk, Source.Outcome.cont,
                          Source.Outcome.leave, Source.Outcome.halt]
                          at hSourceRun
                        case regular =>
                          rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
                          cases hCtxEq
                          exact HandlerScopesEq.refl sourceCtx
  | switch scrutinee cases defaultBody =>
      cases fuel with
      | zero =>
          simp [Source.Stmt.run, Source.invalid, Structured.invalid]
            at hSourceRun
      | succ fuel =>
          cases hEval : Source.Expr.evalOne prim scrutinee source with
          | error err =>
              simp [Source.Stmt.run, hEval] at hSourceRun
          | ok result =>
              rcases result with ⟨stateAfterScrutinee, value⟩
              cases hSelect :
                  Source.Switch.select value cases defaultBody with
              | none =>
                  simp [Source.Stmt.run, hEval, hSelect] at hSourceRun
                  rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
                  cases hCtxEq
                  exact HandlerScopesEq.refl sourceCtx
              | some body =>
                  cases hScoped :
                      Source.Block.runScoped prim program sourceCtx body fuel
                        stateAfterScrutinee with
                  | error err =>
                      simp [Source.Stmt.run, hEval, hSelect, hScoped]
                        at hSourceRun
                  | ok outcome =>
                      cases outcome with
                      | mk blockState mode =>
                          cases mode <;> simp [Source.Stmt.run, hEval,
                            hSelect, hScoped, Source.Outcome.regular,
                            Source.Outcome.brk, Source.Outcome.cont,
                            Source.Outcome.leave, Source.Outcome.halt]
                            at hSourceRun
                          case regular =>
                            rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
                            cases hCtxEq
                            exact HandlerScopesEq.refl sourceCtx
  | for_ init cond post body =>
      cases fuel with
      | zero =>
          simp [Source.Stmt.run, Source.invalid, Structured.invalid]
            at hSourceRun
      | succ fuel =>
          cases hInit :
              Source.Block.runOpen prim program sourceCtx.withoutLoopControl
                fuel init source with
          | error err =>
              simp [Source.Stmt.run, hInit] at hSourceRun
          | ok initResult =>
              rcases initResult with ⟨initOutcome, initCtx⟩
              cases initOutcome with
              | mk initState initMode =>
                  cases initMode <;> simp [Source.Stmt.run, hInit,
                    Source.Outcome.regular, Source.Outcome.brk,
                    Source.Outcome.cont, Source.Outcome.leave,
                    Source.Outcome.halt, Source.invalid,
                    Structured.invalid] at hSourceRun
                  case regular =>
                    cases hLoop :
                        Source.Stmt.runForLoop prim program initCtx cond
                          initCtx.withoutLoopControl post
                          (initCtx.withLoopControl initCtx.scope
                            initCtx.scope)
                          body fuel initState with
                    | error err =>
                        simp [hLoop] at hSourceRun
                    | ok loopOutcome =>
                        cases loopOutcome with
                        | mk loopState loopMode =>
                            cases loopMode <;> simp [hLoop,
                              Source.Outcome.regular, Source.Outcome.brk,
                              Source.Outcome.cont, Source.Outcome.leave,
                              Source.Outcome.halt, Source.invalid,
                              Structured.invalid] at hSourceRun
                            case regular =>
                              rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
                              cases hCtxEq
                              exact HandlerScopesEq.refl sourceCtx
  | brk =>
      rcases hLower with ⟨_hAtomic, _hScoped, _hAccess⟩
      cases hBreak : sourceCtx.breakScope? with
      | none =>
          simp [Source.Stmt.run, hBreak, Source.invalid,
            Structured.invalid] at hSourceRun
      | some breakScope =>
          simp [Source.Stmt.run, hBreak, Source.Outcome.brk] at hSourceRun
          rcases hSourceRun with ⟨hOutcome, _hCtxEq⟩
          cases hOutcome
  | cont =>
      rcases hLower with ⟨_hAtomic, _hScoped, _hAccess⟩
      cases hContinue : sourceCtx.continueScope? with
      | none =>
          simp [Source.Stmt.run, hContinue, Source.invalid,
            Structured.invalid] at hSourceRun
      | some continueScope =>
          simp [Source.Stmt.run, hContinue, Source.Outcome.cont]
            at hSourceRun
          rcases hSourceRun with ⟨hOutcome, _hCtxEq⟩
          cases hOutcome
  | leave =>
      cases hLower
  | call name =>
      cases hLower
  | terminal kind =>
      rcases hLower with ⟨_hAtomic, _hScoped, _hAccess⟩
      cases hTerminal : prim.terminal kind source.shared [] with
      | error err =>
          simp [Source.Stmt.run, hTerminal] at hSourceRun
      | ok shared' =>
          simp [Source.Stmt.run, hTerminal, Source.Outcome.halt]
            at hSourceRun
          rcases hSourceRun with ⟨hOutcome, _hCtxEq⟩
          cases hOutcome
  | terminalArgs kind args =>
      rcases hLower with ⟨_hAtomic, _hScoped, _hAccess⟩
      cases hArgs : Source.Expr.ExprSeq.eval prim args source with
      | error err =>
          simp [Source.Stmt.run, hArgs] at hSourceRun
      | ok argResult =>
          rcases argResult with ⟨stateAfterArgs, values⟩
          cases hTerminal :
              prim.terminal kind stateAfterArgs.shared values with
          | error err =>
              simp [Source.Stmt.run, hArgs, hTerminal] at hSourceRun
          | ok shared' =>
              simp [Source.Stmt.run, hArgs, hTerminal,
                Source.Outcome.halt] at hSourceRun
              rcases hSourceRun with ⟨hOutcome, _hCtxEq⟩
              cases hOutcome

mutual
  theorem blockLowerable_regular_handlerScopesEq
      {prim : Source.PrimitiveSemantics} {program : Program}
      {sourceCtx sourceCtxAfter : Source.Ctx} {fuel : Nat}
      {block : Block} {source sourceAfter : Source.State}
      (hLower : BlockLowerable sourceCtx.scope block)
      (hSourceRun :
        Source.Block.runOpen prim program sourceCtx fuel block source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter)) :
      HandlerScopesEq sourceCtx sourceCtxAfter := by
    cases block with
    | mk stmts =>
        exact
          stmtListLowerable_regular_handlerScopesEq hLower hSourceRun

  theorem stmtListLowerable_regular_handlerScopesEq
      {prim : Source.PrimitiveSemantics} {program : Program}
      {sourceCtx sourceCtxAfter : Source.Ctx} {fuel : Nat}
      {stmts : List Stmt} {source sourceAfter : Source.State}
      (hLower : StmtListLowerable sourceCtx.scope stmts)
      (hSourceRun :
        Source.Block.runOpen prim program sourceCtx fuel { stmts := stmts }
            source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter)) :
      HandlerScopesEq sourceCtx sourceCtxAfter := by
    cases fuel with
    | zero =>
        simp [Source.Block.runOpen, Source.invalid, Structured.invalid]
          at hSourceRun
    | succ fuel =>
        cases stmts with
        | nil =>
            simp [Source.Block.runOpen] at hSourceRun
            rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
            cases hCtxEq
            exact HandlerScopesEq.refl sourceCtx
        | cons stmt rest =>
            rcases hLower with ⟨hStmtLower, hRestLower⟩
            cases hStmt :
                Source.Stmt.run prim program sourceCtx fuel stmt source with
            | error err =>
                simp [Source.Block.runOpen, hStmt] at hSourceRun
            | ok stmtResult =>
                rcases stmtResult with ⟨stmtOutcome, sourceCtxHead⟩
                cases stmtOutcome with
                | mk sourceHead mode =>
                    cases mode <;> simp [Source.Block.runOpen, hStmt,
                      Source.Outcome.regular, Source.Outcome.brk,
                      Source.Outcome.cont, Source.Outcome.leave,
                      Source.Outcome.halt] at hSourceRun
                    case regular =>
                      have hHeadHandlers :
                          HandlerScopesEq sourceCtx sourceCtxHead :=
                        stmtLowerable_regular_handlerScopesEq hStmtLower hStmt
                      have hHeadScope :
                          sourceCtxHead.scope =
                            Scope.Stmt.outEnv sourceCtx.scope stmt :=
                        Source.Stmt.run_regular_scope hStmt
                      have hRestLowerAfter :
                          StmtListLowerable sourceCtxHead.scope rest := by
                        rw [hHeadScope]
                        exact hRestLower
                      exact
                        HandlerScopesEq.trans hHeadHandlers
                          (stmtListLowerable_regular_handlerScopesEq
                            hRestLowerAfter hSourceRun)
end

end Structural

def ScopedOutcomeRelAt (entryCtx : Source.Ctx) (scope : List Name)
    (sourceOutcome : Source.Outcome) (targetOutcome : Outcome) : Prop :=
  match sourceOutcome.mode, targetOutcome.mode with
  | .regular, .regular =>
      StateRel scope sourceOutcome.state targetOutcome.state
  | .brk, .brk =>
      ∃ breakScope,
        entryCtx.breakScope? = some breakScope ∧
          StateRel breakScope sourceOutcome.state targetOutcome.state
  | .cont, .cont =>
      ∃ continueScope,
        entryCtx.continueScope? = some continueScope ∧
          StateRel continueScope sourceOutcome.state targetOutcome.state
  | .leave, .leave =>
      ∃ leaveScope,
        entryCtx.leaveScope? = some leaveScope ∧
          StateRel leaveScope sourceOutcome.state targetOutcome.state
  | .halt sourceKind, .halt targetKind =>
      targetOutcome.state.evm.toSharedState = sourceOutcome.state.shared ∧
        sourceKind = targetKind
  | _, _ => False

namespace RunResultRel

theorem regular {source : Source.State} {target : RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    (hState : StateRel sourceCtx.scope source target)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx) :
    RunResultRel (Source.Outcome.regular source, sourceCtx)
      (Outcome.regular target, targetCtx) := by
  exact ⟨hState, hCtx, hHandlers⟩

theorem brk {layout : List Name} {source : Source.State}
    {target : RunState} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    (hState : StateRel layout source target) :
    RunResultRel (Source.Outcome.brk source, sourceCtx)
      (Outcome.brk target, targetCtx) := by
  exact ⟨layout, hState⟩

theorem cont {layout : List Name} {source : Source.State}
    {target : RunState} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    (hState : StateRel layout source target) :
    RunResultRel (Source.Outcome.cont source, sourceCtx)
      (Outcome.cont target, targetCtx) := by
  exact ⟨layout, hState⟩

theorem leave {layout : List Name} {source : Source.State}
    {target : RunState} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    (hState : StateRel layout source target) :
    RunResultRel (Source.Outcome.leave source, sourceCtx)
      (Outcome.leave target, targetCtx) := by
  exact ⟨layout, hState⟩

theorem halt_shared {source : Source.State} {target : RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Ctx} {kind : Assembly.HaltKind}
    (hShared : target.evm.toSharedState = source.shared) :
    RunResultRel (Source.Outcome.halt kind source, sourceCtx)
      (Outcome.halt kind target, targetCtx) := by
  exact ⟨hShared, rfl⟩

end RunResultRel

namespace RunResultRelAt

theorem regular {source : Source.State} {target : RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {entryCtx : Source.Ctx}
    (hState : StateRel sourceCtx.scope source target)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx) :
    RunResultRelAt entryCtx (Source.Outcome.regular source, sourceCtx)
      (Outcome.regular target, targetCtx) := by
  exact ⟨hState, hCtx, hHandlers⟩

theorem brk {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {breakScope : List Name} {source : Source.State}
    {target : RunState}
    (hBreak : entryCtx.breakScope? = some breakScope)
    (hState : StateRel breakScope source target) :
    RunResultRelAt entryCtx (Source.Outcome.brk source, sourceCtx)
      (Outcome.brk target, targetCtx) := by
  exact ⟨breakScope, hBreak, hState⟩

theorem cont {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {continueScope : List Name} {source : Source.State}
    {target : RunState}
    (hContinue : entryCtx.continueScope? = some continueScope)
    (hState : StateRel continueScope source target) :
    RunResultRelAt entryCtx (Source.Outcome.cont source, sourceCtx)
      (Outcome.cont target, targetCtx) := by
  exact ⟨continueScope, hContinue, hState⟩

theorem leave {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {leaveScope : List Name} {source : Source.State}
    {target : RunState}
    (hLeave : entryCtx.leaveScope? = some leaveScope)
    (hState : StateRel leaveScope source target) :
    RunResultRelAt entryCtx (Source.Outcome.leave source, sourceCtx)
      (Outcome.leave target, targetCtx) := by
  exact ⟨leaveScope, hLeave, hState⟩

theorem halt_shared {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {kind : Assembly.HaltKind}
    (hShared : target.evm.toSharedState = source.shared) :
    RunResultRelAt entryCtx (Source.Outcome.halt kind source, sourceCtx)
      (Outcome.halt kind target, targetCtx) := by
  exact ⟨hShared, rfl⟩

theorem rebase {fromEntry toEntry : Source.Ctx}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Outcome × Ctx}
    (hHandlers : HandlerScopesEq fromEntry toEntry)
    (hRel : RunResultRelAt fromEntry sourceResult targetResult) :
    RunResultRelAt toEntry sourceResult targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [RunResultRelAt] at hRel ⊢
          · exact hRel
          · rcases hHandlers with ⟨hBreakEq, _hContinueEq, _hLeaveEq⟩
            rcases hRel with ⟨breakScope, hBreak, hState⟩
            exact ⟨breakScope, by rw [← hBreakEq]; exact hBreak, hState⟩
          · rcases hHandlers with ⟨_hBreakEq, hContinueEq, _hLeaveEq⟩
            rcases hRel with ⟨continueScope, hContinue, hState⟩
            exact
              ⟨continueScope, by rw [← hContinueEq]; exact hContinue,
                hState⟩
          · rcases hHandlers with ⟨_hBreakEq, _hContinueEq, hLeaveEq⟩
            rcases hRel with ⟨leaveScope, hLeave, hState⟩
            exact ⟨leaveScope, by rw [← hLeaveEq]; exact hLeave, hState⟩
          · exact hRel

theorem toRunResultRel {entryCtx : Source.Ctx}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Outcome × Ctx}
    (hRel : RunResultRelAt entryCtx sourceResult targetResult) :
    RunResultRel sourceResult targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [RunResultRelAt, RunResultRel] at hRel ⊢
          · exact hRel
          · rcases hRel with ⟨scope, _hBreak, hState⟩
            exact ⟨scope, hState⟩
          · rcases hRel with ⟨scope, _hContinue, hState⟩
            exact ⟨scope, hState⟩
          · rcases hRel with ⟨scope, _hLeave, hState⟩
            exact ⟨scope, hState⟩
          · exact hRel

end RunResultRelAt

namespace ScopedOutcomeRelAt

theorem regular {entryCtx : Source.Ctx} {scope : List Name}
    {source : Source.State} {target : RunState}
    (hState : StateRel scope source target) :
    ScopedOutcomeRelAt entryCtx scope (Source.Outcome.regular source)
      (Outcome.regular target) := by
  exact hState

theorem brk {entryCtx : Source.Ctx} {scope breakScope : List Name}
    {source : Source.State} {target : RunState}
    (hBreak : entryCtx.breakScope? = some breakScope)
    (hState : StateRel breakScope source target) :
    ScopedOutcomeRelAt entryCtx scope (Source.Outcome.brk source)
      (Outcome.brk target) := by
  exact ⟨breakScope, hBreak, hState⟩

theorem cont {entryCtx : Source.Ctx} {scope continueScope : List Name}
    {source : Source.State} {target : RunState}
    (hContinue : entryCtx.continueScope? = some continueScope)
    (hState : StateRel continueScope source target) :
    ScopedOutcomeRelAt entryCtx scope (Source.Outcome.cont source)
      (Outcome.cont target) := by
  exact ⟨continueScope, hContinue, hState⟩

theorem leave {entryCtx : Source.Ctx} {scope leaveScope : List Name}
    {source : Source.State} {target : RunState}
    (hLeave : entryCtx.leaveScope? = some leaveScope)
    (hState : StateRel leaveScope source target) :
    ScopedOutcomeRelAt entryCtx scope (Source.Outcome.leave source)
      (Outcome.leave target) := by
  exact ⟨leaveScope, hLeave, hState⟩

theorem halt_shared {entryCtx : Source.Ctx} {scope : List Name}
    {source : Source.State} {target : RunState}
    {kind : Assembly.HaltKind}
    (hShared : target.evm.toSharedState = source.shared) :
    ScopedOutcomeRelAt entryCtx scope (Source.Outcome.halt kind source)
      (Outcome.halt kind target) := by
  exact ⟨hShared, rfl⟩

theorem toScopedOutcomeRel {entryCtx : Source.Ctx} {scope : List Name}
    {sourceOutcome : Source.Outcome} {targetOutcome : Outcome}
    (hRel : ScopedOutcomeRelAt entryCtx scope sourceOutcome targetOutcome) :
    ScopedOutcomeRel scope sourceOutcome targetOutcome := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [ScopedOutcomeRelAt, ScopedOutcomeRel] at hRel ⊢
          · exact hRel
          · rcases hRel with ⟨breakScope, _hBreak, hState⟩
            exact ⟨breakScope, hState⟩
          · rcases hRel with ⟨continueScope, _hContinue, hState⟩
            exact ⟨continueScope, hState⟩
          · rcases hRel with ⟨leaveScope, _hLeave, hState⟩
            exact ⟨leaveScope, hState⟩
          · exact hRel

theorem toRunResultRelAt {entryCtx : Source.Ctx} {scope : List Name}
    {sourceOutcome : Source.Outcome} {targetOutcome : Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    (hRel : ScopedOutcomeRelAt entryCtx scope sourceOutcome targetOutcome)
    (hScope : sourceCtx.scope = scope)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx) :
    RunResultRelAt entryCtx (sourceOutcome, sourceCtx)
      (targetOutcome, targetCtx) := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [ScopedOutcomeRelAt, RunResultRelAt] at hRel ⊢
          · subst hScope
            exact ⟨hRel, hCtx, hHandlers⟩
          · exact hRel
          · exact hRel
          · exact hRel
          · exact hRel

end ScopedOutcomeRelAt

namespace ScopedOutcomeRel

theorem regular {scope : List Name} {source : Source.State}
    {target : RunState}
    (hState : StateRel scope source target) :
    ScopedOutcomeRel scope (Source.Outcome.regular source)
      (Outcome.regular target) := by
  exact hState

theorem brk {scope layout : List Name} {source : Source.State}
    {target : RunState}
    (hState : StateRel layout source target) :
    ScopedOutcomeRel scope (Source.Outcome.brk source)
      (Outcome.brk target) := by
  exact ⟨layout, hState⟩

theorem cont {scope layout : List Name} {source : Source.State}
    {target : RunState}
    (hState : StateRel layout source target) :
    ScopedOutcomeRel scope (Source.Outcome.cont source)
      (Outcome.cont target) := by
  exact ⟨layout, hState⟩

theorem leave {scope layout : List Name} {source : Source.State}
    {target : RunState}
    (hState : StateRel layout source target) :
    ScopedOutcomeRel scope (Source.Outcome.leave source)
      (Outcome.leave target) := by
  exact ⟨layout, hState⟩

theorem halt_shared {scope : List Name} {source : Source.State}
    {target : RunState} {kind : Assembly.HaltKind}
    (hShared : target.evm.toSharedState = source.shared) :
    ScopedOutcomeRel scope (Source.Outcome.halt kind source)
      (Outcome.halt kind target) := by
  exact ⟨hShared, rfl⟩

theorem toRunResultRel {scope : List Name}
    {sourceOutcome : Source.Outcome} {targetOutcome : Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    (hRel : ScopedOutcomeRel scope sourceOutcome targetOutcome)
    (hScope : sourceCtx.scope = scope)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx) :
    RunResultRel (sourceOutcome, sourceCtx) (targetOutcome, targetCtx) := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [ScopedOutcomeRel, RunResultRel] at hRel ⊢
          · subst hScope
            exact ⟨hRel, hCtx, hHandlers⟩
          · exact hRel
          · exact hRel
          · exact hRel
          · exact hRel

end ScopedOutcomeRel

def StmtRunBridge (prim : Source.PrimitiveSemantics)
    (program : Program) (sourceCtx : Source.Ctx) (targetCtx : Ctx)
    (fuel : Nat) (stmt : Stmt) (source : Source.State)
    (target : RunState) : Prop :=
  ∃ sourceResult : Source.Outcome × Source.Ctx,
  ∃ targetResult : Outcome × Ctx,
    Source.Stmt.run prim program sourceCtx fuel stmt source =
      .ok sourceResult ∧
    Direct.Stmt.run program targetCtx fuel stmt target =
      .ok targetResult ∧
    RunResultRel sourceResult targetResult

namespace StmtRunBridge

theorem target_result_of_source {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {fuel : Nat} {stmt : Stmt} {source : Source.State}
    {target : RunState} {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      StmtRunBridge prim program sourceCtx targetCtx fuel stmt source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel stmt source =
        .ok sourceResult) :
    ∃ targetResult : Outcome × Ctx,
      Direct.Stmt.run program targetCtx fuel stmt target = .ok targetResult ∧
        RunResultRel sourceResult targetResult := by
  rcases hBridge with
    ⟨bridgeSourceResult, targetResult, hBridgeSource, hTarget, hRel⟩
  rw [hSourceRun] at hBridgeSource
  cases hBridgeSource
  exact ⟨targetResult, hTarget, hRel⟩

theorem expr {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterExpr : Source.State} {target : RunState}
    {fuel : Nat} {expr : Expr 0} {values : List Word}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hRel : StateRel sourceCtx.scope source target)
    (hEval :
      Source.Expr.eval prim expr source = .ok (sourceAfterExpr, values)) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.expr expr)
      source target := by
  rcases Stmt.expr_bridge hPrim hCtx hNoDup hOwned hAccess hRel hEval with
    ⟨targetAfter, hSource, hTarget, hState, hCtxOut⟩
  exact
    ⟨(Source.Outcome.regular sourceAfterExpr, sourceCtx),
      (Outcome.regular targetAfter, targetCtx), hSource, hTarget,
      RunResultRel.regular hState hCtxOut hHandlers⟩

theorem letExpr {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterValue : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {value : Word} {expr : Expr 1}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalOne :
      Source.Expr.evalOne prim expr source = .ok (sourceAfterValue, value)) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.let_ name expr)
      source target := by
  rcases
      Stmt.let_expr_bridge hPrim hCtx hNoDup hOwned hAccess hFresh hRel
        hEvalOne with
    ⟨targetAfter, hSource, hTarget, hState, hCtxOut⟩
  let sourceCtxOut : Source.Ctx :=
    { sourceCtx with scope := name :: sourceCtx.scope }
  let targetCtxOut : Ctx :=
    targetCtx.withLayout (name :: targetCtx.layout)
  have hHandlersOut :
      CtxHandlersRel sourceCtxOut targetCtxOut := by
    exact CtxHandlersRel.withScopeCons hHandlers
  exact
    ⟨(Source.Outcome.regular (sourceAfterValue.insert name value),
        sourceCtxOut),
      (Outcome.regular targetAfter, targetCtxOut), by simpa [sourceCtxOut] using hSource,
      by simpa [targetCtxOut] using hTarget,
      RunResultRel.regular
        (by simpa [sourceCtxOut] using hState)
        (by simpa [sourceCtxOut, targetCtxOut] using hCtxOut)
        hHandlersOut⟩

theorem assign_expr {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterValue : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {idx : Nat} {value : Word}
    {expr : Expr 1}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hName : sourceCtx.scope[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalOne :
      Source.Expr.evalOne prim expr source = .ok (sourceAfterValue, value)) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.assign name expr)
      source target := by
  rcases
      Stmt.assign_expr_bridge hPrim hCtx hNoDup hName hBound hOwned hAccess
        hRel hEvalOne with
    ⟨targetAfter, hSource, hTarget, hState, hCtxOut⟩
  exact
    ⟨(Source.Outcome.regular
        (sourceAfterValue.withVars
          (Source.Store.insert sourceAfterValue.vars name value)),
        sourceCtx),
      (Outcome.regular targetAfter, targetCtx), hSource, hTarget,
      RunResultRel.regular hState hCtxOut hHandlers⟩

theorem brk {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {breakScope : List Name}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hBreak : sourceCtx.breakScope? = some breakScope)
    (hRel : StateRel targetCtx.layout source target) :
    StmtRunBridge prim program sourceCtx targetCtx fuel .brk source target := by
  rcases Stmt.brk_bridge hCtx hHandlers hBreak hRel with
    ⟨targetAfter, hSource, hTarget, hState, _hCtxOut, _hHandlersOut⟩
  exact
    ⟨(Source.Outcome.brk (source.restrictTo breakScope), sourceCtx),
      (Outcome.brk targetAfter, targetCtx), hSource, hTarget,
      RunResultRel.brk hState⟩

theorem cont {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {continueScope : List Name}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hContinue : sourceCtx.continueScope? = some continueScope)
    (hRel : StateRel targetCtx.layout source target) :
    StmtRunBridge prim program sourceCtx targetCtx fuel .cont source target := by
  rcases Stmt.cont_bridge hCtx hHandlers hContinue hRel with
    ⟨targetAfter, hSource, hTarget, hState, _hCtxOut, _hHandlersOut⟩
  exact
    ⟨(Source.Outcome.cont (source.restrictTo continueScope), sourceCtx),
      (Outcome.cont targetAfter, targetCtx), hSource, hTarget,
      RunResultRel.cont hState⟩

theorem terminal {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {kind : Assembly.HaltKind} {shared' : EvmYul.SharedState .EVM}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hTerminal : prim.terminal kind source.shared [] = .ok shared') :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.terminal kind)
      source target := by
  rcases Stmt.terminal_bridge hPrim hCtx hRel hTerminal with
    ⟨sourceAfter, targetAfter, hSource, hTarget, hOutcome, _hCtxOut⟩
  exact
    ⟨(Source.Outcome.halt kind sourceAfter, sourceCtx),
      (Outcome.halt kind targetAfter, targetCtx), hSource, hTarget,
      by
        rcases hOutcome with ⟨hShared, hKind⟩
        cases hKind
        exact RunResultRel.halt_shared hShared⟩

theorem terminalArgs {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterArgs : Source.State} {target : RunState}
    {fuel : Nat} {kind : Assembly.HaltKind} {args : ExprSeq kind.argCount}
    {values : List Word} {shared' : EvmYul.SharedState .EVM}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.ExprSeq.SourceOwned args)
    (hAccess : ExprSeq.Accessible sourceCtx.scope 0 args)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalArgs :
      Source.Expr.ExprSeq.eval prim args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      prim.terminal kind sourceAfterArgs.shared values = .ok shared') :
    StmtRunBridge prim program sourceCtx targetCtx fuel
      (.terminalArgs kind args) source target := by
  rcases
      Stmt.terminalArgs_bridge hPrim hCtx hNoDup hOwned hAccess hRel
        hEvalArgs hTerminal with
    ⟨targetAfter, hSource, hTarget, hOutcome, _hCtxOut⟩
  exact
    ⟨(Source.Outcome.halt kind (sourceAfterArgs.withShared shared'),
        sourceCtx),
      (Outcome.halt kind targetAfter, targetCtx), hSource, hTarget,
      by
        rcases hOutcome with ⟨hShared, hKind⟩
        cases hKind
        exact RunResultRel.halt_shared hShared⟩

theorem expr_from_scoped {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterExpr : Source.State} {target : RunState}
    {fuel : Nat} {expr : Expr 0} {values : List Word}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope (.expr expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hEval :
      Source.Expr.eval prim expr source = .ok (sourceAfterExpr, values)) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.expr expr)
      source target := by
  exact
    StmtRunBridge.expr hPrim hCtx hHandlers hNoDup
      (Scope.expr_sourceOwned_of_scoped hScoped)
      (CtxRel.expr_accessible_of_scoped (offset := 0) hCtx hScoped
        (by simpa using hAccessBound))
      hRel hEval

theorem letExpr_from_scoped {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterValue : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {value : Word} {expr : Expr 1}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.let_ name expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalOne :
      Source.Expr.evalOne prim expr source = .ok (sourceAfterValue, value)) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.let_ name expr)
      source target := by
  rcases hScoped with ⟨hFresh, hExprScoped⟩
  exact
    letExpr hPrim hCtx hHandlers hNoDup
      (Scope.expr_sourceOwned_of_scoped hExprScoped)
      (CtxRel.expr_accessible_of_scoped (offset := 0) hCtx hExprScoped
        (by simpa using hAccessBound))
      hFresh hRel hEvalOne

theorem assign_expr_from_scoped {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterValue : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {value : Word} {expr : Expr 1}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.assign name expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalOne :
      Source.Expr.evalOne prim expr source = .ok (sourceAfterValue, value)) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.assign name expr)
      source target := by
  rcases hScoped with ⟨hContains, hExprScoped⟩
  rcases List.mem_iff_getElem?.mp hContains with ⟨idx, hName⟩
  have hBound : idx + 1 ≤ 16 := by
    have hIdxLt : idx < sourceCtx.scope.length :=
      (List.getElem?_eq_some_iff.mp hName).1
    rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
    have hScopeLen : sourceCtx.scope.length ≤ 16 := by
      rw [← hLayout]
      omega
    omega
  exact
    assign_expr hPrim hCtx hHandlers hNoDup hName hBound
      (Scope.expr_sourceOwned_of_scoped hExprScoped)
      (CtxRel.expr_accessible_of_scoped (offset := 0) hCtx hExprScoped
        (by simpa using hAccessBound))
      hRel hEvalOne

theorem terminalArgs_from_scoped {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterArgs : Source.State} {target : RunState}
    {fuel : Nat} {kind : Assembly.HaltKind} {args : ExprSeq kind.argCount}
    {values : List Word} {shared' : EvmYul.SharedState .EVM}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.terminalArgs kind args))
    (hAccessBound :
      targetCtx.layout.length + Access.exprSeqWidth args ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalArgs :
      Source.Expr.ExprSeq.eval prim args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      prim.terminal kind sourceAfterArgs.shared values = .ok shared') :
    StmtRunBridge prim program sourceCtx targetCtx fuel
      (.terminalArgs kind args) source target := by
  exact
    terminalArgs hPrim hCtx hNoDup
      (Scope.exprSeq_sourceOwned_of_scoped hScoped)
      (CtxRel.exprSeq_accessible_of_scoped (offset := 0) hCtx hScoped
        (by simpa using hAccessBound))
      hRel hEvalArgs hTerminal

theorem expr_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {expr : Expr 0}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope (.expr expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.expr expr) source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.expr expr)
      source target := by
  cases hEval : Source.Expr.eval prim expr source with
  | error err =>
      simp [Source.Stmt.run, hEval] at hSourceRun
  | ok result =>
      rcases result with ⟨sourceAfterExpr, values⟩
      simp [Source.Stmt.run, hEval] at hSourceRun
      cases hSourceRun
      exact
        expr_from_scoped hPrim hCtx hHandlers hNoDup hScoped hAccessBound
          hRel hEval

theorem letExpr_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {expr : Expr 1}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.let_ name expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.let_ name expr) source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.let_ name expr)
      source target := by
  cases hEvalOne : Source.Expr.evalOne prim expr source with
  | error err =>
      simp [Source.Stmt.run, hEvalOne] at hSourceRun
  | ok result =>
      rcases result with ⟨sourceAfterValue, value⟩
      simp [Source.Stmt.run, hEvalOne] at hSourceRun
      cases hSourceRun
      exact
        letExpr_from_scoped hPrim hCtx hHandlers hNoDup hScoped
          hAccessBound hRel hEvalOne

theorem assign_expr_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {expr : Expr 1}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.assign name expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.assign name expr)
          source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.assign name expr)
      source target := by
  cases hContains : source.vars.contains name with
  | false =>
      simp [Source.Stmt.run, hContains, Source.invalid, invalid,
        Structured.invalid] at hSourceRun
  | true =>
      cases hEvalOne : Source.Expr.evalOne prim expr source with
      | error err =>
          simp [Source.Stmt.run, hContains, hEvalOne] at hSourceRun
      | ok result =>
          rcases result with ⟨sourceAfterValue, value⟩
          simp [Source.Stmt.run, hContains, hEvalOne] at hSourceRun
          cases hSourceRun
          exact
            assign_expr_from_scoped hPrim hCtx hHandlers hNoDup hScoped
              hAccessBound hRel hEvalOne

theorem brk_from_source_run {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel .brk source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel .brk source target := by
  cases hBreak : sourceCtx.breakScope? with
  | none =>
      simp [Source.Stmt.run, hBreak, Source.invalid, Structured.invalid]
        at hSourceRun
  | some breakScope =>
      simp [Source.Stmt.run, hBreak] at hSourceRun
      cases hSourceRun
      have hRelTarget : StateRel targetCtx.layout source target := by
        rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
        simpa [hLayout] using hRel
      exact brk hCtx hHandlers hBreak hRelTarget

theorem cont_from_source_run {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel .cont source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel .cont source target := by
  cases hContinue : sourceCtx.continueScope? with
  | none =>
      simp [Source.Stmt.run, hContinue, Source.invalid, Structured.invalid]
        at hSourceRun
  | some continueScope =>
      simp [Source.Stmt.run, hContinue] at hSourceRun
      cases hSourceRun
      have hRelTarget : StateRel targetCtx.layout source target := by
        rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
        simpa [hLayout] using hRel
      exact cont hCtx hHandlers hContinue hRelTarget

theorem terminal_from_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {kind : Assembly.HaltKind}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.terminal kind) source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.terminal kind)
      source target := by
  cases hTerminal : prim.terminal kind source.shared [] with
  | error err =>
      simp [Source.Stmt.run, hTerminal] at hSourceRun
  | ok shared' =>
      simp [Source.Stmt.run, hTerminal] at hSourceRun
      cases hSourceRun
      exact terminal hPrim hCtx hRel hTerminal

theorem terminalArgs_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {kind : Assembly.HaltKind} {args : ExprSeq kind.argCount}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.terminalArgs kind args))
    (hAccessBound :
      targetCtx.layout.length + Access.exprSeqWidth args ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel
          (.terminalArgs kind args) source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel
      (.terminalArgs kind args) source target := by
  cases hEvalArgs : Source.Expr.ExprSeq.eval prim args source with
  | error err =>
      simp [Source.Stmt.run, hEvalArgs] at hSourceRun
  | ok argResult =>
      rcases argResult with ⟨sourceAfterArgs, values⟩
      simp [Source.Stmt.run, hEvalArgs] at hSourceRun
      cases hTerminal :
          prim.terminal kind sourceAfterArgs.shared values with
      | error err =>
          simp [hTerminal] at hSourceRun
      | ok shared' =>
          simp [hTerminal] at hSourceRun
          cases hSourceRun
          exact
            terminalArgs_from_scoped hPrim hCtx hNoDup hScoped hAccessBound
              hRel hEvalArgs hTerminal

theorem atomic_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {stmt : Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAtomic : AtomicStmt.Holds stmt)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope stmt)
    (hAccessBound :
      AtomicStmt.AccessBound targetCtx.layout.length stmt)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel stmt source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel stmt source target := by
  cases stmt with
  | expr expr =>
      rename_i results
      dsimp [AtomicStmt.Holds] at hAtomic
      subst results
      exact
        expr_from_scoped_source_run hPrim hCtx hHandlers hNoDup hScoped
          (by simpa [AtomicStmt.AccessBound] using hAccessBound)
          hRel hSourceRun
  | exprs exprs =>
      cases hAtomic
  | let_ name value =>
      exact
        letExpr_from_scoped_source_run hPrim hCtx hHandlers hNoDup hScoped
          (by simpa [AtomicStmt.AccessBound] using hAccessBound)
          hRel hSourceRun
  | assign name value =>
      exact
        assign_expr_from_scoped_source_run hPrim hCtx hHandlers hNoDup hScoped
          (by simpa [AtomicStmt.AccessBound] using hAccessBound)
          hRel hSourceRun
  | assignTop name =>
      cases hAtomic
  | assignTopWithOffset offset name =>
      cases hAtomic
  | block body =>
      cases hAtomic
  | if_ cond body =>
      cases hAtomic
  | switch scrutinee cases defaultBody =>
      cases hAtomic
  | for_ init cond post body =>
      cases hAtomic
  | brk =>
      exact brk_from_source_run hCtx hHandlers hRel hSourceRun
  | cont =>
      exact cont_from_source_run hCtx hHandlers hRel hSourceRun
  | leave =>
      cases hAtomic
  | call name =>
      cases hAtomic
  | terminal kind =>
      exact terminal_from_source_run hPrim hCtx hRel hSourceRun
  | terminalArgs kind args =>
      exact
        terminalArgs_from_scoped_source_run hPrim hCtx hNoDup hScoped
          (by simpa [AtomicStmt.AccessBound] using hAccessBound)
          hRel hSourceRun

theorem atomic_from_scoped_source_run_source_bound
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {stmt : Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAtomic : AtomicStmt.Holds stmt)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope stmt)
    (hAccessBound :
      AtomicStmt.SourceAccessBound sourceCtx.scope stmt)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel stmt source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel stmt source target := by
  exact
    atomic_from_scoped_source_run hPrim hCtx hHandlers hNoDup hAtomic
      hScoped (AtomicStmt.accessBound_of_sourceAccessBound hCtx hAccessBound)
      hRel hSourceRun

end StmtRunBridge

def BlockOpenRunBridge (prim : Source.PrimitiveSemantics)
    (program : Program) (sourceCtx : Source.Ctx) (targetCtx : Ctx)
    (fuel : Nat) (block : Block) (source : Source.State)
    (target : RunState) : Prop :=
  ∃ sourceResult : Source.Outcome × Source.Ctx,
  ∃ targetResult : Outcome × Ctx,
    Source.Block.runOpen prim program sourceCtx fuel block source =
      .ok sourceResult ∧
    Direct.Block.runOpen program targetCtx fuel block target =
      .ok targetResult ∧
    RunResultRel sourceResult targetResult

namespace BlockOpenRunBridge

theorem target_result_of_source {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {fuel : Nat} {block : Block} {source : Source.State}
    {target : RunState} {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      BlockOpenRunBridge prim program sourceCtx targetCtx fuel block source
        target)
    (hSourceRun :
      Source.Block.runOpen prim program sourceCtx fuel block source =
        .ok sourceResult) :
    ∃ targetResult : Outcome × Ctx,
      Direct.Block.runOpen program targetCtx fuel block target =
          .ok targetResult ∧
        RunResultRel sourceResult targetResult := by
  rcases hBridge with
    ⟨bridgeSourceResult, targetResult, hBridgeSource, hTarget, hRel⟩
  rw [hSourceRun] at hBridgeSource
  cases hBridgeSource
  exact ⟨targetResult, hTarget, hRel⟩

theorem runScoped_from_open_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {fuel : Nat} {block : Block} {source : Source.State}
    {target : RunState} {sourceOutcome : Source.Outcome}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hBridge :
      BlockOpenRunBridge prim program sourceCtx targetCtx fuel block source
        target)
    (hSourceRun :
      Source.Block.runScoped prim program sourceCtx block fuel source =
        .ok sourceOutcome) :
    ∃ targetOutcome : Outcome,
      Direct.Block.runScoped program targetCtx block fuel target =
          .ok targetOutcome ∧
        ScopedOutcomeRel sourceCtx.scope sourceOutcome targetOutcome := by
  unfold Source.Block.runScoped at hSourceRun
  cases hSourceOpen :
      Source.Block.runOpen prim program sourceCtx fuel block source with
  | error err =>
      simp [hSourceOpen] at hSourceRun
  | ok sourceOpenResult =>
      rcases sourceOpenResult with ⟨sourceOpenOutcome, sourceFinalCtx⟩
      rcases target_result_of_source hBridge hSourceOpen with
        ⟨targetOpenResult, hTargetOpen, hOpenRel⟩
      rcases targetOpenResult with ⟨targetOpenOutcome, targetFinalCtx⟩
      rcases sourceOpenOutcome with ⟨sourceOpenState, sourceMode⟩
      rcases targetOpenOutcome with ⟨targetOpenState, targetMode⟩
      cases sourceMode with
      | regular =>
          cases targetMode with
          | regular =>
              simp [RunResultRel] at hOpenRel
              rcases hOpenRel with
                ⟨hStateOpen, hFinalCtx, _hFinalHandlers⟩
              simp [hSourceOpen, Source.Outcome.regular] at hSourceRun
              cases hSourceRun
              have hFinalScope :
                  sourceFinalCtx.scope =
                    Scope.Block.outEnv sourceCtx.scope block :=
                Source.Block.runOpen_regular_scope hSourceOpen
              rcases hCtx with
                ⟨hInitialLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
              rcases hFinalCtx with
                ⟨hFinalLayout, _hFinalBreak, _hFinalContinue, _hFinalLeave,
                  _hFinalRetc⟩
              have hCleanupScope :
                  CleanupScopeRel targetFinalCtx.layout sourceCtx.scope := by
                rw [hFinalLayout, hFinalScope]
                exact Scope.block_outEnv_cleanupScopeRel sourceCtx.scope block
              rcases
                  StateRel.cleanupTo_scope_exists
                    (ctx := targetFinalCtx) hCleanupScope
                    (by simpa [hFinalLayout] using hStateOpen) with
                ⟨cleaned, hCleanup, hCleanRel, _hReturns⟩
              refine
                ⟨Outcome.regular cleaned, ?_, ScopedOutcomeRel.regular
                  hCleanRel⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.regular,
                hInitialLayout, hCleanup]
          | brk =>
              simp [RunResultRel] at hOpenRel
          | cont =>
              simp [RunResultRel] at hOpenRel
          | leave =>
              simp [RunResultRel] at hOpenRel
          | halt _ =>
              simp [RunResultRel] at hOpenRel
      | brk =>
          cases targetMode with
          | regular =>
              simp [RunResultRel] at hOpenRel
          | brk =>
              simp [RunResultRel] at hOpenRel
              rcases hOpenRel with ⟨layout, hState⟩
              simp [hSourceOpen, Source.Outcome.brk] at hSourceRun
              cases hSourceRun
              refine
                ⟨Outcome.brk targetOpenState, ?_,
                  ScopedOutcomeRel.brk (scope := sourceCtx.scope)
                    (layout := layout) hState⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.brk,
                Structured.Outcome.brk]
          | cont =>
              simp [RunResultRel] at hOpenRel
          | leave =>
              simp [RunResultRel] at hOpenRel
          | halt _ =>
              simp [RunResultRel] at hOpenRel
      | cont =>
          cases targetMode with
          | regular =>
              simp [RunResultRel] at hOpenRel
          | brk =>
              simp [RunResultRel] at hOpenRel
          | cont =>
              simp [RunResultRel] at hOpenRel
              rcases hOpenRel with ⟨layout, hState⟩
              simp [hSourceOpen, Source.Outcome.cont] at hSourceRun
              cases hSourceRun
              refine
                ⟨Outcome.cont targetOpenState, ?_,
                  ScopedOutcomeRel.cont (scope := sourceCtx.scope)
                    (layout := layout) hState⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.cont,
                Structured.Outcome.cont]
          | leave =>
              simp [RunResultRel] at hOpenRel
          | halt _ =>
              simp [RunResultRel] at hOpenRel
      | leave =>
          cases targetMode with
          | regular =>
              simp [RunResultRel] at hOpenRel
          | brk =>
              simp [RunResultRel] at hOpenRel
          | cont =>
              simp [RunResultRel] at hOpenRel
          | leave =>
              simp [RunResultRel] at hOpenRel
              rcases hOpenRel with ⟨layout, hState⟩
              simp [hSourceOpen, Source.Outcome.leave] at hSourceRun
              cases hSourceRun
              refine
                ⟨Outcome.leave targetOpenState, ?_,
                  ScopedOutcomeRel.leave (scope := sourceCtx.scope)
                    (layout := layout) hState⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.leave,
                Structured.Outcome.leave]
          | halt _ =>
              simp [RunResultRel] at hOpenRel
      | halt sourceKind =>
          cases targetMode with
          | regular =>
              simp [RunResultRel] at hOpenRel
          | brk =>
              simp [RunResultRel] at hOpenRel
          | cont =>
              simp [RunResultRel] at hOpenRel
          | leave =>
              simp [RunResultRel] at hOpenRel
          | halt targetKind =>
              simp [RunResultRel] at hOpenRel
              rcases hOpenRel with ⟨hShared, hKind⟩
              subst hKind
              simp [hSourceOpen, Source.Outcome.halt] at hSourceRun
              cases hSourceRun
              refine
                ⟨Outcome.halt sourceKind targetOpenState, ?_,
                  ScopedOutcomeRel.halt_shared hShared⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.halt,
                Structured.Outcome.halt]

end BlockOpenRunBridge

namespace StmtRunBridge

theorem block_from_open_bridge_source_run {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {body : Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hBody :
      BlockOpenRunBridge prim program sourceCtx targetCtx fuel body source
        target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.block body) source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx fuel (.block body)
      source target := by
  cases hSourceScoped :
      Source.Block.runScoped prim program sourceCtx body fuel source with
  | error err =>
      simp [Source.Stmt.run, hSourceScoped] at hSourceRun
  | ok sourceOutcome =>
      rcases
          BlockOpenRunBridge.runScoped_from_open_bridge
            hCtx hBody hSourceScoped with
        ⟨targetOutcome, hTargetScoped, hScopedRel⟩
      simp [Source.Stmt.run, hSourceScoped] at hSourceRun
      cases hSourceRun
      exact
        ⟨(sourceOutcome, sourceCtx), (targetOutcome, targetCtx),
          by simp [Source.Stmt.run, hSourceScoped],
          by simp [Direct.Stmt.run, hTargetScoped],
          ScopedOutcomeRel.toRunResultRel hScopedRel rfl hCtx hHandlers⟩

theorem if_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {cond : Expr 1} {body : Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hCondScoped : Scope.ExprScoped sourceCtx.scope cond)
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth cond ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hBody :
      ∀ {sourceAfterCond : Source.State} {targetAfterCond : RunState},
        Source.Expr.evalCondition prim cond source =
          .ok (sourceAfterCond, true) →
        Direct.Expr.runCondition targetCtx cond target =
          .ok (targetAfterCond, true) →
        StateRel sourceCtx.scope sourceAfterCond targetAfterCond →
          BlockOpenRunBridge prim program sourceCtx targetCtx fuel body
            sourceAfterCond targetAfterCond)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx (fuel + 1) (.if_ cond body)
          source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx (fuel + 1)
      (.if_ cond body) source target := by
  cases hEvalOne : Source.Expr.evalOne prim cond source with
  | error err =>
      simp [Source.Stmt.run, Source.Expr.evalCondition, hEvalOne] at hSourceRun
  | ok condResult =>
      rcases condResult with ⟨sourceAfterCond, value⟩
      rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
      have hCtxRel : CtxRel sourceCtx targetCtx :=
        ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
      rcases
          Expr.evalCondition_bridge_sourceOwned hPrim
            (layout := sourceCtx.scope) (ctx := targetCtx)
            (source := source) (source' := sourceAfterCond)
            (value := value) (target := target)
            (by simpa [hLayout]) hNoDup
            (Scope.expr_sourceOwned_of_scoped hCondScoped)
            (CtxRel.expr_accessible_of_scoped (offset := 0) hCtxRel
              hCondScoped (by simpa using hAccessBound))
            hRel hEvalOne with
        ⟨targetAfterCond, hSourceCond, hTargetCond, hCondRel⟩
      cases hTruth : value != EvmYul.UInt256.ofNat 0
      · have hSourceCondFalse :
            Source.Expr.evalCondition prim cond source =
              .ok (sourceAfterCond, false) := by
          simpa [hTruth] using hSourceCond
        have hTargetCondFalse :
            Direct.Expr.runCondition targetCtx cond target =
              .ok (targetAfterCond, false) := by
          simpa [hTruth] using hTargetCond
        simp [Source.Stmt.run, hSourceCondFalse] at hSourceRun
        cases hSourceRun
        exact
          ⟨(Source.Outcome.regular sourceAfterCond, sourceCtx),
            (Outcome.regular targetAfterCond, targetCtx),
            by simp [Source.Stmt.run, hSourceCondFalse],
            by simp [Direct.Stmt.run, hTargetCondFalse],
            RunResultRel.regular hCondRel hCtxRel hHandlers⟩
      · have hSourceCondTrue :
            Source.Expr.evalCondition prim cond source =
              .ok (sourceAfterCond, true) := by
          simpa [hTruth] using hSourceCond
        have hTargetCondTrue :
            Direct.Expr.runCondition targetCtx cond target =
              .ok (targetAfterCond, true) := by
          simpa [hTruth] using hTargetCond
        cases hSourceBody :
            Source.Block.runScoped prim program sourceCtx body fuel
              sourceAfterCond with
        | error err =>
            simp [Source.Stmt.run, hSourceCondTrue, hSourceBody] at hSourceRun
        | ok sourceOutcome =>
            have hBodyBridge :
                BlockOpenRunBridge prim program sourceCtx targetCtx fuel body
                  sourceAfterCond targetAfterCond :=
              hBody hSourceCondTrue hTargetCondTrue hCondRel
            rcases
                BlockOpenRunBridge.runScoped_from_open_bridge hCtxRel
                  hBodyBridge hSourceBody with
              ⟨targetOutcome, hTargetBody, hScopedRel⟩
            simp [Source.Stmt.run, hSourceCondTrue, hSourceBody] at hSourceRun
            cases hSourceRun
            exact
              ⟨(sourceOutcome, sourceCtx), (targetOutcome, targetCtx),
                by simp [Source.Stmt.run, hSourceCondTrue, hSourceBody],
                by simp [Direct.Stmt.run, hTargetCondTrue, hTargetBody],
                ScopedOutcomeRel.toRunResultRel hScopedRel rfl hCtxRel
                  hHandlers⟩

theorem if_from_scoped_source_run_source_bound
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {cond : Expr 1} {body : Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hCondScoped : Scope.ExprScoped sourceCtx.scope cond)
    (hAccessBound : Access.ExprBound sourceCtx.scope 0 cond)
    (hRel : StateRel sourceCtx.scope source target)
    (hBody :
      ∀ {sourceAfterCond : Source.State} {targetAfterCond : RunState},
        Source.Expr.evalCondition prim cond source =
          .ok (sourceAfterCond, true) →
        Direct.Expr.runCondition targetCtx cond target =
          .ok (targetAfterCond, true) →
        StateRel sourceCtx.scope sourceAfterCond targetAfterCond →
          BlockOpenRunBridge prim program sourceCtx targetCtx fuel body
            sourceAfterCond targetAfterCond)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx (fuel + 1) (.if_ cond body)
          source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx (fuel + 1)
      (.if_ cond body) source target := by
  apply if_from_scoped_source_run hPrim hCtx hHandlers hNoDup hCondScoped
  · rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
    simpa [Access.ExprBound, hLayout] using hAccessBound
  · exact hRel
  · exact hBody
  · exact hSourceRun

theorem switch_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {scrutinee : Expr 1}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScrutineeScoped : Scope.ExprScoped sourceCtx.scope scrutinee)
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth scrutinee ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSelected :
      ∀ {sourceAfterScrutinee : Source.State}
        {targetAfterScrutinee : RunState} {value : Word}
        {selected : Block},
        Source.Expr.evalOne prim scrutinee source =
          .ok (sourceAfterScrutinee, value) →
        Direct.Expr.runState targetCtx scrutinee target =
          .ok targetAfterScrutinee →
        ∀ {stackAfterPop : EvmYul.Stack Word},
        targetAfterScrutinee.evm.stack.pop =
          some (stackAfterPop, value) →
        Source.Switch.select value cases defaultBody = some selected →
        Direct.Switch.select value cases defaultBody = some selected →
        StateRel sourceCtx.scope sourceAfterScrutinee
          (targetAfterScrutinee.withEVM
            { targetAfterScrutinee.evm with stack := stackAfterPop }) →
          BlockOpenRunBridge prim program sourceCtx targetCtx fuel selected
            sourceAfterScrutinee
            (targetAfterScrutinee.withEVM
              { targetAfterScrutinee.evm with stack := stackAfterPop }))
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx (fuel + 1)
          (.switch scrutinee cases defaultBody) source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx (fuel + 1)
      (.switch scrutinee cases defaultBody) source target := by
  cases hEvalOne : Source.Expr.evalOne prim scrutinee source with
  | error err =>
      simp [Source.Stmt.run, hEvalOne] at hSourceRun
  | ok scrutineeResult =>
      rcases scrutineeResult with ⟨sourceAfterScrutinee, value⟩
      rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
      have hCtxRel : CtxRel sourceCtx targetCtx :=
        ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
      rcases
          Expr.evalOne_pop_bridge_sourceOwned hPrim
            (layout := sourceCtx.scope) (ctx := targetCtx)
            (source := source) (source' := sourceAfterScrutinee)
            (value := value) (target := target)
            (by simpa [hLayout]) hNoDup
            (Scope.expr_sourceOwned_of_scoped hScrutineeScoped)
            (CtxRel.expr_accessible_of_scoped (offset := 0) hCtxRel
              hScrutineeScoped (by simpa using hAccessBound))
            hRel hEvalOne with
        ⟨targetAfterScrutinee, targetAfterPop, stackAfterPop,
          hTargetScrutinee, hPop, hTargetAfterPop, hPopRel⟩
      cases hSelect : Source.Switch.select value cases defaultBody with
      | none =>
          have hDirectSelect :
              Direct.Switch.select value cases defaultBody = none := by
            rw [← Switch.source_select_eq]
            exact hSelect
          simp [Source.Stmt.run, hEvalOne, hSelect] at hSourceRun
          cases hSourceRun
          exact
            ⟨(Source.Outcome.regular sourceAfterScrutinee, sourceCtx),
              (Outcome.regular targetAfterPop, targetCtx),
              by simp [Source.Stmt.run, hEvalOne, hSelect],
              by
                subst targetAfterPop
                simp [Direct.Stmt.run, hTargetScrutinee, hPop, hDirectSelect],
              RunResultRel.regular hPopRel hCtxRel hHandlers⟩
      | some selected =>
          have hDirectSelect :
              Direct.Switch.select value cases defaultBody = some selected := by
            rw [← Switch.source_select_eq]
            exact hSelect
          cases hSourceBody :
              Source.Block.runScoped prim program sourceCtx selected fuel
                sourceAfterScrutinee with
          | error err =>
              simp [Source.Stmt.run, hEvalOne, hSelect, hSourceBody]
                at hSourceRun
          | ok sourceOutcome =>
              have hSelectedBridge :
                  BlockOpenRunBridge prim program sourceCtx targetCtx fuel
                    selected sourceAfterScrutinee targetAfterPop := by
                subst targetAfterPop
                exact
                  hSelected hEvalOne hTargetScrutinee hPop hSelect
                    hDirectSelect hPopRel
              rcases
                  BlockOpenRunBridge.runScoped_from_open_bridge hCtxRel
                    hSelectedBridge hSourceBody with
                ⟨targetOutcome, hTargetBody, hScopedRel⟩
              simp [Source.Stmt.run, hEvalOne, hSelect, hSourceBody]
                at hSourceRun
              cases hSourceRun
              exact
                ⟨(sourceOutcome, sourceCtx), (targetOutcome, targetCtx),
                  by simp [Source.Stmt.run, hEvalOne, hSelect, hSourceBody],
                  by
                    subst targetAfterPop
                    simp [Direct.Stmt.run, hTargetScrutinee, hPop,
                      hDirectSelect, hTargetBody],
                  ScopedOutcomeRel.toRunResultRel hScopedRel rfl hCtxRel
                    hHandlers⟩

theorem switch_from_scoped_source_run_source_bound
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {scrutinee : Expr 1}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScrutineeScoped : Scope.ExprScoped sourceCtx.scope scrutinee)
    (hAccessBound : Access.ExprBound sourceCtx.scope 0 scrutinee)
    (hRel : StateRel sourceCtx.scope source target)
    (hSelected :
      ∀ {sourceAfterScrutinee : Source.State}
        {targetAfterScrutinee : RunState} {value : Word}
        {selected : Block},
        Source.Expr.evalOne prim scrutinee source =
          .ok (sourceAfterScrutinee, value) →
        Direct.Expr.runState targetCtx scrutinee target =
          .ok targetAfterScrutinee →
        ∀ {stackAfterPop : EvmYul.Stack Word},
        targetAfterScrutinee.evm.stack.pop =
          some (stackAfterPop, value) →
        Source.Switch.select value cases defaultBody = some selected →
        Direct.Switch.select value cases defaultBody = some selected →
        StateRel sourceCtx.scope sourceAfterScrutinee
          (targetAfterScrutinee.withEVM
            { targetAfterScrutinee.evm with stack := stackAfterPop }) →
          BlockOpenRunBridge prim program sourceCtx targetCtx fuel selected
            sourceAfterScrutinee
            (targetAfterScrutinee.withEVM
              { targetAfterScrutinee.evm with stack := stackAfterPop }))
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx (fuel + 1)
          (.switch scrutinee cases defaultBody) source =
        .ok sourceResult) :
    StmtRunBridge prim program sourceCtx targetCtx (fuel + 1)
      (.switch scrutinee cases defaultBody) source target := by
  apply
    switch_from_scoped_source_run hPrim hCtx hHandlers hNoDup
      hScrutineeScoped
  · rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
    simpa [Access.ExprBound, hLayout] using hAccessBound
  · exact hRel
  · exact hSelected
  · exact hSourceRun

end StmtRunBridge

namespace BlockOpenRunBridge

theorem nil {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target) :
    BlockOpenRunBridge prim program sourceCtx targetCtx (fuel + 1)
      { stmts := [] } source target := by
  exact
    ⟨(Source.Outcome.regular source, sourceCtx),
      (Outcome.regular target, targetCtx),
      by simp [Source.Block.runOpen],
      by simp [Direct.Block.runOpen],
      RunResultRel.regular hRel hCtx hHandlers⟩

theorem cons_from_stmt_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {stmt : Stmt} {rest : List Stmt}
    (hHead :
      StmtRunBridge prim program sourceCtx targetCtx fuel stmt source target)
    (hTail :
      ∀ {sourceAfter : Source.State} {sourceCtxAfter : Source.Ctx}
        {targetAfter : RunState} {targetCtxAfter : Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
        Direct.Stmt.run program targetCtx fuel stmt target =
          .ok (Outcome.regular targetAfter, targetCtxAfter) →
        StateRel sourceCtxAfter.scope sourceAfter targetAfter →
        CtxRel sourceCtxAfter targetCtxAfter →
        CtxHandlersRel sourceCtxAfter targetCtxAfter →
          BlockOpenRunBridge prim program sourceCtxAfter targetCtxAfter fuel
            { stmts := rest } sourceAfter targetAfter) :
    BlockOpenRunBridge prim program sourceCtx targetCtx (fuel + 1)
      { stmts := stmt :: rest } source target := by
  rcases hHead with
    ⟨sourceResult, targetResult, hSourceStmt, hTargetStmt, hResultRel⟩
  rcases sourceResult with ⟨sourceOutcome, sourceCtxAfter⟩
  rcases targetResult with ⟨targetOutcome, targetCtxAfter⟩
  rcases sourceOutcome with ⟨sourceAfter, sourceMode⟩
  rcases targetOutcome with ⟨targetAfter, targetMode⟩
  cases sourceMode with
  | regular =>
      cases targetMode with
      | regular =>
        rcases hResultRel with ⟨hState, hCtx, hHandlers⟩
        rcases
            hTail hSourceStmt hTargetStmt hState hCtx hHandlers with
          ⟨tailSourceResult, tailTargetResult, hSourceTail, hTargetTail,
            hTailRel⟩
        refine ⟨tailSourceResult, tailTargetResult, ?_, ?_, hTailRel⟩
        · simpa [Source.Block.runOpen, Source.Outcome.regular, hSourceStmt]
            using hSourceTail
        · simpa [Direct.Block.runOpen, Outcome.regular, hTargetStmt]
            using hTargetTail
      | brk => cases hResultRel
      | cont => cases hResultRel
      | leave => cases hResultRel
      | halt _ => cases hResultRel
  | brk =>
      cases targetMode with
      | regular => cases hResultRel
      | brk =>
        rcases hResultRel with ⟨layout, hState⟩
        refine
          ⟨(Source.Outcome.brk sourceAfter, sourceCtx),
            (Outcome.brk targetAfter, targetCtx), ?_, ?_,
            RunResultRel.brk (layout := layout) hState⟩
        · simp [Source.Block.runOpen, Source.Outcome.brk, hSourceStmt]
        · simp [Direct.Block.runOpen, Outcome.brk,
            Structured.Outcome.brk, hTargetStmt]
      | cont => cases hResultRel
      | leave => cases hResultRel
      | halt _ => cases hResultRel
  | cont =>
      cases targetMode with
      | regular => cases hResultRel
      | brk => cases hResultRel
      | cont =>
        rcases hResultRel with ⟨layout, hState⟩
        refine
          ⟨(Source.Outcome.cont sourceAfter, sourceCtx),
            (Outcome.cont targetAfter, targetCtx), ?_, ?_,
            RunResultRel.cont (layout := layout) hState⟩
        · simp [Source.Block.runOpen, Source.Outcome.cont, hSourceStmt]
        · simp [Direct.Block.runOpen, Outcome.cont,
            Structured.Outcome.cont, hTargetStmt]
      | leave => cases hResultRel
      | halt _ => cases hResultRel
  | leave =>
      cases targetMode with
      | regular => cases hResultRel
      | brk => cases hResultRel
      | cont => cases hResultRel
      | leave =>
        rcases hResultRel with ⟨layout, hState⟩
        refine
          ⟨(Source.Outcome.leave sourceAfter, sourceCtx),
            (Outcome.leave targetAfter, targetCtx), ?_, ?_,
            RunResultRel.leave (layout := layout) hState⟩
        · simp [Source.Block.runOpen, Source.Outcome.leave, hSourceStmt]
        · simp [Direct.Block.runOpen, Outcome.leave,
            Structured.Outcome.leave, hTargetStmt]
      | halt _ => cases hResultRel
  | halt sourceKind =>
      cases targetMode with
      | regular => cases hResultRel
      | brk => cases hResultRel
      | cont => cases hResultRel
      | leave => cases hResultRel
      | halt targetKind =>
        rcases hResultRel with ⟨hShared, hKind⟩
        subst hKind
        refine
          ⟨(Source.Outcome.halt sourceKind sourceAfter, sourceCtx),
            (Outcome.halt sourceKind targetAfter, targetCtx), ?_, ?_,
            RunResultRel.halt_shared hShared⟩
        · simp [Source.Block.runOpen, Source.Outcome.halt, hSourceStmt]
        · simp [Direct.Block.runOpen, Outcome.halt,
          Structured.Outcome.halt, hTargetStmt]

theorem cons_from_stmt_source_run {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {stmt : Stmt} {rest : List Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hSourceBlock :
      Source.Block.runOpen prim program sourceCtx (fuel + 1)
          { stmts := stmt :: rest } source =
        .ok sourceResult)
    (hHead :
      ∀ {sourceHeadResult : Source.Outcome × Source.Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok sourceHeadResult →
        StmtRunBridge prim program sourceCtx targetCtx fuel stmt source target)
    (hTail :
      ∀ {sourceAfter : Source.State} {sourceCtxAfter : Source.Ctx}
        {targetAfter : RunState} {targetCtxAfter : Ctx}
        {tailSourceResult : Source.Outcome × Source.Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
        Direct.Stmt.run program targetCtx fuel stmt target =
          .ok (Outcome.regular targetAfter, targetCtxAfter) →
        StateRel sourceCtxAfter.scope sourceAfter targetAfter →
        CtxRel sourceCtxAfter targetCtxAfter →
        CtxHandlersRel sourceCtxAfter targetCtxAfter →
        Source.Block.runOpen prim program sourceCtxAfter fuel
            { stmts := rest } sourceAfter =
          .ok tailSourceResult →
          BlockOpenRunBridge prim program sourceCtxAfter targetCtxAfter fuel
            { stmts := rest } sourceAfter targetAfter) :
    BlockOpenRunBridge prim program sourceCtx targetCtx (fuel + 1)
      { stmts := stmt :: rest } source target := by
  cases hSourceStmt :
      Source.Stmt.run prim program sourceCtx fuel stmt source with
  | error err =>
      simp [Source.Block.runOpen, hSourceStmt] at hSourceBlock
  | ok sourceHeadResult =>
      apply cons_from_stmt_bridge (hHead hSourceStmt)
      intro sourceAfter sourceCtxAfter targetAfter targetCtxAfter
        hSourceStmtRegular hTargetStmtRegular hState hCtx hHandlers
      have hTailSource :
          Source.Block.runOpen prim program sourceCtxAfter fuel
              { stmts := rest } sourceAfter =
            .ok sourceResult := by
        simpa [Source.Block.runOpen, hSourceStmtRegular] using hSourceBlock
      exact
        hTail hSourceStmtRegular hTargetStmtRegular hState hCtx hHandlers
          hTailSource

theorem cons_from_atomic_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {stmt : Stmt} {rest : List Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hSourceBlock :
      Source.Block.runOpen prim program sourceCtx (fuel + 1)
          { stmts := stmt :: rest } source =
        .ok sourceResult)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAtomic : AtomicStmt.Holds stmt)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope stmt)
    (hAccessBound :
      AtomicStmt.AccessBound targetCtx.layout.length stmt)
    (hRel : StateRel sourceCtx.scope source target)
    (hTail :
      ∀ {sourceAfter : Source.State} {sourceCtxAfter : Source.Ctx}
        {targetAfter : RunState} {targetCtxAfter : Ctx}
        {tailSourceResult : Source.Outcome × Source.Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
        Direct.Stmt.run program targetCtx fuel stmt target =
          .ok (Outcome.regular targetAfter, targetCtxAfter) →
        StateRel sourceCtxAfter.scope sourceAfter targetAfter →
        CtxRel sourceCtxAfter targetCtxAfter →
        CtxHandlersRel sourceCtxAfter targetCtxAfter →
        Source.Block.runOpen prim program sourceCtxAfter fuel
            { stmts := rest } sourceAfter =
          .ok tailSourceResult →
          BlockOpenRunBridge prim program sourceCtxAfter targetCtxAfter fuel
            { stmts := rest } sourceAfter targetAfter) :
    BlockOpenRunBridge prim program sourceCtx targetCtx (fuel + 1)
      { stmts := stmt :: rest } source target := by
  exact
    cons_from_stmt_source_run hSourceBlock
      (fun {sourceHeadResult} hSourceStmt =>
        StmtRunBridge.atomic_from_scoped_source_run hPrim hCtx hHandlers
          hNoDup hAtomic hScoped hAccessBound hRel hSourceStmt)
      hTail

end BlockOpenRunBridge

/--
Handler-aware statement bridge.  `entryCtx` is the context whose break,
continue, and leave handlers should own abrupt exits; `sourceCtx` is the
current lexical context used to run the statement.

The older `StmtRunBridge` projects from this by forgetting the exact handler
scope carried by abrupt exits.
-/
def StmtRunBridgeAt (prim : Source.PrimitiveSemantics)
    (program : Program) (entryCtx sourceCtx : Source.Ctx) (targetCtx : Ctx)
    (fuel : Nat) (stmt : Stmt) (source : Source.State)
    (target : RunState) : Prop :=
  ∃ sourceResult : Source.Outcome × Source.Ctx,
  ∃ targetResult : Outcome × Ctx,
    Source.Stmt.run prim program sourceCtx fuel stmt source =
      .ok sourceResult ∧
    Direct.Stmt.run program targetCtx fuel stmt target =
      .ok targetResult ∧
    RunResultRelAt entryCtx sourceResult targetResult

namespace StmtRunBridgeAt

theorem toStmtRunBridge {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {fuel : Nat} {stmt : Stmt} {source : Source.State}
    {target : RunState}
    (hBridge :
      StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel stmt
        source target) :
    StmtRunBridge prim program sourceCtx targetCtx fuel stmt source target := by
  rcases hBridge with
    ⟨sourceResult, targetResult, hSource, hTarget, hRel⟩
  exact
    ⟨sourceResult, targetResult, hSource, hTarget,
      RunResultRelAt.toRunResultRel hRel⟩

theorem rebase {prim : Source.PrimitiveSemantics}
    {program : Program} {fromEntry toEntry sourceCtx : Source.Ctx}
    {targetCtx : Ctx} {fuel : Nat} {stmt : Stmt}
    {source : Source.State} {target : RunState}
    (hHandlers : HandlerScopesEq fromEntry toEntry)
    (hBridge :
      StmtRunBridgeAt prim program fromEntry sourceCtx targetCtx fuel stmt
        source target) :
    StmtRunBridgeAt prim program toEntry sourceCtx targetCtx fuel stmt source
      target := by
  rcases hBridge with
    ⟨sourceResult, targetResult, hSource, hTarget, hRel⟩
  exact
    ⟨sourceResult, targetResult, hSource, hTarget,
      RunResultRelAt.rebase hHandlers hRel⟩

theorem expr {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterExpr : Source.State} {target : RunState}
    {fuel : Nat} {expr : Expr 0} {values : List Word}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hRel : StateRel sourceCtx.scope source target)
    (hEval :
      Source.Expr.eval prim expr source = .ok (sourceAfterExpr, values)) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel (.expr expr)
      source target := by
  rcases Stmt.expr_bridge hPrim hCtx hNoDup hOwned hAccess hRel hEval with
    ⟨targetAfter, hSource, hTarget, hState, hCtxOut⟩
  exact
    ⟨(Source.Outcome.regular sourceAfterExpr, sourceCtx),
      (Outcome.regular targetAfter, targetCtx), hSource, hTarget,
      RunResultRelAt.regular hState hCtxOut hHandlers⟩

theorem letExpr {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterValue : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {value : Word} {expr : Expr 1}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalOne :
      Source.Expr.evalOne prim expr source = .ok (sourceAfterValue, value)) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.let_ name expr) source target := by
  rcases
      Stmt.let_expr_bridge hPrim hCtx hNoDup hOwned hAccess hFresh hRel
        hEvalOne with
    ⟨targetAfter, hSource, hTarget, hState, hCtxOut⟩
  let sourceCtxOut : Source.Ctx :=
    { sourceCtx with scope := name :: sourceCtx.scope }
  let targetCtxOut : Ctx :=
    targetCtx.withLayout (name :: targetCtx.layout)
  have hHandlersOut :
      CtxHandlersRel sourceCtxOut targetCtxOut := by
    exact CtxHandlersRel.withScopeCons hHandlers
  exact
    ⟨(Source.Outcome.regular (sourceAfterValue.insert name value),
        sourceCtxOut),
      (Outcome.regular targetAfter, targetCtxOut),
      by simpa [sourceCtxOut] using hSource,
      by simpa [targetCtxOut] using hTarget,
      RunResultRelAt.regular
        (by simpa [sourceCtxOut] using hState)
        (by simpa [sourceCtxOut, targetCtxOut] using hCtxOut)
        hHandlersOut⟩

theorem assign_expr {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterValue : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {idx : Nat} {value : Word}
    {expr : Expr 1}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hName : sourceCtx.scope[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hOwned : Source.Expr.SourceOwned expr)
    (hAccess : Expr.Accessible sourceCtx.scope 0 expr)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalOne :
      Source.Expr.evalOne prim expr source = .ok (sourceAfterValue, value)) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.assign name expr) source target := by
  rcases
      Stmt.assign_expr_bridge hPrim hCtx hNoDup hName hBound hOwned hAccess
        hRel hEvalOne with
    ⟨targetAfter, hSource, hTarget, hState, hCtxOut⟩
  exact
    ⟨(Source.Outcome.regular
        (sourceAfterValue.withVars
          (Source.Store.insert sourceAfterValue.vars name value)),
        sourceCtx),
      (Outcome.regular targetAfter, targetCtx), hSource, hTarget,
      RunResultRelAt.regular hState hCtxOut hHandlers⟩

theorem brk {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {breakScope : List Name}
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hBreak : sourceCtx.breakScope? = some breakScope)
    (hRel : StateRel targetCtx.layout source target) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel .brk source
      target := by
  rcases Stmt.brk_bridge hCtx hHandlers hBreak hRel with
    ⟨targetAfter, hSource, hTarget, hState, _hCtxOut, _hHandlersOut⟩
  rcases hEntryHandlers with ⟨hBreakEq, _hContinueEq, _hLeaveEq⟩
  have hEntryBreak : entryCtx.breakScope? = some breakScope :=
    hBreakEq.trans hBreak
  exact
    ⟨(Source.Outcome.brk (source.restrictTo breakScope), sourceCtx),
      (Outcome.brk targetAfter, targetCtx), hSource, hTarget,
      RunResultRelAt.brk hEntryBreak hState⟩

theorem cont {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {continueScope : List Name}
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hContinue : sourceCtx.continueScope? = some continueScope)
    (hRel : StateRel targetCtx.layout source target) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel .cont source
      target := by
  rcases Stmt.cont_bridge hCtx hHandlers hContinue hRel with
    ⟨targetAfter, hSource, hTarget, hState, _hCtxOut, _hHandlersOut⟩
  rcases hEntryHandlers with ⟨_hBreakEq, hContinueEq, _hLeaveEq⟩
  have hEntryContinue : entryCtx.continueScope? = some continueScope :=
    hContinueEq.trans hContinue
  exact
    ⟨(Source.Outcome.cont (source.restrictTo continueScope), sourceCtx),
      (Outcome.cont targetAfter, targetCtx), hSource, hTarget,
      RunResultRelAt.cont hEntryContinue hState⟩

theorem terminal {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {kind : Assembly.HaltKind} {shared' : EvmYul.SharedState .EVM}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hTerminal : prim.terminal kind source.shared [] = .ok shared') :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.terminal kind) source target := by
  rcases Stmt.terminal_bridge hPrim hCtx hRel hTerminal with
    ⟨sourceAfter, targetAfter, hSource, hTarget, hOutcome, _hCtxOut⟩
  exact
    ⟨(Source.Outcome.halt kind sourceAfter, sourceCtx),
      (Outcome.halt kind targetAfter, targetCtx), hSource, hTarget,
      by
        rcases hOutcome with ⟨hShared, hKind⟩
        cases hKind
        exact RunResultRelAt.halt_shared hShared⟩

theorem terminalArgs {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source sourceAfterArgs : Source.State} {target : RunState}
    {fuel : Nat} {kind : Assembly.HaltKind} {args : ExprSeq kind.argCount}
    {values : List Word} {shared' : EvmYul.SharedState .EVM}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hOwned : Source.ExprSeq.SourceOwned args)
    (hAccess : ExprSeq.Accessible sourceCtx.scope 0 args)
    (hRel : StateRel sourceCtx.scope source target)
    (hEvalArgs :
      Source.Expr.ExprSeq.eval prim args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      prim.terminal kind sourceAfterArgs.shared values = .ok shared') :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.terminalArgs kind args) source target := by
  rcases
      Stmt.terminalArgs_bridge hPrim hCtx hNoDup hOwned hAccess hRel
        hEvalArgs hTerminal with
    ⟨targetAfter, hSource, hTarget, hOutcome, _hCtxOut⟩
  exact
    ⟨(Source.Outcome.halt kind (sourceAfterArgs.withShared shared'),
        sourceCtx),
      (Outcome.halt kind targetAfter, targetCtx), hSource, hTarget,
      by
        rcases hOutcome with ⟨hShared, hKind⟩
        cases hKind
        exact RunResultRelAt.halt_shared hShared⟩

theorem expr_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {expr : Expr 0}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope (.expr expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.expr expr) source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel (.expr expr)
      source target := by
  cases hEval : Source.Expr.eval prim expr source with
  | error err =>
      simp [Source.Stmt.run, hEval] at hSourceRun
  | ok result =>
      rcases result with ⟨sourceAfterExpr, values⟩
      simp [Source.Stmt.run, hEval] at hSourceRun
      cases hSourceRun
      exact
        StmtRunBridgeAt.expr hPrim hCtx hHandlers hNoDup
          (Scope.expr_sourceOwned_of_scoped hScoped)
          (CtxRel.expr_accessible_of_scoped (offset := 0) hCtx hScoped
            (by simpa using hAccessBound))
          hRel hEval

theorem letExpr_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {expr : Expr 1}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.let_ name expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.let_ name expr) source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.let_ name expr) source target := by
  cases hEvalOne : Source.Expr.evalOne prim expr source with
  | error err =>
      simp [Source.Stmt.run, hEvalOne] at hSourceRun
  | ok result =>
      rcases result with ⟨sourceAfterValue, value⟩
      simp [Source.Stmt.run, hEvalOne] at hSourceRun
      cases hSourceRun
      rcases hScoped with ⟨hFresh, hExprScoped⟩
      exact
        letExpr hPrim hCtx hHandlers hNoDup
          (Scope.expr_sourceOwned_of_scoped hExprScoped)
          (CtxRel.expr_accessible_of_scoped (offset := 0) hCtx hExprScoped
            (by simpa using hAccessBound))
          hFresh hRel hEvalOne

theorem assign_expr_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {name : Name} {expr : Expr 1}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.assign name expr))
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth expr ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.assign name expr)
          source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.assign name expr) source target := by
  cases hContains : source.vars.contains name with
  | false =>
      simp [Source.Stmt.run, hContains, Source.invalid, invalid,
        Structured.invalid] at hSourceRun
  | true =>
      cases hEvalOne : Source.Expr.evalOne prim expr source with
      | error err =>
          simp [Source.Stmt.run, hContains, hEvalOne] at hSourceRun
      | ok result =>
          rcases result with ⟨sourceAfterValue, value⟩
          simp [Source.Stmt.run, hContains, hEvalOne] at hSourceRun
          cases hSourceRun
          rcases hScoped with ⟨hContainsScope, hExprScoped⟩
          rcases List.mem_iff_getElem?.mp hContainsScope with ⟨idx, hName⟩
          have hBound : idx + 1 ≤ 16 := by
            have hIdxLt : idx < sourceCtx.scope.length :=
              (List.getElem?_eq_some_iff.mp hName).1
            rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
            have hScopeLen : sourceCtx.scope.length ≤ 16 := by
              rw [← hLayout]
              omega
            omega
          exact
            assign_expr hPrim hCtx hHandlers hNoDup hName hBound
              (Scope.expr_sourceOwned_of_scoped hExprScoped)
              (CtxRel.expr_accessible_of_scoped (offset := 0) hCtx
                hExprScoped (by simpa using hAccessBound))
              hRel hEvalOne

theorem brk_from_source_run {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel .brk source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel .brk source
      target := by
  cases hBreak : sourceCtx.breakScope? with
  | none =>
      simp [Source.Stmt.run, hBreak, Source.invalid, invalid,
        Structured.invalid] at hSourceRun
  | some breakScope =>
      simp [Source.Stmt.run, hBreak] at hSourceRun
      cases hSourceRun
      have hRelTarget : StateRel targetCtx.layout source target := by
        rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
        simpa [hLayout] using hRel
      exact brk hEntryHandlers hCtx hHandlers hBreak hRelTarget

theorem cont_from_source_run {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel .cont source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel .cont source
      target := by
  cases hContinue : sourceCtx.continueScope? with
  | none =>
      simp [Source.Stmt.run, hContinue, Source.invalid, invalid,
        Structured.invalid] at hSourceRun
  | some continueScope =>
      simp [Source.Stmt.run, hContinue] at hSourceRun
      cases hSourceRun
      have hRelTarget : StateRel targetCtx.layout source target := by
        rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
        simpa [hLayout] using hRel
      exact cont hEntryHandlers hCtx hHandlers hContinue hRelTarget

theorem terminal_from_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {kind : Assembly.HaltKind}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.terminal kind) source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.terminal kind) source target := by
  cases hTerminal : prim.terminal kind source.shared [] with
  | error err =>
      simp [Source.Stmt.run, hTerminal] at hSourceRun
  | ok shared' =>
      simp [Source.Stmt.run, hTerminal] at hSourceRun
      cases hSourceRun
      exact terminal hPrim hCtx hRel hTerminal

theorem terminalArgs_from_scoped_source_run
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {kind : Assembly.HaltKind} {args : ExprSeq kind.argCount}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope
        (.terminalArgs kind args))
    (hAccessBound :
      targetCtx.layout.length + Access.exprSeqWidth args ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel
          (.terminalArgs kind args) source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.terminalArgs kind args) source target := by
  cases hEvalArgs : Source.Expr.ExprSeq.eval prim args source with
  | error err =>
      simp [Source.Stmt.run, hEvalArgs] at hSourceRun
  | ok argResult =>
      rcases argResult with ⟨sourceAfterArgs, values⟩
      simp [Source.Stmt.run, hEvalArgs] at hSourceRun
      cases hTerminal :
          prim.terminal kind sourceAfterArgs.shared values with
      | error err =>
          simp [hTerminal] at hSourceRun
      | ok shared' =>
          simp [hTerminal] at hSourceRun
          cases hSourceRun
          exact
            terminalArgs hPrim hCtx hNoDup
              (Scope.exprSeq_sourceOwned_of_scoped hScoped)
              (CtxRel.exprSeq_accessible_of_scoped (offset := 0) hCtx
                hScoped (by simpa using hAccessBound))
              hRel hEvalArgs hTerminal

theorem atomic_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {stmt : Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAtomic : AtomicStmt.Holds stmt)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope stmt)
    (hAccessBound :
      AtomicStmt.AccessBound targetCtx.layout.length stmt)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel stmt source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel stmt source
      target := by
  cases stmt with
  | expr expr =>
      rename_i results
      dsimp [AtomicStmt.Holds] at hAtomic
      subst results
      exact
        expr_from_scoped_source_run hPrim hCtx hHandlers hNoDup hScoped
          (by simpa [AtomicStmt.AccessBound] using hAccessBound)
          hRel hSourceRun
  | exprs exprs =>
      cases hAtomic
  | let_ name value =>
      exact
        letExpr_from_scoped_source_run hPrim hCtx hHandlers hNoDup hScoped
          (by simpa [AtomicStmt.AccessBound] using hAccessBound)
          hRel hSourceRun
  | assign name value =>
      exact
        assign_expr_from_scoped_source_run hPrim hCtx hHandlers hNoDup hScoped
          (by simpa [AtomicStmt.AccessBound] using hAccessBound)
          hRel hSourceRun
  | assignTop name =>
      cases hAtomic
  | assignTopWithOffset offset name =>
      cases hAtomic
  | block body =>
      cases hAtomic
  | if_ cond body =>
      cases hAtomic
  | switch scrutinee cases defaultBody =>
      cases hAtomic
  | for_ init cond post body =>
      cases hAtomic
  | brk =>
      exact
        brk_from_source_run hEntryHandlers hCtx hHandlers hRel hSourceRun
  | cont =>
      exact
        cont_from_source_run hEntryHandlers hCtx hHandlers hRel hSourceRun
  | leave =>
      cases hAtomic
  | call name =>
      cases hAtomic
  | terminal kind =>
      exact terminal_from_source_run hPrim hCtx hRel hSourceRun
  | terminalArgs kind args =>
      exact
        terminalArgs_from_scoped_source_run hPrim hCtx hNoDup hScoped
          (by simpa [AtomicStmt.AccessBound] using hAccessBound)
          hRel hSourceRun

theorem atomic_from_scoped_source_run_source_bound
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {stmt : Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAtomic : AtomicStmt.Holds stmt)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope stmt)
    (hAccessBound :
      AtomicStmt.SourceAccessBound sourceCtx.scope stmt)
    (hRel : StateRel sourceCtx.scope source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel stmt source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel stmt source
      target := by
  exact
    atomic_from_scoped_source_run hPrim hEntryHandlers hCtx hHandlers hNoDup
      hAtomic hScoped
      (AtomicStmt.accessBound_of_sourceAccessBound hCtx hAccessBound)
      hRel hSourceRun

theorem atomic_regular_handlerScopesEq {prim : Source.PrimitiveSemantics}
    {program : Program} {sourceCtx sourceCtxAfter : Source.Ctx}
    {fuel : Nat} {stmt : Stmt} {source sourceAfter : Source.State}
    (hAtomic : AtomicStmt.Holds stmt)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel stmt source =
        .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter)) :
    HandlerScopesEq sourceCtx sourceCtxAfter := by
  cases stmt with
  | expr expr =>
      rename_i results
      dsimp [AtomicStmt.Holds] at hAtomic
      subst results
      cases hEval : Source.Expr.eval prim expr source with
      | error err =>
          simp [Source.Stmt.run, hEval] at hSourceRun
      | ok result =>
          rcases result with ⟨stateAfterExpr, values⟩
          simp [Source.Stmt.run, hEval] at hSourceRun
          rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
          cases hCtxEq
          exact HandlerScopesEq.refl sourceCtx
  | exprs exprs =>
      cases hAtomic
  | let_ name value =>
      cases hEval : Source.Expr.evalOne prim value source with
      | error err =>
          simp [Source.Stmt.run, hEval] at hSourceRun
      | ok result =>
          rcases result with ⟨stateAfterValue, value'⟩
          simp [Source.Stmt.run, hEval] at hSourceRun
          rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
          cases hCtxEq
          simp [HandlerScopesEq]
  | assign name value =>
      cases hContains : source.vars.contains name with
      | false =>
          simp [Source.Stmt.run, hContains, Source.invalid,
            Structured.invalid] at hSourceRun
      | true =>
          cases hEval : Source.Expr.evalOne prim value source with
          | error err =>
              simp [Source.Stmt.run, hContains, hEval] at hSourceRun
          | ok result =>
              rcases result with ⟨stateAfterValue, value'⟩
              simp [Source.Stmt.run, hContains, hEval] at hSourceRun
              rcases hSourceRun with ⟨_hOutcome, hCtxEq⟩
              cases hCtxEq
              exact HandlerScopesEq.refl sourceCtx
  | assignTop name =>
      cases hAtomic
  | assignTopWithOffset offset name =>
      cases hAtomic
  | block body =>
      cases hAtomic
  | if_ cond body =>
      cases hAtomic
  | switch scrutinee cases defaultBody =>
      cases hAtomic
  | for_ init cond post body =>
      cases hAtomic
  | brk =>
      cases hBreak : sourceCtx.breakScope? with
      | none =>
          simp [Source.Stmt.run, hBreak, Source.invalid,
            Structured.invalid] at hSourceRun
      | some breakScope =>
          simp [Source.Stmt.run, hBreak, Source.Outcome.brk] at hSourceRun
          rcases hSourceRun with ⟨hOutcome, _hCtxEq⟩
          cases hOutcome
  | cont =>
      cases hContinue : sourceCtx.continueScope? with
      | none =>
          simp [Source.Stmt.run, hContinue, Source.invalid,
            Structured.invalid] at hSourceRun
      | some continueScope =>
          simp [Source.Stmt.run, hContinue, Source.Outcome.cont] at hSourceRun
          rcases hSourceRun with ⟨hOutcome, _hCtxEq⟩
          cases hOutcome
  | leave =>
      cases hAtomic
  | call name =>
      cases hAtomic
  | terminal kind =>
      cases hTerminal : prim.terminal kind source.shared [] with
      | error err =>
          simp [Source.Stmt.run, hTerminal] at hSourceRun
      | ok shared' =>
          simp [Source.Stmt.run, hTerminal, Source.Outcome.halt]
            at hSourceRun
          rcases hSourceRun with ⟨hOutcome, _hCtxEq⟩
          cases hOutcome
  | terminalArgs kind args =>
      cases hEvalArgs : Source.Expr.ExprSeq.eval prim args source with
      | error err =>
          simp [Source.Stmt.run, hEvalArgs] at hSourceRun
      | ok argResult =>
          rcases argResult with ⟨stateAfterArgs, values⟩
          cases hTerminal :
              prim.terminal kind stateAfterArgs.shared values with
          | error err =>
              simp [Source.Stmt.run, hEvalArgs, hTerminal] at hSourceRun
          | ok shared' =>
              simp [Source.Stmt.run, hEvalArgs, hTerminal,
                Source.Outcome.halt] at hSourceRun
              rcases hSourceRun with ⟨hOutcome, _hCtxEq⟩
              cases hOutcome

end StmtRunBridgeAt

/--
Handler-aware open-block bridge.  The block executes under `sourceCtx`, but
abrupt exits are related to the handlers installed by `entryCtx`.  This is the
compositional boundary needed once a regular head statement changes the lexical
scope before the tail runs.
-/
def BlockOpenRunBridgeAt (prim : Source.PrimitiveSemantics)
    (program : Program) (entryCtx sourceCtx : Source.Ctx) (targetCtx : Ctx)
    (fuel : Nat) (block : Block) (source : Source.State)
    (target : RunState) : Prop :=
  ∃ sourceResult : Source.Outcome × Source.Ctx,
  ∃ targetResult : Outcome × Ctx,
    Source.Block.runOpen prim program sourceCtx fuel block source =
      .ok sourceResult ∧
    Direct.Block.runOpen program targetCtx fuel block target =
      .ok targetResult ∧
    RunResultRelAt entryCtx sourceResult targetResult

namespace BlockOpenRunBridgeAt

theorem toBlockOpenRunBridge {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {fuel : Nat} {block : Block} {source : Source.State}
    {target : RunState}
    (hBridge :
      BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel block
        source target) :
    BlockOpenRunBridge prim program sourceCtx targetCtx fuel block source
      target := by
  rcases hBridge with
    ⟨sourceResult, targetResult, hSource, hTarget, hRel⟩
  exact
    ⟨sourceResult, targetResult, hSource, hTarget,
      RunResultRelAt.toRunResultRel hRel⟩

theorem rebase {prim : Source.PrimitiveSemantics}
    {program : Program} {fromEntry toEntry sourceCtx : Source.Ctx}
    {targetCtx : Ctx} {fuel : Nat} {block : Block}
    {source : Source.State} {target : RunState}
    (hHandlers : HandlerScopesEq fromEntry toEntry)
    (hBridge :
      BlockOpenRunBridgeAt prim program fromEntry sourceCtx targetCtx fuel block
        source target) :
    BlockOpenRunBridgeAt prim program toEntry sourceCtx targetCtx fuel block
      source target := by
  rcases hBridge with
    ⟨sourceResult, targetResult, hSource, hTarget, hRel⟩
  exact
    ⟨sourceResult, targetResult, hSource, hTarget,
      RunResultRelAt.rebase hHandlers hRel⟩

theorem target_result_of_source {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {fuel : Nat} {block : Block} {source : Source.State}
    {target : RunState} {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel block
        source target)
    (hSourceRun :
      Source.Block.runOpen prim program sourceCtx fuel block source =
        .ok sourceResult) :
    ∃ targetResult : Outcome × Ctx,
      Direct.Block.runOpen program targetCtx fuel block target =
          .ok targetResult ∧
        RunResultRelAt entryCtx sourceResult targetResult := by
  rcases hBridge with
    ⟨bridgeSourceResult, targetResult, hBridgeSource, hTarget, hRel⟩
  rw [hSourceRun] at hBridgeSource
  cases hBridgeSource
  exact ⟨targetResult, hTarget, hRel⟩

theorem runScoped_from_open_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {fuel : Nat} {block : Block} {source : Source.State}
    {target : RunState} {sourceOutcome : Source.Outcome}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hBridge :
      BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel block
        source target)
    (hSourceRun :
      Source.Block.runScoped prim program sourceCtx block fuel source =
        .ok sourceOutcome) :
    ∃ targetOutcome : Outcome,
      Direct.Block.runScoped program targetCtx block fuel target =
          .ok targetOutcome ∧
        ScopedOutcomeRelAt entryCtx sourceCtx.scope sourceOutcome
          targetOutcome := by
  unfold Source.Block.runScoped at hSourceRun
  cases hSourceOpen :
      Source.Block.runOpen prim program sourceCtx fuel block source with
  | error err =>
      simp [hSourceOpen] at hSourceRun
  | ok sourceOpenResult =>
      rcases sourceOpenResult with ⟨sourceOpenOutcome, sourceFinalCtx⟩
      rcases target_result_of_source hBridge hSourceOpen with
        ⟨targetOpenResult, hTargetOpen, hOpenRel⟩
      rcases targetOpenResult with ⟨targetOpenOutcome, targetFinalCtx⟩
      rcases sourceOpenOutcome with ⟨sourceOpenState, sourceMode⟩
      rcases targetOpenOutcome with ⟨targetOpenState, targetMode⟩
      cases sourceMode with
      | regular =>
          cases targetMode with
          | regular =>
              simp [RunResultRelAt] at hOpenRel
              rcases hOpenRel with
                ⟨hStateOpen, hFinalCtx, _hFinalHandlers⟩
              simp [hSourceOpen, Source.Outcome.regular] at hSourceRun
              cases hSourceRun
              have hFinalScope :
                  sourceFinalCtx.scope =
                    Scope.Block.outEnv sourceCtx.scope block :=
                Source.Block.runOpen_regular_scope hSourceOpen
              rcases hCtx with
                ⟨hInitialLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
              rcases hFinalCtx with
                ⟨hFinalLayout, _hFinalBreak, _hFinalContinue, _hFinalLeave,
                  _hFinalRetc⟩
              have hCleanupScope :
                  CleanupScopeRel targetFinalCtx.layout sourceCtx.scope := by
                rw [hFinalLayout, hFinalScope]
                exact Scope.block_outEnv_cleanupScopeRel sourceCtx.scope block
              rcases
                  StateRel.cleanupTo_scope_exists
                    (ctx := targetFinalCtx) hCleanupScope
                    (by simpa [hFinalLayout] using hStateOpen) with
                ⟨cleaned, hCleanup, hCleanRel, _hReturns⟩
              refine
                ⟨Outcome.regular cleaned, ?_, ScopedOutcomeRelAt.regular
                  hCleanRel⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.regular,
                hInitialLayout, hCleanup]
          | brk =>
              simp [RunResultRelAt] at hOpenRel
          | cont =>
              simp [RunResultRelAt] at hOpenRel
          | leave =>
              simp [RunResultRelAt] at hOpenRel
          | halt _ =>
              simp [RunResultRelAt] at hOpenRel
      | brk =>
          cases targetMode with
          | regular =>
              simp [RunResultRelAt] at hOpenRel
          | brk =>
              simp [RunResultRelAt] at hOpenRel
              rcases hOpenRel with ⟨breakScope, hBreak, hState⟩
              simp [hSourceOpen] at hSourceRun
              cases hSourceRun
              refine
                ⟨Outcome.brk targetOpenState, ?_,
                  ScopedOutcomeRelAt.brk (scope := sourceCtx.scope)
                    hBreak hState⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.brk,
                Structured.Outcome.brk]
          | cont =>
              simp [RunResultRelAt] at hOpenRel
          | leave =>
              simp [RunResultRelAt] at hOpenRel
          | halt _ =>
              simp [RunResultRelAt] at hOpenRel
      | cont =>
          cases targetMode with
          | regular =>
              simp [RunResultRelAt] at hOpenRel
          | brk =>
              simp [RunResultRelAt] at hOpenRel
          | cont =>
              simp [RunResultRelAt] at hOpenRel
              rcases hOpenRel with ⟨continueScope, hContinue, hState⟩
              simp [hSourceOpen] at hSourceRun
              cases hSourceRun
              refine
                ⟨Outcome.cont targetOpenState, ?_,
                  ScopedOutcomeRelAt.cont (scope := sourceCtx.scope)
                    hContinue hState⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.cont,
                Structured.Outcome.cont]
          | leave =>
              simp [RunResultRelAt] at hOpenRel
          | halt _ =>
              simp [RunResultRelAt] at hOpenRel
      | leave =>
          cases targetMode with
          | regular =>
              simp [RunResultRelAt] at hOpenRel
          | brk =>
              simp [RunResultRelAt] at hOpenRel
          | cont =>
              simp [RunResultRelAt] at hOpenRel
          | leave =>
              simp [RunResultRelAt] at hOpenRel
              rcases hOpenRel with ⟨leaveScope, hLeave, hState⟩
              simp [hSourceOpen] at hSourceRun
              cases hSourceRun
              refine
                ⟨Outcome.leave targetOpenState, ?_,
                  ScopedOutcomeRelAt.leave (scope := sourceCtx.scope)
                    hLeave hState⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.leave,
                Structured.Outcome.leave]
          | halt _ =>
              simp [RunResultRelAt] at hOpenRel
      | halt sourceKind =>
          cases targetMode with
          | regular =>
              simp [RunResultRelAt] at hOpenRel
          | brk =>
              simp [RunResultRelAt] at hOpenRel
          | cont =>
              simp [RunResultRelAt] at hOpenRel
          | leave =>
              simp [RunResultRelAt] at hOpenRel
          | halt targetKind =>
              simp [RunResultRelAt] at hOpenRel
              rcases hOpenRel with ⟨hShared, hKind⟩
              subst hKind
              simp [hSourceOpen] at hSourceRun
              cases hSourceRun
              refine
                ⟨Outcome.halt sourceKind targetOpenState, ?_,
                  ScopedOutcomeRelAt.halt_shared hShared⟩
              simp [Direct.Block.runScoped, hTargetOpen, Outcome.halt,
                Structured.Outcome.halt]

theorem nil {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hRel : StateRel sourceCtx.scope source target) :
    BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      { stmts := [] } source target := by
  exact
    ⟨(Source.Outcome.regular source, sourceCtx),
      (Outcome.regular target, targetCtx),
      by simp [Source.Block.runOpen],
      by simp [Direct.Block.runOpen],
      RunResultRelAt.regular hRel hCtx hHandlers⟩

theorem cons_from_stmt_bridge {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {stmt : Stmt} {rest : List Stmt}
    (hHead :
      StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel stmt
        source target)
    (hTail :
      ∀ {sourceAfter : Source.State} {sourceCtxAfter : Source.Ctx}
        {targetAfter : RunState} {targetCtxAfter : Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
        Direct.Stmt.run program targetCtx fuel stmt target =
          .ok (Outcome.regular targetAfter, targetCtxAfter) →
        StateRel sourceCtxAfter.scope sourceAfter targetAfter →
        CtxRel sourceCtxAfter targetCtxAfter →
        CtxHandlersRel sourceCtxAfter targetCtxAfter →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtxAfter
            targetCtxAfter fuel { stmts := rest } sourceAfter targetAfter) :
    BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      { stmts := stmt :: rest } source target := by
  rcases hHead with
    ⟨sourceResult, targetResult, hSourceStmt, hTargetStmt, hResultRel⟩
  rcases sourceResult with ⟨sourceOutcome, sourceCtxAfter⟩
  rcases targetResult with ⟨targetOutcome, targetCtxAfter⟩
  rcases sourceOutcome with ⟨sourceAfter, sourceMode⟩
  rcases targetOutcome with ⟨targetAfter, targetMode⟩
  cases sourceMode with
  | regular =>
      cases targetMode with
      | regular =>
          simp [RunResultRelAt] at hResultRel
          rcases hResultRel with ⟨hState, hCtx, hHandlers⟩
          rcases
              hTail hSourceStmt hTargetStmt hState hCtx hHandlers with
            ⟨tailSourceResult, tailTargetResult, hSourceTail, hTargetTail,
              hTailRel⟩
          refine ⟨tailSourceResult, tailTargetResult, ?_, ?_, hTailRel⟩
          · simpa [Source.Block.runOpen, Source.Outcome.regular,
              hSourceStmt] using hSourceTail
          · simpa [Direct.Block.runOpen, Outcome.regular, hTargetStmt]
              using hTargetTail
      | brk => simp [RunResultRelAt] at hResultRel
      | cont => simp [RunResultRelAt] at hResultRel
      | leave => simp [RunResultRelAt] at hResultRel
      | halt _ => simp [RunResultRelAt] at hResultRel
  | brk =>
      cases targetMode with
      | regular => simp [RunResultRelAt] at hResultRel
      | brk =>
          simp [RunResultRelAt] at hResultRel
          rcases hResultRel with ⟨breakScope, hBreak, hState⟩
          refine
            ⟨(Source.Outcome.brk sourceAfter, sourceCtx),
              (Outcome.brk targetAfter, targetCtx), ?_, ?_,
              RunResultRelAt.brk hBreak hState⟩
          · simp [Source.Block.runOpen, Source.Outcome.brk, hSourceStmt]
          · simp [Direct.Block.runOpen, Outcome.brk,
              Structured.Outcome.brk, hTargetStmt]
      | cont => simp [RunResultRelAt] at hResultRel
      | leave => simp [RunResultRelAt] at hResultRel
      | halt _ => simp [RunResultRelAt] at hResultRel
  | cont =>
      cases targetMode with
      | regular => simp [RunResultRelAt] at hResultRel
      | brk => simp [RunResultRelAt] at hResultRel
      | cont =>
          simp [RunResultRelAt] at hResultRel
          rcases hResultRel with ⟨continueScope, hContinue, hState⟩
          refine
            ⟨(Source.Outcome.cont sourceAfter, sourceCtx),
              (Outcome.cont targetAfter, targetCtx), ?_, ?_,
              RunResultRelAt.cont hContinue hState⟩
          · simp [Source.Block.runOpen, Source.Outcome.cont, hSourceStmt]
          · simp [Direct.Block.runOpen, Outcome.cont,
              Structured.Outcome.cont, hTargetStmt]
      | leave => simp [RunResultRelAt] at hResultRel
      | halt _ => simp [RunResultRelAt] at hResultRel
  | leave =>
      cases targetMode with
      | regular => simp [RunResultRelAt] at hResultRel
      | brk => simp [RunResultRelAt] at hResultRel
      | cont => simp [RunResultRelAt] at hResultRel
      | leave =>
          simp [RunResultRelAt] at hResultRel
          rcases hResultRel with ⟨leaveScope, hLeave, hState⟩
          refine
            ⟨(Source.Outcome.leave sourceAfter, sourceCtx),
              (Outcome.leave targetAfter, targetCtx), ?_, ?_,
              RunResultRelAt.leave hLeave hState⟩
          · simp [Source.Block.runOpen, Source.Outcome.leave, hSourceStmt]
          · simp [Direct.Block.runOpen, Outcome.leave,
              Structured.Outcome.leave, hTargetStmt]
      | halt _ => simp [RunResultRelAt] at hResultRel
  | halt sourceKind =>
      cases targetMode with
      | regular => simp [RunResultRelAt] at hResultRel
      | brk => simp [RunResultRelAt] at hResultRel
      | cont => simp [RunResultRelAt] at hResultRel
      | leave => simp [RunResultRelAt] at hResultRel
      | halt targetKind =>
          simp [RunResultRelAt] at hResultRel
          rcases hResultRel with ⟨hShared, hKind⟩
          subst hKind
          refine
            ⟨(Source.Outcome.halt sourceKind sourceAfter, sourceCtx),
              (Outcome.halt sourceKind targetAfter, targetCtx), ?_, ?_,
              RunResultRelAt.halt_shared hShared⟩
          · simp [Source.Block.runOpen, Source.Outcome.halt, hSourceStmt]
          · simp [Direct.Block.runOpen, Outcome.halt,
              Structured.Outcome.halt, hTargetStmt]

theorem cons_from_stmt_source_run {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {stmt : Stmt} {rest : List Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hSourceBlock :
      Source.Block.runOpen prim program sourceCtx (fuel + 1)
          { stmts := stmt :: rest } source =
        .ok sourceResult)
    (hHead :
      ∀ {sourceHeadResult : Source.Outcome × Source.Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok sourceHeadResult →
        StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel stmt
          source target)
    (hTail :
      ∀ {sourceAfter : Source.State} {sourceCtxAfter : Source.Ctx}
        {targetAfter : RunState} {targetCtxAfter : Ctx}
        {tailSourceResult : Source.Outcome × Source.Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
        Direct.Stmt.run program targetCtx fuel stmt target =
          .ok (Outcome.regular targetAfter, targetCtxAfter) →
        StateRel sourceCtxAfter.scope sourceAfter targetAfter →
        CtxRel sourceCtxAfter targetCtxAfter →
        CtxHandlersRel sourceCtxAfter targetCtxAfter →
        Source.Block.runOpen prim program sourceCtxAfter fuel
            { stmts := rest } sourceAfter =
          .ok tailSourceResult →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtxAfter
            targetCtxAfter fuel { stmts := rest } sourceAfter targetAfter) :
    BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      { stmts := stmt :: rest } source target := by
  cases hSourceStmt :
      Source.Stmt.run prim program sourceCtx fuel stmt source with
  | error err =>
      simp [Source.Block.runOpen, hSourceStmt] at hSourceBlock
  | ok sourceHeadResult =>
      apply cons_from_stmt_bridge (hHead hSourceStmt)
      intro sourceAfter sourceCtxAfter targetAfter targetCtxAfter
        hSourceStmtRegular hTargetStmtRegular hState hCtx hHandlers
      have hTailSource :
          Source.Block.runOpen prim program sourceCtxAfter fuel
              { stmts := rest } sourceAfter =
            .ok sourceResult := by
        simpa [Source.Block.runOpen, hSourceStmtRegular] using hSourceBlock
      exact
        hTail hSourceStmtRegular hTargetStmtRegular hState hCtx hHandlers
          hTailSource

theorem cons_from_atomic_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {stmt : Stmt} {rest : List Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hSourceBlock :
      Source.Block.runOpen prim program sourceCtx (fuel + 1)
          { stmts := stmt :: rest } source =
        .ok sourceResult)
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAtomic : AtomicStmt.Holds stmt)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope stmt)
    (hAccessBound :
      AtomicStmt.AccessBound targetCtx.layout.length stmt)
    (hRel : StateRel sourceCtx.scope source target)
    (hTail :
      ∀ {sourceAfter : Source.State} {sourceCtxAfter : Source.Ctx}
        {targetAfter : RunState} {targetCtxAfter : Ctx}
        {tailSourceResult : Source.Outcome × Source.Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
        Direct.Stmt.run program targetCtx fuel stmt target =
          .ok (Outcome.regular targetAfter, targetCtxAfter) →
        StateRel sourceCtxAfter.scope sourceAfter targetAfter →
        CtxRel sourceCtxAfter targetCtxAfter →
        CtxHandlersRel sourceCtxAfter targetCtxAfter →
        Source.Block.runOpen prim program sourceCtxAfter fuel
            { stmts := rest } sourceAfter =
          .ok tailSourceResult →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtxAfter
            targetCtxAfter fuel { stmts := rest } sourceAfter targetAfter) :
    BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      { stmts := stmt :: rest } source target := by
  exact
    cons_from_stmt_source_run hSourceBlock
      (fun {sourceHeadResult} hSourceStmt =>
        StmtRunBridgeAt.atomic_from_scoped_source_run hPrim hEntryHandlers
          hCtx hHandlers hNoDup hAtomic hScoped hAccessBound hRel hSourceStmt)
      hTail

theorem cons_from_atomic_source_run_with_handlers
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {stmt : Stmt} {rest : List Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hSourceBlock :
      Source.Block.runOpen prim program sourceCtx (fuel + 1)
          { stmts := stmt :: rest } source =
        .ok sourceResult)
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAtomic : AtomicStmt.Holds stmt)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope stmt)
    (hAccessBound :
      AtomicStmt.AccessBound targetCtx.layout.length stmt)
    (hRel : StateRel sourceCtx.scope source target)
    (hTail :
      ∀ {sourceAfter : Source.State} {sourceCtxAfter : Source.Ctx}
        {targetAfter : RunState} {targetCtxAfter : Ctx}
        {tailSourceResult : Source.Outcome × Source.Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
        Direct.Stmt.run program targetCtx fuel stmt target =
          .ok (Outcome.regular targetAfter, targetCtxAfter) →
        StateRel sourceCtxAfter.scope sourceAfter targetAfter →
        CtxRel sourceCtxAfter targetCtxAfter →
        CtxHandlersRel sourceCtxAfter targetCtxAfter →
        HandlerScopesEq entryCtx sourceCtxAfter →
        Source.Block.runOpen prim program sourceCtxAfter fuel
            { stmts := rest } sourceAfter =
          .ok tailSourceResult →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtxAfter
            targetCtxAfter fuel { stmts := rest } sourceAfter targetAfter) :
    BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      { stmts := stmt :: rest } source target := by
  exact
    cons_from_atomic_source_run hPrim hSourceBlock hEntryHandlers hCtx
      hHandlers hNoDup hAtomic hScoped hAccessBound hRel
      (fun {sourceAfter} {sourceCtxAfter} {targetAfter} {targetCtxAfter}
          {tailSourceResult} hSourceStmtRegular hTargetStmtRegular hState
          hCtxAfter hHandlersAfter hTailSource =>
        let hLocalHandlers :
            HandlerScopesEq sourceCtx sourceCtxAfter :=
          StmtRunBridgeAt.atomic_regular_handlerScopesEq hAtomic
            hSourceStmtRegular
        let hEntryHandlersAfter :
            HandlerScopesEq entryCtx sourceCtxAfter :=
          HandlerScopesEq.trans hEntryHandlers hLocalHandlers
        hTail hSourceStmtRegular hTargetStmtRegular hState hCtxAfter
          hHandlersAfter hEntryHandlersAfter hTailSource)

theorem cons_from_atomic_source_run_with_handlers_source_bound
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState} {fuel : Nat}
    {stmt : Stmt} {rest : List Stmt}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hSourceBlock :
      Source.Block.runOpen prim program sourceCtx (fuel + 1)
          { stmts := stmt :: rest } source =
        .ok sourceResult)
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hAtomic : AtomicStmt.Holds stmt)
    (hScoped :
      EvmCompiler.Locals.Scope.Stmt.Scoped sourceCtx.scope stmt)
    (hAccessBound :
      AtomicStmt.SourceAccessBound sourceCtx.scope stmt)
    (hRel : StateRel sourceCtx.scope source target)
    (hTail :
      ∀ {sourceAfter : Source.State} {sourceCtxAfter : Source.Ctx}
        {targetAfter : RunState} {targetCtxAfter : Ctx}
        {tailSourceResult : Source.Outcome × Source.Ctx},
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok (Source.Outcome.regular sourceAfter, sourceCtxAfter) →
        Direct.Stmt.run program targetCtx fuel stmt target =
          .ok (Outcome.regular targetAfter, targetCtxAfter) →
        StateRel sourceCtxAfter.scope sourceAfter targetAfter →
        CtxRel sourceCtxAfter targetCtxAfter →
        CtxHandlersRel sourceCtxAfter targetCtxAfter →
        HandlerScopesEq entryCtx sourceCtxAfter →
        Source.Block.runOpen prim program sourceCtxAfter fuel
            { stmts := rest } sourceAfter =
          .ok tailSourceResult →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtxAfter
            targetCtxAfter fuel { stmts := rest } sourceAfter targetAfter) :
    BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      { stmts := stmt :: rest } source target := by
  exact
    cons_from_atomic_source_run_with_handlers hPrim hSourceBlock
      hEntryHandlers hCtx hHandlers hNoDup hAtomic hScoped
      (AtomicStmt.accessBound_of_sourceAccessBound hCtx hAccessBound)
      hRel hTail

end BlockOpenRunBridgeAt

namespace StmtRunBridgeAt

theorem block_from_open_bridge_source_run {prim : Source.PrimitiveSemantics}
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {body : Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hBody :
      BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel body
        source target)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.block body) source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel (.block body)
      source target := by
  cases hSourceScoped :
      Source.Block.runScoped prim program sourceCtx body fuel source with
  | error err =>
      simp [Source.Stmt.run, hSourceScoped] at hSourceRun
  | ok sourceOutcome =>
      rcases
          BlockOpenRunBridgeAt.runScoped_from_open_bridge
            hCtx hBody hSourceScoped with
        ⟨targetOutcome, hTargetScoped, hScopedRel⟩
      simp [Source.Stmt.run, hSourceScoped] at hSourceRun
      cases hSourceRun
      exact
        ⟨(sourceOutcome, sourceCtx), (targetOutcome, targetCtx),
          by simp [Source.Stmt.run, hSourceScoped],
          by simp [Direct.Stmt.run, hTargetScoped],
          ScopedOutcomeRelAt.toRunResultRelAt hScopedRel rfl hCtx
            hHandlers⟩

theorem if_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {cond : Expr 1} {body : Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hCondScoped : Scope.ExprScoped sourceCtx.scope cond)
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth cond ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hBody :
      ∀ {sourceAfterCond : Source.State} {targetAfterCond : RunState},
        Source.Expr.evalCondition prim cond source =
          .ok (sourceAfterCond, true) →
        Direct.Expr.runCondition targetCtx cond target =
          .ok (targetAfterCond, true) →
        StateRel sourceCtx.scope sourceAfterCond targetAfterCond →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
            body sourceAfterCond targetAfterCond)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx (fuel + 1) (.if_ cond body)
          source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      (.if_ cond body) source target := by
  cases hEvalOne : Source.Expr.evalOne prim cond source with
  | error err =>
      simp [Source.Stmt.run, Source.Expr.evalCondition, hEvalOne] at hSourceRun
  | ok condResult =>
      rcases condResult with ⟨sourceAfterCond, value⟩
      rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
      have hCtxRel : CtxRel sourceCtx targetCtx :=
        ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
      rcases
          Expr.evalCondition_bridge_sourceOwned hPrim
            (layout := sourceCtx.scope) (ctx := targetCtx)
            (source := source) (source' := sourceAfterCond)
            (value := value) (target := target)
            (by simp [hLayout]) hNoDup
            (Scope.expr_sourceOwned_of_scoped hCondScoped)
            (CtxRel.expr_accessible_of_scoped (offset := 0) hCtxRel
              hCondScoped (by simpa using hAccessBound))
            hRel hEvalOne with
        ⟨targetAfterCond, hSourceCond, hTargetCond, hCondRel⟩
      cases hTruth : value != EvmYul.UInt256.ofNat 0
      · have hSourceCondFalse :
            Source.Expr.evalCondition prim cond source =
              .ok (sourceAfterCond, false) := by
          simpa [hTruth] using hSourceCond
        have hTargetCondFalse :
            Direct.Expr.runCondition targetCtx cond target =
              .ok (targetAfterCond, false) := by
          simpa [hTruth] using hTargetCond
        simp [Source.Stmt.run, hSourceCondFalse] at hSourceRun
        cases hSourceRun
        exact
          ⟨(Source.Outcome.regular sourceAfterCond, sourceCtx),
            (Outcome.regular targetAfterCond, targetCtx),
            by simp [Source.Stmt.run, hSourceCondFalse],
            by simp [Direct.Stmt.run, hTargetCondFalse],
            RunResultRelAt.regular hCondRel hCtxRel hHandlers⟩
      · have hSourceCondTrue :
            Source.Expr.evalCondition prim cond source =
              .ok (sourceAfterCond, true) := by
          simpa [hTruth] using hSourceCond
        have hTargetCondTrue :
            Direct.Expr.runCondition targetCtx cond target =
              .ok (targetAfterCond, true) := by
          simpa [hTruth] using hTargetCond
        cases hSourceBody :
            Source.Block.runScoped prim program sourceCtx body fuel
              sourceAfterCond with
        | error err =>
            simp [Source.Stmt.run, hSourceCondTrue, hSourceBody] at hSourceRun
        | ok sourceOutcome =>
            have hBodyBridge :
                BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx
                  fuel body sourceAfterCond targetAfterCond :=
              hBody hSourceCondTrue hTargetCondTrue hCondRel
            rcases
                BlockOpenRunBridgeAt.runScoped_from_open_bridge hCtxRel
                  hBodyBridge hSourceBody with
              ⟨targetOutcome, hTargetBody, hScopedRel⟩
            simp [Source.Stmt.run, hSourceCondTrue, hSourceBody] at hSourceRun
            cases hSourceRun
            exact
              ⟨(sourceOutcome, sourceCtx), (targetOutcome, targetCtx),
                by simp [Source.Stmt.run, hSourceCondTrue, hSourceBody],
                by simp [Direct.Stmt.run, hTargetCondTrue, hTargetBody],
                ScopedOutcomeRelAt.toRunResultRelAt hScopedRel rfl hCtxRel
                  hHandlers⟩

theorem if_from_scoped_source_run_source_bound
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {cond : Expr 1} {body : Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hCondScoped : Scope.ExprScoped sourceCtx.scope cond)
    (hAccessBound : Access.ExprBound sourceCtx.scope 0 cond)
    (hRel : StateRel sourceCtx.scope source target)
    (hBody :
      ∀ {sourceAfterCond : Source.State} {targetAfterCond : RunState},
        Source.Expr.evalCondition prim cond source =
          .ok (sourceAfterCond, true) →
        Direct.Expr.runCondition targetCtx cond target =
          .ok (targetAfterCond, true) →
        StateRel sourceCtx.scope sourceAfterCond targetAfterCond →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
            body sourceAfterCond targetAfterCond)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx (fuel + 1) (.if_ cond body)
          source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      (.if_ cond body) source target := by
  apply if_from_scoped_source_run hPrim hCtx hHandlers hNoDup hCondScoped
  · rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
    simpa [Access.ExprBound, hLayout] using hAccessBound
  · exact hRel
  · exact hBody
  · exact hSourceRun

theorem switch_from_scoped_source_run {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {scrutinee : Expr 1}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScrutineeScoped : Scope.ExprScoped sourceCtx.scope scrutinee)
    (hAccessBound :
      targetCtx.layout.length + Access.exprWidth scrutinee ≤ 16)
    (hRel : StateRel sourceCtx.scope source target)
    (hSelected :
      ∀ {sourceAfterScrutinee : Source.State}
        {targetAfterScrutinee : RunState} {value : Word}
        {selected : Block},
        Source.Expr.evalOne prim scrutinee source =
          .ok (sourceAfterScrutinee, value) →
        Direct.Expr.runState targetCtx scrutinee target =
          .ok targetAfterScrutinee →
        ∀ {stackAfterPop : EvmYul.Stack Word},
        targetAfterScrutinee.evm.stack.pop =
          some (stackAfterPop, value) →
        Source.Switch.select value cases defaultBody = some selected →
        Direct.Switch.select value cases defaultBody = some selected →
        StateRel sourceCtx.scope sourceAfterScrutinee
          (targetAfterScrutinee.withEVM
            { targetAfterScrutinee.evm with stack := stackAfterPop }) →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
            selected sourceAfterScrutinee
            (targetAfterScrutinee.withEVM
              { targetAfterScrutinee.evm with stack := stackAfterPop }))
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx (fuel + 1)
          (.switch scrutinee cases defaultBody) source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      (.switch scrutinee cases defaultBody) source target := by
  cases hEvalOne : Source.Expr.evalOne prim scrutinee source with
  | error err =>
      simp [Source.Stmt.run, hEvalOne] at hSourceRun
  | ok scrutineeResult =>
      rcases scrutineeResult with ⟨sourceAfterScrutinee, value⟩
      rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
      have hCtxRel : CtxRel sourceCtx targetCtx :=
        ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
      rcases
          Expr.evalOne_pop_bridge_sourceOwned hPrim
            (layout := sourceCtx.scope) (ctx := targetCtx)
            (source := source) (source' := sourceAfterScrutinee)
            (value := value) (target := target)
            (by simp [hLayout]) hNoDup
            (Scope.expr_sourceOwned_of_scoped hScrutineeScoped)
            (CtxRel.expr_accessible_of_scoped (offset := 0) hCtxRel
              hScrutineeScoped (by simpa using hAccessBound))
            hRel hEvalOne with
        ⟨targetAfterScrutinee, targetAfterPop, stackAfterPop,
          hTargetScrutinee, hPop, hTargetAfterPop, hPopRel⟩
      cases hSelect : Source.Switch.select value cases defaultBody with
      | none =>
          have hDirectSelect :
              Direct.Switch.select value cases defaultBody = none := by
            rw [← Switch.source_select_eq]
            exact hSelect
          simp [Source.Stmt.run, hEvalOne, hSelect] at hSourceRun
          cases hSourceRun
          exact
            ⟨(Source.Outcome.regular sourceAfterScrutinee, sourceCtx),
              (Outcome.regular targetAfterPop, targetCtx),
              by simp [Source.Stmt.run, hEvalOne, hSelect],
              by
                subst targetAfterPop
                simp [Direct.Stmt.run, hTargetScrutinee, hPop, hDirectSelect],
              RunResultRelAt.regular hPopRel hCtxRel hHandlers⟩
      | some selected =>
          have hDirectSelect :
              Direct.Switch.select value cases defaultBody = some selected := by
            rw [← Switch.source_select_eq]
            exact hSelect
          cases hSourceBody :
              Source.Block.runScoped prim program sourceCtx selected fuel
                sourceAfterScrutinee with
          | error err =>
              simp [Source.Stmt.run, hEvalOne, hSelect, hSourceBody]
                at hSourceRun
          | ok sourceOutcome =>
              have hSelectedBridge :
                  BlockOpenRunBridgeAt prim program entryCtx sourceCtx
                    targetCtx fuel selected sourceAfterScrutinee
                    targetAfterPop := by
                subst targetAfterPop
                exact
                  hSelected hEvalOne hTargetScrutinee hPop hSelect
                    hDirectSelect hPopRel
              rcases
                  BlockOpenRunBridgeAt.runScoped_from_open_bridge hCtxRel
                    hSelectedBridge hSourceBody with
                ⟨targetOutcome, hTargetBody, hScopedRel⟩
              simp [Source.Stmt.run, hEvalOne, hSelect, hSourceBody]
                at hSourceRun
              cases hSourceRun
              exact
                ⟨(sourceOutcome, sourceCtx), (targetOutcome, targetCtx),
                  by simp [Source.Stmt.run, hEvalOne, hSelect, hSourceBody],
                  by
                    subst targetAfterPop
                    simp [Direct.Stmt.run, hTargetScrutinee, hPop,
                      hDirectSelect, hTargetBody],
                  ScopedOutcomeRelAt.toRunResultRelAt hScopedRel rfl hCtxRel
                    hHandlers⟩

theorem switch_from_scoped_source_run_source_bound
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
    {source : Source.State} {target : RunState}
    {fuel : Nat} {scrutinee : Expr 1}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hScrutineeScoped : Scope.ExprScoped sourceCtx.scope scrutinee)
    (hAccessBound : Access.ExprBound sourceCtx.scope 0 scrutinee)
    (hRel : StateRel sourceCtx.scope source target)
    (hSelected :
      ∀ {sourceAfterScrutinee : Source.State}
        {targetAfterScrutinee : RunState} {value : Word}
        {selected : Block},
        Source.Expr.evalOne prim scrutinee source =
          .ok (sourceAfterScrutinee, value) →
        Direct.Expr.runState targetCtx scrutinee target =
          .ok targetAfterScrutinee →
        ∀ {stackAfterPop : EvmYul.Stack Word},
        targetAfterScrutinee.evm.stack.pop =
          some (stackAfterPop, value) →
        Source.Switch.select value cases defaultBody = some selected →
        Direct.Switch.select value cases defaultBody = some selected →
        StateRel sourceCtx.scope sourceAfterScrutinee
          (targetAfterScrutinee.withEVM
            { targetAfterScrutinee.evm with stack := stackAfterPop }) →
          BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
            selected sourceAfterScrutinee
            (targetAfterScrutinee.withEVM
              { targetAfterScrutinee.evm with stack := stackAfterPop }))
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx (fuel + 1)
          (.switch scrutinee cases defaultBody) source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx (fuel + 1)
      (.switch scrutinee cases defaultBody) source target := by
  apply
    switch_from_scoped_source_run hPrim hCtx hHandlers hNoDup
      hScrutineeScoped
  · rcases hCtx with ⟨hLayout, _hBreak, _hContinue, _hLeave, _hRetc⟩
    simpa [Access.ExprBound, hLayout] using hAccessBound
  · exact hRel
  · exact hSelected
  · exact hSourceRun

end StmtRunBridgeAt

namespace Structural

theorem runForLoopBridgeAt_of_source_run_fixed_aux
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program}
    {entryCtx sourceLoopCtx : Source.Ctx}
    {targetLoopCtx : Ctx} {cond : Expr 1} {post body : Block}
    {maxFuel : Nat}
    (hPostBridge :
      ∀ {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
        {source : Source.State} {target : RunState} {fuel : Nat}
        {sourceResult : Source.Outcome × Source.Ctx},
        fuel < maxFuel →
        BlockLowerable sourceCtx.scope post →
        HandlerScopesEq entryCtx sourceCtx →
        CtxRel sourceCtx targetCtx →
        CtxHandlersRel sourceCtx targetCtx →
        sourceCtx.scope.Nodup →
        StateRel sourceCtx.scope source target →
        Source.Block.runOpen prim program sourceCtx fuel post source =
          .ok sourceResult →
        BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
          post source target)
    (hBodyBridge :
      ∀ {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
        {source : Source.State} {target : RunState} {fuel : Nat}
        {sourceResult : Source.Outcome × Source.Ctx},
        fuel < maxFuel →
        BlockLowerable sourceCtx.scope body →
        HandlerScopesEq entryCtx sourceCtx →
        CtxRel sourceCtx targetCtx →
        CtxHandlersRel sourceCtx targetCtx →
        sourceCtx.scope.Nodup →
        StateRel sourceCtx.scope source target →
        Source.Block.runOpen prim program sourceCtx fuel body source =
          .ok sourceResult →
        BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
          body source target)
    {fuel : Nat} {source sourceAfter : Source.State}
    {target : RunState} {sourceOutcome : Source.Outcome}
    (hLoopFuelLt : fuel < maxFuel)
    (hCondScoped : Scope.ExprScoped sourceLoopCtx.scope cond)
    (hCondAccess : Access.ExprBound sourceLoopCtx.scope 0 cond)
    (hPostLower : BlockLowerable sourceLoopCtx.scope post)
    (hBodyLower : BlockLowerable sourceLoopCtx.scope body)
    (hEntryLeave : entryCtx.leaveScope? = sourceLoopCtx.leaveScope?)
    (hCtx : CtxRel sourceLoopCtx targetLoopCtx)
    (hHandlers : CtxHandlersRel sourceLoopCtx targetLoopCtx)
    (hNoDup : sourceLoopCtx.scope.Nodup)
    (hRel : StateRel sourceLoopCtx.scope source target)
    (hSourceRun :
      Source.Stmt.runForLoop prim program sourceLoopCtx cond
          sourceLoopCtx.withoutLoopControl post
          (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
            sourceLoopCtx.scope)
          body fuel source =
        .ok sourceOutcome) :
    ∃ targetOutcome : Outcome,
      Direct.Stmt.runForLoop program targetLoopCtx cond
          targetLoopCtx.withoutLoopControl post
          (targetLoopCtx.withLoopControl targetLoopCtx.layout.length) body
          fuel target =
        .ok targetOutcome ∧
      ScopedOutcomeRelAt entryCtx sourceLoopCtx.scope sourceOutcome
        targetOutcome := by
  induction fuel generalizing source target sourceOutcome with
  | zero =>
      simp [Source.Stmt.runForLoop, Source.invalid, Structured.invalid]
        at hSourceRun
  | succ fuel ih =>
      have hFuelLtMax : fuel < maxFuel := by
        omega
      cases hEvalOne : Source.Expr.evalOne prim cond source with
      | error err =>
          simp [Source.Stmt.runForLoop, Source.Expr.evalCondition,
            hEvalOne] at hSourceRun
      | ok condResult =>
          rcases condResult with ⟨sourceAfterCond, value⟩
          rcases hCtx with ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
          have hCtxRel : CtxRel sourceLoopCtx targetLoopCtx :=
            ⟨hLayout, hBreak, hContinue, hLeave, hRetc⟩
          rcases
              Expr.evalCondition_bridge_sourceOwned hPrim
                (layout := sourceLoopCtx.scope) (ctx := targetLoopCtx)
                (source := source) (source' := sourceAfterCond)
                (value := value) (target := target)
                (by simp [hLayout]) hNoDup
                (Scope.expr_sourceOwned_of_scoped hCondScoped)
                (CtxRel.expr_accessible_of_scoped (offset := 0) hCtxRel
                  hCondScoped
                  (by simpa [Access.ExprBound, hLayout] using hCondAccess))
                hRel hEvalOne with
            ⟨targetAfterCond, hSourceCond, hTargetCond, hCondRel⟩
          cases hTruth : value != EvmYul.UInt256.ofNat 0
          · have hSourceCondFalse :
                Source.Expr.evalCondition prim cond source =
                  .ok (sourceAfterCond, false) := by
              simpa [hTruth] using hSourceCond
            have hTargetCondFalse :
                Direct.Expr.runCondition targetLoopCtx cond target =
                  .ok (targetAfterCond, false) := by
              simpa [hTruth] using hTargetCond
            simp [Source.Stmt.runForLoop, hSourceCondFalse] at hSourceRun
            cases hSourceRun
            exact
              ⟨Outcome.regular targetAfterCond,
                by simp [Direct.Stmt.runForLoop, hTargetCondFalse],
                ScopedOutcomeRelAt.regular
                  (StateRel.restrictTo_self hCondRel)⟩
          · have hSourceCondTrue :
                Source.Expr.evalCondition prim cond source =
                  .ok (sourceAfterCond, true) := by
              simpa [hTruth] using hSourceCond
            have hTargetCondTrue :
                Direct.Expr.runCondition targetLoopCtx cond target =
                  .ok (targetAfterCond, true) := by
              simpa [hTruth] using hTargetCond
            let sourceBodyCtx :=
              sourceLoopCtx.withLoopControl sourceLoopCtx.scope
                sourceLoopCtx.scope
            let targetBodyCtx :=
              targetLoopCtx.withLoopControl targetLoopCtx.layout.length
            have hBodyCtx : CtxRel sourceBodyCtx targetBodyCtx := by
              exact CtxRel.withLoopControl_self hCtxRel
            have hBodyHandlers :
                CtxHandlersRel sourceBodyCtx targetBodyCtx := by
              exact CtxHandlersRel.withLoopControl_self hCtxRel hHandlers
            have hBodyNoDup : sourceBodyCtx.scope.Nodup := by
              simpa [sourceBodyCtx, Source.Ctx.withLoopControl] using hNoDup
            cases hSourceBody :
                Source.Block.runScoped prim program sourceBodyCtx body fuel
                  sourceAfterCond with
            | error err =>
                simp [Source.Stmt.runForLoop, hSourceCondTrue, sourceBodyCtx,
                  hSourceBody] at hSourceRun
            | ok bodyOutcome =>
                have hSourceBodyScoped := hSourceBody
                unfold Source.Block.runScoped at hSourceBody
                cases hSourceBodyOpen :
                    Source.Block.runOpen prim program sourceBodyCtx fuel body
                      sourceAfterCond with
                | error err =>
                    simp [hSourceBodyOpen] at hSourceBody
                | ok bodyOpenResult =>
                    have hBodyLowerCtx :
                        BlockLowerable sourceBodyCtx.scope body := by
                      simpa [sourceBodyCtx, Source.Ctx.withLoopControl]
                        using hBodyLower
                    have hBodyBridge :
                        BlockOpenRunBridgeAt prim program sourceBodyCtx
                          sourceBodyCtx targetBodyCtx fuel body
                          sourceAfterCond targetAfterCond :=
                      hBodyBridge hFuelLtMax hBodyLowerCtx
                        (HandlerScopesEq.refl sourceBodyCtx) hBodyCtx
                        hBodyHandlers hBodyNoDup hCondRel hSourceBodyOpen
                    rcases
                        BlockOpenRunBridgeAt.runScoped_from_open_bridge
                          hBodyCtx hBodyBridge hSourceBodyScoped with
                      ⟨targetBodyOutcome, hTargetBody, hBodyRel⟩
                    rcases bodyOutcome with ⟨sourceBodyState, sourceBodyMode⟩
                    rcases targetBodyOutcome with
                      ⟨targetBodyState, targetBodyMode⟩
                    cases sourceBodyMode <;> cases targetBodyMode <;>
                      simp [ScopedOutcomeRelAt] at hBodyRel
                    · -- regular body; run post, then recurse or exit.
                      have hBodyStateRel :
                          StateRel sourceLoopCtx.scope sourceBodyState
                            targetBodyState := by
                        simpa [sourceBodyCtx, Source.Ctx.withLoopControl]
                          using hBodyRel
                      let sourcePostCtx := sourceLoopCtx.withoutLoopControl
                      let targetPostCtx := targetLoopCtx.withoutLoopControl
                      have hPostCtx : CtxRel sourcePostCtx targetPostCtx := by
                        exact CtxRel.withoutLoopControl hCtxRel
                      have hPostHandlers :
                          CtxHandlersRel sourcePostCtx targetPostCtx := by
                        exact CtxHandlersRel.withoutLoopControl hHandlers
                      have hPostNoDup : sourcePostCtx.scope.Nodup := by
                        simpa [sourcePostCtx, Source.Ctx.withoutLoopControl]
                          using hNoDup
                      cases hSourcePost :
                          Source.Block.runScoped prim program sourcePostCtx
                            post fuel sourceBodyState with
                      | error err =>
                          simp [Source.Stmt.runForLoop, hSourceCondTrue,
                            sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                            hSourcePost] at hSourceRun
                      | ok postOutcome =>
                          have hSourcePostScoped := hSourcePost
                          unfold Source.Block.runScoped at hSourcePost
                          cases hSourcePostOpen :
                              Source.Block.runOpen prim program sourcePostCtx
                                fuel post sourceBodyState with
                          | error err =>
                              simp [hSourcePostOpen] at hSourcePost
                          | ok postOpenResult =>
                              have hPostLowerCtx :
                                  BlockLowerable sourcePostCtx.scope post := by
                                simpa [sourcePostCtx,
                                  Source.Ctx.withoutLoopControl]
                                  using hPostLower
                              have hPostBridge :
                                  BlockOpenRunBridgeAt prim program
                                    sourcePostCtx sourcePostCtx targetPostCtx
                                    fuel post sourceBodyState
                                    targetBodyState :=
                                hPostBridge hFuelLtMax hPostLowerCtx
                                  (HandlerScopesEq.refl sourcePostCtx)
                                  hPostCtx hPostHandlers hPostNoDup
                                  hBodyStateRel hSourcePostOpen
                              rcases
                                  BlockOpenRunBridgeAt.runScoped_from_open_bridge
                                    hPostCtx hPostBridge hSourcePostScoped with
                                ⟨targetPostOutcome, hTargetPost, hPostRel⟩
                              rcases postOutcome with
                                ⟨sourcePostState, sourcePostMode⟩
                              rcases targetPostOutcome with
                                ⟨targetPostState, targetPostMode⟩
                              cases sourcePostMode <;> cases targetPostMode <;>
                                simp [ScopedOutcomeRelAt] at hPostRel
                              · simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx,
                                  hSourceBodyScoped, hSourcePostScoped]
                                  at hSourceRun
                                rcases
                                  ih hFuelLtMax hPostRel hSourceRun with
                                ⟨targetLoopOutcome, hTargetLoop,
                                  hLoopRel⟩
                                exact
                                  ⟨targetLoopOutcome,
                                    by
                                      simp [Direct.Stmt.runForLoop,
                                        targetBodyCtx, targetPostCtx,
                                        hTargetCondTrue, hTargetBody,
                                        hTargetPost, hTargetLoop],
                                    hLoopRel⟩
                              · simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                                  hSourcePostScoped, Source.invalid,
                                  Structured.invalid] at hSourceRun
                              · simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                                  hSourcePostScoped, Source.invalid,
                                  Structured.invalid] at hSourceRun
                              · rcases hPostRel with
                                  ⟨leaveScope, hPostLeave, hState⟩
                                have hEntryLeaveSome :
                                    entryCtx.leaveScope? =
                                      some leaveScope := by
                                  rw [hEntryLeave]
                                  simpa [sourcePostCtx,
                                    Source.Ctx.withoutLoopControl]
                                    using hPostLeave
                                simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                                  hSourcePostScoped] at hSourceRun
                                cases hSourceRun
                                exact
                                  ⟨Outcome.leave targetPostState,
                                    by
                                      simp [Direct.Stmt.runForLoop,
                                        targetBodyCtx, targetPostCtx,
                                        hTargetCondTrue, hTargetBody,
                                        hTargetPost, Structured.Outcome.leave],
                                    ScopedOutcomeRelAt.leave hEntryLeaveSome
                                      hState⟩
                              · rename_i sourceKind targetKind
                                rcases hPostRel with ⟨hShared, hKind⟩
                                simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                                  hSourcePostScoped] at hSourceRun
                                cases hSourceRun
                                exact
                                  ⟨Outcome.halt targetKind targetPostState,
                                    by
                                      simp [Direct.Stmt.runForLoop,
                                        targetBodyCtx, targetPostCtx,
                                        hTargetCondTrue, hTargetBody,
                                        hTargetPost, Structured.Outcome.halt],
                                    by
                                      simpa [ScopedOutcomeRelAt] using
                                        ⟨hShared, hKind⟩⟩
                    · -- body break exits the loop regularly.
                      rcases hBodyRel with ⟨breakScope, hBreakBody, hState⟩
                      have hBreakScope : breakScope = sourceLoopCtx.scope := by
                        simpa [sourceBodyCtx, Source.Ctx.withLoopControl]
                          using hBreakBody.symm
                      subst breakScope
                      simp [Source.Stmt.runForLoop, hSourceCondTrue,
                        sourceBodyCtx, hSourceBodyScoped] at hSourceRun
                      cases hSourceRun
                      exact
                        ⟨Outcome.regular targetBodyState,
                          by
                            simp [Direct.Stmt.runForLoop, targetBodyCtx,
                              hTargetCondTrue,
                              hTargetBody],
                          ScopedOutcomeRelAt.regular hState⟩
                    · -- body continue runs post, then recurses or exits.
                      rcases hBodyRel with
                        ⟨continueScope, hContinueBody, hState⟩
                      have hContinueScope :
                          continueScope = sourceLoopCtx.scope := by
                        simpa [sourceBodyCtx, Source.Ctx.withLoopControl]
                          using hContinueBody.symm
                      subst continueScope
                      let sourcePostCtx := sourceLoopCtx.withoutLoopControl
                      let targetPostCtx := targetLoopCtx.withoutLoopControl
                      have hPostCtx : CtxRel sourcePostCtx targetPostCtx := by
                        exact CtxRel.withoutLoopControl hCtxRel
                      have hPostHandlers :
                          CtxHandlersRel sourcePostCtx targetPostCtx := by
                        exact CtxHandlersRel.withoutLoopControl hHandlers
                      have hPostNoDup : sourcePostCtx.scope.Nodup := by
                        simpa [sourcePostCtx, Source.Ctx.withoutLoopControl]
                          using hNoDup
                      cases hSourcePost :
                          Source.Block.runScoped prim program sourcePostCtx
                            post fuel sourceBodyState with
                      | error err =>
                          simp [Source.Stmt.runForLoop, hSourceCondTrue,
                            sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                            hSourcePost] at hSourceRun
                      | ok postOutcome =>
                          have hSourcePostScoped := hSourcePost
                          unfold Source.Block.runScoped at hSourcePost
                          cases hSourcePostOpen :
                              Source.Block.runOpen prim program sourcePostCtx
                                fuel post sourceBodyState with
                          | error err =>
                              simp [hSourcePostOpen] at hSourcePost
                          | ok postOpenResult =>
                              have hPostLowerCtx :
                                  BlockLowerable sourcePostCtx.scope post := by
                                simpa [sourcePostCtx,
                                  Source.Ctx.withoutLoopControl]
                                  using hPostLower
                              have hPostBridge :
                                  BlockOpenRunBridgeAt prim program
                                    sourcePostCtx sourcePostCtx targetPostCtx
                                    fuel post sourceBodyState
                                    targetBodyState :=
                                hPostBridge hFuelLtMax hPostLowerCtx
                                  (HandlerScopesEq.refl sourcePostCtx)
                                  hPostCtx hPostHandlers hPostNoDup hState
                                  hSourcePostOpen
                              rcases
                                  BlockOpenRunBridgeAt.runScoped_from_open_bridge
                                    hPostCtx hPostBridge hSourcePostScoped with
                                ⟨targetPostOutcome, hTargetPost, hPostRel⟩
                              rcases postOutcome with
                                ⟨sourcePostState, sourcePostMode⟩
                              rcases targetPostOutcome with
                                ⟨targetPostState, targetPostMode⟩
                              cases sourcePostMode <;> cases targetPostMode <;>
                                simp [ScopedOutcomeRelAt] at hPostRel
                              · simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx,
                                  hSourceBodyScoped, hSourcePostScoped]
                                  at hSourceRun
                                rcases
                                  ih hFuelLtMax hPostRel hSourceRun with
                                ⟨targetLoopOutcome, hTargetLoop,
                                  hLoopRel⟩
                                exact
                                  ⟨targetLoopOutcome,
                                    by
                                      simp [Direct.Stmt.runForLoop,
                                        targetBodyCtx, targetPostCtx,
                                        hTargetCondTrue, hTargetBody,
                                        hTargetPost, hTargetLoop],
                                    hLoopRel⟩
                              · simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                                  hSourcePostScoped, Source.invalid,
                                  Structured.invalid] at hSourceRun
                              · simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                                  hSourcePostScoped, Source.invalid,
                                  Structured.invalid] at hSourceRun
                              · rcases hPostRel with
                                  ⟨leaveScope, hPostLeave, hStatePost⟩
                                have hEntryLeaveSome :
                                    entryCtx.leaveScope? =
                                      some leaveScope := by
                                  rw [hEntryLeave]
                                  simpa [sourcePostCtx,
                                    Source.Ctx.withoutLoopControl]
                                    using hPostLeave
                                simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                                  hSourcePostScoped] at hSourceRun
                                cases hSourceRun
                                exact
                                  ⟨Outcome.leave targetPostState,
                                    by
                                      simp [Direct.Stmt.runForLoop,
                                        targetBodyCtx, targetPostCtx,
                                        hTargetCondTrue, hTargetBody,
                                        hTargetPost, Structured.Outcome.leave],
                                    ScopedOutcomeRelAt.leave hEntryLeaveSome
                                      hStatePost⟩
                              · rename_i sourceKind targetKind
                                rcases hPostRel with ⟨hShared, hKind⟩
                                simp [Source.Stmt.runForLoop, hSourceCondTrue,
                                  sourceBodyCtx, sourcePostCtx, hSourceBodyScoped,
                                  hSourcePostScoped] at hSourceRun
                                cases hSourceRun
                                exact
                                  ⟨Outcome.halt targetKind targetPostState,
                                    by
                                      simp [Direct.Stmt.runForLoop,
                                        targetBodyCtx, targetPostCtx,
                                        hTargetCondTrue, hTargetBody,
                                        hTargetPost, Structured.Outcome.halt],
                                    by
                                      simpa [ScopedOutcomeRelAt] using
                                        ⟨hShared, hKind⟩⟩
                    · -- body leave exits the loop.
                      rcases hBodyRel with
                        ⟨leaveScope, hBodyLeave, hState⟩
                      have hEntryLeaveSome :
                          entryCtx.leaveScope? = some leaveScope := by
                        rw [hEntryLeave]
                        simpa [sourceBodyCtx, Source.Ctx.withLoopControl]
                          using hBodyLeave
                      simp [Source.Stmt.runForLoop, hSourceCondTrue,
                        sourceBodyCtx, hSourceBodyScoped] at hSourceRun
                      cases hSourceRun
                      exact
                        ⟨Outcome.leave targetBodyState,
                          by
                            simp [Direct.Stmt.runForLoop, targetBodyCtx,
                              hTargetCondTrue,
                              hTargetBody, Structured.Outcome.leave],
                          ScopedOutcomeRelAt.leave hEntryLeaveSome hState⟩
                    · -- body halt exits the loop.
                      rename_i sourceKind targetKind
                      rcases hBodyRel with ⟨hShared, hKind⟩
                      simp [Source.Stmt.runForLoop, hSourceCondTrue,
                        sourceBodyCtx, hSourceBodyScoped] at hSourceRun
                      cases hSourceRun
                      exact
                        ⟨Outcome.halt targetKind targetBodyState,
                          by
                            simp [Direct.Stmt.runForLoop, targetBodyCtx,
                              hTargetCondTrue,
                              hTargetBody, Structured.Outcome.halt],
                          by
                            simpa [ScopedOutcomeRelAt] using
                              ⟨hShared, hKind⟩⟩

theorem runForLoopBridgeAt_of_source_run_aux
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program}
    (hBlockBridge :
      ∀ {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
        {source : Source.State} {target : RunState} {fuel : Nat}
        {block : Block} {sourceResult : Source.Outcome × Source.Ctx},
        BlockLowerable sourceCtx.scope block →
        HandlerScopesEq entryCtx sourceCtx →
        CtxRel sourceCtx targetCtx →
        CtxHandlersRel sourceCtx targetCtx →
        sourceCtx.scope.Nodup →
        StateRel sourceCtx.scope source target →
        Source.Block.runOpen prim program sourceCtx fuel block source =
          .ok sourceResult →
        BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
          block source target)
    {entryCtx sourceLoopCtx : Source.Ctx}
    {targetLoopCtx : Ctx} {cond : Expr 1} {post body : Block}
    {fuel : Nat} {source sourceAfter : Source.State}
    {target : RunState} {sourceOutcome : Source.Outcome}
    (hCondScoped : Scope.ExprScoped sourceLoopCtx.scope cond)
    (hCondAccess : Access.ExprBound sourceLoopCtx.scope 0 cond)
    (hPostLower : BlockLowerable sourceLoopCtx.scope post)
    (hBodyLower : BlockLowerable sourceLoopCtx.scope body)
    (hEntryLeave : entryCtx.leaveScope? = sourceLoopCtx.leaveScope?)
    (hCtx : CtxRel sourceLoopCtx targetLoopCtx)
    (hHandlers : CtxHandlersRel sourceLoopCtx targetLoopCtx)
    (hNoDup : sourceLoopCtx.scope.Nodup)
    (hRel : StateRel sourceLoopCtx.scope source target)
    (hSourceRun :
      Source.Stmt.runForLoop prim program sourceLoopCtx cond
          sourceLoopCtx.withoutLoopControl post
          (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
            sourceLoopCtx.scope)
          body fuel source =
        .ok sourceOutcome) :
    ∃ targetOutcome : Outcome,
      Direct.Stmt.runForLoop program targetLoopCtx cond
          targetLoopCtx.withoutLoopControl post
          (targetLoopCtx.withLoopControl targetLoopCtx.layout.length) body
          fuel target =
        .ok targetOutcome ∧
      ScopedOutcomeRelAt entryCtx sourceLoopCtx.scope sourceOutcome
        targetOutcome := by
  exact
    runForLoopBridgeAt_of_source_run_fixed_aux
      (maxFuel := fuel + 1) (sourceAfter := sourceAfter)
      hPrim
      (fun _hFuelLt hLower hEntryHandlers hCtx hHandlers hNoDup hRel hSourceRun =>
        hBlockBridge hLower hEntryHandlers hCtx hHandlers hNoDup hRel
          hSourceRun)
      (fun _hFuelLt hLower hEntryHandlers hCtx hHandlers hNoDup hRel hSourceRun =>
        hBlockBridge hLower hEntryHandlers hCtx hHandlers hNoDup hRel
          hSourceRun)
      (Nat.lt_succ_self fuel)
      hCondScoped hCondAccess hPostLower hBodyLower hEntryLeave hCtx
      hHandlers hNoDup hRel hSourceRun

theorem forStmtRunBridgeAt_of_source_run_fixed_aux
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx}
    {targetCtx : Ctx} {source : Source.State} {target : RunState}
    {stmtFuel : Nat}
    {fuel : Nat} {init : Block} {cond : Expr 1} {post body : Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hInitBridge :
      ∀ {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
        {source : Source.State} {target : RunState} {fuel : Nat}
        {sourceResult : Source.Outcome × Source.Ctx},
        fuel < stmtFuel →
        BlockLowerable sourceCtx.scope init →
        HandlerScopesEq entryCtx sourceCtx →
        CtxRel sourceCtx targetCtx →
        CtxHandlersRel sourceCtx targetCtx →
        sourceCtx.scope.Nodup →
        StateRel sourceCtx.scope source target →
        Source.Block.runOpen prim program sourceCtx fuel init source =
          .ok sourceResult →
        BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
          init source target)
    (hPostBridge :
      ∀ {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
        {source : Source.State} {target : RunState} {fuel : Nat}
        {sourceResult : Source.Outcome × Source.Ctx},
        fuel < stmtFuel →
        BlockLowerable sourceCtx.scope post →
        HandlerScopesEq entryCtx sourceCtx →
        CtxRel sourceCtx targetCtx →
        CtxHandlersRel sourceCtx targetCtx →
        sourceCtx.scope.Nodup →
        StateRel sourceCtx.scope source target →
        Source.Block.runOpen prim program sourceCtx fuel post source =
          .ok sourceResult →
        BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
          post source target)
    (hBodyBridge :
      ∀ {entryCtx sourceCtx : Source.Ctx} {targetCtx : Ctx}
        {source : Source.State} {target : RunState} {fuel : Nat}
        {sourceResult : Source.Outcome × Source.Ctx},
        fuel < stmtFuel →
        BlockLowerable sourceCtx.scope body →
        HandlerScopesEq entryCtx sourceCtx →
        CtxRel sourceCtx targetCtx →
        CtxHandlersRel sourceCtx targetCtx →
        sourceCtx.scope.Nodup →
        StateRel sourceCtx.scope source target →
        Source.Block.runOpen prim program sourceCtx fuel body source =
          .ok sourceResult →
        BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
          body source target)
    (hStmtFuelEq : stmtFuel = fuel)
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hRel : StateRel sourceCtx.scope source target)
    (hInitLower : BlockLowerable sourceCtx.scope init)
    (hCondScoped :
      Scope.ExprScoped (Scope.Block.outEnv sourceCtx.scope init) cond)
    (hCondAccess :
      Access.ExprBound (Scope.Block.outEnv sourceCtx.scope init) 0 cond)
    (hPostLower : BlockLowerable (Scope.Block.outEnv sourceCtx.scope init) post)
    (hBodyLower : BlockLowerable (Scope.Block.outEnv sourceCtx.scope init) body)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.for_ init cond post body)
          source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.for_ init cond post body) source target := by
  cases fuel with
  | zero =>
      simp [Source.Stmt.run, Source.invalid, Structured.invalid] at hSourceRun
  | succ fuel =>
      have hSubFuelLt : fuel < stmtFuel := by
        rw [hStmtFuelEq]
        exact Nat.lt_succ_self fuel
      let sourceInitCtx := sourceCtx.withoutLoopControl
      let targetInitCtx := targetCtx.withoutLoopControl
      have hInitCtx : CtxRel sourceInitCtx targetInitCtx := by
        exact CtxRel.withoutLoopControl hCtx
      have hInitHandlers :
          CtxHandlersRel sourceInitCtx targetInitCtx := by
        exact CtxHandlersRel.withoutLoopControl hHandlers
      have hInitNoDup : sourceInitCtx.scope.Nodup := by
        simpa [sourceInitCtx, Source.Ctx.withoutLoopControl] using hNoDup
      cases hSourceInit :
          Source.Block.runOpen prim program sourceInitCtx fuel init source with
      | error err =>
          simp [Source.Stmt.run, sourceInitCtx, hSourceInit] at hSourceRun
      | ok sourceInitResult =>
          have hInitBridgeResult :
              BlockOpenRunBridgeAt prim program sourceInitCtx sourceInitCtx
                targetInitCtx fuel init source target :=
            hInitBridge hSubFuelLt hInitLower
              (HandlerScopesEq.refl sourceInitCtx) hInitCtx hInitHandlers
              hInitNoDup hRel hSourceInit
          rcases
              BlockOpenRunBridgeAt.target_result_of_source hInitBridgeResult
                hSourceInit with
            ⟨targetInitResult, hTargetInit, hInitRel⟩
          rcases sourceInitResult with ⟨sourceInitOutcome, sourceLoopCtx⟩
          rcases targetInitResult with ⟨targetInitOutcome, targetLoopCtx⟩
          rcases sourceInitOutcome with ⟨sourceInitState, sourceInitMode⟩
          rcases targetInitOutcome with ⟨targetInitState, targetInitMode⟩
          cases sourceInitMode <;> cases targetInitMode <;>
            simp [RunResultRelAt] at hInitRel
          · rcases hInitRel with ⟨hInitStateRel, hLoopCtx, hLoopHandlers⟩
            have hSourceInitRegular :
                Source.Block.runOpen prim program sourceInitCtx fuel init
                    source =
                  .ok (Source.Outcome.regular sourceInitState,
                    sourceLoopCtx) := by
              simpa [Source.Outcome.regular] using hSourceInit
            have hInitScopeBase :
                sourceLoopCtx.scope =
                  Scope.Block.outEnv sourceInitCtx.scope init :=
              Source.Block.runOpen_regular_scope hSourceInitRegular
            have hInitScope :
                sourceLoopCtx.scope =
                  Scope.Block.outEnv sourceCtx.scope init := by
              simpa [sourceInitCtx, Source.Ctx.withoutLoopControl]
                using hInitScopeBase
            have hLoopNoDup : sourceLoopCtx.scope.Nodup := by
              rw [hInitScope]
              exact
                Block.scoped_outEnv_nodup hNoDup
                  (blockLowerable_scoped hInitLower)
            have hCondScopedLoop :
                Scope.ExprScoped sourceLoopCtx.scope cond := by
              rw [hInitScope]
              exact hCondScoped
            have hCondAccessLoop :
                Access.ExprBound sourceLoopCtx.scope 0 cond := by
              rw [hInitScope]
              exact hCondAccess
            have hPostLowerLoop :
                BlockLowerable sourceLoopCtx.scope post := by
              rw [hInitScope]
              exact hPostLower
            have hBodyLowerLoop :
                BlockLowerable sourceLoopCtx.scope body := by
              rw [hInitScope]
              exact hBodyLower
            have hInitHandlerScopes :
                HandlerScopesEq sourceInitCtx sourceLoopCtx :=
              blockLowerable_regular_handlerScopesEq hInitLower
                hSourceInitRegular
            have hEntryLeave :
                entryCtx.leaveScope? = sourceLoopCtx.leaveScope? := by
              rcases hEntryHandlers with
                ⟨_hEntryBreak, _hEntryContinue, hEntryLeaveSource⟩
              rcases hInitHandlerScopes with
                ⟨_hInitBreak, _hInitContinue, hInitLeave⟩
              calc
                entryCtx.leaveScope? = sourceCtx.leaveScope? :=
                  hEntryLeaveSource
                _ = sourceInitCtx.leaveScope? := by
                  simp [sourceInitCtx, Source.Ctx.withoutLoopControl]
                _ = sourceLoopCtx.leaveScope? := hInitLeave
            cases hSourceLoop :
                Source.Stmt.runForLoop prim program sourceLoopCtx cond
                  sourceLoopCtx.withoutLoopControl post
                  (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
                    sourceLoopCtx.scope)
                  body fuel sourceInitState with
            | error err =>
                simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                  hSourceLoop] at hSourceRun
            | ok sourceLoopOutcome =>
                rcases
                    runForLoopBridgeAt_of_source_run_fixed_aux
                      (post := post) (body := body) (maxFuel := stmtFuel)
                      (sourceAfter := sourceInitState) hPrim hPostBridge
                      hBodyBridge hSubFuelLt hCondScopedLoop hCondAccessLoop
                      hPostLowerLoop hBodyLowerLoop hEntryLeave hLoopCtx
                      hLoopHandlers hLoopNoDup hInitStateRel hSourceLoop with
                  ⟨targetLoopOutcome, hTargetLoop, hLoopRel⟩
                rcases sourceLoopOutcome with
                  ⟨sourceLoopState, sourceLoopMode⟩
                rcases targetLoopOutcome with
                  ⟨targetLoopState, targetLoopMode⟩
                cases sourceLoopMode <;> cases targetLoopMode <;>
                  simp [ScopedOutcomeRelAt] at hLoopRel
                · rcases hLoopCtx with
                    ⟨hLoopLayout, _hBreakDepth, _hContinueDepth,
                      _hLeaveDepth, _hRetc⟩
                  have hCleanupScope :
                      CleanupScopeRel targetLoopCtx.layout sourceCtx.scope := by
                    rw [hLoopLayout, hInitScope]
                    exact
                      Scope.block_outEnv_cleanupScopeRel sourceCtx.scope init
                  have hLoopRelTarget :
                      StateRel targetLoopCtx.layout sourceLoopState
                        targetLoopState := by
                    simpa [hLoopLayout] using hLoopRel
                  rcases
                      StateRel.cleanupTo_scope_exists (ctx := targetLoopCtx)
                        hCleanupScope hLoopRelTarget with
                    ⟨targetCleaned, hCleanup, hCleanRel, _hReturns⟩
                  simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop] at hSourceRun
                  cases hSourceRun
                  refine
                    ⟨(Source.Outcome.regular
                        (sourceLoopState.restrictTo sourceCtx.scope),
                        sourceCtx),
                      (Outcome.regular targetCleaned, targetCtx),
                      ?_, ?_,
                      RunResultRelAt.regular hCleanRel hCtx hHandlers⟩
                  · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                      hSourceLoop]
                  · rcases hCtx with
                      ⟨hTargetLayout, _hBreakDepth, _hContinueDepth,
                        _hLeaveDepth, _hRetc⟩
                    simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                      hTargetLoop, hCleanup, hTargetLayout]
                · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop, Source.invalid, Structured.invalid]
                    at hSourceRun
                · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop, Source.invalid, Structured.invalid]
                    at hSourceRun
                · rcases hLoopRel with ⟨leaveScope, hLeave, hLeaveState⟩
                  simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop] at hSourceRun
                  cases hSourceRun
                  exact
                    ⟨(Source.Outcome.leave sourceLoopState, sourceCtx),
                      (Outcome.leave targetLoopState, targetCtx),
                      by
                        show
                          Source.Stmt.run prim program sourceCtx (fuel + 1)
                              (Stmt.for_ init cond post body) source =
                            .ok (Source.Outcome.leave sourceLoopState,
                              sourceCtx)
                        simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                          hSourceLoop, Source.Outcome.leave],
                      by simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                        hTargetLoop, Structured.Outcome.leave],
                      RunResultRelAt.leave hLeave hLeaveState⟩
                · rename_i sourceKind targetKind
                  rcases hLoopRel with ⟨hShared, hKind⟩
                  subst hKind
                  simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop] at hSourceRun
                  cases hSourceRun
                  exact
                    ⟨(Source.Outcome.halt sourceKind sourceLoopState,
                        sourceCtx),
                      (Outcome.halt sourceKind targetLoopState, targetCtx),
                      by
                        show
                          Source.Stmt.run prim program sourceCtx (fuel + 1)
                              (Stmt.for_ init cond post body) source =
                            .ok (Source.Outcome.halt sourceKind
                              sourceLoopState, sourceCtx)
                        simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                          hSourceLoop, Source.Outcome.halt],
                      by simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                        hTargetLoop, Structured.Outcome.halt],
                      RunResultRelAt.halt_shared hShared⟩
          · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
              Source.invalid, Structured.invalid] at hSourceRun
          · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
              Source.invalid, Structured.invalid] at hSourceRun
          · rcases hInitRel with ⟨leaveScope, hInitLeave, hLeaveState⟩
            have hEntryLeaveSome : entryCtx.leaveScope? = some leaveScope := by
              rcases hEntryHandlers with
                ⟨_hBreak, _hContinue, hEntryLeaveSource⟩
              rw [hEntryLeaveSource]
              simpa [sourceInitCtx, Source.Ctx.withoutLoopControl]
                using hInitLeave
            simp [Source.Stmt.run, sourceInitCtx, hSourceInit] at hSourceRun
            cases hSourceRun
            exact
              ⟨(Source.Outcome.leave sourceInitState, sourceCtx),
                (Outcome.leave targetInitState, targetCtx),
                by simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                  Source.Outcome.leave],
                by simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                  Structured.Outcome.leave],
                RunResultRelAt.leave hEntryLeaveSome hLeaveState⟩
          · rename_i sourceKind targetKind
            rcases hInitRel with ⟨hShared, hKind⟩
            subst hKind
            simp [Source.Stmt.run, sourceInitCtx, hSourceInit] at hSourceRun
            cases hSourceRun
            exact
              ⟨(Source.Outcome.halt sourceKind sourceInitState, sourceCtx),
                (Outcome.halt sourceKind targetInitState, targetCtx),
                by simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                  Source.Outcome.halt],
                by simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                  Structured.Outcome.halt],
                RunResultRelAt.halt_shared hShared⟩

mutual
  theorem blockOpenRunBridgeAt_of_source_run
      {prim : Source.PrimitiveSemantics}
      (hPrim : PrimitiveSound prim)
      {program : Program} {entryCtx sourceCtx : Source.Ctx}
      {targetCtx : Ctx} {source : Source.State} {target : RunState}
      {fuel : Nat} {block : Block}
      {sourceResult : Source.Outcome × Source.Ctx}
      (hLower : BlockLowerable sourceCtx.scope block)
      (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
      (hCtx : CtxRel sourceCtx targetCtx)
      (hHandlers : CtxHandlersRel sourceCtx targetCtx)
      (hNoDup : sourceCtx.scope.Nodup)
      (hRel : StateRel sourceCtx.scope source target)
      (hSourceRun :
        Source.Block.runOpen prim program sourceCtx fuel block source =
          .ok sourceResult) :
      BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel block
        source target := by
    cases block with
    | mk stmts =>
        exact
          stmtListOpenRunBridgeAt_of_source_run hPrim hLower hEntryHandlers
            hCtx hHandlers hNoDup hRel hSourceRun
  termination_by (fuel, 2, BlockMeasure block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | omega

  theorem stmtListOpenRunBridgeAt_of_source_run
      {prim : Source.PrimitiveSemantics}
      (hPrim : PrimitiveSound prim)
      {program : Program} {entryCtx sourceCtx : Source.Ctx}
      {targetCtx : Ctx} {source : Source.State} {target : RunState}
      {fuel : Nat} {stmts : List Stmt}
      {sourceResult : Source.Outcome × Source.Ctx}
      (hLower : StmtListLowerable sourceCtx.scope stmts)
      (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
      (hCtx : CtxRel sourceCtx targetCtx)
      (hHandlers : CtxHandlersRel sourceCtx targetCtx)
      (hNoDup : sourceCtx.scope.Nodup)
      (hRel : StateRel sourceCtx.scope source target)
      (hSourceRun :
        Source.Block.runOpen prim program sourceCtx fuel { stmts := stmts }
            source =
          .ok sourceResult) :
      BlockOpenRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
        { stmts := stmts } source target := by
    cases fuel with
    | zero =>
        simp [Source.Block.runOpen, Source.invalid, Structured.invalid]
          at hSourceRun
    | succ fuel =>
        cases stmts with
        | nil =>
            exact BlockOpenRunBridgeAt.nil hCtx hHandlers hRel
        | cons stmt rest =>
            rcases hLower with ⟨hStmtLower, hRestLower⟩
            exact
              BlockOpenRunBridgeAt.cons_from_stmt_source_run hSourceRun
                (fun {sourceHeadResult} hSourceStmt =>
                  stmtRunBridgeAt_of_source_run hPrim hStmtLower
                    hEntryHandlers hCtx hHandlers hNoDup hRel hSourceStmt)
                (fun {sourceAfter} {sourceCtxAfter} {targetAfter}
                    {targetCtxAfter} {tailSourceResult}
                    hSourceStmtRegular hTargetStmtRegular hState hCtxAfter
                    hHandlersAfter hTailSource => by
                  have hScopeAfter :
                      sourceCtxAfter.scope =
                        Scope.Stmt.outEnv sourceCtx.scope stmt :=
                    Source.Stmt.run_regular_scope hSourceStmtRegular
                  have hRestLowerAfter :
                      StmtListLowerable sourceCtxAfter.scope rest := by
                    rw [hScopeAfter]
                    exact hRestLower
                  have hNoDupAfter : sourceCtxAfter.scope.Nodup := by
                    rw [hScopeAfter]
                    exact
                      Stmt.scoped_outEnv_nodup hNoDup
                        (stmtLowerable_scoped hStmtLower)
                  have hEntryHandlersAfter :
                      HandlerScopesEq entryCtx sourceCtxAfter :=
                    HandlerScopesEq.trans hEntryHandlers
                      (stmtLowerable_regular_handlerScopesEq hStmtLower
                        hSourceStmtRegular)
                  exact
                    stmtListOpenRunBridgeAt_of_source_run hPrim
                      hRestLowerAfter hEntryHandlersAfter hCtxAfter
                      hHandlersAfter hNoDupAfter hState hTailSource)
  termination_by (fuel, 1, StmtListMeasure stmts)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | omega


  theorem stmtRunBridgeAt_of_source_run
      {prim : Source.PrimitiveSemantics}
      (hPrim : PrimitiveSound prim)
      {program : Program} {entryCtx sourceCtx : Source.Ctx}
      {targetCtx : Ctx} {source : Source.State} {target : RunState}
      {fuel : Nat} {stmt : Stmt}
      {sourceResult : Source.Outcome × Source.Ctx}
      (hLower : StmtLowerable sourceCtx.scope stmt)
      (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
      (hCtx : CtxRel sourceCtx targetCtx)
      (hHandlers : CtxHandlersRel sourceCtx targetCtx)
      (hNoDup : sourceCtx.scope.Nodup)
      (hRel : StateRel sourceCtx.scope source target)
      (hSourceRun :
        Source.Stmt.run prim program sourceCtx fuel stmt source =
          .ok sourceResult) :
      StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel stmt
        source target := by
    cases stmt with
    | expr expr =>
        exact
          StmtRunBridgeAt.atomic_from_scoped_source_run_source_bound hPrim
            hEntryHandlers hCtx hHandlers hNoDup hLower.1 hLower.2.1
            hLower.2.2 hRel hSourceRun
    | exprs exprs =>
        cases hLower
    | let_ name value =>
        exact
          StmtRunBridgeAt.atomic_from_scoped_source_run_source_bound hPrim
            hEntryHandlers hCtx hHandlers hNoDup hLower.1 hLower.2.1
            hLower.2.2 hRel hSourceRun
    | assign name value =>
        exact
          StmtRunBridgeAt.atomic_from_scoped_source_run_source_bound hPrim
            hEntryHandlers hCtx hHandlers hNoDup hLower.1 hLower.2.1
            hLower.2.2 hRel hSourceRun
    | assignTop name =>
        cases hLower
    | assignTopWithOffset offset name =>
        cases hLower
    | block body =>
        cases hSourceScoped :
            Source.Block.runScoped prim program sourceCtx body fuel source with
        | error err =>
            simp [Source.Stmt.run, hSourceScoped] at hSourceRun
        | ok sourceOutcome =>
            unfold Source.Block.runScoped at hSourceScoped
            cases hSourceOpen :
                Source.Block.runOpen prim program sourceCtx fuel body source with
            | error err =>
                simp [hSourceOpen] at hSourceScoped
            | ok sourceOpenResult =>
                have hBodyBridge :
                    BlockOpenRunBridgeAt prim program entryCtx sourceCtx
                      targetCtx fuel body source target :=
                  blockOpenRunBridgeAt_of_source_run hPrim hLower
                    hEntryHandlers hCtx hHandlers hNoDup hRel hSourceOpen
                exact
                  StmtRunBridgeAt.block_from_open_bridge_source_run hCtx
                    hHandlers hBodyBridge hSourceRun
    | if_ cond body =>
        rcases hLower with ⟨hCondScoped, hCondAccess, hBodyLower⟩
        cases fuel with
        | zero =>
            simp [Source.Stmt.run, Source.invalid, Structured.invalid]
              at hSourceRun
        | succ fuel =>
            exact
              StmtRunBridgeAt.if_from_scoped_source_run_source_bound hPrim
                hCtx hHandlers hNoDup hCondScoped hCondAccess hRel
                (fun {sourceAfterCond} {targetAfterCond} hSourceCondTrue
                    hTargetCondTrue hCondRel => by
                  cases hSourceScoped :
                      Source.Block.runScoped prim program sourceCtx body fuel
                        sourceAfterCond with
                  | error err =>
                      simp [Source.Stmt.run, hSourceCondTrue, hSourceScoped]
                        at hSourceRun
                  | ok sourceOutcome =>
                      unfold Source.Block.runScoped at hSourceScoped
                      cases hSourceOpen :
                          Source.Block.runOpen prim program sourceCtx fuel body
                            sourceAfterCond with
                      | error err =>
                          simp [hSourceOpen] at hSourceScoped
                      | ok sourceOpenResult =>
                          exact
                            blockOpenRunBridgeAt_of_source_run hPrim
                              hBodyLower hEntryHandlers hCtx hHandlers hNoDup
                              hCondRel hSourceOpen)
                hSourceRun
    | switch scrutinee cases defaultBody =>
        rcases hLower with
          ⟨hScrutineeScoped, hScrutineeAccess, hCasesLower, hDefaultLower⟩
        cases fuel with
        | zero =>
            simp [Source.Stmt.run, Source.invalid, Structured.invalid]
              at hSourceRun
        | succ fuel =>
            exact
              StmtRunBridgeAt.switch_from_scoped_source_run_source_bound hPrim
                hCtx hHandlers hNoDup hScrutineeScoped hScrutineeAccess
                hRel
                (fun {sourceAfterScrutinee} {targetAfterScrutinee} {value}
                    {selected} hSourceScrutinee hTargetScrutinee
                    {stackAfterPop} hPop hSourceSelect hDirectSelect hPopRel => by
                  cases hSourceScoped :
                      Source.Block.runScoped prim program sourceCtx selected
                        fuel sourceAfterScrutinee with
                  | error err =>
                      simp [Source.Stmt.run, hSourceScrutinee, hSourceSelect,
                        hSourceScoped] at hSourceRun
                  | ok sourceOutcome =>
                      unfold Source.Block.runScoped at hSourceScoped
                      cases hSourceOpen :
                          Source.Block.runOpen prim program sourceCtx fuel
                            selected sourceAfterScrutinee with
                      | error err =>
                          simp [hSourceOpen] at hSourceScoped
                      | ok sourceOpenResult =>
                          have hSelectedLower :
                              BlockLowerable sourceCtx.scope selected :=
                            select_lowerable hCasesLower hDefaultLower
                              hSourceSelect
                          exact
                            blockOpenRunBridgeAt_of_source_run hPrim
                              hSelectedLower hEntryHandlers hCtx hHandlers
                              hNoDup hPopRel hSourceOpen)
                hSourceRun
    | for_ init cond post body =>
        rcases hLower with
          ⟨hInitLower, hCondScoped, hCondAccess, hPostLower, hBodyLower⟩
        exact
          forStmtRunBridgeAt_of_source_run_fixed_aux
            (stmtFuel := fuel) hPrim
            (fun hFuelLt hLower hEntryHandlers hCtx hHandlers hNoDup hRel
                hSourceRun =>
              blockOpenRunBridgeAt_of_source_run hPrim hLower
                hEntryHandlers hCtx hHandlers hNoDup hRel hSourceRun)
            (fun hFuelLt hLower hEntryHandlers hCtx hHandlers hNoDup hRel
                hSourceRun =>
              blockOpenRunBridgeAt_of_source_run hPrim hLower
                hEntryHandlers hCtx hHandlers hNoDup hRel hSourceRun)
            (fun hFuelLt hLower hEntryHandlers hCtx hHandlers hNoDup hRel
                hSourceRun =>
              blockOpenRunBridgeAt_of_source_run hPrim hLower
                hEntryHandlers hCtx hHandlers hNoDup hRel hSourceRun)
            rfl
            hEntryHandlers hCtx hHandlers hNoDup hRel hInitLower
            hCondScoped hCondAccess hPostLower hBodyLower hSourceRun
    | brk =>
        exact
          StmtRunBridgeAt.atomic_from_scoped_source_run_source_bound hPrim
            hEntryHandlers hCtx hHandlers hNoDup hLower.1 hLower.2.1
            hLower.2.2 hRel hSourceRun
    | cont =>
        exact
          StmtRunBridgeAt.atomic_from_scoped_source_run_source_bound hPrim
            hEntryHandlers hCtx hHandlers hNoDup hLower.1 hLower.2.1
            hLower.2.2 hRel hSourceRun
    | leave =>
        cases hLower
    | call name =>
        cases hLower
    | terminal kind =>
        exact
          StmtRunBridgeAt.atomic_from_scoped_source_run_source_bound hPrim
            hEntryHandlers hCtx hHandlers hNoDup hLower.1 hLower.2.1
            hLower.2.2 hRel hSourceRun
    | terminalArgs kind args =>
        exact
          StmtRunBridgeAt.atomic_from_scoped_source_run_source_bound hPrim
            hEntryHandlers hCtx hHandlers hNoDup hLower.1 hLower.2.1
            hLower.2.2 hRel hSourceRun
  termination_by (fuel, 3, StmtMeasure stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
      | omega
end



theorem runForLoopBridgeAt_of_source_run
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceLoopCtx : Source.Ctx}
    {targetLoopCtx : Ctx} {cond : Expr 1} {post body : Block}
    {fuel : Nat} {source sourceAfter : Source.State}
    {target : RunState} {sourceOutcome : Source.Outcome}
    (hCondScoped : Scope.ExprScoped sourceLoopCtx.scope cond)
    (hCondAccess : Access.ExprBound sourceLoopCtx.scope 0 cond)
    (hPostLower : BlockLowerable sourceLoopCtx.scope post)
    (hBodyLower : BlockLowerable sourceLoopCtx.scope body)
    (hEntryLeave : entryCtx.leaveScope? = sourceLoopCtx.leaveScope?)
    (hCtx : CtxRel sourceLoopCtx targetLoopCtx)
    (hHandlers : CtxHandlersRel sourceLoopCtx targetLoopCtx)
    (hNoDup : sourceLoopCtx.scope.Nodup)
    (hRel : StateRel sourceLoopCtx.scope source target)
    (hSourceRun :
      Source.Stmt.runForLoop prim program sourceLoopCtx cond
          sourceLoopCtx.withoutLoopControl post
          (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
            sourceLoopCtx.scope)
          body fuel source =
        .ok sourceOutcome) :
    ∃ targetOutcome : Outcome,
      Direct.Stmt.runForLoop program targetLoopCtx cond
          targetLoopCtx.withoutLoopControl post
          (targetLoopCtx.withLoopControl targetLoopCtx.layout.length) body
          fuel target =
        .ok targetOutcome ∧
      ScopedOutcomeRelAt entryCtx sourceLoopCtx.scope sourceOutcome
        targetOutcome := by
  exact
    runForLoopBridgeAt_of_source_run_aux (sourceAfter := sourceAfter) hPrim
      (fun hLower hEntryHandlers hCtx hHandlers hNoDup hRel hSourceRun =>
        blockOpenRunBridgeAt_of_source_run hPrim hLower hEntryHandlers hCtx
          hHandlers hNoDup hRel hSourceRun)
      hCondScoped hCondAccess hPostLower hBodyLower hEntryLeave hCtx
      hHandlers hNoDup hRel hSourceRun

theorem forStmtRunBridgeAt_of_source_run
    {prim : Source.PrimitiveSemantics}
    (hPrim : PrimitiveSound prim)
    {program : Program} {entryCtx sourceCtx : Source.Ctx}
    {targetCtx : Ctx} {source : Source.State} {target : RunState}
    {fuel : Nat} {init : Block} {cond : Expr 1} {post body : Block}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hEntryHandlers : HandlerScopesEq entryCtx sourceCtx)
    (hCtx : CtxRel sourceCtx targetCtx)
    (hHandlers : CtxHandlersRel sourceCtx targetCtx)
    (hNoDup : sourceCtx.scope.Nodup)
    (hRel : StateRel sourceCtx.scope source target)
    (hInitLower : BlockLowerable sourceCtx.scope init)
    (hCondScoped :
      Scope.ExprScoped (Scope.Block.outEnv sourceCtx.scope init) cond)
    (hCondAccess :
      Access.ExprBound (Scope.Block.outEnv sourceCtx.scope init) 0 cond)
    (hPostLower : BlockLowerable (Scope.Block.outEnv sourceCtx.scope init) post)
    (hBodyLower : BlockLowerable (Scope.Block.outEnv sourceCtx.scope init) body)
    (hSourceRun :
      Source.Stmt.run prim program sourceCtx fuel (.for_ init cond post body)
          source =
        .ok sourceResult) :
    StmtRunBridgeAt prim program entryCtx sourceCtx targetCtx fuel
      (.for_ init cond post body) source target := by
  cases fuel with
  | zero =>
      simp [Source.Stmt.run, Source.invalid, Structured.invalid] at hSourceRun
  | succ fuel =>
      let sourceInitCtx := sourceCtx.withoutLoopControl
      let targetInitCtx := targetCtx.withoutLoopControl
      have hInitCtx : CtxRel sourceInitCtx targetInitCtx := by
        exact CtxRel.withoutLoopControl hCtx
      have hInitHandlers :
          CtxHandlersRel sourceInitCtx targetInitCtx := by
        exact CtxHandlersRel.withoutLoopControl hHandlers
      have hInitNoDup : sourceInitCtx.scope.Nodup := by
        simpa [sourceInitCtx, Source.Ctx.withoutLoopControl] using hNoDup
      cases hSourceInit :
          Source.Block.runOpen prim program sourceInitCtx fuel init source with
      | error err =>
          simp [Source.Stmt.run, sourceInitCtx, hSourceInit] at hSourceRun
      | ok sourceInitResult =>
          have hInitBridge :
              BlockOpenRunBridgeAt prim program sourceInitCtx sourceInitCtx
                targetInitCtx fuel init source target :=
            blockOpenRunBridgeAt_of_source_run hPrim hInitLower
              (HandlerScopesEq.refl sourceInitCtx) hInitCtx hInitHandlers
              hInitNoDup hRel hSourceInit
          rcases
              BlockOpenRunBridgeAt.target_result_of_source hInitBridge
                hSourceInit with
            ⟨targetInitResult, hTargetInit, hInitRel⟩
          rcases sourceInitResult with ⟨sourceInitOutcome, sourceLoopCtx⟩
          rcases targetInitResult with ⟨targetInitOutcome, targetLoopCtx⟩
          rcases sourceInitOutcome with ⟨sourceInitState, sourceInitMode⟩
          rcases targetInitOutcome with ⟨targetInitState, targetInitMode⟩
          cases sourceInitMode <;> cases targetInitMode <;>
            simp [RunResultRelAt] at hInitRel
          · rcases hInitRel with ⟨hInitStateRel, hLoopCtx, hLoopHandlers⟩
            have hSourceInitRegular :
                Source.Block.runOpen prim program sourceInitCtx fuel init
                    source =
                  .ok (Source.Outcome.regular sourceInitState,
                    sourceLoopCtx) := by
              simpa [Source.Outcome.regular] using hSourceInit
            have hInitScopeBase :
                sourceLoopCtx.scope =
                  Scope.Block.outEnv sourceInitCtx.scope init :=
              Source.Block.runOpen_regular_scope hSourceInitRegular
            have hInitScope :
                sourceLoopCtx.scope =
                  Scope.Block.outEnv sourceCtx.scope init := by
              simpa [sourceInitCtx, Source.Ctx.withoutLoopControl]
                using hInitScopeBase
            have hLoopNoDup : sourceLoopCtx.scope.Nodup := by
              rw [hInitScope]
              exact
                Block.scoped_outEnv_nodup hNoDup
                  (blockLowerable_scoped hInitLower)
            have hCondScopedLoop :
                Scope.ExprScoped sourceLoopCtx.scope cond := by
              rw [hInitScope]
              exact hCondScoped
            have hCondAccessLoop :
                Access.ExprBound sourceLoopCtx.scope 0 cond := by
              rw [hInitScope]
              exact hCondAccess
            have hPostLowerLoop :
                BlockLowerable sourceLoopCtx.scope post := by
              rw [hInitScope]
              exact hPostLower
            have hBodyLowerLoop :
                BlockLowerable sourceLoopCtx.scope body := by
              rw [hInitScope]
              exact hBodyLower
            have hInitHandlerScopes :
                HandlerScopesEq sourceInitCtx sourceLoopCtx :=
              blockLowerable_regular_handlerScopesEq hInitLower
                hSourceInitRegular
            have hEntryLeave :
                entryCtx.leaveScope? = sourceLoopCtx.leaveScope? := by
              rcases hEntryHandlers with
                ⟨_hEntryBreak, _hEntryContinue, hEntryLeaveSource⟩
              rcases hInitHandlerScopes with
                ⟨_hInitBreak, _hInitContinue, hInitLeave⟩
              calc
                entryCtx.leaveScope? = sourceCtx.leaveScope? :=
                  hEntryLeaveSource
                _ = sourceInitCtx.leaveScope? := by
                  simp [sourceInitCtx, Source.Ctx.withoutLoopControl]
                _ = sourceLoopCtx.leaveScope? := hInitLeave
            cases hSourceLoop :
                Source.Stmt.runForLoop prim program sourceLoopCtx cond
                  sourceLoopCtx.withoutLoopControl post
                  (sourceLoopCtx.withLoopControl sourceLoopCtx.scope
                    sourceLoopCtx.scope)
                  body fuel sourceInitState with
            | error err =>
                simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                  hSourceLoop] at hSourceRun
            | ok sourceLoopOutcome =>
                rcases
                    runForLoopBridgeAt_of_source_run
                      (sourceAfter := sourceInitState) hPrim hCondScopedLoop
                      hCondAccessLoop hPostLowerLoop hBodyLowerLoop
                      hEntryLeave hLoopCtx hLoopHandlers hLoopNoDup
                      hInitStateRel hSourceLoop with
                  ⟨targetLoopOutcome, hTargetLoop, hLoopRel⟩
                rcases sourceLoopOutcome with
                  ⟨sourceLoopState, sourceLoopMode⟩
                rcases targetLoopOutcome with
                  ⟨targetLoopState, targetLoopMode⟩
                cases sourceLoopMode <;> cases targetLoopMode <;>
                  simp [ScopedOutcomeRelAt] at hLoopRel
                · rcases hLoopCtx with
                    ⟨hLoopLayout, _hBreakDepth, _hContinueDepth,
                      _hLeaveDepth, _hRetc⟩
                  have hCleanupScope :
                      CleanupScopeRel targetLoopCtx.layout sourceCtx.scope := by
                    rw [hLoopLayout, hInitScope]
                    exact
                      Scope.block_outEnv_cleanupScopeRel sourceCtx.scope init
                  have hLoopRelTarget :
                      StateRel targetLoopCtx.layout sourceLoopState
                        targetLoopState := by
                    simpa [hLoopLayout] using hLoopRel
                  rcases
                      StateRel.cleanupTo_scope_exists (ctx := targetLoopCtx)
                        hCleanupScope hLoopRelTarget with
                    ⟨targetCleaned, hCleanup, hCleanRel, _hReturns⟩
                  simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop] at hSourceRun
                  cases hSourceRun
                  refine
                    ⟨(Source.Outcome.regular
                        (sourceLoopState.restrictTo sourceCtx.scope),
                        sourceCtx),
                      (Outcome.regular targetCleaned, targetCtx),
                      ?_, ?_,
                      RunResultRelAt.regular hCleanRel hCtx hHandlers⟩
                  · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                      hSourceLoop]
                  · rcases hCtx with
                      ⟨hTargetLayout, _hBreakDepth, _hContinueDepth,
                        _hLeaveDepth, _hRetc⟩
                    simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                      hTargetLoop, hCleanup, hTargetLayout]
                · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop, Source.invalid, Structured.invalid]
                    at hSourceRun
                · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop, Source.invalid, Structured.invalid]
                    at hSourceRun
                · rcases hLoopRel with ⟨leaveScope, hLeave, hLeaveState⟩
                  simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop] at hSourceRun
                  cases hSourceRun
                  exact
                    ⟨(Source.Outcome.leave sourceLoopState, sourceCtx),
                      (Outcome.leave targetLoopState, targetCtx),
                      by
                        show
                          Source.Stmt.run prim program sourceCtx (fuel + 1)
                              (Stmt.for_ init cond post body) source =
                            .ok (Source.Outcome.leave sourceLoopState,
                              sourceCtx)
                        simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                          hSourceLoop, Source.Outcome.leave],
                      by simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                        hTargetLoop, Structured.Outcome.leave],
                      RunResultRelAt.leave hLeave hLeaveState⟩
                · rename_i sourceKind targetKind
                  rcases hLoopRel with ⟨hShared, hKind⟩
                  subst hKind
                  simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                    hSourceLoop] at hSourceRun
                  cases hSourceRun
                  exact
                    ⟨(Source.Outcome.halt sourceKind sourceLoopState,
                        sourceCtx),
                      (Outcome.halt sourceKind targetLoopState, targetCtx),
                      by
                        show
                          Source.Stmt.run prim program sourceCtx (fuel + 1)
                              (Stmt.for_ init cond post body) source =
                            .ok (Source.Outcome.halt sourceKind
                              sourceLoopState, sourceCtx)
                        simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                          hSourceLoop, Source.Outcome.halt],
                      by simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                        hTargetLoop, Structured.Outcome.halt],
                      RunResultRelAt.halt_shared hShared⟩
          · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
              Source.invalid, Structured.invalid] at hSourceRun
          · simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
              Source.invalid, Structured.invalid] at hSourceRun
          · rcases hInitRel with ⟨leaveScope, hInitLeave, hLeaveState⟩
            have hEntryLeaveSome : entryCtx.leaveScope? = some leaveScope := by
              rcases hEntryHandlers with
                ⟨_hBreak, _hContinue, hEntryLeaveSource⟩
              rw [hEntryLeaveSource]
              simpa [sourceInitCtx, Source.Ctx.withoutLoopControl]
                using hInitLeave
            simp [Source.Stmt.run, sourceInitCtx, hSourceInit] at hSourceRun
            cases hSourceRun
            exact
              ⟨(Source.Outcome.leave sourceInitState, sourceCtx),
                (Outcome.leave targetInitState, targetCtx),
                by simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                  Source.Outcome.leave],
                by simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                  Structured.Outcome.leave],
                RunResultRelAt.leave hEntryLeaveSome hLeaveState⟩
          · rename_i sourceKind targetKind
            rcases hInitRel with ⟨hShared, hKind⟩
            subst hKind
            simp [Source.Stmt.run, sourceInitCtx, hSourceInit] at hSourceRun
            cases hSourceRun
            exact
              ⟨(Source.Outcome.halt sourceKind sourceInitState, sourceCtx),
                (Outcome.halt sourceKind targetInitState, targetCtx),
                by simp [Source.Stmt.run, sourceInitCtx, hSourceInit,
                  Source.Outcome.halt],
                by simp [Direct.Stmt.run, targetInitCtx, hTargetInit,
                  Structured.Outcome.halt],
                RunResultRelAt.halt_shared hShared⟩

end Structural

end SourceLowering

namespace Source

/--
Whole-program observation relation for the stack-free locals source
interpreter.

The direct scoped-stack outcome is intentionally existentially hidden here:
higher layers should talk about named local stores and source modes, while this
lowering boundary owns stack layouts, cleanup depths, and DUP/SWAP resource
facts.
-/
def WholeProgramOutcomeRel (source : Outcome)
    (target : Assembly.StepResult) : Prop :=
  ∃ direct,
    SourceLowering.ScopedOutcomeRelAt Source.Ctx.initial [] source direct ∧
      Structured.Preservation.WholeProgramOutcomeRel direct target

namespace Program

/--
Source-facing compiler acceptance for the locals layer.

`source` is pure source wellformedness/ownership. `lowerable` is a checked
compiler-resource contract for the lowering to the direct scoped-stack backend:
it packages structural lowerability and concrete stack-access bounds without
putting stack slots into the source interpreter.
-/
structure CompileAccepted (program : Locals.Program) : Prop where
  source : Locals.Program.SourceAccepted program
  lowerable : SourceLowering.Structural.BlockLowerable [] program.body

noncomputable def compileChecked? (program : Locals.Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Structured.Preservation.ProcedurePreservation.compileChecked?
    lower.toStructured

theorem compileChecked?_eq_some {program : Locals.Program}
    {asm : Assembly.Program}
    (hCompile : compileChecked? program = some asm) :
    ∃ lower : Expressions.Program,
      program.toExpressions? = some lower ∧
        Structured.Preservation.ProcedurePreservation.compileChecked?
          lower.toStructured = some asm := by
  unfold compileChecked? at hCompile
  cases hLower : program.toExpressions? with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact ⟨lower, rfl, hCompile⟩

theorem compileChecked?_noCallCreate {program : Locals.Program}
    {asm : Assembly.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  exact
    Structured.Preservation.ProcedurePreservation.compileChecked?_noCallCreate
      (program := lower.toStructured) (asm := asm)
      (by
        have hLowerNo :=
          Locals.CompilerFacts.Program.toExpressions?_noCallCreate
            program hProgram hLower
        simpa [Expressions.CompilerFacts.Program.toStructured_usesCallCreate]
          using hLowerNo)
      hLowerCompile

theorem runState_toDirect_exists
    {prim : PrimitiveSemantics}
    (hPrim : SourceLowering.PrimitiveSound prim)
    {program : Locals.Program} {fuel : Nat}
    {source : State} {target : RunState}
    {sourceOutcome : Outcome}
    (hAccepted : CompileAccepted program)
    (hSourceRun :
      Program.runState prim fuel program source = .ok sourceOutcome)
    (hRel : SourceLowering.StateRel [] source target) :
    ∃ targetOutcome,
      Direct.Program.runState fuel program target = .ok targetOutcome ∧
      SourceLowering.ScopedOutcomeRelAt Source.Ctx.initial []
        sourceOutcome targetOutcome := by
  have hScoped :
      Block.runScoped prim program Source.Ctx.initial program.body fuel source =
        .ok sourceOutcome := by
    simpa [Program.runState] using hSourceRun
  have hScopedForOpen := hScoped
  unfold Block.runScoped at hScopedForOpen
  cases hOpen :
      Block.runOpen prim program Source.Ctx.initial fuel program.body
        source with
  | error err =>
      simp [hOpen] at hScopedForOpen
  | ok sourceOpenResult =>
      have hBridge :
          SourceLowering.BlockOpenRunBridgeAt prim program
            Source.Ctx.initial Source.Ctx.initial Locals.Ctx.initial fuel
            program.body source target :=
        SourceLowering.Structural.blockOpenRunBridgeAt_of_source_run
          hPrim hAccepted.lowerable
          (SourceLowering.HandlerScopesEq.refl Source.Ctx.initial)
          SourceLowering.CtxRel.initial
          SourceLowering.CtxHandlersRel.initial
          (by simp [Source.Ctx.initial])
          hRel hOpen
      rcases
          SourceLowering.BlockOpenRunBridgeAt.runScoped_from_open_bridge
            SourceLowering.CtxRel.initial hBridge hScoped with
        ⟨targetOutcome, hTargetRun, hOutcomeRel⟩
      exact
        ⟨targetOutcome,
          by simpa [Direct.Program.runState] using hTargetRun,
          hOutcomeRel⟩

theorem run_toDirect_exists
    {prim : PrimitiveSemantics}
    (hPrim : SourceLowering.PrimitiveSound prim)
    {program : Locals.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hAccepted : CompileAccepted program)
    (hInitialStack : initial.stack = [])
    (hSourceRun :
      Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetOutcome,
      Direct.Program.run fuel program initial = .ok targetOutcome ∧
      SourceLowering.ScopedOutcomeRelAt Source.Ctx.initial []
        sourceOutcome targetOutcome := by
  exact
    runState_toDirect_exists (prim := prim) hPrim
      (program := program) (fuel := fuel)
      (source := Program.initialState initial.toSharedState)
      (target := Structured.RunState.initial initial)
      (sourceOutcome := sourceOutcome) hAccepted
      (by simpa [Program.run] using hSourceRun)
      (SourceLowering.StateRel.initial hInitialStack)

theorem compile_preserves_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : SourceLowering.PrimitiveSound prim)
    {program : Locals.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hAccepted : CompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hSourceRun :
      Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases
      run_toDirect_exists (prim := prim) hPrim (program := program)
        (fuel := fuel) (initial := initial) (sourceOutcome := sourceOutcome)
        hAccepted hInitialStack hSourceRun with
    ⟨directOutcome, hDirectRun, hSourceRel⟩
  rcases
      Locals.Program.compile_preserves
        (program := program) (lower := lower) (asm := asm)
        (fuel := fuel) (initial := initial) (outcome := directOutcome)
        hLower hCompile hInitialPc
        (by simpa [Locals.Program.run] using hDirectRun) with
    ⟨targetFuel, targetOutcome, hTargetRun, hDirectRel⟩
  exact
    ⟨targetFuel, targetOutcome, hTargetRun, directOutcome, hSourceRel,
      hDirectRel⟩

theorem compile_preserves_checked_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : SourceLowering.PrimitiveSound prim)
    {program : Locals.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : CompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hSourceRun :
      Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  exact
    compile_preserves_of_compileAccepted hPrim hAccepted hLower
      hStructuredCompile hInitialPc hInitialStack hSourceRun

end Program

end Source

end Locals
end EvmCompiler
