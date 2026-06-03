import EvmCompiler.Yul.Reference

/-!
Inhabitation of `Reference.SourceBridgeFacts.RecursiveSourceBridgeWhenUpToAt`.

The recursive bridge is the induction target for the imported-Yul / source-tower
preservation theorem.  Existing leaf wrappers in `Yul.Reference` cover terminal
calls (`stop`, `return`, `revert`, `selfdestruct`) and abrupt control flow
(`break`, `continue`, `leave`), but the bridge structure itself has never been
inhabited — every theorem that mentions it takes it as a hypothesis.

This file is the new home for the recursive inhabitation.  It begins with the
fuel-zero base case, which is uniform across all statements: at zero source
fuel the imported Yul interpreter returns `.error .OutOfFuel`, and the
`allowed`/`SourceResultRelatable` filter rules that out.  The successor cases
will be added in follow-up commits as the per-constructor source-tower leaves
mature.
-/

namespace EvmCompiler
namespace Yul
namespace Reference
namespace SourceBridgeFacts

/--
Base case of the recursive bridge induction.

At `bound = 0` the bridge's fuel premise `sourceFuel ≤ 0` forces `sourceFuel
= 0`, the imported Yul interpreter trivially produces `.error .OutOfFuel`,
and the run-filter excludes that result from the `allowed` set.  The proof is
the same for both the statement and block fields.
-/
theorem recursiveSourceBridgeWhenUpToAt_zero
    {cfg : StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} :
    RecursiveSourceBridgeWhenUpToAt cfg terminalRel revertRel prim program 0 := by
  refine ⟨?_, ?_⟩
  · -- statement field
    intro layout outcomeLayout ctx sourceFuel sourceStmt codeOverride allowed
      hAllowed hFuel hScope
    have hFuelEq : sourceFuel = 0 := Nat.le_zero.mp hFuel
    subst hFuelEq
    intro freshState freshState' lowerStmts _hCovers _hLower
    refine ⟨hScope, ?_⟩
    intro source compiler sourceResult _hInitial hAllow hSource
    have hZero :
        EvmYul.Yul.exec 0 (.Block [sourceStmt]) codeOverride source =
          .error .OutOfFuel :=
      Imported.exec_zero (.Block [sourceStmt]) codeOverride source
    rw [hZero] at hSource
    subst sourceResult
    have hRelatable :
        SourceResultRelatable (.error (.OutOfFuel : Exception)) :=
      hAllowed hAllow
    cases hRelatable
  · -- block field
    intro layout outcomeLayout ctx sourceFuel sourceStmts codeOverride allowed
      hAllowed hFuel hScope
    have hFuelEq : sourceFuel = 0 := Nat.le_zero.mp hFuel
    subst hFuelEq
    intro freshState freshState' lowerBlock _hCovers _hLower
    refine ⟨hScope, ?_⟩
    intro source compiler sourceResult _hInitial hAllow hSource
    have hZero :
        EvmYul.Yul.exec 0 (.Block sourceStmts) codeOverride source =
          .error .OutOfFuel :=
      Imported.exec_zero (.Block sourceStmts) codeOverride source
    rw [hZero] at hSource
    subst sourceResult
    have hRelatable :
        SourceResultRelatable (.error (.OutOfFuel : Exception)) :=
      hAllowed hAllow
    cases hRelatable

/-!
## Source-tower argument-evaluation bridge

Architectural direction: instead of building seven per-constructor leaves at
the source-tower invariant, build a single generic argument-evaluation bridge
(mirroring the legacy `BoundArgsBridgeWithLayoutSlotValues` at the source-tower
invariant `SourceStateRel` / `Functions.Source.Block.runOpen`).  Each of the
seven open constructors (`Let`, `Assign`, `ExprStmtCall`, `If`, `Switch`,
`For`, `Block`-cons) becomes a thin wrapper over this bridge plus a
constructor-specific outcome step.

The bridge is **layout-transforming**: it extends `ctx.scope` by the names
that the compiler prelude allocates for argument values.

This is oracle-confirmed direction (B) — see PROGRESS_LOG entry
`oracle/yul-bridge-direction-confirmed` for the architectural decision.
-/

/--
Regular-success bridge: an imported `evalArgs` of `args` (in Yul's
right-to-left evaluation order) is mimicked by a source-tower prelude block
`pre` whose execution leaves the argument values accessible through
expressions `lowerArgs` evaluated in the post-prelude state.

`lowerArgs[i]` evaluates (via `Locals.Source.Expr.evalOne`) to the i-th
imported argument value in the post-prelude `stateAfter`, with imported and
source-tower states related at `argLayout` (an extension of `layout` by names
the prelude introduces).

The terminal/error branches of `evalArgs` (e.g., halts during argument
evaluation if a primitive triggers a halt) are intentionally not part of this
regular-success interface; they are handled by separate halt/revert wrappers.
-/
def SourceArgEvalRegular
    (cfg : StateRelConfig)
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program)
    (layout argLayout : List Name)
    (ctx : Functions.Source.Ctx)
    (argFuel : Nat) (args : List AstExpr)
    (codeOverride : Option AstContract)
    (pre : List Functions.Stmt)
    (lowerArgs : List (Locals.Expr 1)) : Prop :=
  ctx.scope = layout ∧ lowerArgs.length = args.length ∧
    ∀ {source sourceAfter : State} {compiler : Objects.Source.State}
      {values : List Word},
      SourceStateRel cfg layout source compiler →
      EvmYul.Yul.evalArgs argFuel args.reverse codeOverride source =
        .ok (sourceAfter, values.reverse) →
      ∃ stateAfter : Locals.Source.State, ∃ targetFuel : Nat,
      ∃ ctxAfter : Functions.Source.Ctx,
        Functions.Source.Block.runOpen prim program ctx targetFuel
            { stmts := pre } compiler =
          .ok (Functions.Source.Outcome.regular stateAfter, ctxAfter) ∧
        ctxAfter.scope = argLayout ∧
        SourceStateRel cfg argLayout sourceAfter stateAfter ∧
        (∀ i (hi : i < lowerArgs.length) (hv : i < values.length),
          ∃ valueStateAfter : Locals.Source.State,
            Locals.Source.Expr.evalOne prim
                (lowerArgs[i]'hi) stateAfter =
              .ok (valueStateAfter, values[i]'hv))

/--
Empty-arguments base case.

When the source has no arguments the prelude is empty, the source-tower
`Block.runOpen` returns the input state with a regular outcome, and the
imported `evalArgs` on the empty list returns the same state with no values.
-/
theorem sourceArgEvalRegular_nil
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {codeOverride : Option AstContract}
    (hScope : ctx.scope = layout) :
    SourceArgEvalRegular cfg prim program layout layout ctx argFuel.succ
      [] codeOverride [] [] := by
  refine ⟨hScope, rfl, ?_⟩
  intro source sourceAfter compiler values hInitial hImpEval
  simp [Imported.evalArgs_nil_succ] at hImpEval
  obtain ⟨hStateEq, hValuesReverse⟩ := hImpEval
  subst hStateEq
  have hValuesEmpty : values = [] := by
    have := congrArg List.reverse hValuesReverse
    simpa using this
  subst hValuesEmpty
  refine ⟨compiler, 1, ctx, ?_, hScope, hInitial, ?_⟩
  · simp [Functions.Source.Block.runOpen]
  · intro i hi _hv
    exact absurd hi (Nat.not_lt_zero _)

/--
Singleton-literal argument case.

For `args = [.Lit value]` the imported `evalArgs` produces the singleton value
list and the unchanged source state.  No source-tower prelude is needed because
the lowered argument expression `.lit value` is a direct literal; evaluating
it in any state gives back the value.  This is the simplest non-trivial
instance of the source-tower argument-evaluation bridge.
-/
theorem sourceArgEvalRegular_singleton_lit
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {value : Word}
    {codeOverride : Option AstContract}
    (hScope : ctx.scope = layout) :
    SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel.succ.succ.succ [.Lit value] codeOverride []
      [Locals.Expr.lit value] := by
  refine ⟨hScope, by simp, ?_⟩
  intro source sourceAfter compiler values hInitial hImpEval
  cases hInitial with
  | @ok shared store _ hShared hVars =>
      rcases BridgeFacts.evalArgs_singleton_lit_reverse_ok_eq
        (fuel := argFuel) (value := value) (codeOverride := codeOverride)
        (shared := shared) (store := store) (sourceAfter := sourceAfter)
        (values := values) hImpEval with ⟨hStateEq, hValuesEq⟩
      subst hStateEq
      subst hValuesEq
      refine ⟨compiler, 1, ctx, ?_, hScope, ?_, ?_⟩
      · simp [Functions.Source.Block.runOpen]
      · exact SourceStateRel.ok hShared hVars
      · intro i hi hv
        match i, hi, hv with
        | 0, _, _ =>
            refine ⟨compiler, ?_⟩
            simp [Locals.Source.Expr.evalOne,
              Locals.Source.Expr.eval]

/--
Pair-of-literals argument case.

For `args = [.Lit offset, .Lit size]` (source order) the imported `evalArgs`
operates on the reversed list `[.Lit size, .Lit offset]` and returns
`(source, [offset, size])` unchanged.  The source-tower lowered argument
expressions are `[.lit offset, .lit size]`; each evaluates directly to its
literal value without any prelude.
-/
theorem sourceArgEvalRegular_pair_lit
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {offset size : Word}
    {codeOverride : Option AstContract}
    (hScope : ctx.scope = layout) :
    SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel.succ.succ.succ.succ.succ [.Lit offset, .Lit size] codeOverride []
      [Locals.Expr.lit offset, Locals.Expr.lit size] := by
  refine ⟨hScope, by simp, ?_⟩
  intro source sourceAfter compiler values hInitial hImpEval
  cases hInitial with
  | @ok shared store _ hShared hVars =>
      rcases BridgeFacts.evalArgs_lit_lit_reverse_ok_eq
        (fuel := argFuel) (offset := offset) (size := size)
        (codeOverride := codeOverride) (shared := shared) (store := store)
        (sourceAfter := sourceAfter) (values := values) hImpEval with
        ⟨hStateEq, hValuesEq⟩
      subst hStateEq
      subst hValuesEq
      refine ⟨compiler, 1, ctx, ?_, hScope, ?_, ?_⟩
      · simp [Functions.Source.Block.runOpen]
      · exact SourceStateRel.ok hShared hVars
      · intro i hi hv
        match i, hi, hv with
        | 0, _, _ =>
            refine ⟨compiler, ?_⟩
            simp [Locals.Source.Expr.evalOne,
              Locals.Source.Expr.eval]
        | 1, _, _ =>
            refine ⟨compiler, ?_⟩
            simp [Locals.Source.Expr.evalOne,
              Locals.Source.Expr.eval]

/--
Helper: imported semantics of `.Block [.Let [] none]` at productive fuel.

Modeled after `Imported.exec_block_break_succ_succ_succ` (line 615).  The
empty-names `Let none` succeeds vacuously: `checkDeclaration` on an empty
list passes, `zeroFill` is identity, and the outer `restrictStoreTo` is
self-restriction.  Result: `.ok` with the original state.
-/
theorem exec_block_let_empty_none_succ_succ_succ (fuel : Nat)
    (codeOverride : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.exec fuel.succ.succ.succ (.Block [.Let [] none]) codeOverride
        (.Ok shared store) =
      .ok (.Ok shared store) := by
  rw [Imported.exec_block_cons_succ]
  simp [Imported.execSeq_cons_ok_result_succ
    (hHead := Imported.exec_let_none_succ fuel [] codeOverride
      (.Ok shared store))
    (hTail := Imported.execSeq_nil_succ fuel codeOverride
      ((.Ok shared store : State).zeroFill [])),
    EvmYul.Yul.State.zeroFill, EvmYul.Yul.State.restrictStoreTo,
    EvmYul.Yul.State.store, EvmYul.Yul.checkDeclaration,
    FinmapFacts.restrictVarStore_self]

/--
Imported semantics of `.Block [.Block []]` (single source statement = empty
inner block) at productive fuel.

Two block-cons layers each consume one fuel; the inner empty-block reduction
contributes another two via `exec_block_nil_ok_succ_succ`.
-/
theorem exec_block_block_empty_succ_succ_succ_succ (fuel : Nat)
    (codeOverride : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.exec fuel.succ.succ.succ.succ (.Block [.Block []]) codeOverride
        (.Ok shared store) =
      .ok (.Ok shared store) := by
  rw [Imported.exec_block_cons_succ]
  simp [Imported.execSeq_cons_ok_result_succ
    (hHead := Imported.exec_block_nil_ok_succ_succ fuel codeOverride
      shared store)
    (hTail := Imported.execSeq_nil_succ fuel.succ codeOverride
      (.Ok shared store : State)),
    EvmYul.Yul.State.restrictStoreTo, EvmYul.Yul.State.store,
    FinmapFacts.restrictVarStore_self]

/--
`Locals.Source.Store.restrictTo` is idempotent at a fixed scope.

This is the missing fact for nested-block source-tower bridges: the outer
`Block.runScoped`'s restrictTo composes with the inner `Block.runScoped`'s
restrictTo, both at the same scope.
-/
theorem Locals_Source_Store_restrictTo_idem
    (scope : List Name) (store : Locals.Source.Store) :
    Locals.Source.Store.restrictTo scope
        (Locals.Source.Store.restrictTo scope store) =
      Locals.Source.Store.restrictTo scope store := by
  funext key
  by_cases hMem : key ∈ scope
  · simp [Locals.Source.Store.restrictTo, hMem]
  · simp [Locals.Source.Store.restrictTo, hMem]

theorem Locals_Source_State_restrictTo_idem
    (scope : List Name) (state : Locals.Source.State) :
    (state.restrictTo scope).restrictTo scope = state.restrictTo scope := by
  simp [Locals.Source.State.restrictTo,
    Locals_Source_Store_restrictTo_idem]

/--
Constructor leaf for `.Block []` (empty inner block) at the source-tower invariant.
-/
theorem sourceResultBlockSoundWhenAt_block_empty
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {sourceFuel : Nat} {codeOverride : Option AstContract}
    {allowed : Except Exception State → Prop}
    (hAllowed :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultRelatable sourceResult)
    (hScope : ctx.scope = layout) :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel [.Block []] codeOverride
      { stmts := [Functions.Stmt.block { stmts := [] }] } allowed := by
  refine ⟨hScope, ?_⟩
  intro source compiler sourceResult hInitial hAllow hSource
  cases sourceFuel with
  | zero =>
      have hZero :=
        Imported.exec_zero (.Block [.Block []]) codeOverride source
      rw [hZero] at hSource
      subst sourceResult
      cases hAllowed hAllow
  | succ fuel =>
      cases fuel with
      | zero =>
          have hOne :
              EvmYul.Yul.exec 1 (.Block [.Block []]) codeOverride source =
                .error .OutOfFuel := by
            simp [EvmYul.Yul.exec, EvmYul.Yul.execSeq]
          rw [hOne] at hSource
          subst sourceResult
          cases hAllowed hAllow
      | succ fuel =>
          cases fuel with
          | zero =>
              have hTwo :
                  EvmYul.Yul.exec 2 (.Block [.Block []]) codeOverride source =
                    .error .OutOfFuel := by
                simp [EvmYul.Yul.exec, EvmYul.Yul.execSeq,
                  EvmYul.Yul.exec]
              rw [hTwo] at hSource
              subst sourceResult
              cases hAllowed hAllow
          | succ fuel =>
              cases fuel with
              | zero =>
                  have hThree :
                      EvmYul.Yul.exec 3 (.Block [.Block []]) codeOverride
                          source =
                        .error .OutOfFuel := by
                    simp [EvmYul.Yul.exec, EvmYul.Yul.execSeq,
                      EvmYul.Yul.exec]
                  rw [hThree] at hSource
                  subst sourceResult
                  cases hAllowed hAllow
              | succ fuel =>
                  cases hInitial with
                  | @ok shared store _ hShared hVars =>
                      refine
                        ⟨Functions.Source.Outcome.regular
                            (compiler.restrictTo layout), 3, ?_, ?_⟩
                      · simp [Functions.Source.Block.runScoped,
                          Functions.Source.Block.runOpen,
                          Functions.Source.Stmt.run, hScope,
                          Functions.Source.Outcome.regular,
                          Locals.Source.Outcome.regular,
                          Locals_Source_State_restrictTo_idem]
                      · rw [← hSource]
                        rw [exec_block_block_empty_succ_succ_succ_succ]
                        exact
                          SourceResultOutcomeRel.ok
                            (SourceOkOutcomeRel.regular
                              (SourceStateRel.ok hShared (by
                                intro name hMem
                                simpa [Locals.Source.State.restrictTo,
                                  Locals.Source.Store.restrictTo_mem hMem]
                                  using hVars name hMem)))
/--
Lowerer-aware checked leaf for `.Block []` (empty inner block).

Lifts `sourceResultBlockSoundWhenAt_block_empty` through `Stmt.toFunctionsList?`.
Uses `toFunctionsListFuel?_block_components` to extract the inner empty
block from the lowerer output.
-/
theorem checkedStmtBlockLoweringSoundWhenFreshAt_block_empty
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {sourceFuel : Nat} {codeOverride : Option AstContract}
    {allowed : Except Exception State → Prop}
    (hAllowed :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultRelatable sourceResult)
    (hScope : ctx.scope = layout) :
    CheckedStmtBlockLoweringSoundWhenFreshAt cfg layout layout terminalRel
      revertRel prim program ctx sourceFuel (.Block []) codeOverride
      allowed := by
  intro freshState freshState' lowerStmts _hCovers hLower
  -- Compute Stmt.toFunctionsList? on .Block [] directly
  have hExpected :
      Stmt.toFunctionsList? freshState (.Block []) =
        some ([Functions.Stmt.block { stmts := [] }], freshState) := by
    unfold Stmt.toFunctionsList?
    show Stmt.toFunctionsListFuel? 4 freshState (.Block []) =
      some ([Functions.Stmt.block { stmts := [] }], freshState)
    rfl
  rw [hExpected] at hLower
  injection hLower with hPair
  obtain ⟨hStmts, hFresh⟩ := Prod.mk.injEq .. |>.mp hPair
  subst hStmts
  exact sourceResultBlockSoundWhenAt_block_empty hAllowed hScope

/--
Imported semantics of `.Block [.If (.Lit 0) []]` (zero-condition empty if).
-/
theorem exec_block_if_zero_empty_succ_succ_succ_succ (fuel : Nat)
    (codeOverride : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.exec fuel.succ.succ.succ.succ
        (.Block [.If (.Lit (EvmYul.UInt256.ofNat 0)) []]) codeOverride
        (.Ok shared store) =
      .ok (.Ok shared store) := by
  have hZero : EvmYul.UInt256.ofNat 0 = ({ val := 0 } : Word) := rfl
  rw [Imported.exec_block_cons_succ]
  simp [EvmYul.Yul.execSeq, Imported.exec_if_succ,
    Imported.eval_lit_succ, hZero,
    EvmYul.Yul.State.restrictStoreTo,
    EvmYul.Yul.State.store, FinmapFacts.restrictVarStore_self]

/--
Specialized `checkDeclaration` success for a single fresh name.
-/
theorem checkDeclaration_ok_singleton
    {name : EvmYul.Identifier} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (hFresh : store.lookup (identName name) = none) :
    EvmYul.Yul.checkDeclaration (.Ok shared store) [name] = .ok () := by
  have hNoDup : ([name] : List EvmYul.Identifier).Nodup := by simp
  have hFirstDup :
      EvmYul.Yul.firstDuplicate? ([name] : List EvmYul.Identifier) = none :=
    StoreDomainExact.firstDuplicate?_none_of_nodup [name] hNoDup
  have hFirstDecl :
      EvmYul.Yul.firstDeclared? (.Ok shared store)
          ([name] : List EvmYul.Identifier) = none := by
    unfold EvmYul.Yul.firstDeclared?
    apply List.find?_eq_none.mpr
    intro n hMem
    simp only [List.mem_singleton] at hMem
    subst hMem
    have hLookupNone :
        (.Ok shared store : State).lookup? n = none := by
      simpa [EvmYul.Yul.State.lookup?, identName] using hFresh
    simp [hLookupNone]
  simp [EvmYul.Yul.checkDeclaration, hFirstDup, hFirstDecl]

/--
Imported semantics of `exec fuel.succ (.Let [name] none) state` when the
name is not already declared in the store.
-/
theorem exec_let_single_none_succ_of_fresh (fuel : Nat)
    (codeOverride : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier)
    (hFresh : store.lookup (identName name) = none) :
    EvmYul.Yul.exec fuel.succ (.Let [name] none) codeOverride
        (.Ok shared store) =
      .ok ((.Ok shared store : State).zeroFill [name]) := by
  rw [Imported.exec_let_none_succ fuel [name] codeOverride
    (.Ok shared store)]
  rw [checkDeclaration_ok_singleton (shared := shared) hFresh]

/--
**Finmap simplification**: `restrictVarStore (store.insert k v) store = store`
when `k` is fresh in `store`. Used to clean up the imported post-state after
a Let-introduced name gets restricted away by the surrounding block scope.
-/
theorem restrictVarStore_insert_of_fresh
    (store : EvmYul.Yul.VarStore) (k : EvmYul.Identifier) (v : Word)
    (hFresh : store.lookup k = none) :
    EvmYul.Yul.State.restrictVarStore (store.insert k v) store = store := by
  apply Finmap.ext_lookup
  intro k'
  unfold EvmYul.Yul.State.restrictVarStore
  by_cases hEq : k' = k
  · -- Use rw instead of subst to preserve both k and k'
    rw [hEq]
    rw [FinmapFacts.lookup_sdiff_of_lookup_some
      (store := store.insert k v)
      (scope := (store.insert k v).sdiff store)
      (key := k)
      (value := v) (by
        rw [FinmapFacts.lookup_sdiff_of_lookup_none _ _ _ hFresh]
        simp [Finmap.lookup_insert])]
    exact hFresh.symm
  · rw [FinmapFacts.lookup_sdiff_of_lookup_none]
    · rw [Finmap.lookup_insert_of_ne (a := k) (a' := k') (b := v) store hEq]
    · cases hLookup : store.lookup k' with
      | none =>
          rw [FinmapFacts.lookup_sdiff_of_lookup_none _ _ _ hLookup]
          rw [Finmap.lookup_insert_of_ne (a := k) (a' := k') (b := v) store hEq]
          exact hLookup
      | some w =>
          exact FinmapFacts.lookup_sdiff_of_lookup_some _ _ _ hLookup

/--
**State-level form** of `restrictVarStore_insert_of_fresh`:
`((Ok shared store).insert k v).restrictStoreTo (Ok shared store).store =
 Ok shared store` when `k` is fresh in `store`. This is the form that
appears in the imported-side reduction of `.Block [.Let [name] (some (.Lit
value))]`, ready for direct use in the corresponding bridge leaf.
-/
theorem restrictStoreTo_insert_of_fresh
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (k : EvmYul.Identifier) (v : Word)
    (hFresh : store.lookup k = none) :
    ((EvmYul.Yul.State.Ok shared store).insert k v).restrictStoreTo
        (EvmYul.Yul.State.Ok shared store).store =
      (EvmYul.Yul.State.Ok shared store : State) := by
  show ((EvmYul.Yul.State.Ok shared store).insert k v).restrictStoreTo
      store = (EvmYul.Yul.State.Ok shared store)
  unfold EvmYul.Yul.State.restrictStoreTo
  unfold EvmYul.Yul.State.insert
  simp [restrictVarStore_insert_of_fresh store k v hFresh]

/--
Imported semantics of `exec fuel.succ.succ (.Let [name] (some (.Lit value)))
state` when the name is not already declared in the store. Returns the
state with `name → value` inserted.
-/
theorem exec_let_single_some_lit_succ_succ_of_fresh (fuel : Nat)
    (codeOverride : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) (value : Word)
    (hFresh : store.lookup (identName name) = none) :
    EvmYul.Yul.exec fuel.succ.succ (.Let [name] (some (.Lit value)))
        codeOverride (.Ok shared store) =
      .ok ((.Ok shared store : State).insert name value) := by
  rw [Imported.exec_let_lit_succ fuel.succ [name] value codeOverride
    (.Ok shared store)]
  rw [checkDeclaration_ok_singleton (shared := shared) hFresh]
  have hEvalValues :
      EvmYul.Yul.evalValues fuel.succ (.Lit value) codeOverride
          (.Ok shared store) =
        .ok ((.Ok shared store : State), [value]) := by
    simp [EvmYul.Yul.evalValues, Imported.eval_lit_succ]
  rw [hEvalValues]
  simp [EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.insert]

/--
Imported semantics of `.Block [.Let [name] (some (.Lit value))]` for a fresh
single name. The post-state has `name → value` inserted then restricted away
via the outer block's `restrictStoreTo state.store` (since `name ∉ store`).

Composes:
1. `exec_block_cons_succ`: outer block reduces to execSeq + restrictStoreTo
2. `execSeq_cons_ok_result_succ` with `exec_let_single_some_lit_succ_succ_of_fresh`
-/
theorem exec_block_let_single_some_lit_succ_succ_succ_succ_of_fresh (fuel : Nat)
    (codeOverride : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) (value : Word)
    (hFresh : store.lookup (identName name) = none) :
    EvmYul.Yul.exec fuel.succ.succ.succ.succ
        (.Block [.Let [name] (some (.Lit value))]) codeOverride
        (.Ok shared store) =
      .ok (((.Ok shared store : State).insert name value).restrictStoreTo
        (.Ok shared store : State).store) := by
  rw [Imported.exec_block_cons_succ]
  rw [Imported.execSeq_cons_ok_result_succ
    (hHead := exec_let_single_some_lit_succ_succ_of_fresh fuel codeOverride
      shared store name value hFresh)
    (hTail := Imported.execSeq_nil_succ fuel.succ codeOverride
      ((.Ok shared store : State).insert name value))]

-- TODO(next session): zeroFill_restrictStoreTo_of_fresh — the lemma stating
-- that for a name not in the store domain, (zeroFill [name] state).restrictStoreTo
-- state.store = state. Needed to simplify the outer-block-let-single-none result.
-- Likely requires FinmapFacts about inserting then restricting by the original
-- domain. Without this, `exec_block_let_single_none_succ_succ_succ_of_fresh`
-- yields a slightly awkward post-state form rather than the clean `state`.

/--
Imported semantics of `.Block [.Let [name] none]` for a fresh single name.

Composes:
1. `exec_block_cons_succ`: outer block reduces to execSeq + restrictStoreTo
2. `execSeq_cons_ok_result_succ` with our `exec_let_single_none_succ_of_fresh`
3. Restrict-to-self after zeroFill drops the new name (since not in original
   domain), yielding the original state.
-/
theorem exec_block_let_single_none_succ_succ_succ_of_fresh (fuel : Nat)
    (codeOverride : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier)
    (hFresh : store.lookup (identName name) = none) :
    EvmYul.Yul.exec fuel.succ.succ.succ (.Block [.Let [name] none])
        codeOverride (.Ok shared store) =
      .ok (((.Ok shared store : State).zeroFill [name]).restrictStoreTo
        (.Ok shared store : State).store) := by
  rw [Imported.exec_block_cons_succ]
  rw [Imported.execSeq_cons_ok_result_succ
    (hHead := exec_let_single_none_succ_of_fresh fuel codeOverride shared
      store name hFresh)
    (hTail := Imported.execSeq_nil_succ fuel codeOverride
      ((.Ok shared store : State).zeroFill [name]))]

-- TODO(next session): sourceResultBlockSoundWhenAt_if_zero_empty —
-- the imported helper `exec_block_if_zero_empty_succ_succ_succ_succ` is
-- proved, but the bridge leaf's low-fuel OutOfFuel branches (fuel = 2 and
-- fuel = 3) don't reduce with `simp [exec, execSeq, exec]`. The `.If`
-- constructor has multiple unfolding layers; the simp set needs to cover
-- the .If branch of exec specifically (perhaps via `EvmYul.Yul.exec.eq_def`
-- match unfolding) and the eval-cond at low fuel.

/--
Imported `evalArgs` on a singleton-variable argument with successful lookup.
-/
theorem evalArgs_singleton_var_reverse_ok_eq
    {fuel : Nat} {name : EvmYul.Identifier}
    {codeOverride : Option AstContract}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {value : Word}
    (hLookup : store.lookup (identName name) = some value) :
    EvmYul.Yul.evalArgs fuel.succ.succ.succ [.Var name] codeOverride
        (.Ok shared store) =
      .ok (.Ok shared store, [value]) := by
  have hStateLookup :
      (.Ok shared store : State).lookup? name = some value :=
    BridgeFacts.lookup?_ok (shared := shared) hLookup
  have hEvalValues :
      EvmYul.Yul.evalValues fuel.succ.succ (.Var name) codeOverride
          (.Ok shared store) =
        .ok (.Ok shared store, [value]) := by
    rw [EvmYul.Yul.evalValues]
    simp [hStateLookup]
  exact
    BridgeFacts.evalArgs_singleton_of_evalValues_single hEvalValues

/--
Imported semantics of `evalArgs` for a singleton-var with lookup failure.
Returns the `UnknownIdentifier` error.
-/
theorem evalArgs_singleton_var_reverse_error_of_none
    {fuel : Nat} {name : EvmYul.Identifier}
    {codeOverride : Option AstContract}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    (hFresh : store.lookup (identName name) = none) :
    EvmYul.Yul.evalArgs fuel.succ.succ.succ [.Var name] codeOverride
        (.Ok shared store) =
      .error (.UnknownIdentifier name) := by
  rw [Imported.evalArgs_cons_succ]
  rw [Imported.eval_var_succ]
  have hStateLookup :
      (.Ok shared store : State).lookup? name = none := by
    show (.Ok shared store : State).lookup? name = none
    simp only [EvmYul.Yul.State.lookup?]
    show store.lookup (identName name) = none
    exact hFresh
  rw [hStateLookup]
  simp [EvmYul.Yul.evalTail]

/--
Singleton-variable argument case for the source-tower argument-eval bridge.
-/
theorem sourceArgEvalRegular_singleton_var
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {name : EvmYul.Identifier}
    {codeOverride : Option AstContract}
    (hScope : ctx.scope = layout)
    (hMem : identName name ∈ layout) :
    SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel.succ.succ.succ [.Var name] codeOverride []
      [Locals.Expr.var (identName name)] := by
  refine ⟨hScope, by simp, ?_⟩
  intro source sourceAfter compiler values hInitial hImpEval
  simp only [List.reverse_singleton] at hImpEval
  cases hInitial with
  | @ok shared store _ hShared hVars =>
      cases hLookup : store.lookup (identName name) with
      | none =>
          exfalso
          have hEvalArgsErr :=
            evalArgs_singleton_var_reverse_error_of_none
              (fuel := argFuel) (codeOverride := codeOverride)
              (shared := shared) (store := store) (name := name) hLookup
          rw [hEvalArgsErr] at hImpEval
          cases hImpEval
      | some value =>
          have hEvalArgsOk :
              EvmYul.Yul.evalArgs argFuel.succ.succ.succ [.Var name]
                  codeOverride (.Ok shared store) =
                .ok ((.Ok shared store : State), [value]) :=
            evalArgs_singleton_var_reverse_ok_eq (fuel := argFuel) hLookup
          rw [hEvalArgsOk] at hImpEval
          injection hImpEval with hPair
          have hStateEq : sourceAfter = (.Ok shared store : State) :=
            (Prod.mk.injEq _ _ _ _).mp hPair.symm |>.1
          have hValuesRev : values.reverse = [value] :=
            (Prod.mk.injEq _ _ _ _).mp hPair.symm |>.2
          subst hStateEq
          have hValues : values = [value] := by
            have := congrArg List.reverse hValuesRev
            simpa using this
          subst hValues
          refine ⟨compiler, 1, ctx, ?_, hScope, ?_, ?_⟩
          · simp [Functions.Source.Block.runOpen]
          · exact SourceStateRel.ok hShared hVars
          · intro i hi hv
            match i, hi, hv with
            | 0, _, _ =>
                refine ⟨compiler, ?_⟩
                have hVarsName :
                    compiler.vars (identName name) = some value := by
                  have hRel := hVars (identName name) hMem
                  rw [hRel]
                  exact hLookup
                simp [Locals.Source.Expr.evalOne,
                  Locals.Source.Expr.eval, hVarsName]

/--
Imported `evalArgs` on a pair-of-variables when both lookups succeed.

Uses `BridgeFacts.evalArgs_pair_of_evalValues_single` with two evalValues
facts derived from the respective lookups.  Args = [.Var leftName, .Var rightName]
in SOURCE order, passed as reverse to evalArgs.
-/
theorem evalArgs_pair_var_var_reverse_ok_eq
    {fuel : Nat} {leftName rightName : EvmYul.Identifier}
    {codeOverride : Option AstContract}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {leftValue rightValue : Word}
    (hLeft : store.lookup (identName leftName) = some leftValue)
    (hRight : store.lookup (identName rightName) = some rightValue) :
    EvmYul.Yul.evalArgs fuel.succ.succ.succ.succ.succ
        [.Var rightName, .Var leftName] codeOverride
        (.Ok shared store) =
      .ok ((.Ok shared store : State), [rightValue, leftValue]) := by
  have hRightStateLookup :
      (.Ok shared store : State).lookup? rightName = some rightValue :=
    BridgeFacts.lookup?_ok (shared := shared) hRight
  have hLeftStateLookup :
      (.Ok shared store : State).lookup? leftName = some leftValue :=
    BridgeFacts.lookup?_ok (shared := shared) hLeft
  have hRightEvalValues :
      EvmYul.Yul.evalValues fuel.succ.succ.succ.succ (.Var rightName)
          codeOverride (.Ok shared store) =
        .ok (.Ok shared store, [rightValue]) := by
    rw [EvmYul.Yul.evalValues]
    simp [hRightStateLookup]
  have hLeftEvalValues :
      EvmYul.Yul.evalValues fuel.succ.succ (.Var leftName)
          codeOverride (.Ok shared store) =
        .ok (.Ok shared store, [leftValue]) := by
    rw [EvmYul.Yul.evalValues]
    simp [hLeftStateLookup]
  exact
    BridgeFacts.evalArgs_pair_of_evalValues_single
      (left := .Var leftName) (right := .Var rightName)
      hRightEvalValues hLeftEvalValues

/--
**Compositional cons rule for imported `evalArgs`** on the reverse-source list.
Given that `evalArgs fuel args state = .ok (state, values)` (the tail's
evaluation succeeded leaving state unchanged), prepending one variable that
looks up successfully extends the result by one value at the front.

This is the imported-side ancestor of every reversed-list `evalArgs_*_var_*`
evaluation lemma. Compose it `k` times to handle any var-list of length `k`,
avoiding the previous per-length enumeration.

The fuel needs `+2` per cons: one for the outer `evalArgs.succ` matching the
cons constructor, one for the `evalTail` inside.
-/
theorem Imported_evalArgs_cons_var_state_preserved
    (fuel : Nat) (name : EvmYul.Identifier) (args : List AstExpr)
    (codeOverride : Option AstContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (value : Word) (values : List Word)
    (hLookup : store.lookup (identName name) = some value)
    (hArgs : EvmYul.Yul.evalArgs fuel args codeOverride (.Ok shared store) =
      .ok (.Ok shared store, values)) :
    EvmYul.Yul.evalArgs fuel.succ.succ (.Var name :: args) codeOverride
        (.Ok shared store) =
      .ok (.Ok shared store, value :: values) := by
  have hStateLookup :
      (.Ok shared store : State).lookup? name = some value :=
    BridgeFacts.lookup?_ok (shared := shared) hLookup
  rw [Imported.evalArgs_cons_succ]
  rw [Imported.eval_var_succ]
  rw [hStateLookup]
  simp [EvmYul.Yul.evalTail, EvmYul.Yul.cons', hArgs]

/--
**Compositional cons rule for imported `evalArgs`** on the reverse-source list,
with `.Lit` prepended. Like the var case, this lets us compose evaluation of
any lit-containing arg list by repeated cons applications.
-/
theorem Imported_evalArgs_cons_lit_state_preserved
    (fuel : Nat) (value : Word) (args : List AstExpr)
    (codeOverride : Option AstContract)
    (state : State) (values : List Word)
    (hArgs : EvmYul.Yul.evalArgs fuel args codeOverride state =
      .ok (state, values)) :
    EvmYul.Yul.evalArgs fuel.succ.succ (.Lit value :: args) codeOverride state =
      .ok (state, value :: values) := by
  rw [Imported.evalArgs_cons_succ]
  rw [Imported.eval_lit_succ]
  simp [EvmYul.Yul.evalTail, EvmYul.Yul.cons', hArgs]

/--
**Length-preservation for imported `evalArgs`**: a successful `evalArgs n xs`
produces a values list of the same length as `xs`. This is a structural
property of `evalArgs` (each input expression contributes exactly one value).

The proof is by induction on `xs`, generalizing over the fuel, input/output
states, and value list. Each recursive `evalArgs` step consumes one input
expression and emits exactly one value via `eval` + `cons'`.

This is the substrate the cons/snoc rules for `SourceArgEvalRegular` need to
make the index analysis go through: the bridge's `lowerArgs.length = args.length`
equation lifts to `lowerArgs.length = values.length` via this lemma.
-/
theorem Imported_evalArgs_length :
    ∀ (n : Nat) (xs : List AstExpr) (codeOverride : Option AstContract)
      (state s : EvmYul.Yul.State) (vs : List Word),
      EvmYul.Yul.evalArgs n xs codeOverride state = .ok (s, vs) →
      vs.length = xs.length := by
  intro n xs
  induction xs generalizing n with
  | nil =>
      intro codeOverride state s vs hEval
      cases n with
      | zero =>
          simp [EvmYul.Yul.evalArgs, EvmYul.Yul.Exception.OutOfFuel] at hEval
      | succ n =>
          simp [EvmYul.Yul.evalArgs] at hEval
          obtain ⟨_hState, hVs⟩ := hEval
          subst hVs
          rfl
  | cons head tail ih =>
      intro codeOverride state s vs hEval
      cases n with
      | zero =>
          simp [EvmYul.Yul.evalArgs, EvmYul.Yul.Exception.OutOfFuel] at hEval
      | succ n =>
          rw [Imported.evalArgs_cons_succ] at hEval
          cases hHead : EvmYul.Yul.eval n head codeOverride state with
          | error err =>
              rw [hHead] at hEval
              simp [EvmYul.Yul.evalTail] at hEval
          | ok pairHead =>
              rcases pairHead with ⟨sHead, vHead⟩
              rw [hHead] at hEval
              cases n with
              | zero =>
                  simp [EvmYul.Yul.evalTail] at hEval
              | succ m =>
                  -- evalTail (m+1) tail codeOverride (.ok (sHead, vHead))
                  --   = cons' vHead (evalArgs m tail codeOverride sHead)
                  cases hTail : EvmYul.Yul.evalArgs m tail codeOverride sHead with
                  | error err =>
                      simp [EvmYul.Yul.evalTail, hTail, EvmYul.Yul.cons']
                        at hEval
                  | ok pairTail =>
                      rcases pairTail with ⟨sTail, vsTail⟩
                      simp [EvmYul.Yul.evalTail, hTail, EvmYul.Yul.cons']
                        at hEval
                      rcases hEval with ⟨_hState, hVs⟩
                      have hTailLen :=
                        ih m codeOverride sHead sTail vsTail hTail
                      rw [← hVs]
                      simp [hTailLen]

/--
**Bidirectional reduction for var-cons**: `evalArgs (n+2) (.Var name :: args) state`
reduces to either `cons'` over `evalArgs n args state` (when lookup succeeds)
or to `.error (.UnknownIdentifier name)` (when lookup fails). This is the
inverse-form of `Imported_evalArgs_cons_var_state_preserved` for proofs that
need to recover the tail-evaluation from a cons-result.
-/
theorem Imported_evalArgs_cons_var_succ_succ_unfold
    (fuel : Nat) (name : EvmYul.Identifier) (args : List AstExpr)
    (codeOverride : Option AstContract) (state : State) :
    EvmYul.Yul.evalArgs fuel.succ.succ (.Var name :: args) codeOverride state =
      match state.lookup? name with
      | some value =>
          EvmYul.Yul.cons' value
            (EvmYul.Yul.evalArgs fuel args codeOverride state)
      | none => .error (.UnknownIdentifier name) := by
  rw [Imported.evalArgs_cons_succ]
  rw [Imported.eval_var_succ]
  cases hLookup : state.lookup? name with
  | none => simp [EvmYul.Yul.evalTail]
  | some value => simp [EvmYul.Yul.evalTail]

/--
**Bidirectional reduction**: `evalArgs (n+2) (.Lit value :: args) state`
reduces to a `cons'` over `evalArgs n args state`. This is the inverse-form
of `Imported_evalArgs_cons_lit_state_preserved` — given a cons-result we can
recover the tail-evaluation.
-/
theorem Imported_evalArgs_cons_lit_succ_succ_unfold
    (fuel : Nat) (value : Word) (args : List AstExpr)
    (codeOverride : Option AstContract) (state : State) :
    EvmYul.Yul.evalArgs fuel.succ.succ (.Lit value :: args) codeOverride state =
      EvmYul.Yul.cons' value
        (EvmYul.Yul.evalArgs fuel args codeOverride state) := by
  rw [Imported.evalArgs_cons_succ]
  rw [Imported.eval_lit_succ]
  simp [EvmYul.Yul.evalTail]

/--
Projection: `SourceResultBlockSoundWhenAt` implies `ctx.scope = layout`.

Used by recursive bridge case-analysis: when destructuring an outer bridge
to apply a leaf, this projection gives the scope-layout equation that the
leaves themselves require.
-/
theorem SourceResultBlockSoundWhenAt.scope_eq
    {cfg : StateRelConfig} {layout outcomeLayout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {sourceFuel : Nat} {sourceStmts : List AstStmt}
    {codeOverride : Option AstContract} {lowerBlock : Functions.Block}
    {allowed : Except Exception State → Prop}
    (hBridge :
      SourceResultBlockSoundWhenAt cfg layout outcomeLayout terminalRel
        revertRel prim program ctx sourceFuel sourceStmts codeOverride
        lowerBlock allowed) :
    ctx.scope = layout :=
  hBridge.1

/--
Projection: the `SourceArgEvalRegular` bridge implies `ctx.scope = layout`.
Useful for the cons rule's case analysis on the post-tail ctx.
-/
theorem SourceArgEvalRegular.scope_eq
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout argLayout : List Name}
    {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {args : List AstExpr}
    {codeOverride : Option AstContract}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    (hBridge :
      SourceArgEvalRegular cfg prim program layout argLayout ctx argFuel args
        codeOverride pre lowerArgs) :
    ctx.scope = layout :=
  hBridge.1

/--
Projection: the `SourceArgEvalRegular` bridge implies
`lowerArgs.length = args.length`.  Used by cons rules to derive the
lowered-args length from the bridge structure.
-/
theorem SourceArgEvalRegular.length_eq
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout argLayout : List Name}
    {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {args : List AstExpr}
    {codeOverride : Option AstContract}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    (hBridge :
      SourceArgEvalRegular cfg prim program layout argLayout ctx argFuel args
        codeOverride pre lowerArgs) :
    lowerArgs.length = args.length :=
  hBridge.2.1

/--
Empty-prelude version of `SourceArgEvalRegular`: when the prelude is empty,
the source-tower side is just `runOpen ctx 1 ⟨[]⟩ compiler = .ok (regular
compiler, ctx)`, which is independent of the args.  Useful for the
`evalArgs` cases where the lowerer produces no prelude (single literals,
direct variable references) and the bridge content reduces to evaluating
`lowerArgs` directly in the input state.
-/
theorem SourceArgEvalRegular.empty_prelude_iff
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name}
    {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {args : List AstExpr}
    {codeOverride : Option AstContract}
    {lowerArgs : List (Locals.Expr 1)}
    (hScope : ctx.scope = layout)
    (hLen : lowerArgs.length = args.length)
    (hSemantics :
      ∀ {source sourceAfter : State} {compiler : Objects.Source.State}
        {values : List Word},
        SourceStateRel cfg layout source compiler →
        EvmYul.Yul.evalArgs argFuel args.reverse codeOverride source =
          .ok (sourceAfter, values.reverse) →
        SourceStateRel cfg layout sourceAfter compiler ∧
        (∀ i (_hi : i < lowerArgs.length) (_hv : i < values.length),
          ∃ valueStateAfter : Locals.Source.State,
            Locals.Source.Expr.evalOne prim
                (lowerArgs[i]'_hi) compiler =
              .ok (valueStateAfter, values[i]'_hv))) :
    SourceArgEvalRegular cfg prim program layout layout ctx argFuel args
      codeOverride [] lowerArgs := by
  refine ⟨hScope, hLen, ?_⟩
  intro source sourceAfter compiler values hInitial hImpEval
  obtain ⟨hStateAfter, hValues⟩ := hSemantics hInitial hImpEval
  refine ⟨compiler, 1, ctx, ?_, hScope, hStateAfter, ?_⟩
  · simp [Functions.Source.Block.runOpen]
  · intro i hi hv
    exact hValues i hi hv

/--
Definitional unfolding for `Locals.Source.Expr.eval` on literal expressions.

Useful in source-tower bridge proofs that need to derive the value of a
lowered literal argument from a `Locals.Expr.lit value` lowering.
-/
theorem Locals_Source_Expr_eval_lit
    (prim : Objects.Source.PrimitiveSemantics)
    (state : Locals.Source.State) (value : Word) :
    Locals.Source.Expr.eval prim (Locals.Expr.lit value) state =
      .ok (state, [value]) := rfl

/--
Definitional unfolding for `Locals.Source.Expr.evalOne` on literal expressions.
-/
theorem Locals_Source_Expr_evalOne_lit
    (prim : Objects.Source.PrimitiveSemantics)
    (state : Locals.Source.State) (value : Word) :
    Locals.Source.Expr.evalOne prim (Locals.Expr.lit value) state =
      .ok (state, value) := rfl

/--
Variable evaluation with successful store lookup: `Locals.Source.Expr.eval`
on `.var name` returns the value stored at `name` (when defined).
-/
theorem Locals_Source_Expr_eval_var_of_lookup
    (prim : Objects.Source.PrimitiveSemantics)
    (state : Locals.Source.State) (name : Name) (value : Word)
    (hLookup : state.vars name = some value) :
    Locals.Source.Expr.eval prim (Locals.Expr.var name) state =
      .ok (state, [value]) := by
  simp [Locals.Source.Expr.eval, hLookup]

/--
Variable single-value evaluation with successful lookup.
-/
theorem Locals_Source_Expr_evalOne_var_of_lookup
    (prim : Objects.Source.PrimitiveSemantics)
    (state : Locals.Source.State) (name : Name) (value : Word)
    (hLookup : state.vars name = some value) :
    Locals.Source.Expr.evalOne prim (Locals.Expr.var name) state =
      .ok (state, value) := by
  simp [Locals.Source.Expr.evalOne, Locals.Source.Expr.eval, hLookup]

/--
Inserting a name outside `scope` then restricting back to `scope` is the
same as just restricting (the inserted name is filtered out).

This is the algebraic fact that makes `let_` declarations inside a block
"disappear" at the scoped boundary: a fresh local introduced inside the
block doesn't leak into the outer scope.
-/
theorem Locals_Source_Store_insert_restrictTo_of_not_mem
    {scope : List Name} (store : Locals.Source.Store)
    (name : Name) (value : Word) (hNotMem : name ∉ scope) :
    Locals.Source.Store.restrictTo scope
        (Locals.Source.Store.insert store name value) =
      Locals.Source.Store.restrictTo scope store := by
  funext key
  by_cases hMemKey : key ∈ scope
  · have hNe : key ≠ name := by
      intro hEq
      exact hNotMem (hEq ▸ hMemKey)
    simp [Locals.Source.Store.restrictTo, hMemKey,
      Locals.Source.Store.insert_of_ne hNe]
  · simp [Locals.Source.Store.restrictTo, hMemKey]

/--
State-level version of `Locals_Source_Store_insert_restrictTo_of_not_mem`.
-/
theorem Locals_Source_State_insert_restrictTo_of_not_mem
    {scope : List Name} (state : Locals.Source.State)
    (name : Name) (value : Word) (hNotMem : name ∉ scope) :
    (state.insert name value).restrictTo scope = state.restrictTo scope := by
  simp [Locals.Source.State.restrictTo, Locals.Source.State.insert,
    Locals_Source_Store_insert_restrictTo_of_not_mem _ name value hNotMem]

/--
Source-tower `Block.runOpen` on a single `let_ name (.var src)` statement
when `src` is in scope (returns the looked-up value).
-/
theorem Functions_Source_Block_runOpen_singleton_let_var
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (name src : Name) (value : Word)
    (hLookup : state.vars src = some value) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ.succ
        { stmts := [Functions.Stmt.let_ name (Locals.Expr.var src)] }
        state =
      .ok (Functions.Source.Outcome.regular (state.insert name value),
        { ctx with scope := name :: ctx.scope }) := by
  simp [Functions.Source.Block.runOpen, Functions.Source.Stmt.run,
    Locals.Source.Expr.evalOne, Locals.Source.Expr.eval, hLookup,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular]

/--
Source-tower `Block.runOpen` on a single `let_ name (.lit value)` statement
evaluates to inserting the literal value at the new name, extending the
scope.
-/
theorem Functions_Source_Block_runOpen_singleton_let_lit
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (name : Name) (value : Word) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ.succ
        { stmts := [Functions.Stmt.let_ name (Locals.Expr.lit value)] }
        state =
      .ok (Functions.Source.Outcome.regular (state.insert name value),
        { ctx with scope := name :: ctx.scope }) := by
  simp [Functions.Source.Block.runOpen, Functions.Source.Stmt.run,
    Locals.Source.Expr.evalOne, Locals.Source.Expr.eval,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular]

/--
Source-tower `vars` lookup via `SourceStoreRel`: if a name is in scope and
the imported store has a successful lookup, then the source-tower `vars`
agrees.
-/
theorem SourceStoreRel.vars_eq_some_of_layout_lookup
    {layout : List Name} {store : EvmYul.Yul.VarStore}
    {vars : Locals.Source.Store} {name : Name} {value : Word}
    (hRel : SourceStoreRel layout store vars)
    (hMem : name ∈ layout)
    (hLookup : store.lookup name = some value) :
    vars name = some value := by
  rw [hRel name hMem]
  exact hLookup

/--
Source-tower `Block.runOpen` on `stmt :: rest` when the head statement
returns a break outcome: the tail is short-circuited; result is the head
outcome with the original ctx.
-/
theorem Functions_Source_Block_runOpen_cons_brk
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hStmt :
      Functions.Source.Stmt.run prim program ctx fuel stmt state =
        .ok (Functions.Source.Outcome.brk stateAfter, ctx')) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ
        ⟨stmt :: rest⟩ state =
      .ok (Functions.Source.Outcome.brk stateAfter, ctx) := by
  simp [Functions.Source.Block.runOpen, hStmt,
    Functions.Source.Outcome.brk, Locals.Source.Outcome.brk]

/--
Source-tower `Block.runOpen` on `stmt :: rest` when the head statement
returns a continue outcome.
-/
theorem Functions_Source_Block_runOpen_cons_cont
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hStmt :
      Functions.Source.Stmt.run prim program ctx fuel stmt state =
        .ok (Functions.Source.Outcome.cont stateAfter, ctx')) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ
        ⟨stmt :: rest⟩ state =
      .ok (Functions.Source.Outcome.cont stateAfter, ctx) := by
  simp [Functions.Source.Block.runOpen, hStmt,
    Functions.Source.Outcome.cont, Locals.Source.Outcome.cont]

/--
Source-tower `Block.runOpen` on `stmt :: rest` when the head statement
returns a leave outcome.
-/
theorem Functions_Source_Block_runOpen_cons_leave
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hStmt :
      Functions.Source.Stmt.run prim program ctx fuel stmt state =
        .ok (Functions.Source.Outcome.leave stateAfter, ctx')) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ
        ⟨stmt :: rest⟩ state =
      .ok (Functions.Source.Outcome.leave stateAfter, ctx) := by
  simp [Functions.Source.Block.runOpen, hStmt,
    Functions.Source.Outcome.leave, Locals.Source.Outcome.leave]

/--
Source-tower `Block.runOpen` on `stmt :: rest` when the head statement
returns a halt outcome.
-/
theorem Functions_Source_Block_runOpen_cons_halt
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    {kind : Assembly.HaltKind}
    (hStmt :
      Functions.Source.Stmt.run prim program ctx fuel stmt state =
        .ok (Functions.Source.Outcome.halt kind stateAfter, ctx')) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ
        ⟨stmt :: rest⟩ state =
      .ok (Functions.Source.Outcome.halt kind stateAfter, ctx) := by
  simp [Functions.Source.Block.runOpen, hStmt,
    Functions.Source.Outcome.halt, Locals.Source.Outcome.halt]

/--
Source-tower `Block.runOpen` on `stmt :: rest` when the head statement
returns regular: the rest is run from the post-head state with the
post-head ctx.

This is a key compositional fact for the block-list cons rule: regular
head outcomes pass through and the tail runs from where head left off.
-/
theorem Functions_Source_Block_runOpen_cons_regular
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hStmt :
      Functions.Source.Stmt.run prim program ctx fuel stmt state =
        .ok (Functions.Source.Outcome.regular stateAfter, ctx')) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ
        ⟨stmt :: rest⟩ state =
      Functions.Source.Block.runOpen prim program ctx' fuel ⟨rest⟩
        stateAfter := by
  simp [Functions.Source.Block.runOpen, hStmt,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular]

/--
Source-tower `Stmt.run` on `.let_ name (.lit value)` directly, without
wrapping in a block.  Returns regular with the inserted value and extended
scope.
-/
theorem Functions_Source_Stmt_run_let_lit
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (name : Name) (value : Word) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.let_ name (Locals.Expr.lit value)) state =
      .ok (Functions.Source.Outcome.regular (state.insert name value),
        { ctx with scope := name :: ctx.scope }) := by
  simp [Functions.Source.Stmt.run, Locals.Source.Expr.evalOne,
    Locals.Source.Expr.eval, Functions.Source.Outcome.regular,
    Locals.Source.Outcome.regular]

-- TODO: Functions_Source_Stmt_run_expr_lit/var — the Functions.Stmt.expr
-- constructor has a generic results arity that needs explicit instantiation;
-- a careful attempt would need to match the constructor's signature exactly.

/--
Source-tower `Stmt.run` on `.assign name (.lit value)` when the name is
already in the source store.
-/
theorem Functions_Source_Stmt_run_assign_lit
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (name : Name) (value : Word)
    (hContains : state.vars.contains name = true) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.assign name (Locals.Expr.lit value)) state =
      .ok (Functions.Source.Outcome.regular
        (state.withVars (Locals.Source.Store.insert state.vars name value)),
        ctx) := by
  simp [Functions.Source.Stmt.run, Locals.Source.Expr.evalOne,
    Locals.Source.Expr.eval, hContains, Functions.Source.Outcome.regular,
    Locals.Source.Outcome.regular]

/--
Source-tower `Stmt.run` on `.assign name (.var src)` when both are in scope.
-/
theorem Functions_Source_Stmt_run_assign_var_of_lookup
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (name src : Name) (value : Word)
    (hContains : state.vars.contains name = true)
    (hLookup : state.vars src = some value) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.assign name (Locals.Expr.var src)) state =
      .ok (Functions.Source.Outcome.regular
        (state.withVars (Locals.Source.Store.insert state.vars name value)),
        ctx) := by
  simp [Functions.Source.Stmt.run, Locals.Source.Expr.evalOne,
    Locals.Source.Expr.eval, hContains, hLookup,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular]

/--
`Outcome.regular state` has mode `.regular`. Used by `Block.runOpen`/`runScoped`
case-analysis on outcome mode after destructuring.
-/
theorem Functions_Source_Outcome_regular_mode
    (state : Functions.Source.State) :
    (Functions.Source.Outcome.regular state).mode = Locals.Source.Mode.regular := rfl

/--
`Outcome.brk state` has mode `.brk`.
-/
theorem Functions_Source_Outcome_brk_mode
    (state : Functions.Source.State) :
    (Functions.Source.Outcome.brk state).mode = Locals.Source.Mode.brk := rfl

/--
`Outcome.cont state` has mode `.cont`.
-/
theorem Functions_Source_Outcome_cont_mode
    (state : Functions.Source.State) :
    (Functions.Source.Outcome.cont state).mode = Locals.Source.Mode.cont := rfl

/--
`Outcome.leave state` has mode `.leave`.
-/
theorem Functions_Source_Outcome_leave_mode
    (state : Functions.Source.State) :
    (Functions.Source.Outcome.leave state).mode = Locals.Source.Mode.leave := rfl

/--
`Outcome.halt kind state` has mode `.halt kind`.
-/
theorem Functions_Source_Outcome_halt_mode
    (kind : Assembly.HaltKind) (state : Functions.Source.State) :
    (Functions.Source.Outcome.halt kind state).mode =
      Locals.Source.Mode.halt kind := rfl

/--
`Outcome.regular` is definitionally the outcome with `regular` mode at a
given state.
-/
theorem Functions_Source_Outcome_regular_state
    (state : Functions.Source.State) :
    (Functions.Source.Outcome.regular state).state = state := rfl

/--
`Outcome.brk` state projection.
-/
theorem Functions_Source_Outcome_brk_state
    (state : Functions.Source.State) :
    (Functions.Source.Outcome.brk state).state = state := rfl

/--
`Outcome.cont` state projection.
-/
theorem Functions_Source_Outcome_cont_state
    (state : Functions.Source.State) :
    (Functions.Source.Outcome.cont state).state = state := rfl

/--
`Outcome.leave` state projection.
-/
theorem Functions_Source_Outcome_leave_state
    (state : Functions.Source.State) :
    (Functions.Source.Outcome.leave state).state = state := rfl

/--
`Outcome.halt` state projection.
-/
theorem Functions_Source_Outcome_halt_state
    (kind : Assembly.HaltKind) (state : Functions.Source.State) :
    (Functions.Source.Outcome.halt kind state).state = state := rfl

-- TODO: Functions_Source_Block_runOpen_singleton_regular — the fuel=0 case
-- requires careful handling. For fuel.succ outer, the cons_regular reduction
-- gives Block.runOpen at fuel = inner stmt fuel. If inner stmt fuel = 0,
-- runOpen on [] returns invalid. Need a fuel-monotonicity adjustment or
-- restrict to fuel ≥ 1 inside.

/--
Source-tower `Stmt.run` on `.brk` when the context has a break scope.
-/
theorem Functions_Source_Stmt_run_brk_of_scope
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (breakScope : List Name)
    (hBreak : ctx.breakScope? = some breakScope) :
    Functions.Source.Stmt.run prim program ctx fuel
        Functions.Stmt.brk state =
      .ok (Functions.Source.Outcome.brk (state.restrictTo breakScope), ctx) := by
  simp [Functions.Source.Stmt.run, hBreak,
    Functions.Source.Outcome.brk, Locals.Source.Outcome.brk]

/--
Source-tower `Stmt.run` on `.cont` when the context has a continue scope.
-/
theorem Functions_Source_Stmt_run_cont_of_scope
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (contScope : List Name)
    (hCont : ctx.continueScope? = some contScope) :
    Functions.Source.Stmt.run prim program ctx fuel
        Functions.Stmt.cont state =
      .ok (Functions.Source.Outcome.cont (state.restrictTo contScope), ctx) := by
  simp [Functions.Source.Stmt.run, hCont,
    Functions.Source.Outcome.cont, Locals.Source.Outcome.cont]

/--
Source-tower `Stmt.run` on `.leave` when the context has a leave scope.
-/
theorem Functions_Source_Stmt_run_leave_of_scope
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (leaveScope : List Name)
    (hLeave : ctx.leaveScope? = some leaveScope) :
    Functions.Source.Stmt.run prim program ctx fuel
        Functions.Stmt.leave state =
      .ok (Functions.Source.Outcome.leave (state.restrictTo leaveScope), ctx) := by
  simp [Functions.Source.Stmt.run, hLeave,
    Functions.Source.Outcome.leave, Locals.Source.Outcome.leave]

/--
Source-tower `Stmt.run` on `.let_ name (.var src)` when `src` is in scope.
-/
theorem Functions_Source_Stmt_run_let_var_of_lookup
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (name src : Name) (value : Word)
    (hLookup : state.vars src = some value) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.let_ name (Locals.Expr.var src)) state =
      .ok (Functions.Source.Outcome.regular (state.insert name value),
        { ctx with scope := name :: ctx.scope }) := by
  simp [Functions.Source.Stmt.run, Locals.Source.Expr.evalOne,
    Locals.Source.Expr.eval, hLookup, Functions.Source.Outcome.regular,
    Locals.Source.Outcome.regular]

/--
Source-tower `Block.runOpen` on a single `assign name (.lit value)` statement
when the name is already in the source store.
-/
theorem Functions_Source_Block_runOpen_singleton_assign_lit
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (name : Name) (value : Word)
    (hContains : state.vars.contains name = true) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ.succ
        { stmts := [Functions.Stmt.assign name (Locals.Expr.lit value)] }
        state =
      .ok (Functions.Source.Outcome.regular
        (state.withVars
          (Locals.Source.Store.insert state.vars name value)),
        ctx) := by
  simp [Functions.Source.Block.runOpen, Functions.Source.Stmt.run,
    Locals.Source.Expr.evalOne, Locals.Source.Expr.eval, hContains,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular]

/--
`Block.runScoped` from `Block.runOpen` with a break outcome.
Abrupt outcomes pass through unchanged.
-/
theorem Functions_Source_Block_runScoped_of_runOpen_brk
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {block : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hRunOpen :
      Functions.Source.Block.runOpen prim program ctx fuel block state =
        .ok (Functions.Source.Outcome.brk stateAfter, ctx')) :
    Functions.Source.Block.runScoped prim program ctx block fuel state =
      .ok (Functions.Source.Outcome.brk stateAfter) := by
  simp [Functions.Source.Block.runScoped, hRunOpen,
    Functions.Source.Outcome.brk, Locals.Source.Outcome.brk]

/--
`Block.runScoped` from `Block.runOpen` with a continue outcome.
-/
theorem Functions_Source_Block_runScoped_of_runOpen_cont
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {block : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hRunOpen :
      Functions.Source.Block.runOpen prim program ctx fuel block state =
        .ok (Functions.Source.Outcome.cont stateAfter, ctx')) :
    Functions.Source.Block.runScoped prim program ctx block fuel state =
      .ok (Functions.Source.Outcome.cont stateAfter) := by
  simp [Functions.Source.Block.runScoped, hRunOpen,
    Functions.Source.Outcome.cont, Locals.Source.Outcome.cont]

/--
`Block.runScoped` from `Block.runOpen` with a leave outcome.
-/
theorem Functions_Source_Block_runScoped_of_runOpen_leave
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {block : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hRunOpen :
      Functions.Source.Block.runOpen prim program ctx fuel block state =
        .ok (Functions.Source.Outcome.leave stateAfter, ctx')) :
    Functions.Source.Block.runScoped prim program ctx block fuel state =
      .ok (Functions.Source.Outcome.leave stateAfter) := by
  simp [Functions.Source.Block.runScoped, hRunOpen,
    Functions.Source.Outcome.leave, Locals.Source.Outcome.leave]

/--
`Block.runScoped` from `Block.runOpen` with a halt outcome.
-/
theorem Functions_Source_Block_runScoped_of_runOpen_halt
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctx' : Functions.Source.Ctx}
    {block : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    {kind : Assembly.HaltKind}
    (hRunOpen :
      Functions.Source.Block.runOpen prim program ctx fuel block state =
        .ok (Functions.Source.Outcome.halt kind stateAfter, ctx')) :
    Functions.Source.Block.runScoped prim program ctx block fuel state =
      .ok (Functions.Source.Outcome.halt kind stateAfter) := by
  simp [Functions.Source.Block.runScoped, hRunOpen,
    Functions.Source.Outcome.halt, Locals.Source.Outcome.halt]

/--
`Block.runScoped` from `Block.runOpen` with a regular outcome.

When the underlying `runOpen` returns a regular outcome, `runScoped`
returns regular with the state restricted to the entry scope.  This is
the compositional decomposition: scoped execution = open execution +
scope-restriction.
-/
theorem Functions_Source_Block_runScoped_of_runOpen_regular
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx ctxAfter : Functions.Source.Ctx}
    {block : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hRunOpen :
      Functions.Source.Block.runOpen prim program ctx fuel block state =
        .ok (Functions.Source.Outcome.regular stateAfter, ctxAfter)) :
    Functions.Source.Block.runScoped prim program ctx block fuel state =
      .ok (Functions.Source.Outcome.regular
        (stateAfter.restrictTo ctx.scope)) := by
  simp [Functions.Source.Block.runScoped, hRunOpen,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular]

/--
Source-tower `vars` lookup via `SourceStateRel`: combines state destructuring
with the `SourceStoreRel.vars_eq_some_of_layout_lookup` fact.
-/
theorem SourceStateRel.vars_eq_some_of_layout_lookup
    {cfg : StateRelConfig} {layout : List Name}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {compiler : Objects.Source.State}
    {name : Name} {value : Word}
    (hRel : SourceStateRel cfg layout (.Ok shared store) compiler)
    (hMem : name ∈ layout)
    (hLookup : store.lookup name = some value) :
    compiler.vars name = some value := by
  cases hRel with
  | ok _ hVars => exact hVars.vars_eq_some_of_layout_lookup hMem hLookup

/--
State-level form of `Locals.Source.Store.insert_self`: looking up the
inserted name in `state.insert name value` returns `some value`.
-/
theorem Locals_Source_State_insert_self_lookup
    (state : Locals.Source.State) (name : Name) (value : Word) :
    (state.insert name value).vars name = some value := by
  simp [Locals.Source.State.insert]

/--
State-level form of `Locals.Source.Store.insert_of_ne`: looking up a
different name in `state.insert name value` returns the original lookup.
-/
theorem Locals_Source_State_insert_of_ne_lookup
    (state : Locals.Source.State) (name other : Name) (value : Word)
    (hNe : other ≠ name) :
    (state.insert name value).vars other = state.vars other := by
  simp [Locals.Source.State.insert,
    Locals.Source.Store.insert_of_ne hNe]

/--
Source-tower `Block.runScoped` on a single fresh `let_ name (.lit value)`:
the result is the input state restricted to the original scope.
-/
theorem Functions_Source_Block_runScoped_singleton_let_lit_fresh
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) (name : Name) (value : Word)
    (hFresh : name ∉ ctx.scope) :
    Functions.Source.Block.runScoped prim program ctx
        { stmts := [Functions.Stmt.let_ name (Locals.Expr.lit value)] }
        fuel.succ.succ state =
      .ok (Functions.Source.Outcome.regular
        (state.restrictTo ctx.scope)) := by
  simp [Functions.Source.Block.runScoped,
    Functions_Source_Block_runOpen_singleton_let_lit ctx fuel state name value,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular,
    Locals_Source_State_insert_restrictTo_of_not_mem _ name value hFresh]

/--
Block-list nil at `WhenFreshAt`: the empty statement list bridges trivially
at any outcome layout that matches the entry layout.  Derived from the
existing `sourceResultBlockSoundWhen_nil` via the standard adapter chain.

This is the block-field analog of the recursive bridge's nil case — the
generic compositional theorem that lets the bridge's `block` field reduce
to `_nil` when the statement list is empty.
-/
theorem sourceResultBlockSoundWhenAt_nil
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {sourceFuel : Nat} {codeOverride : Option AstContract}
    {allowed : Except Exception State → Prop}
    (hAllowed :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultRelatable sourceResult)
    (hScope : ctx.scope = layout) :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel [] codeOverride { stmts := [] } allowed :=
  sourceResultBlockSoundWhenAt_of_when
    (sourceResultBlockSoundWhen_nil hAllowed hScope)

/--
`Locals.Source.Store.empty` returns `none` for any name.
-/
theorem Locals_Source_Store_empty_lookup (name : Name) :
    Locals.Source.Store.empty name = none := rfl

/--
Source-tower `Stmt.run` on `.block body` delegates to `Block.runScoped` and
preserves the entry ctx. When the runScoped returns a regular outcome,
Stmt.run returns that outcome with the original ctx.
-/
theorem Functions_Source_Stmt_run_block_regular
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx : Functions.Source.Ctx}
    {body : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hRun :
      Functions.Source.Block.runScoped prim program ctx body fuel state =
        .ok (Functions.Source.Outcome.regular stateAfter)) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.block body) state =
      .ok (Functions.Source.Outcome.regular stateAfter, ctx) := by
  simp [Functions.Source.Stmt.run, hRun,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular]

/--
Source-tower `Stmt.run` on `.block body` with a brk outcome.
-/
theorem Functions_Source_Stmt_run_block_brk
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx : Functions.Source.Ctx}
    {body : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hRun :
      Functions.Source.Block.runScoped prim program ctx body fuel state =
        .ok (Functions.Source.Outcome.brk stateAfter)) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.block body) state =
      .ok (Functions.Source.Outcome.brk stateAfter, ctx) := by
  simp [Functions.Source.Stmt.run, hRun,
    Functions.Source.Outcome.brk, Locals.Source.Outcome.brk]

/--
Source-tower `Stmt.run` on `.block body` with a cont outcome.
-/
theorem Functions_Source_Stmt_run_block_cont
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx : Functions.Source.Ctx}
    {body : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hRun :
      Functions.Source.Block.runScoped prim program ctx body fuel state =
        .ok (Functions.Source.Outcome.cont stateAfter)) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.block body) state =
      .ok (Functions.Source.Outcome.cont stateAfter, ctx) := by
  simp [Functions.Source.Stmt.run, hRun,
    Functions.Source.Outcome.cont, Locals.Source.Outcome.cont]

/--
Source-tower `Stmt.run` on `.block body` with a leave outcome.
-/
theorem Functions_Source_Stmt_run_block_leave
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx : Functions.Source.Ctx}
    {body : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    (hRun :
      Functions.Source.Block.runScoped prim program ctx body fuel state =
        .ok (Functions.Source.Outcome.leave stateAfter)) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.block body) state =
      .ok (Functions.Source.Outcome.leave stateAfter, ctx) := by
  simp [Functions.Source.Stmt.run, hRun,
    Functions.Source.Outcome.leave, Locals.Source.Outcome.leave]

/--
Source-tower outcomes are equal iff their underlying state/mode components
match. Useful when inverting `Block.runScoped`/`runOpen` results.
-/
theorem Functions_Source_Outcome_regular_eq_iff
    {state1 state2 : Functions.Source.State} :
    Functions.Source.Outcome.regular state1 =
        Functions.Source.Outcome.regular state2 ↔ state1 = state2 := by
  constructor
  · intro h
    have : (Functions.Source.Outcome.regular state1).state =
        (Functions.Source.Outcome.regular state2).state := by
      rw [h]
    exact this
  · intro h
    rw [h]

/--
Different outcome constructors are not equal — used in case analysis to
rule out mismatched outcome shapes.
-/
theorem Functions_Source_Outcome_regular_ne_brk
    {s1 s2 : Functions.Source.State} :
    Functions.Source.Outcome.regular s1 ≠ Functions.Source.Outcome.brk s2 := by
  intro h
  have hMode : (Functions.Source.Outcome.regular s1).mode =
      (Functions.Source.Outcome.brk s2).mode := by rw [h]
  simp [Functions_Source_Outcome_regular_mode,
    Functions_Source_Outcome_brk_mode] at hMode

theorem Functions_Source_Outcome_regular_ne_cont
    {s1 s2 : Functions.Source.State} :
    Functions.Source.Outcome.regular s1 ≠ Functions.Source.Outcome.cont s2 := by
  intro h
  have hMode : (Functions.Source.Outcome.regular s1).mode =
      (Functions.Source.Outcome.cont s2).mode := by rw [h]
  simp [Functions_Source_Outcome_regular_mode,
    Functions_Source_Outcome_cont_mode] at hMode

theorem Functions_Source_Outcome_regular_ne_leave
    {s1 s2 : Functions.Source.State} :
    Functions.Source.Outcome.regular s1 ≠ Functions.Source.Outcome.leave s2 := by
  intro h
  have hMode : (Functions.Source.Outcome.regular s1).mode =
      (Functions.Source.Outcome.leave s2).mode := by rw [h]
  simp [Functions_Source_Outcome_regular_mode,
    Functions_Source_Outcome_leave_mode] at hMode

/--
**Mode-based outcome distinctness.** Two source-tower outcomes whose modes
differ cannot be equal. This is the compositional ancestor of every pairwise
distinctness lemma — instantiate it with concrete mode literals on each side
and let `decide`/`simp` discharge the mode inequality.
-/
theorem Functions_Source_Outcome_ne_of_mode_ne
    {o1 o2 : Functions.Source.Outcome} (h : o1.mode ≠ o2.mode) :
    o1 ≠ o2 := by
  intro hEq
  apply h
  rw [hEq]

/--
Contrapositive of `Functions_Source_Outcome_ne_of_mode_ne`: equal outcomes
have equal modes. Used to extract a mode equation from an outcome equation
during case analysis.
-/
theorem Functions_Source_Outcome_mode_eq_of_eq
    {o1 o2 : Functions.Source.Outcome} (h : o1 = o2) :
    o1.mode = o2.mode := by
  rw [h]

/--
Brk outcomes are equal iff their state components match.
-/
theorem Functions_Source_Outcome_brk_eq_iff
    {state1 state2 : Functions.Source.State} :
    Functions.Source.Outcome.brk state1 =
        Functions.Source.Outcome.brk state2 ↔ state1 = state2 := by
  constructor
  · intro h
    have : (Functions.Source.Outcome.brk state1).state =
        (Functions.Source.Outcome.brk state2).state := by
      rw [h]
    exact this
  · intro h
    rw [h]

/--
Cont outcomes are equal iff their state components match.
-/
theorem Functions_Source_Outcome_cont_eq_iff
    {state1 state2 : Functions.Source.State} :
    Functions.Source.Outcome.cont state1 =
        Functions.Source.Outcome.cont state2 ↔ state1 = state2 := by
  constructor
  · intro h
    have : (Functions.Source.Outcome.cont state1).state =
        (Functions.Source.Outcome.cont state2).state := by
      rw [h]
    exact this
  · intro h
    rw [h]

/--
Leave outcomes are equal iff their state components match.
-/
theorem Functions_Source_Outcome_leave_eq_iff
    {state1 state2 : Functions.Source.State} :
    Functions.Source.Outcome.leave state1 =
        Functions.Source.Outcome.leave state2 ↔ state1 = state2 := by
  constructor
  · intro h
    have : (Functions.Source.Outcome.leave state1).state =
        (Functions.Source.Outcome.leave state2).state := by
      rw [h]
    exact this
  · intro h
    rw [h]

/--
Halt outcomes are equal iff their kind and state components match.
-/
theorem Functions_Source_Outcome_halt_eq_iff
    {kind1 kind2 : Assembly.HaltKind}
    {state1 state2 : Functions.Source.State} :
    Functions.Source.Outcome.halt kind1 state1 =
        Functions.Source.Outcome.halt kind2 state2 ↔
      kind1 = kind2 ∧ state1 = state2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hMode : (Functions.Source.Outcome.halt kind1 state1).mode =
          (Functions.Source.Outcome.halt kind2 state2).mode := by
        rw [h]
      simp [Functions_Source_Outcome_halt_mode] at hMode
      exact hMode
    · have hState : (Functions.Source.Outcome.halt kind1 state1).state =
          (Functions.Source.Outcome.halt kind2 state2).state := by
        rw [h]
      exact hState
  · intro ⟨hKind, hState⟩
    rw [hKind, hState]

/--
Source-tower `Stmt.run` on `.block body` with a halt outcome.
-/
theorem Functions_Source_Stmt_run_block_halt
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {ctx : Functions.Source.Ctx}
    {body : Functions.Block} {fuel : Nat}
    {state stateAfter : Functions.Source.State}
    {kind : Assembly.HaltKind}
    (hRun :
      Functions.Source.Block.runScoped prim program ctx body fuel state =
        .ok (Functions.Source.Outcome.halt kind stateAfter)) :
    Functions.Source.Stmt.run prim program ctx fuel
        (Functions.Stmt.block body) state =
      .ok (Functions.Source.Outcome.halt kind stateAfter, ctx) := by
  simp [Functions.Source.Stmt.run, hRun,
    Functions.Source.Outcome.halt, Locals.Source.Outcome.halt]

/--
`Locals.Source.Store.insert` overrides existing values at the same name.
-/
theorem Locals_Source_Store_insert_override
    (store : Locals.Source.Store) (name : Name) (v1 v2 : Word) :
    Locals.Source.Store.insert (Locals.Source.Store.insert store name v1) name v2 =
      Locals.Source.Store.insert store name v2 := by
  funext key
  by_cases h : key = name
  · subst h
    simp [Locals.Source.Store.insert_self]
  · simp [Locals.Source.Store.insert_of_ne h]

/--
`state.vars` after `withVars vars'` is `vars'`.
-/
theorem Locals_Source_State_withVars_self
    (state : Locals.Source.State) (vars : Locals.Source.Store)
    (name : Name) :
    (state.withVars vars).vars name = vars name := rfl

/--
`state.withVars vars` projection: the new state has the given vars.
-/
theorem Locals_Source_State_withVars_vars
    (state : Locals.Source.State) (vars : Locals.Source.Store) :
    (state.withVars vars).vars = vars := rfl

/--
`state.withVars vars` projection: the shared state is unchanged.
-/
theorem Locals_Source_State_withVars_shared
    (state : Locals.Source.State) (vars : Locals.Source.Store) :
    (state.withVars vars).shared = state.shared := rfl

/--
`state.withShared shared` projection: the new state has the given shared.
-/
theorem Locals_Source_State_withShared_shared
    (state : Locals.Source.State) (shared : EvmYul.SharedState .EVM) :
    (state.withShared shared).shared = shared := rfl

/--
`state.withShared shared` projection: the vars are unchanged.
-/
theorem Locals_Source_State_withShared_vars
    (state : Locals.Source.State) (shared : EvmYul.SharedState .EVM) :
    (state.withShared shared).vars = state.vars := rfl

/--
Ctx scope projection after a structural update.
-/
theorem Functions_Source_Ctx_scope_with_scope
    (ctx : Functions.Source.Ctx) (s : List Name) :
    ({ ctx with scope := s } : Functions.Source.Ctx).scope = s := rfl

/--
Ctx breakScope? unchanged after scope update.
-/
theorem Functions_Source_Ctx_breakScope_with_scope
    (ctx : Functions.Source.Ctx) (s : List Name) :
    ({ ctx with scope := s } : Functions.Source.Ctx).breakScope? =
      ctx.breakScope? := rfl

/--
Ctx continueScope? unchanged after scope update.
-/
theorem Functions_Source_Ctx_continueScope_with_scope
    (ctx : Functions.Source.Ctx) (s : List Name) :
    ({ ctx with scope := s } : Functions.Source.Ctx).continueScope? =
      ctx.continueScope? := rfl

/--
Ctx leaveScope? unchanged after scope update.
-/
theorem Functions_Source_Ctx_leaveScope_with_scope
    (ctx : Functions.Source.Ctx) (s : List Name) :
    ({ ctx with scope := s } : Functions.Source.Ctx).leaveScope? =
      ctx.leaveScope? := rfl

/--
Source-tower `Block.runScoped` on the empty body at any positive fuel
returns regular with the state restricted to the entry scope.

Compositional consequence of `runOpen_nil` + `runScoped_of_runOpen_regular`.
-/
theorem Functions_Source_Block_runScoped_nil
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) :
    Functions.Source.Block.runScoped prim program ctx
        { stmts := [] } fuel.succ state =
      .ok (Functions.Source.Outcome.regular
        (state.restrictTo ctx.scope)) := by
  simp [Functions.Source.Block.runScoped, Functions.Source.Block.runOpen,
    Functions.Source.Outcome.regular, Locals.Source.Outcome.regular]

/--
The empty-block source-tower run at any sufficient fuel.

Useful compositional building block: shows that source-tower `Block.runOpen`
on an empty body returns `Outcome.regular state` for any positive fuel.
Generalizes the inline simp-unfolds scattered across the constructor-leaf
proofs above and below.
-/
theorem Functions_Source_Block_runOpen_nil
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.Source.State) :
    Functions.Source.Block.runOpen prim program ctx fuel.succ
        { stmts := [] } state =
      .ok (Functions.Source.Outcome.regular state, ctx) := by
  simp [Functions.Source.Block.runOpen]

/--
Monotonicity of the recursive bridge in the bound parameter: a bridge that
covers fuels up to `m` also covers fuels up to any smaller `n ≤ m`.

This is the structural fact that makes the bridge induction's recursive
hypothesis available at all smaller fuels: once you have the bridge at
`bound = k+1`, you can use it freely at any `sourceFuel ≤ k` for nested
constructs.
-/
theorem RecursiveSourceBridgeWhenUpToAt.mono
    {cfg : StateRelConfig}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {m n : Nat}
    (hLe : n ≤ m)
    (hBridge :
      RecursiveSourceBridgeWhenUpToAt cfg terminalRel revertRel prim program m) :
    RecursiveSourceBridgeWhenUpToAt cfg terminalRel revertRel prim program n :=
  ⟨fun hAllowed hFuel hScope =>
      hBridge.stmt hAllowed (Nat.le_trans hFuel hLe) hScope,
   fun hAllowed hFuel hScope =>
      hBridge.block hAllowed (Nat.le_trans hFuel hLe) hScope⟩

/--
Concatenation of generated preludes is itself a generated prelude.

This is the small algebraic fact that makes prelude composition work:
GeneratedPrelude is closed under `++`. Used by the cons rule for the
source-tower argument-eval bridge (the prelude of a composed bridge is the
concatenation of the component preludes).
-/
theorem GeneratedPrelude.append
    {pre suffix : List Functions.Stmt}
    (hPre : GeneratedPrelude pre)
    (hSuffix : GeneratedPrelude suffix) :
    GeneratedPrelude (pre ++ suffix) := by
  induction hPre with
  | nil => exact hSuffix
  | let_ hRest ih =>
      rename_i name expr rest
      exact GeneratedPrelude.let_ ih

/--
Generic adapter: any `SourceResultBlockSound` (no allowed filter, same outcome
layout) lifts to `SourceResultBlockSoundWhenAt` (with allowed filter, same
outcome layout = entry layout).

This is the key composability bridge: it lets us reuse the agent's existing
~10 terminal-call/control-flow `Sound` leaves as `WhenFreshAt` building blocks
for the recursive bridge without manual per-construct wrapping.
-/
theorem sourceResultBlockSoundWhenAt_of_sound
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {sourceFuel : Nat} {sourceStmts : List AstStmt}
    {codeOverride : Option AstContract} {lowerBlock : Functions.Block}
    {allowed : Except Exception State → Prop}
    (hSound :
      SourceResultBlockSound cfg layout terminalRel revertRel prim program ctx
        sourceFuel sourceStmts codeOverride lowerBlock) :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel sourceStmts codeOverride lowerBlock
      allowed :=
  sourceResultBlockSoundWhenAt_of_when
    (sourceResultBlockSoundWhen_of_sound hSound)

/--
Constructor leaf for `.ExprStmtCall (.Call (.inl .STOP) [])` at WhenFreshAt.

Lifts the existing `Fresh`-shape `sourceResultBlockSound_stop_call`
through `_of_sound` and `_of_when` adapters to reach the layout-aware
`WhenFreshAt` shape used by the recursive bridge.
-/
theorem sourceResultBlockSoundWhenAt_stop_call
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (hScope : ctx.scope = layout)
    (hTerminal :
      ∀ {source compiler},
        SourceStateRel cfg layout source compiler →
        ∃ sharedAfter : EvmYul.SharedState .EVM,
          prim.terminal .stop compiler.shared [] = .ok sharedAfter ∧
          terminalRel .stop (EvmYul.UInt256.ofNat 0)
            (Imported.stopTerminalSourceState source)
            (compiler.withShared sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.StopArith .STOP : EvmYul.Operation .Yul))) [])]
      codeOverride
      { stmts := [Functions.Stmt.terminalArgs .stop Locals.ExprSeq.nil] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_stop_call sourceFuel codeOverride hScope hTerminal)

/--
Checked lowerer-aware version of `sourceResultBlockSoundWhenAt_stop_call`.
The lowerer for `.ExprStmtCall (.Call (.inl .STOP) [])` outputs
`[Functions.Stmt.terminalArgs .stop Locals.ExprSeq.nil]`.
-/
theorem checkedStmtBlockLoweringSoundWhenFreshAt_stop_call
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (hScope : ctx.scope = layout)
    (hTerminal :
      ∀ {source compiler},
        SourceStateRel cfg layout source compiler →
        ∃ sharedAfter : EvmYul.SharedState .EVM,
          prim.terminal .stop compiler.shared [] = .ok sharedAfter ∧
          terminalRel .stop (EvmYul.UInt256.ofNat 0)
            (Imported.stopTerminalSourceState source)
            (compiler.withShared sharedAfter))
    {allowed : Except Exception State → Prop} :
    CheckedStmtBlockLoweringSoundWhenFreshAt cfg layout layout terminalRel
      revertRel prim program ctx sourceFuel.succ.succ.succ.succ
      (.ExprStmtCall
        (.Call (.inl ((.StopArith .STOP : EvmYul.Operation .Yul))) []))
      codeOverride allowed := by
  intro freshState freshState' lowerStmts _hCovers hLower
  have hExpected :
      Stmt.toFunctionsList? freshState
          (.ExprStmtCall
            (.Call (.inl ((.StopArith .STOP : EvmYul.Operation .Yul))) [])) =
        some ([Functions.Stmt.terminalArgs .stop Locals.ExprSeq.nil],
          freshState) := by
    unfold Stmt.toFunctionsList?
    show Stmt.toFunctionsListFuel? 2 freshState
        (.ExprStmtCall
          (.Call (.inl ((.StopArith .STOP : EvmYul.Operation .Yul))) [])) = _
    simp [Stmt.toFunctionsListFuel?, Prim.terminal?,
      Expr.List.lowerBound1?, Expr.List.toStackSeq?, Expr.List.toSeq?,
      Assembly.HaltKind.argCount]
  rw [hExpected] at hLower
  injection hLower with hPair
  obtain ⟨hStmts, hFresh⟩ := Prod.mk.injEq .. |>.mp hPair
  subst hStmts
  exact
    sourceResultBlockSoundWhenAt_stop_call sourceFuel codeOverride hScope
      hTerminal

/--
Constructor leaf for `.ExprStmtCall (.Call (.inl .REVERT) [.Lit 0, .Lit 0])`
at WhenFreshAt. Wraps the Sound leaf via the generic adapter.
-/
theorem sourceResultBlockSoundWhenAt_revert_zero_zero_prelude_call
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (sizeTmp offsetTmp : Name)
    (hScope : ctx.scope = layout)
    (hFreshSize : sizeTmp ∉ layout)
    (hFreshOffset : offsetTmp ∉ layout)
    (hDistinct : offsetTmp ≠ sizeTmp)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .revert
                ((compiler.insert sizeTmp (EvmYul.UInt256.ofNat 0)).insert
                  offsetTmp (EvmYul.UInt256.ofNat 0)).shared
                [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 0] =
              .ok sharedAfter ∧
            revertRel
              (Imported.revertLitLitSourceState (EvmYul.UInt256.ofNat 0)
                (EvmYul.UInt256.ofNat 0) shared store)
              (((compiler.insert sizeTmp (EvmYul.UInt256.ofNat 0)).insert
                  offsetTmp (EvmYul.UInt256.ofNat 0)).withShared
                sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .REVERT : EvmYul.Operation .Yul)))
          [.Lit (EvmYul.UInt256.ofNat 0),
           .Lit (EvmYul.UInt256.ofNat 0)])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ sizeTmp (Locals.Expr.lit (EvmYul.UInt256.ofNat 0)),
         Functions.Stmt.let_ offsetTmp
           (Locals.Expr.lit (EvmYul.UInt256.ofNat 0)),
         Functions.Stmt.terminalArgs .revert
          (Locals.ExprSeq.cons (Locals.Expr.var sizeTmp)
            (Locals.ExprSeq.cons (Locals.Expr.var offsetTmp)
              Locals.ExprSeq.nil))] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_revert_zero_zero_prelude_call sourceFuel
      codeOverride sizeTmp offsetTmp hScope hFreshSize hFreshOffset
      hDistinct hTerminal)

/--
Constructor leaf for `.ExprStmtCall (.Call (.inl .RETURN) [.Lit 0, .Lit 0])`
at WhenFreshAt.
-/
theorem sourceResultBlockSoundWhenAt_return_zero_zero_prelude_call
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (sizeTmp offsetTmp : Name)
    (hScope : ctx.scope = layout)
    (hFreshSize : sizeTmp ∉ layout)
    (hFreshOffset : offsetTmp ∉ layout)
    (hDistinct : offsetTmp ≠ sizeTmp)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .return
                ((compiler.insert sizeTmp (EvmYul.UInt256.ofNat 0)).insert
                  offsetTmp (EvmYul.UInt256.ofNat 0)).shared
                [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 0] =
              .ok sharedAfter ∧
            terminalRel .return (EvmYul.UInt256.ofNat 1)
              (Imported.returnLitLitSourceState (EvmYul.UInt256.ofNat 0)
                (EvmYul.UInt256.ofNat 0) shared store)
              (((compiler.insert sizeTmp (EvmYul.UInt256.ofNat 0)).insert
                  offsetTmp (EvmYul.UInt256.ofNat 0)).withShared
                sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .RETURN : EvmYul.Operation .Yul)))
          [.Lit (EvmYul.UInt256.ofNat 0),
           .Lit (EvmYul.UInt256.ofNat 0)])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ sizeTmp (Locals.Expr.lit (EvmYul.UInt256.ofNat 0)),
         Functions.Stmt.let_ offsetTmp
           (Locals.Expr.lit (EvmYul.UInt256.ofNat 0)),
         Functions.Stmt.terminalArgs .return
          (Locals.ExprSeq.cons (Locals.Expr.var sizeTmp)
            (Locals.ExprSeq.cons (Locals.Expr.var offsetTmp)
              Locals.ExprSeq.nil))] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_return_zero_zero_prelude_call sourceFuel
      codeOverride sizeTmp offsetTmp hScope hFreshSize hFreshOffset
      hDistinct hTerminal)

/--
Constructor leaf for `.ExprStmtCall (.Call (.inl .SELFDESTRUCT) [.Lit 0])`
at WhenFreshAt.
-/
theorem sourceResultBlockSoundWhenAt_selfdestruct_zero_prelude_call
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (tmp : Name)
    (hScope : ctx.scope = layout)
    (hFresh : tmp ∉ layout)
    (hWritable :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          shared.executionEnv.perm = true)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .selfdestruct compiler.shared
                [EvmYul.UInt256.ofNat 0] =
              .ok sharedAfter ∧
            terminalRel .selfdestruct (EvmYul.UInt256.ofNat 0)
              (Imported.selfdestructZeroSourceState shared store)
              ((compiler.insert tmp (EvmYul.UInt256.ofNat 0)).withShared
                sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .SELFDESTRUCT : EvmYul.Operation .Yul)))
          [.Lit (EvmYul.UInt256.ofNat 0)])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ tmp (Locals.Expr.lit (EvmYul.UInt256.ofNat 0)),
         Functions.Stmt.terminalArgs .selfdestruct
          (Locals.ExprSeq.cons (Locals.Expr.var tmp) Locals.ExprSeq.nil)] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_selfdestruct_zero_prelude_call sourceFuel
      codeOverride tmp hScope hFresh hWritable hTerminal)

/--
Constructor leaf for `.ExprStmtCall (.Call (.inl .RETURN) [.Lit offset, .Lit size])`
at WhenFreshAt (generic literal offset/size).
-/
theorem sourceResultBlockSoundWhenAt_return_lit_lit_prelude_call
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (offset size : Word) (sizeTmp offsetTmp : Name)
    (hScope : ctx.scope = layout)
    (hFreshSize : sizeTmp ∉ layout)
    (hFreshOffset : offsetTmp ∉ layout)
    (hDistinct : offsetTmp ≠ sizeTmp)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .return
                ((compiler.insert sizeTmp size).insert offsetTmp offset).shared
                [size, offset] =
              .ok sharedAfter ∧
            terminalRel .return (EvmYul.UInt256.ofNat 1)
              (Imported.returnLitLitSourceState offset size shared store)
              (((compiler.insert sizeTmp size).insert offsetTmp offset).withShared
                sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .RETURN : EvmYul.Operation .Yul)))
          [.Lit offset, .Lit size])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ sizeTmp (Locals.Expr.lit size),
         Functions.Stmt.let_ offsetTmp (Locals.Expr.lit offset),
         Functions.Stmt.terminalArgs .return
          (Locals.ExprSeq.cons (Locals.Expr.var sizeTmp)
            (Locals.ExprSeq.cons (Locals.Expr.var offsetTmp)
              Locals.ExprSeq.nil))] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_return_lit_lit_prelude_call sourceFuel
      codeOverride offset size sizeTmp offsetTmp hScope hFreshSize
      hFreshOffset hDistinct hTerminal)

/--
Constructor leaf for `.ExprStmtCall (.Call (.inl .REVERT) [.Lit offset, .Lit size])`
at WhenFreshAt (generic literal offset/size).
-/
theorem sourceResultBlockSoundWhenAt_revert_lit_lit_prelude_call
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (offset size : Word) (sizeTmp offsetTmp : Name)
    (hScope : ctx.scope = layout)
    (hFreshSize : sizeTmp ∉ layout)
    (hFreshOffset : offsetTmp ∉ layout)
    (hDistinct : offsetTmp ≠ sizeTmp)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .revert
                ((compiler.insert sizeTmp size).insert offsetTmp offset).shared
                [size, offset] =
              .ok sharedAfter ∧
            revertRel
              (Imported.revertLitLitSourceState offset size shared store)
              (((compiler.insert sizeTmp size).insert offsetTmp offset).withShared
                sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .REVERT : EvmYul.Operation .Yul)))
          [.Lit offset, .Lit size])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ sizeTmp (Locals.Expr.lit size),
         Functions.Stmt.let_ offsetTmp (Locals.Expr.lit offset),
         Functions.Stmt.terminalArgs .revert
          (Locals.ExprSeq.cons (Locals.Expr.var sizeTmp)
            (Locals.ExprSeq.cons (Locals.Expr.var offsetTmp)
              Locals.ExprSeq.nil))] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_revert_lit_lit_prelude_call sourceFuel
      codeOverride offset size sizeTmp offsetTmp hScope hFreshSize
      hFreshOffset hDistinct hTerminal)

/--
Constructor leaf for `.ExprStmtCall (.Call (.inl .SELFDESTRUCT) [.Lit recipient])`
at WhenFreshAt.
-/
theorem sourceResultBlockSoundWhenAt_selfdestruct_lit_prelude_call
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (recipient : Word) (tmp : Name)
    (hScope : ctx.scope = layout)
    (hFresh : tmp ∉ layout)
    (hWritable :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          shared.executionEnv.perm = true)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .selfdestruct compiler.shared [recipient] =
              .ok sharedAfter ∧
            terminalRel .selfdestruct (EvmYul.UInt256.ofNat 0)
              (Imported.selfdestructLitSourceState recipient shared store)
              ((compiler.insert tmp recipient).withShared sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .SELFDESTRUCT : EvmYul.Operation .Yul)))
          [.Lit recipient])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ tmp (Locals.Expr.lit recipient),
         Functions.Stmt.terminalArgs .selfdestruct
          (Locals.ExprSeq.cons (Locals.Expr.var tmp) Locals.ExprSeq.nil)] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_selfdestruct_lit_prelude_call sourceFuel
      codeOverride recipient tmp hScope hFresh hWritable hTerminal)

/--
Compositional variant of `_selfdestruct_lit_prelude_call` at WhenFreshAt:
the terminal premise is over the post-prelude state.
-/
theorem sourceResultBlockSoundWhenAt_selfdestruct_lit_prelude_call_compositional
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (recipient : Word) (tmp : Name)
    (hScope : ctx.scope = layout)
    (hFresh : tmp ∉ layout)
    (hWritable :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compiler : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compiler →
          shared.executionEnv.perm = true)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compilerAfterArgs : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compilerAfterArgs →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .selfdestruct compilerAfterArgs.shared
                [recipient] =
              .ok sharedAfter ∧
            terminalRel .selfdestruct (EvmYul.UInt256.ofNat 0)
              (Imported.selfdestructLitSourceState recipient shared store)
              (compilerAfterArgs.withShared sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .SELFDESTRUCT : EvmYul.Operation .Yul)))
          [.Lit recipient])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ tmp (Locals.Expr.lit recipient),
         Functions.Stmt.terminalArgs .selfdestruct
          (Locals.ExprSeq.cons (Locals.Expr.var tmp) Locals.ExprSeq.nil)] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_selfdestruct_lit_prelude_call_compositional
      sourceFuel codeOverride recipient tmp hScope hFresh hWritable hTerminal)

/--
Compositional variant of `_return_lit_lit_prelude_call` at WhenFreshAt.
-/
theorem sourceResultBlockSoundWhenAt_return_lit_lit_prelude_call_compositional
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (offset size : Word) (sizeTmp offsetTmp : Name)
    (hScope : ctx.scope = layout)
    (hFreshSize : sizeTmp ∉ layout)
    (hFreshOffset : offsetTmp ∉ layout)
    (hDistinct : offsetTmp ≠ sizeTmp)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compilerAfterArgs : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compilerAfterArgs →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .return compilerAfterArgs.shared [size, offset] =
              .ok sharedAfter ∧
            terminalRel .return (EvmYul.UInt256.ofNat 1)
              (Imported.returnLitLitSourceState offset size shared store)
              (compilerAfterArgs.withShared sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .RETURN : EvmYul.Operation .Yul)))
          [.Lit offset, .Lit size])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ sizeTmp (Locals.Expr.lit size),
         Functions.Stmt.let_ offsetTmp (Locals.Expr.lit offset),
         Functions.Stmt.terminalArgs .return
          (Locals.ExprSeq.cons (Locals.Expr.var sizeTmp)
            (Locals.ExprSeq.cons (Locals.Expr.var offsetTmp)
              Locals.ExprSeq.nil))] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_return_lit_lit_prelude_call_compositional
      sourceFuel codeOverride offset size sizeTmp offsetTmp hScope hFreshSize
      hFreshOffset hDistinct hTerminal)

/--
Compositional variant of `_revert_lit_lit_prelude_call` at WhenFreshAt.
-/
theorem sourceResultBlockSoundWhenAt_revert_lit_lit_prelude_call_compositional
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    (sourceFuel : Nat) (codeOverride : Option AstContract)
    (offset size : Word) (sizeTmp offsetTmp : Name)
    (hScope : ctx.scope = layout)
    (hFreshSize : sizeTmp ∉ layout)
    (hFreshOffset : offsetTmp ∉ layout)
    (hDistinct : offsetTmp ≠ sizeTmp)
    (hTerminal :
      ∀ {shared : EvmYul.SharedState .Yul}
        {store : EvmYul.Yul.VarStore}
        {compilerAfterArgs : Objects.Source.State},
        SourceStateRel cfg layout (.Ok shared store) compilerAfterArgs →
          ∃ sharedAfter : EvmYul.SharedState .EVM,
            prim.terminal .revert compilerAfterArgs.shared [size, offset] =
              .ok sharedAfter ∧
            revertRel
              (Imported.revertLitLitSourceState offset size shared store)
              (compilerAfterArgs.withShared sharedAfter))
    {allowed : Except Exception State → Prop} :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel.succ.succ.succ.succ.succ.succ.succ.succ
      [.ExprStmtCall
        (.Call (.inl ((.System .REVERT : EvmYul.Operation .Yul)))
          [.Lit offset, .Lit size])]
      codeOverride
      { stmts :=
        [Functions.Stmt.let_ sizeTmp (Locals.Expr.lit size),
         Functions.Stmt.let_ offsetTmp (Locals.Expr.lit offset),
         Functions.Stmt.terminalArgs .revert
          (Locals.ExprSeq.cons (Locals.Expr.var sizeTmp)
            (Locals.ExprSeq.cons (Locals.Expr.var offsetTmp)
              Locals.ExprSeq.nil))] }
      allowed :=
  sourceResultBlockSoundWhenAt_of_sound
    (sourceResultBlockSound_revert_lit_lit_prelude_call_compositional
      sourceFuel codeOverride offset size sizeTmp offsetTmp hScope hFreshSize
      hFreshOffset hDistinct hTerminal)

/--
Constructor leaf for `.Let [] none` at the source-tower invariant.

The lowerer produces an empty block (`initNames []`), so the source-tower
side runs the empty list and returns a regular outcome with the cleaned
state at `layout`.  The imported side, via
`exec_block_let_empty_none_succ_succ_succ`, returns the original state at
fuel ≥ 3.  The two are related via `SourceOkOutcomeRel.regular`.

This is the first non-control-flow constructor leaf — a starting template
for the eventual `Let xs none` (general empty-init case) and beyond.
-/
theorem sourceResultBlockSoundWhenAt_let_empty_none
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {sourceFuel : Nat} {codeOverride : Option AstContract}
    {allowed : Except Exception State → Prop}
    (hAllowed :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultRelatable sourceResult)
    (hScope : ctx.scope = layout) :
    SourceResultBlockSoundWhenAt cfg layout layout terminalRel revertRel
      prim program ctx sourceFuel [.Let [] none] codeOverride
      { stmts := [] } allowed := by
  refine ⟨hScope, ?_⟩
  intro source compiler sourceResult hInitial hAllow hSource
  cases sourceFuel with
  | zero =>
      have hZero :
          EvmYul.Yul.exec 0 (.Block [.Let [] none]) codeOverride source =
            .error .OutOfFuel :=
        Imported.exec_zero (.Block [.Let [] none]) codeOverride source
      rw [hZero] at hSource
      subst sourceResult
      have hRelatable :
          SourceResultRelatable (.error (.OutOfFuel : Exception)) :=
        hAllowed hAllow
      cases hRelatable
  | succ fuel =>
      cases fuel with
      | zero =>
          have hOne :
              EvmYul.Yul.exec 1 (.Block [.Let [] none]) codeOverride source =
                .error .OutOfFuel := by
            simp [EvmYul.Yul.exec, EvmYul.Yul.execSeq]
          rw [hOne] at hSource
          subst sourceResult
          have hRelatable :
              SourceResultRelatable (.error (.OutOfFuel : Exception)) :=
            hAllowed hAllow
          cases hRelatable
      | succ fuel =>
          cases fuel with
          | zero =>
              have hTwo :
                  EvmYul.Yul.exec 2 (.Block [.Let [] none]) codeOverride
                      source =
                    .error .OutOfFuel := by
                simp [EvmYul.Yul.exec, EvmYul.Yul.execSeq,
                  EvmYul.Yul.exec]
              rw [hTwo] at hSource
              subst sourceResult
              have hRelatable :
                  SourceResultRelatable (.error (.OutOfFuel : Exception)) :=
                hAllowed hAllow
              cases hRelatable
          | succ fuel =>
              cases hInitial with
              | @ok shared store _ hShared hVars =>
                  refine
                    ⟨Functions.Source.Outcome.regular
                        (compiler.restrictTo layout), 1, ?_, ?_⟩
                  · simp [Functions.Source.Block.runScoped,
                      Functions.Source.Block.runOpen, hScope,
                      Functions.Source.Outcome.regular,
                      Locals.Source.Outcome.regular]
                  · rw [← hSource]
                    rw [exec_block_let_empty_none_succ_succ_succ]
                    exact
                      SourceResultOutcomeRel.ok
                        (SourceOkOutcomeRel.regular
                          (SourceStateRel.ok hShared (by
                            intro name hMem
                            simpa [Locals.Source.State.restrictTo,
                              Locals.Source.Store.restrictTo_mem hMem]
                              using hVars name hMem)))

/--
Lowerer-aware checked leaf for `.Let [] none`.

Lifts `sourceResultBlockSoundWhenAt_let_empty_none` through `Stmt.toFunctionsList?`.
The lowerer for `.Let [] none` outputs an empty statement list (since
`initNames (identNames []) = initNames [] = []`).
-/
theorem checkedStmtBlockLoweringSoundWhenFreshAt_let_empty_none
    {cfg : StateRelConfig} {layout : List Name}
    {terminalRel :
      Assembly.HaltKind → Word → State → Objects.Source.State → Prop}
    {revertRel : State → Objects.Source.State → Prop}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {sourceFuel : Nat} {codeOverride : Option AstContract}
    {allowed : Except Exception State → Prop}
    (hAllowed :
      ∀ {sourceResult}, allowed sourceResult →
        SourceResultRelatable sourceResult)
    (hScope : ctx.scope = layout) :
    CheckedStmtBlockLoweringSoundWhenFreshAt cfg layout layout terminalRel
      revertRel prim program ctx sourceFuel (.Let [] none) codeOverride
      allowed := by
  intro freshState freshState' lowerStmts _hCovers hLower
  have hLower' :
      (some (([] : List Functions.Stmt), freshState) :
          Option (List Functions.Stmt × Fresh.State)) =
        some (lowerStmts, freshState') := by
    simpa [Stmt.toFunctionsList?, Stmt.toFunctionsListFuel?, Stmt.fuel,
      Stmt.initNames, identNames]
      using hLower
  injection hLower' with hPair
  cases hPair
  exact sourceResultBlockSoundWhenAt_let_empty_none hAllowed hScope

/--
**Compositional snoc rule for `SourceArgEvalRegular` with empty preludes,
appending a literal**. Given a bridge for source-args `oldArgs` (no prelude),
extending with a trailing `.Lit lastValue` yields a bridge for
`oldArgs ++ [.Lit lastValue]` with lowered args extended by
`Locals.Expr.lit lastValue`. Fuel grows by `+2`. The state and ctx are
preserved (empty prelude throughout).

This is the structural snoc-on-source-side rule the cons-style argument-eval
inductive proof needs, decomposing the snoc'd evalArgs through the imported
cons rule on the reversed list.
-/
theorem sourceArgEvalRegular_snoc_lit_empty_prelude
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {lastValue : Word}
    {oldArgs : List AstExpr} {lowerArgsOld : List (Locals.Expr 1)}
    {codeOverride : Option AstContract}
    (hBridgeOld : SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel oldArgs codeOverride [] lowerArgsOld) :
    SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel.succ.succ
      (oldArgs ++ [EvmYul.Yul.Ast.Expr.Lit lastValue]) codeOverride []
      (lowerArgsOld ++ [Locals.Expr.lit lastValue]) := by
  obtain ⟨hScope, hLenOld, hMain⟩ := hBridgeOld
  refine ⟨hScope, ?_, ?_⟩
  · simp [hLenOld]
  · intro source sourceAfter compiler values hInitial hImpEval
    have hReverseEq :
        (oldArgs ++ [EvmYul.Yul.Ast.Expr.Lit lastValue]).reverse =
          EvmYul.Yul.Ast.Expr.Lit lastValue :: oldArgs.reverse := by simp
    rw [hReverseEq] at hImpEval
    rw [Imported_evalArgs_cons_lit_succ_succ_unfold] at hImpEval
    cases hOld : EvmYul.Yul.evalArgs argFuel oldArgs.reverse codeOverride
        source with
    | error err =>
        rw [hOld] at hImpEval
        exact absurd hImpEval (by simp [EvmYul.Yul.cons'])
    | ok pair =>
        rcases pair with ⟨sourceAfter_old, oldOutputValues⟩
        rw [hOld] at hImpEval
        simp [EvmYul.Yul.cons'] at hImpEval
        obtain ⟨hStateEq, hValuesEq⟩ := hImpEval
        subst hStateEq
        have hValuesEq' :
            values = oldOutputValues.reverse ++ [lastValue] := by
          have := congrArg List.reverse hValuesEq
          have h := this
          simp at h
          exact h.symm
        subst hValuesEq'
        -- Get the length equation from Imported_evalArgs_length
        have hOldLen : oldOutputValues.length = oldArgs.length := by
          have h := Imported_evalArgs_length argFuel oldArgs.reverse
            codeOverride source sourceAfter_old oldOutputValues hOld
          simpa using h
        -- Apply the old bridge's main with values_old = oldOutputValues.reverse
        have hImpEvalOld :
            EvmYul.Yul.evalArgs argFuel oldArgs.reverse codeOverride source =
              .ok (sourceAfter_old, oldOutputValues.reverse.reverse) := by
          rw [hOld]
          simp
        obtain ⟨stateAfter_old, targetFuel_old, ctxAfter_old,
                hRunOpen_old, _hCtxScope_old, hStateRel_old, hValues_old⟩ :=
          hMain hInitial hImpEvalOld
        -- Empty prelude: runOpen ⟨[]⟩ compiler returns regular compiler with same ctx.
        -- Derive stateAfter_old = compiler and ctxAfter_old = ctx in one go.
        rcases targetFuel_old with _ | m
        · -- targetFuel_old = 0: runOpen returns invalid, contradicting hRunOpen_old
          exfalso
          simp [Functions.Source.Block.runOpen, Functions.Source.invalid,
            Structured.invalid] at hRunOpen_old
        · -- targetFuel_old = m+1: runOpen returns .ok (regular compiler, ctx)
          simp [Functions.Source.Block.runOpen,
            Functions.Source.Outcome.regular,
            Locals.Source.Outcome.regular] at hRunOpen_old
          obtain ⟨hSAE, hCAE⟩ := hRunOpen_old
          subst hSAE
          subst hCAE
          refine ⟨compiler, 1, ctx, ?_, hScope, hStateRel_old, ?_⟩
          · simp [Functions.Source.Block.runOpen]
          · intro i hi hv
            -- Length equations:
            --   lowerArgsOld.length = oldArgs.length (from hLenOld)
            --   oldOutputValues.length = oldArgs.length (from hOldLen)
            --   So lowerArgsOld.length = oldOutputValues.length = oldOutputValues.reverse.length
            have hOldRevLen :
                oldOutputValues.reverse.length = lowerArgsOld.length := by
              rw [List.length_reverse, hOldLen, hLenOld]
            rcases Nat.lt_or_ge i lowerArgsOld.length with hLt | hGe
            · -- i < lowerArgsOld.length
              have hi_old : i < lowerArgsOld.length := hLt
              have hv_old : i < oldOutputValues.reverse.length := by
                rw [hOldRevLen]; exact hLt
              obtain ⟨valueState, hValEval⟩ := hValues_old i hi_old hv_old
              refine ⟨valueState, ?_⟩
              have hIdx :
                  (lowerArgsOld ++ [Locals.Expr.lit lastValue])[i]'hi =
                    lowerArgsOld[i]'hi_old :=
                List.getElem_append_left hi_old
              rw [hIdx]
              have hValIdx :
                  (oldOutputValues.reverse ++ [lastValue])[i]'hv =
                    oldOutputValues.reverse[i]'hv_old :=
                List.getElem_append_left hv_old
              rw [hValIdx]
              exact hValEval
            · -- i = lowerArgsOld.length (only other case since hi : i < lowerArgsOld.length + 1)
              have hLen_new :
                  (lowerArgsOld ++ [Locals.Expr.lit lastValue]).length =
                    lowerArgsOld.length + 1 := by simp
              rw [hLen_new] at hi
              have hi_eq : i = lowerArgsOld.length := by omega
              subst hi_eq
              refine ⟨compiler, ?_⟩
              -- hi has type `i < (lowerArgsOld ++ [.lit ..]).length`, which
              -- reduces to lowerArgsOld.length + 1 after simp.
              have hi_append :
                  lowerArgsOld.length <
                    (lowerArgsOld ++ [Locals.Expr.lit lastValue]).length := by
                show lowerArgsOld.length <
                  (lowerArgsOld ++ [Locals.Expr.lit lastValue]).length
                rw [List.length_append, List.length_singleton]
                exact Nat.lt_succ_self _
              have hIdx :
                  (lowerArgsOld ++ [Locals.Expr.lit lastValue])[lowerArgsOld.length]'hi_append =
                    Locals.Expr.lit lastValue := by
                simp [List.getElem_append]
              rw [hIdx]
              have hValIdx :
                  (oldOutputValues.reverse ++ [lastValue])[lowerArgsOld.length]'hv =
                    lastValue := by
                have hL : oldOutputValues.reverse.length = lowerArgsOld.length :=
                  hOldRevLen
                simp [List.getElem_append, hL]
              rw [hValIdx]
              simp [Locals.Source.Expr.evalOne, Locals.Source.Expr.eval]

/--
Compositional snoc rule for `SourceArgEvalRegular` with empty preludes,
appending a variable.

This is the variable sibling of
`sourceArgEvalRegular_snoc_lit_empty_prelude`: the imported evaluator sees the
new variable first because arguments are evaluated over the reversed source
list, while the source-tower lowered argument list extends in source order.
-/
theorem sourceArgEvalRegular_snoc_var_empty_prelude
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {lastName : EvmYul.Identifier}
    {oldArgs : List AstExpr} {lowerArgsOld : List (Locals.Expr 1)}
    {codeOverride : Option AstContract}
    (hMem : identName lastName ∈ layout)
    (hBridgeOld : SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel oldArgs codeOverride [] lowerArgsOld) :
    SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel.succ.succ
      (oldArgs ++ [EvmYul.Yul.Ast.Expr.Var lastName]) codeOverride []
      (lowerArgsOld ++ [Locals.Expr.var (identName lastName)]) := by
  obtain ⟨hScope, hLenOld, hMain⟩ := hBridgeOld
  refine ⟨hScope, ?_, ?_⟩
  · simp [hLenOld]
  · intro source sourceAfter compiler values hInitial hImpEval
    have hReverseEq :
        (oldArgs ++ [EvmYul.Yul.Ast.Expr.Var lastName]).reverse =
          EvmYul.Yul.Ast.Expr.Var lastName :: oldArgs.reverse := by
      simp
    rw [hReverseEq] at hImpEval
    cases hInitial with
    | @ok shared store _ hShared hVars =>
        rw [Imported_evalArgs_cons_var_succ_succ_unfold] at hImpEval
        cases hLookup :
            (.Ok shared store : State).lookup? lastName with
        | none =>
            rw [hLookup] at hImpEval
            exact absurd hImpEval (by simp)
        | some lastValue =>
            rw [hLookup] at hImpEval
            cases hOld :
                EvmYul.Yul.evalArgs argFuel oldArgs.reverse codeOverride
                  (.Ok shared store : State) with
            | error err =>
                rw [hOld] at hImpEval
                exact absurd hImpEval (by simp [EvmYul.Yul.cons'])
            | ok pair =>
                rcases pair with ⟨sourceAfterOld, oldOutputValues⟩
                rw [hOld] at hImpEval
                simp [EvmYul.Yul.cons'] at hImpEval
                obtain ⟨hStateEq, hValuesEq⟩ := hImpEval
                subst hStateEq
                have hValuesEq' :
                    values = oldOutputValues.reverse ++ [lastValue] := by
                  have := congrArg List.reverse hValuesEq
                  simp at this
                  exact this.symm
                subst hValuesEq'
                have hOldLen : oldOutputValues.length = oldArgs.length := by
                  have h := Imported_evalArgs_length argFuel oldArgs.reverse
                    codeOverride (.Ok shared store : State) sourceAfterOld
                    oldOutputValues hOld
                  simpa using h
                have hImpEvalOld :
                    EvmYul.Yul.evalArgs argFuel oldArgs.reverse codeOverride
                        (.Ok shared store : State) =
                      .ok (sourceAfterOld, oldOutputValues.reverse.reverse) := by
                  rw [hOld]
                  simp
                obtain ⟨stateAfterOld, targetFuelOld, ctxAfterOld,
                    hRunOpenOld, _hCtxScopeOld, hStateRelOld,
                    hValuesOld⟩ :=
                  hMain (SourceStateRel.ok hShared hVars) hImpEvalOld
                rcases targetFuelOld with _ | m
                · exfalso
                  simp [Functions.Source.Block.runOpen,
                    Functions.Source.invalid, Structured.invalid] at hRunOpenOld
                · simp [Functions.Source.Block.runOpen,
                    Functions.Source.Outcome.regular,
                    Locals.Source.Outcome.regular] at hRunOpenOld
                  obtain ⟨hSAE, hCAE⟩ := hRunOpenOld
                  subst hSAE
                  subst hCAE
                  refine ⟨compiler, 1, ctx, ?_, hScope, hStateRelOld, ?_⟩
                  · simp [Functions.Source.Block.runOpen]
                  · intro i hi hv
                    have hOldRevLen :
                        oldOutputValues.reverse.length =
                          lowerArgsOld.length := by
                      rw [List.length_reverse, hOldLen, hLenOld]
                    rcases Nat.lt_or_ge i lowerArgsOld.length with hLt | hGe
                    · have hiOld : i < lowerArgsOld.length := hLt
                      have hvOld : i < oldOutputValues.reverse.length := by
                        rw [hOldRevLen]
                        exact hLt
                      obtain ⟨valueState, hValEval⟩ :=
                        hValuesOld i hiOld hvOld
                      refine ⟨valueState, ?_⟩
                      have hIdx :
                          (lowerArgsOld ++
                              [Locals.Expr.var (identName lastName)])[i]'hi =
                            lowerArgsOld[i]'hiOld :=
                        List.getElem_append_left hiOld
                      rw [hIdx]
                      have hValIdx :
                          (oldOutputValues.reverse ++ [lastValue])[i]'hv =
                            oldOutputValues.reverse[i]'hvOld :=
                        List.getElem_append_left hvOld
                      rw [hValIdx]
                      exact hValEval
                    · have hLenNew :
                          (lowerArgsOld ++
                              [Locals.Expr.var (identName lastName)]).length =
                            lowerArgsOld.length + 1 := by
                        simp
                      rw [hLenNew] at hi
                      have hiEq : i = lowerArgsOld.length := by omega
                      subst hiEq
                      refine ⟨compiler, ?_⟩
                      have hiAppend :
                          lowerArgsOld.length <
                            (lowerArgsOld ++
                              [Locals.Expr.var (identName lastName)]).length := by
                        rw [List.length_append, List.length_singleton]
                        exact Nat.lt_succ_self _
                      have hIdx :
                          ((lowerArgsOld ++ [Locals.Expr.var (identName lastName)])[lowerArgsOld.length]'hiAppend) =
                            Locals.Expr.var (identName lastName) := by
                        simp [List.getElem_append]
                      rw [hIdx]
                      have hValIdx :
                          ((oldOutputValues.reverse ++ [lastValue])[lowerArgsOld.length]'hv) =
                            lastValue := by
                        have hL :
                            oldOutputValues.reverse.length =
                              lowerArgsOld.length := hOldRevLen
                        simp [List.getElem_append, hL]
                      rw [hValIdx]
                      have hStoreLookup :
                          store.lookup (identName lastName) =
                            some lastValue := by
                        simpa [EvmYul.Yul.State.lookup?] using hLookup
                      have hVarsName :
                          compiler.vars (identName lastName) =
                            some lastValue := by
                        have hRel := hVars (identName lastName) hMem
                        rw [hRel]
                        exact hStoreLookup
                      simp [Locals.Source.Expr.evalOne,
                        Locals.Source.Expr.eval, hVarsName]

/--
Mixed two-argument bridge for `[literal, variable]` with no prelude.
-/
theorem sourceArgEvalRegular_pair_lit_var
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {value : Word} {name : EvmYul.Identifier}
    {codeOverride : Option AstContract}
    (hScope : ctx.scope = layout)
    (hMem : identName name ∈ layout) :
    SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel.succ.succ.succ.succ.succ [.Lit value, .Var name] codeOverride []
      [Locals.Expr.lit value, Locals.Expr.var (identName name)] :=
  sourceArgEvalRegular_snoc_var_empty_prelude
    (cfg := cfg) (prim := prim) (program := program) (layout := layout)
    (ctx := ctx) (argFuel := argFuel.succ.succ.succ)
    (lastName := name) (oldArgs := [.Lit value])
    (lowerArgsOld := [Locals.Expr.lit value])
    (codeOverride := codeOverride) hMem
    (sourceArgEvalRegular_singleton_lit
      (cfg := cfg) (prim := prim) (program := program) (layout := layout)
      (ctx := ctx) (argFuel := argFuel) (value := value)
      (codeOverride := codeOverride) hScope)

/--
Mixed two-argument bridge for `[variable, literal]` with no prelude.
-/
theorem sourceArgEvalRegular_pair_var_lit
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {argFuel : Nat} {name : EvmYul.Identifier} {value : Word}
    {codeOverride : Option AstContract}
    (hScope : ctx.scope = layout)
    (hMem : identName name ∈ layout) :
    SourceArgEvalRegular cfg prim program layout layout ctx
      argFuel.succ.succ.succ.succ.succ [.Var name, .Lit value] codeOverride []
      [Locals.Expr.var (identName name), Locals.Expr.lit value] :=
  sourceArgEvalRegular_snoc_lit_empty_prelude
    (cfg := cfg) (prim := prim) (program := program) (layout := layout)
    (ctx := ctx) (argFuel := argFuel.succ.succ.succ)
    (lastValue := value) (oldArgs := [.Var name])
    (lowerArgsOld := [Locals.Expr.var (identName name)])
    (codeOverride := codeOverride)
    (sourceArgEvalRegular_singleton_var
      (cfg := cfg) (prim := prim) (program := program) (layout := layout)
      (ctx := ctx) (argFuel := argFuel) (name := name)
      (codeOverride := codeOverride) hScope hMem)

/--
Direct literal/variable argument lists with their direct lowered expressions.

The constructors are snoc-shaped because imported Yul evaluates arguments by
first reversing the source-order list.  This matches the compositional snoc
lemmas above.
-/
inductive SourceArgSimple (layout : List Name) :
    List AstExpr → List (Locals.Expr 1) → Prop where
  | nil : SourceArgSimple layout [] []
  | snoc_lit {args : List AstExpr} {lowerArgs : List (Locals.Expr 1)}
      {value : Word}
      (hArgs : SourceArgSimple layout args lowerArgs) :
      SourceArgSimple layout (args ++ [.Lit value])
        (lowerArgs ++ [Locals.Expr.lit value])
  | snoc_var {args : List AstExpr} {lowerArgs : List (Locals.Expr 1)}
      {name : EvmYul.Identifier}
      (hMem : identName name ∈ layout)
      (hArgs : SourceArgSimple layout args lowerArgs) :
      SourceArgSimple layout (args ++ [.Var name])
        (lowerArgs ++ [Locals.Expr.var (identName name)])

def sourceArgSimpleFuel (base : Nat) : Nat → Nat
  | 0 => base.succ
  | n + 1 => (sourceArgSimpleFuel base n).succ.succ

/--
No-prelude argument bridge for any source-order list of direct literals and
variables.

The fuel index is intentionally explicit and length-based.  Each snoc step
costs the two fuel successors consumed by `evalArgs`/`evalTail`, while the base
empty argument list needs one successor.
-/
theorem sourceArgEvalRegular_simple_empty_prelude
    {cfg : StateRelConfig}
    {prim : Objects.Source.PrimitiveSemantics}
    {program : Functions.Program}
    {layout : List Name} {ctx : Functions.Source.Ctx}
    {baseFuel : Nat} {args : List AstExpr}
    {lowerArgs : List (Locals.Expr 1)}
    {codeOverride : Option AstContract}
    (hScope : ctx.scope = layout)
    (hArgs : SourceArgSimple layout args lowerArgs) :
    SourceArgEvalRegular cfg prim program layout layout ctx
      (sourceArgSimpleFuel baseFuel args.length) args codeOverride []
      lowerArgs := by
  induction hArgs with
  | nil =>
      simpa [sourceArgSimpleFuel] using
        sourceArgEvalRegular_nil
          (cfg := cfg) (prim := prim) (program := program)
          (layout := layout) (ctx := ctx) (argFuel := baseFuel)
          (codeOverride := codeOverride) hScope
  | @snoc_lit args lowerArgs value hArgs ih =>
      simpa [sourceArgSimpleFuel] using
        sourceArgEvalRegular_snoc_lit_empty_prelude
          (cfg := cfg) (prim := prim) (program := program)
          (layout := layout) (ctx := ctx)
          (argFuel := sourceArgSimpleFuel baseFuel args.length)
          (lastValue := value) (oldArgs := args)
          (lowerArgsOld := lowerArgs) (codeOverride := codeOverride) ih
  | @snoc_var args lowerArgs name hMem hArgs ih =>
      simpa [sourceArgSimpleFuel] using
        sourceArgEvalRegular_snoc_var_empty_prelude
          (cfg := cfg) (prim := prim) (program := program)
          (layout := layout) (ctx := ctx)
          (argFuel := sourceArgSimpleFuel baseFuel args.length)
          (lastName := name) (oldArgs := args)
          (lowerArgsOld := lowerArgs) (codeOverride := codeOverride)
          hMem ih

/-!
## Compositional evaluation preservation under store extension

Building block for the cons rule and for proving each constructor leaf:
when we insert a fresh name into the state, looking up any OTHER name is
unaffected. This is the compositional ancestor of the various
"`evalOne` of a lowered arg-expression unchanged when extra prelude lets
have been inserted" obligations.
-/

/--
Looking up a different name in an extended store yields the original value.
Compositional ancestor of all "store insert preserves lookup" obligations
that arise when extending the local environment with fresh prelude bindings.
-/
theorem Locals_Source_Store_lookup_insert_of_ne
    {store : Locals.Source.Store} {name other : Name} {value : Word}
    (hNe : other ≠ name) :
    (store.insert name value) other = store other := by
  exact Locals.Source.Store.insert_of_ne hNe

/--
The store of `state.insert name value` at `other ≠ name` agrees with the
original state's store at `other`. State-level version of
`Locals_Source_Store_lookup_insert_of_ne`.
-/
theorem Locals_Source_State_insert_vars_of_ne
    {state : Locals.Source.State} {name other : Name} {value : Word}
    (hNe : other ≠ name) :
    (state.insert name value).vars other = state.vars other :=
  Locals.Source.Store.insert_of_ne hNe

/--
Evaluation of `Locals.Expr.lit value` is state-passthrough: returns the
input state unchanged paired with the literal value.
-/
theorem Locals_Source_Expr_lit_evalOne
    {prim : Locals.Source.PrimitiveSemantics}
    {value : Word} {state : Locals.Source.State} :
    Locals.Source.Expr.evalOne prim (Locals.Expr.lit value) state =
      .ok (state, value) := by
  simp [Locals.Source.Expr.evalOne, Locals.Source.Expr.eval]

/--
Evaluation of `Locals.Expr.var other` succeeds with value `v` iff
`state.vars other = some v`. Used to reduce var-eval obligations to
direct store lookups in proofs about lowered argument expressions.
-/
theorem Locals_Source_Expr_var_evalOne_of_lookup
    {prim : Locals.Source.PrimitiveSemantics}
    {other : Name} {state : Locals.Source.State} {value : Word}
    (hLookup : state.vars other = some value) :
    Locals.Source.Expr.evalOne prim (Locals.Expr.var other) state =
      .ok (state, value) := by
  simp [Locals.Source.Expr.evalOne, Locals.Source.Expr.eval, hLookup]

/--
Var-evalOne preservation under store extension at a different name.
If `evalOne (.var other) state = .ok (state, v)` and `other ≠ name`,
then `evalOne (.var other) (state.insert name w) = .ok (state.insert name w, v)`.
The lookup in the original store survives the insert (different name) and
yields the same value, with the result state being the new extended state.
-/
theorem Locals_Source_Expr_var_evalOne_insert_of_ne
    {prim : Locals.Source.PrimitiveSemantics}
    {name other : Name} {state : Locals.Source.State}
    {value newValue : Word}
    (hNe : other ≠ name)
    (hLookup : state.vars other = some value) :
    Locals.Source.Expr.evalOne prim (Locals.Expr.var other)
        (state.insert name newValue) =
      .ok (state.insert name newValue, value) := by
  have hLookupAfter :
      (state.insert name newValue).vars other = some value := by
    rw [Locals_Source_State_insert_vars_of_ne hNe]
    exact hLookup
  exact Locals_Source_Expr_var_evalOne_of_lookup hLookupAfter

/-!
## Roadmap for completing the bridge

Following the oracle's direction (PROGRESS_LOG `oracle/yul-bridge-direction-confirmed`):

1. **Extend `SourceArgEvalRegular` to a cons case** — pattern match on `args = head :: tail`
   and compose the head's evaluation (via `EvmYul.Yul.eval` + `evalTail`) with the tail's
   evaluation. Requires an `evalTail_nil_ok_succ` lemma not yet in `Yul/Reference.lean`.
2. **Refine the interface** — replace the current `lowerNames : List Name` field with
   `lowerArgs : List (Locals.Expr 1)`, matching the legacy `BoundArgsBridgeWithLayoutSlotValues`
   shape and the actual `Expr.List.lowerBound1?` output. Add an asserted-value-evaluation
   clause: each `lowerArgs[i]` evaluates to `values[i]` in the post-prelude state.
3. **Constructor leaves**: `Let xs none` (no arg-bridge needed; pure declaration); then
   `Let xs (some e)` / `Assign xs e` / `ExprStmtCall e` using single-argument arg-bridge;
   then `If` / `Switch` (arity-1 arg bridge + recursive block); then `For` (loop fuel
   substrate); then `Block s::ss` (generic stmt-then-block sequence via IH).
4. **Compose into the recursive bridge**: `recursiveSourceBridgeWhenUpToAt_succ` taking
   the IH at `bound = k` and producing the bridge at `k+1`. Use `induction bound` to
   establish the full bridge.
5. **Thread through public theorem**: feed the inhabitation into
   `compile_source_preserves_checked_of_compileAccepted` (currently in
   `EvmCompiler/Yul/Preservation.lean`) so the public theorem no longer takes a recursive
   callback.
-/

end SourceBridgeFacts
end Reference
end Yul
end EvmCompiler
