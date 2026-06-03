import EvmCompiler.Functions.LiveLayout
import EvmCompiler.Functions.SourceDirect

namespace EvmCompiler
namespace Functions
namespace LiveLayout

/-!
Semantic bridge bricks for the live-layout lowerer.

`Functions.LiveLayout` owns the executable liveness/layout checker and the
cleanup-emitting lowerer.  This module imports the heavier source/direct bridge
only for facts that connect inserted cleanup statements to the existing
`Functions.SourceDirect.StateRel` invariant.
-/

namespace SourceScoped

theorem blockScoped_of_source_select_some {env : List Name} {value : Word}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {body : Block}
    (hCases : Scope.CaseList.Scoped env cases)
    (hDefault : Scope.Default.Scoped env defaultBody)
    (hSelect : Source.Switch.select value cases defaultBody = some body) :
    Scope.Block.Scoped env body := by
  induction cases with
  | nil =>
      cases defaultBody with
      | none =>
          simp [Source.Switch.select] at hSelect
      | some defaultBlock =>
          simp [Source.Switch.select, Scope.Default.Scoped] at hDefault hSelect
          cases hSelect
          exact hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, caseBody⟩
      rcases hCases with ⟨hCaseScoped, hRestScoped⟩
      by_cases hEq : caseValue = value
      · simp [Source.Switch.select, hEq] at hSelect
        cases hSelect
        exact hCaseScoped
      · simp [Source.Switch.select, hEq] at hSelect
        exact ih hRestScoped hSelect

theorem blockScoped_of_switch_select_some {env : List Name} {value : Word}
    {scrutinee : Expr 1} {cases : List (Word × Block)}
    {defaultBody : Option Block} {body : Block}
    (hScoped :
      Scope.Stmt.Scoped env (.switch scrutinee cases defaultBody))
    (hSelect : Source.Switch.select value cases defaultBody = some body) :
    Scope.Block.Scoped env body := by
  exact blockScoped_of_source_select_some hScoped.2.1 hScoped.2.2 hSelect

end SourceScoped

namespace Layout

theorem cleanupLayoutRel_trimDeadPrefix_of_all_mem
    {layout live : List Name}
    (hAll : ∀ {name : Name}, name ∈ layout → name ∈ live) :
    SourceDirect.CleanupLayoutRel (trimDeadPrefix layout live) layout := by
  rw [trimDeadPrefix_eq_self_of_all_mem hAll]
  exact SourceDirect.CleanupLayoutRel.refl layout

theorem cleanupLayoutRel_trimDeadPrefix_scopedAfter
    {layout after : List Name} :
    SourceDirect.CleanupLayoutRel
      (trimDeadPrefix layout (Checked.scopedAfter layout after)) layout :=
  cleanupLayoutRel_trimDeadPrefix_of_all_mem
    (by
      intro name hName
      exact Checked.mem_scopedAfter_of_mem_layout hName)

theorem cleanupScope_trimDeadPrefix_of_sameScope :
    ∀ {layout live scope : List Name},
      layout.Nodup →
      SourceDirect.CleanupScopeRel layout scope →
      SourceDirect.SameScope live scope →
      SourceDirect.CleanupScopeRel (trimDeadPrefix layout live) scope
  | [], live, scope, _hNoDup, hCleanup, hLive => by
      rcases hCleanup with ⟨hLength, hMem⟩
      simp [trimDeadPrefix, SourceDirect.CleanupScopeRel,
        SourceDirect.SameScope] at hLength hMem ⊢
      constructor
      · exact hLength
      · intro name
        exact hMem name
  | name :: rest, live, scope, hNoDup, hCleanup, hLive => by
      by_cases hNameLive : name ∈ live
      · simpa [trimDeadPrefix, hNameLive] using hCleanup
      · have hNoDupRest : rest.Nodup := by
          simpa using hNoDup.tail
        have hNameNotScope : name ∉ scope := by
          intro hNameScope
          exact hNameLive ((hLive.2 name).mpr hNameScope)
        have hScopeLeRest : scope.length ≤ rest.length := by
          by_contra hNotLe
          have hScopeLeLayout : scope.length ≤ (name :: rest).length := by
            rcases hCleanup with ⟨hLength, _hMem⟩
            rw [List.length_drop] at hLength
            omega
          have hScopeLen : scope.length = rest.length + 1 := by
            simp at hScopeLeLayout
            omega
          have hDrop :
              (name :: rest).drop
                  ((name :: rest).length - scope.length) =
                name :: rest := by
            simp [hScopeLen]
          have hNameDrop :
              name ∈
                (name :: rest).drop
                  ((name :: rest).length - scope.length) := by
            rw [hDrop]
            simp
          exact hNameNotScope ((hCleanup.2 name).mp hNameDrop)
        have hCleanupRest :
            SourceDirect.CleanupScopeRel rest scope := by
          rcases hCleanup with ⟨hLength, hMem⟩
          constructor
          · rw [List.length_drop] at hLength ⊢
            simp at hLength
            omega
          · intro needle
            have hDrop :
                (name :: rest).drop (rest.length + 1 - scope.length) =
                  rest.drop (rest.length - scope.length) := by
              have hNat :
                  rest.length + 1 - scope.length =
                    (rest.length - scope.length) + 1 := by
                omega
              simp [hNat]
            simpa [hDrop] using hMem needle
        simpa [trimDeadPrefix, hNameLive] using
          cleanupScope_trimDeadPrefix_of_sameScope
            hNoDupRest hCleanupRest hLive

theorem trimDeadPrefix_suffix_drop {layout live : List Name} {depth : Nat}
    (hDepth : depth ≤ (trimDeadPrefix layout live).length) :
    (trimDeadPrefix layout live).drop
        ((trimDeadPrefix layout live).length - depth) =
      layout.drop (layout.length - depth) := by
  rw [← drop_trimDeadPrefixCount_eq_trimDeadPrefix layout live]
  rw [List.drop_drop]
  have hCountLe : trimDeadPrefixCount layout live ≤ layout.length := by
    clear hDepth depth
    induction layout with
    | nil =>
        simp [trimDeadPrefixCount]
    | cons name rest ih =>
        by_cases hName : name ∈ live
        · simp [trimDeadPrefixCount, hName]
        · simpa [trimDeadPrefixCount, hName] using ih
  have hDepthDrop :
      depth ≤ (layout.drop (trimDeadPrefixCount layout live)).length := by
    simpa [← drop_trimDeadPrefixCount_eq_trimDeadPrefix layout live] using
      hDepth
  have hDropLen :
      (layout.drop (trimDeadPrefixCount layout live)).length =
        layout.length - trimDeadPrefixCount layout live := by
    simp
  have hArith :
      trimDeadPrefixCount layout live +
          ((layout.drop (trimDeadPrefixCount layout live)).length - depth) =
        layout.length - depth := by
    rw [hDropLen]
    omega
  rw [hArith]

theorem cleanupLayoutRel_self_trimDeadPrefix
    {layout live : List Name} :
    SourceDirect.CleanupLayoutRel layout (trimDeadPrefix layout live) := by
  have hSuffix :
      (trimDeadPrefix layout live).drop
          ((trimDeadPrefix layout live).length -
            (trimDeadPrefix layout live).length) =
        layout.drop (layout.length - (trimDeadPrefix layout live).length) :=
    trimDeadPrefix_suffix_drop (layout := layout) (live := live)
      (depth := (trimDeadPrefix layout live).length) (Nat.le_refl _)
  simpa [SourceDirect.CleanupLayoutRel] using hSuffix.symm

theorem cleanupLayoutRel_trimDeadPrefix_append
    (pref base live : List Name) :
    SourceDirect.CleanupLayoutRel
      (trimDeadPrefix (pref ++ base) live) (trimDeadPrefix base live) := by
  induction pref with
  | nil =>
      simp [SourceDirect.CleanupLayoutRel]
  | cons name rest ih =>
      by_cases hLive : name ∈ live
      · have hRest :
            SourceDirect.CleanupLayoutRel (rest ++ base)
              (trimDeadPrefix base live) :=
          SourceDirect.CleanupLayoutRel.trans
            (cleanupLayoutRel_self_trimDeadPrefix
              (layout := rest ++ base) (live := live)) ih
        simpa [trimDeadPrefix, hLive, List.cons_append] using
          SourceDirect.CleanupLayoutRel.cons (name := name) hRest
      · simpa [trimDeadPrefix, hLive, List.cons_append] using ih

theorem cleanupLayoutRel_trimDeadPrefix_of_cleanupLayoutRel
    {layout base live : List Name}
    (hRel : SourceDirect.CleanupLayoutRel layout base) :
    SourceDirect.CleanupLayoutRel
      (trimDeadPrefix layout live) (trimDeadPrefix base live) := by
  let pref := layout.take (layout.length - base.length)
  have hLayout : pref ++ base = layout := by
    dsimp [pref]
    calc
      layout.take (layout.length - base.length) ++ base =
          layout.take (layout.length - base.length) ++
            layout.drop (layout.length - base.length) := by
            rw [hRel]
      _ = layout := List.take_append_drop (layout.length - base.length) layout
  rw [← hLayout]
  exact cleanupLayoutRel_trimDeadPrefix_append pref base live

theorem cleanupLayoutRel_suffix_drop {layout base : List Name} {depth : Nat}
    (hRel : SourceDirect.CleanupLayoutRel layout base)
    (hDepth : depth ≤ base.length) :
    layout.drop (layout.length - depth) =
      base.drop (base.length - depth) := by
  have hBaseLen : base.length ≤ layout.length := by
    have hLength := congrArg List.length hRel
    simp [SourceDirect.CleanupLayoutRel, List.length_drop] at hLength
    omega
  have hIndex :
      layout.length - depth =
        (layout.length - base.length) + (base.length - depth) := by
    omega
  calc
    layout.drop (layout.length - depth)
        =
          layout.drop
            ((layout.length - base.length) + (base.length - depth)) := by
          rw [hIndex]
    _ = (layout.drop (layout.length - base.length)).drop
          (base.length - depth) := by
          rw [List.drop_drop]
    _ = base.drop (base.length - depth) := by
          rw [hRel]

end Layout

namespace Checked
namespace Stmt

theorem regularOutLayout_cleanupLayoutRel (layout : List Name) (stmt : Stmt) :
    SourceDirect.CleanupLayoutRel (regularOutLayout layout stmt) layout := by
  cases stmt <;>
    simp [regularOutLayout, SourceDirect.CleanupLayoutRel.refl,
      SourceDirect.CleanupLayoutRel.cons]

theorem regularOutLayout_suffix_drop {layout : List Name} {stmt : Stmt}
    {depth : Nat}
    (hDepth : depth ≤ layout.length) :
    (regularOutLayout layout stmt).drop
        ((regularOutLayout layout stmt).length - depth) =
      layout.drop (layout.length - depth) := by
  cases stmt <;> simp [regularOutLayout]
  rename_i name value
  have hDrop :
      (name :: layout).drop ((name :: layout).length - depth) =
        layout.drop (layout.length - depth) := by
    have hNat :
        (name :: layout).length - depth =
          (layout.length - depth) + 1 := by
      simp
      omega
    rw [hNat]
    simp
  exact hDrop

theorem check?_suffix_drop {returns : List Name} {ctx : Ctx}
    {layout after : List Name} {stmt : Stmt} {outLayout : List Name}
    {depth : Nat}
    (hCheck :
      check? returns ctx layout after stmt = some outLayout)
    (hDepth : depth ≤ layout.length) :
    outLayout.drop (outLayout.length - depth) =
      layout.drop (layout.length - depth) := by
  cases stmt with
  | expr expr =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .expr expr)
        (layout := layout) hDepth
  | let_ name value =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .let_ name value)
        (layout := layout) hDepth
  | assign name value =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .assign name value)
        (layout := layout) hDepth
  | block body =>
      cases hBody :
          Block.check? returns (ctx.withProtectedLayout layout) layout
            (scopedAfter layout after) body with
      | none =>
          simp [check?, hBody] at hCheck
      | some bodyLayout =>
          simp [check?, hBody] at hCheck
          cases hCheck
          rfl
  | if_ cond body =>
      cases hBody :
          Block.check? returns (ctx.withProtectedLayout layout) layout
            (scopedAfter layout after) body with
      | none =>
          simp [check?, hBody] at hCheck
      | some bodyLayout =>
          simp [check?, hBody] at hCheck
          cases hCheck
          rfl
  | switch scrutinee cases defaultBody =>
      simp [check?] at hCheck
      rcases hCheck with ⟨_hBranches, hEq⟩
      subst outLayout
      rfl
  | for_ init cond post body =>
      simp only [check?] at hCheck
      cases hInit :
          Block.check? returns (ctx.withProtectedLayout layout) layout
            (NameSet.union
              (NameSet.unions
                [Reads.expr cond, after,
                  Block.liveBefore ctx
                    (NameSet.unions
                      [Reads.expr cond, Reads.block post, Reads.block body,
                        after]) post,
                  Block.liveBefore
                    (ctx.withLoop after
                      (Block.liveBefore ctx
                        (NameSet.unions
                          [Reads.expr cond, Reads.block post,
                            Reads.block body, after]) post))
                    (Block.liveBefore ctx
                      (NameSet.unions
                        [Reads.expr cond, Reads.block post, Reads.block body,
                          after]) post) body])
              layout) init with
      | none =>
          simp [hInit] at hCheck
      | some loopLayout =>
          simp [hInit] at hCheck
          by_cases hCond : ExprAccess.expr? 0 loopLayout cond = true
          · simp [hCond] at hCheck
            cases hPost :
                Block.check? returns (ctx.withProtectedLayout loopLayout)
                  loopLayout
                  (scopedAfter loopLayout
                    (NameSet.unions
                      [Reads.expr cond, Reads.block post, Reads.block body,
                        after])) post with
            | none =>
                simp [hPost] at hCheck
            | some postLayout =>
                simp [hPost] at hCheck
                cases hBody :
                    Block.check? returns
                      ((ctx.withLoop (scopedAfter loopLayout after)
                            (scopedAfter loopLayout
                              (Block.liveBefore ctx
                                (NameSet.unions
                                  [Reads.expr cond, Reads.block post,
                                    Reads.block body, after]) post))).withProtectedLayout
                        loopLayout)
                      loopLayout
                      (scopedAfter loopLayout
                        (Block.liveBefore ctx
                          (NameSet.unions
                            [Reads.expr cond, Reads.block post,
                              Reads.block body, after]) post)) body with
                | none =>
                    simp [hBody] at hCheck
                | some bodyLayout =>
                    simp [hBody] at hCheck
                    cases hCheck
                    rfl
          · simp [hCond] at hCheck
  | brk =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .brk)
        (layout := layout) hDepth
  | cont =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .cont)
        (layout := layout) hDepth
  | leave =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .leave)
        (layout := layout) hDepth
  | call targets functionName args =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .call targets functionName args)
        (layout := layout) hDepth
  | terminal kind =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .terminal kind)
        (layout := layout) hDepth
  | terminalArgs kind args =>
      simp [check?, regularOutLayout] at hCheck
      cases hCheck
      exact regularOutLayout_suffix_drop (stmt := .terminalArgs kind args)
        (layout := layout) hDepth

end Stmt
end Checked

namespace NamesAccess

theorem to_returnValuesAccessible {layout names : List Name} {offset : Nat} :
    Accessible layout offset names →
      SourceDirect.ReturnValuesRel.Accessible layout offset names := by
  intro hAccess
  induction names generalizing offset with
  | nil =>
      trivial
  | cons name rest ih =>
      rcases hAccess with ⟨hHead, hTail⟩
      exact ⟨hHead, ih hTail⟩

theorem offset_length_le_16_of_accessible_cons
    {layout : List Name} :
    ∀ {offset : Nat} {name : Name} {rest : List Name},
      Accessible layout offset (name :: rest) →
        offset + (name :: rest).length ≤ 16
  | offset, name, [], hAccess => by
      rcases hAccess with ⟨⟨idx, _hGet, hBound⟩, _hTail⟩
      simp
      omega
  | offset, name, next :: rest, hAccess => by
      rcases hAccess with ⟨_hHead, hTail⟩
      have hTailBound :=
        offset_length_le_16_of_accessible_cons
          (layout := layout) (offset := offset + 1)
          (name := next) (rest := rest) hTail
      simp at hTailBound ⊢
      omega

theorem length_le_16_of_accessible_zero {layout names : List Name}
    (hAccess : Accessible layout 0 names) :
    names.length ≤ 16 := by
  cases names with
  | nil =>
      simp
  | cons name rest =>
      have hBound :=
        offset_length_le_16_of_accessible_cons
          (layout := layout) (offset := 0) (name := name)
          (rest := rest) hAccess
      simpa using hBound

end NamesAccess

namespace SourceDirectBridge

/-!
The ordinary `SourceDirect.CtxRel` says that target layouts and source scopes
contain exactly the same names. Live cleanup intentionally invalidates that:
dead source variables stay in the source store/scope, while the target layout
drops a dead prefix. The live-layout bridge therefore uses a relaxed context
relation that keeps the control-cleanup depths and only requires the current
target layout to be a source-scope subset.
-/

def LiveCleanupScopeRel (layout : List Name) (depth : Nat)
    (scope : List Name) : Prop :=
  depth ≤ layout.length ∧
    ∀ {name : Name}, name ∈ layout.drop (layout.length - depth) →
      name ∈ scope

namespace LiveCleanupScopeRel

theorem of_cleanupScope {layout scope : List Name}
    (hRel : SourceDirect.CleanupScopeRel layout scope) :
    LiveCleanupScopeRel layout scope.length scope := by
  rcases hRel with ⟨hLength, hMem⟩
  constructor
  · rw [List.length_drop] at hLength
    omega
  · intro name hName
    exact (hMem name).mp hName

theorem cons {layout scope : List Name} {depth : Nat} {name : Name}
    (hRel : LiveCleanupScopeRel layout depth scope) :
    LiveCleanupScopeRel (name :: layout) depth scope := by
  rcases hRel with ⟨hDepth, hMem⟩
  constructor
  · simp
    omega
  · intro needle hNeedle
    have hDrop :
        (name :: layout).drop ((name :: layout).length - depth) =
          layout.drop (layout.length - depth) := by
      have hNat :
          (name :: layout).length - depth =
            (layout.length - depth) + 1 := by
        simp
        omega
      rw [hNat]
      simp
    rw [hDrop] at hNeedle
    exact hMem hNeedle

theorem prepend {layout scope : List Name} {depth : Nat}
    (added : List Name)
    (hRel : LiveCleanupScopeRel layout depth scope) :
    LiveCleanupScopeRel (added ++ layout) depth scope := by
  induction added with
  | nil =>
      simpa using hRel
  | cons name rest ih =>
      simpa [List.cons_append] using cons (name := name) ih

theorem of_cleanupLayoutRel {layout base scope : List Name} {depth : Nat}
    (hLayout : SourceDirect.CleanupLayoutRel layout base)
    (hRel : LiveCleanupScopeRel base depth scope) :
    LiveCleanupScopeRel layout depth scope := by
  rcases hRel with ⟨hDepth, hMem⟩
  have hBaseLen : base.length ≤ layout.length := by
    have hLen := congrArg List.length hLayout
    simp [List.length_drop] at hLen
    omega
  constructor
  · omega
  · intro needle hNeedle
    have hDrop :
        layout.drop (layout.length - depth) =
          base.drop (base.length - depth) := by
      calc
        layout.drop (layout.length - depth)
            = layout.drop
                ((layout.length - base.length) + (base.length - depth)) := by
                congr
                omega
        _ = (layout.drop (layout.length - base.length)).drop
              (base.length - depth) := by
                rw [List.drop_drop]
        _ = base.drop (base.length - depth) := by
                rw [hLayout]
    rw [hDrop] at hNeedle
    exact hMem hNeedle

theorem promoteAt_of_idx_lt_suffix {layout scope : List Name} {depth idx : Nat}
    {name : Name}
    (hRel : LiveCleanupScopeRel layout depth scope)
    (hGet : layout[idx]? = some name)
    (hIdx : idx < layout.length - depth) :
    LiveCleanupScopeRel (Layout.promoteAt idx layout) depth scope := by
  rcases hRel with ⟨hDepth, hMem⟩
  constructor
  · simpa [Layout.promoteAt_length] using hDepth
  · intro needle hNeedle
    have hDrop :=
      Layout.drop_promoteAt_suffix_eq
        (layout := layout) (idx := idx) (depth := depth) hGet hIdx
    rw [hDrop] at hNeedle
    exact hMem hNeedle

theorem promoteName_of_idx_lt_suffix {layout promoted scope : List Name}
    {depth idx : Nat} {name : Name}
    (hRel : LiveCleanupScopeRel layout depth scope)
    (hPromote : Layout.promoteName? layout name = some (promoted, idx))
    (hIdx : idx < layout.length - depth) :
    LiveCleanupScopeRel promoted depth scope := by
  rcases Layout.promoteName?_eq_some hPromote with
    ⟨hIndex, _hBound, hPromoted, _hTop, _hLength⟩
  rw [hPromoted]
  exact
    promoteAt_of_idx_lt_suffix hRel (Layout.index?_sound hIndex) hIdx

theorem prepareLoopAboveSuffix_of_depth_bound {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt} {reqs : List Prepare.NameReq}
    {depth : Nat} {scope : List Name} :
    ∀ {fuel layout prep finalLayout},
      Prepare.loopAboveSuffix protectedDepth returns live stmt reqs fuel layout =
          some (prep, finalLayout) →
      LiveCleanupScopeRel layout depth scope →
      depth ≤ protectedDepth →
      LiveCleanupScopeRel finalLayout depth scope := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hPrepare hRel _hDepth
      unfold Prepare.loopAboveSuffix at hPrepare
      cases hChecked : Prepare.checked? returns live layout stmt with
      | false =>
          simp [hChecked] at hPrepare
      | true =>
          simp [hChecked] at hPrepare
          rcases hPrepare with ⟨rfl, rfl⟩
          exact hRel
  | succ fuel ih =>
      intro layout prep finalLayout hPrepare hRel hDepth
      unfold Prepare.loopAboveSuffix at hPrepare
      cases hChecked : Prepare.checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hPrepare
          rcases hPrepare with ⟨rfl, rfl⟩
          exact hRel
      | false =>
          simp [hChecked] at hPrepare
          cases hPromote :
              Prepare.promoteBlockedAboveSuffix? protectedDepth layout reqs with
          | none =>
              simp [hPromote] at hPrepare
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promotedLayout⟩
              simp [hPromote] at hPrepare
              cases hRest :
                  Prepare.loopAboveSuffix protectedDepth returns live stmt reqs
                    fuel promotedLayout with
              | none =>
                  simp [hRest] at hPrepare
              | some restPair =>
                  rcases restPair with ⟨restPrep, restLayout⟩
                  simp [hRest] at hPrepare
                  rcases hPrepare with ⟨rfl, rfl⟩
                  rcases Prepare.promoteBlockedAboveSuffix?_eq_some hPromote
                    with ⟨name, idx, hPromoteStmt, hPromoteLayout, hIdx⟩
                  have hIdxDepth : idx < layout.length - depth := by
                    omega
                  have hPromotedRel :
                      LiveCleanupScopeRel promotedLayout depth scope :=
                    promoteName_of_idx_lt_suffix hRel hPromoteLayout
                      hIdxDepth
                  exact ih hRest hPromotedRel hDepth

theorem forStmtAboveSuffix_of_depth_bound {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    {layout : List Name} {depth : Nat} {scope : List Name}
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout))
    (hRel : LiveCleanupScopeRel layout depth scope)
    (hDepth : depth ≤ protectedDepth) :
    LiveCleanupScopeRel finalLayout depth scope := by
  unfold Prepare.forStmtAboveSuffix? at hPrepare
  exact prepareLoopAboveSuffix_of_depth_bound hPrepare hRel hDepth

theorem prepareLoopAboveSuffix_suffix_drop {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt} {reqs : List Prepare.NameReq}
    {depth : Nat} :
    ∀ {fuel layout prep finalLayout},
      Prepare.loopAboveSuffix protectedDepth returns live stmt reqs fuel layout =
          some (prep, finalLayout) →
      depth ≤ protectedDepth →
      finalLayout.drop (finalLayout.length - depth) =
        layout.drop (layout.length - depth) := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hPrepare _hDepth
      unfold Prepare.loopAboveSuffix at hPrepare
      cases hChecked : Prepare.checked? returns live layout stmt with
      | false =>
          simp [hChecked] at hPrepare
      | true =>
          simp [hChecked] at hPrepare
          rcases hPrepare with ⟨rfl, rfl⟩
          rfl
  | succ fuel ih =>
      intro layout prep finalLayout hPrepare hDepth
      unfold Prepare.loopAboveSuffix at hPrepare
      cases hChecked : Prepare.checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hPrepare
          rcases hPrepare with ⟨rfl, rfl⟩
          rfl
      | false =>
          simp [hChecked] at hPrepare
          cases hPromote :
              Prepare.promoteBlockedAboveSuffix? protectedDepth layout reqs with
          | none =>
              simp [hPromote] at hPrepare
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promotedLayout⟩
              simp [hPromote] at hPrepare
              cases hRest :
                  Prepare.loopAboveSuffix protectedDepth returns live stmt reqs
                    fuel promotedLayout with
              | none =>
                  simp [hRest] at hPrepare
              | some restPair =>
                  rcases restPair with ⟨restPrep, restLayout⟩
                  simp [hRest] at hPrepare
                  rcases hPrepare with ⟨rfl, rfl⟩
                  rcases Prepare.promoteBlockedAboveSuffix?_eq_some hPromote
                    with ⟨_name, idx, _hPromoteStmt, hPromoteLayout, hIdx⟩
                  have hIdxDepth : idx < layout.length - depth := by omega
                  have hPromotedDrop :
                      promotedLayout.drop (promotedLayout.length - depth) =
                        layout.drop (layout.length - depth) := by
                    rcases Layout.promoteName?_eq_some hPromoteLayout with
                      ⟨hIndex, _hBound, hPromoted, _hTop, _hLength⟩
                    rw [hPromoted]
                    exact
                      Layout.drop_promoteAt_suffix_eq
                        (Layout.index?_sound hIndex) hIdxDepth
                  exact (ih hRest hDepth).trans hPromotedDrop

theorem forStmtAboveSuffix_suffix_drop {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    {layout : List Name} {depth : Nat}
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout))
    (hDepth : depth ≤ protectedDepth) :
    finalLayout.drop (finalLayout.length - depth) =
      layout.drop (layout.length - depth) := by
  unfold Prepare.forStmtAboveSuffix? at hPrepare
  exact prepareLoopAboveSuffix_suffix_drop hPrepare hDepth

theorem forStmtAboveSuffix_trimDeadPrefix_suffix_mem
    {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    {layout liveLayout : List Name} {depth : Nat} {name : Name}
    (hLiveLayout : liveLayout = Layout.trimDeadPrefix layout live)
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns liveLayout live stmt =
        some (prep, finalLayout))
    (hDepthProtected : depth ≤ protectedDepth)
    (hDepthLive : depth ≤ liveLayout.length)
    (hMem :
      name ∈ finalLayout.drop (finalLayout.length - depth)) :
    name ∈ layout.drop (layout.length - depth) := by
  subst liveLayout
  have hPrepareDrop :
      finalLayout.drop (finalLayout.length - depth) =
        (Layout.trimDeadPrefix layout live).drop
          ((Layout.trimDeadPrefix layout live).length - depth) :=
    forStmtAboveSuffix_suffix_drop hPrepare hDepthProtected
  have hTrimDrop :
      (Layout.trimDeadPrefix layout live).drop
          ((Layout.trimDeadPrefix layout live).length - depth) =
        layout.drop (layout.length - depth) :=
    Layout.trimDeadPrefix_suffix_drop hDepthLive
  rw [hPrepareDrop, hTrimDrop] at hMem
  exact hMem

theorem forStmtAboveSuffix_trimDeadPrefix_suffix_drop
    {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    {layout liveLayout : List Name} {depth : Nat}
    (hLiveLayout : liveLayout = Layout.trimDeadPrefix layout live)
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns liveLayout live stmt =
        some (prep, finalLayout))
    (hDepthProtected : depth ≤ protectedDepth)
    (hDepthLive : depth ≤ liveLayout.length) :
    finalLayout.drop (finalLayout.length - depth) =
      layout.drop (layout.length - depth) := by
  subst liveLayout
  calc
    finalLayout.drop (finalLayout.length - depth)
        =
          (Layout.trimDeadPrefix layout live).drop
            ((Layout.trimDeadPrefix layout live).length - depth) :=
          forStmtAboveSuffix_suffix_drop hPrepare hDepthProtected
    _ = layout.drop (layout.length - depth) :=
          Layout.trimDeadPrefix_suffix_drop hDepthLive

theorem depth_le_live_length_of_nodup_sameScope {layout live scope : List Name}
    {depth : Nat}
    (hRel : LiveCleanupScopeRel layout depth scope)
    (hNoDup : layout.Nodup)
    (hSame : SourceDirect.SameScope live scope) :
    depth ≤ live.length := by
  let suffix := layout.drop (layout.length - depth)
  have hSuffixLen : suffix.length = depth := by
    have hDepth := hRel.1
    simp [suffix, List.length_drop]
    omega
  have hSuffixNodup : suffix.Nodup :=
    List.Nodup.sublist (List.drop_sublist (layout.length - depth) layout)
      hNoDup
  have hSuffixSubset : suffix ⊆ live := by
    intro name hName
    exact (hSame.2 name).mpr (hRel.2 (by simpa [suffix] using hName))
  have hSubperm : suffix.Subperm live :=
    List.subperm_of_subset hSuffixNodup hSuffixSubset
  have hLenLe := List.Subperm.length_le hSubperm
  omega

theorem trimDeadPrefix_of_keep :
    ∀ {layout live scope : List Name} {depth : Nat},
      LiveCleanupScopeRel layout depth scope →
      (∀ {name : Name},
        name ∈ layout.drop (layout.length - depth) → name ∈ live) →
      LiveCleanupScopeRel (Layout.trimDeadPrefix layout live) depth scope
  | [], live, scope, depth, hRel, _hKeep => by
      rcases hRel with ⟨hDepth, hMem⟩
      have hDepthZero : depth = 0 := by
        simp at hDepth
        omega
      subst depth
      constructor
      · simp [Layout.trimDeadPrefix]
      · intro name hName
        simp [Layout.trimDeadPrefix] at hName
  | name :: rest, live, scope, depth, hRel, hKeep => by
      by_cases hNameLive : name ∈ live
      · simpa [Layout.trimDeadPrefix, hNameLive] using hRel
      · rcases hRel with ⟨hDepth, hMem⟩
        have hDepthRest : depth ≤ rest.length := by
          by_contra hNot
          have hDepthEq : depth = rest.length + 1 := by
            simp at hDepth
            omega
          have hNameSuffix :
              name ∈
                (name :: rest).drop
                  ((name :: rest).length - depth) := by
            simp [hDepthEq]
          exact hNameLive (hKeep hNameSuffix)
        have hDropEq :
            (name :: rest).drop ((name :: rest).length - depth) =
              rest.drop (rest.length - depth) := by
          have hNat :
              (name :: rest).length - depth =
                (rest.length - depth) + 1 := by
            simp
            omega
          rw [hNat]
          simp
        have hRelRest : LiveCleanupScopeRel rest depth scope := by
          constructor
          · exact hDepthRest
          · intro needle hNeedle
            exact hMem (by
              rw [hDropEq]
              exact hNeedle)
        have hKeepRest :
            ∀ {needle : Name},
              needle ∈ rest.drop (rest.length - depth) → needle ∈ live := by
          intro needle hNeedle
          exact hKeep (by
            rw [hDropEq]
            exact hNeedle)
        simpa [Layout.trimDeadPrefix, hNameLive] using
          trimDeadPrefix_of_keep hRelRest hKeepRest

theorem trimDeadPrefix_of_sameScope {layout live scope : List Name}
    {depth : Nat}
    (hRel : LiveCleanupScopeRel layout depth scope)
    (hSame : SourceDirect.SameScope live scope) :
    LiveCleanupScopeRel (Layout.trimDeadPrefix layout live) depth scope :=
  trimDeadPrefix_of_keep hRel (by
    intro name hName
    exact (hSame.2 name).mpr (hRel.2 hName))

theorem full_layout {layout scope : List Name}
    (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ scope) :
    LiveCleanupScopeRel layout layout.length scope := by
  constructor
  · simp
  · intro name hName
    exact hSubset (by simpa using hName)

theorem break_of_ctxRel {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx} {scope : List Name} {depth : Nat}
    (hRel : SourceDirect.CtxRel retc source target)
    (hBreak : source.breakScope? = some scope)
    (hTargetDepth : target.breakDepth? = some depth) :
    LiveCleanupScopeRel target.layout depth scope := by
  rcases hRel with
    ⟨_hScope, hBreakDepth, _hContinueDepth, _hLeaveDepth, _hRetc,
      hBreakScope, _hContinueScope⟩
  have hDepthEq : some depth = some scope.length := by
    calc
      some depth = target.breakDepth? := hTargetDepth.symm
      _ = source.breakScope?.map List.length := hBreakDepth
      _ = some scope.length := by simp [hBreak]
  cases hDepthEq
  exact of_cleanupScope (hBreakScope scope hBreak)

theorem continue_of_ctxRel {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx} {scope : List Name} {depth : Nat}
    (hRel : SourceDirect.CtxRel retc source target)
    (hContinue : source.continueScope? = some scope)
    (hTargetDepth : target.continueDepth? = some depth) :
    LiveCleanupScopeRel target.layout depth scope := by
  rcases hRel with
    ⟨_hScope, _hBreakDepth, hContinueDepth, _hLeaveDepth, _hRetc,
      _hBreakScope, hContinueScope⟩
  have hDepthEq : some depth = some scope.length := by
    calc
      some depth = target.continueDepth? := hTargetDepth.symm
      _ = source.continueScope?.map List.length := hContinueDepth
      _ = some scope.length := by simp [hContinue]
  cases hDepthEq
  exact of_cleanupScope (hContinueScope scope hContinue)

end LiveCleanupScopeRel

end SourceDirectBridge

theorem cleanupLayoutRel_promoteName_of_idx_lt_protected
    {layout promoted base : List Name}
    {protectedDepth idx : Nat} {name : Name}
    (hRel : SourceDirect.CleanupLayoutRel layout base)
    (hPromote : Layout.promoteName? layout name = some (promoted, idx))
    (hIdx : idx < layout.length - protectedDepth)
    (hBaseDepth : base.length ≤ protectedDepth) :
    SourceDirect.CleanupLayoutRel promoted base := by
  rcases Layout.promoteName?_eq_some hPromote with
    ⟨hIndex, _hBound, hPromoted, _hTop, _hLength⟩
  rw [hPromoted]
  have hIdxBase : idx < layout.length - base.length := by
    omega
  have hDrop :=
    Layout.drop_promoteAt_suffix_eq
      (layout := layout) (idx := idx) (depth := base.length)
      (Layout.index?_sound hIndex) hIdxBase
  rw [SourceDirect.CleanupLayoutRel, hDrop]
  exact hRel

namespace Prepare

theorem loopAboveSuffix_cleanupLayoutRel_of_baseDepth
    {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt} {reqs : List NameReq}
    {base : List Name} :
    ∀ {fuel layout prep finalLayout},
      loopAboveSuffix protectedDepth returns live stmt reqs fuel layout =
          some (prep, finalLayout) →
      SourceDirect.CleanupLayoutRel layout base →
      base.length ≤ protectedDepth →
      SourceDirect.CleanupLayoutRel finalLayout base := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hPrepare hRel _hBaseDepth
      unfold loopAboveSuffix at hPrepare
      cases hChecked : checked? returns live layout stmt with
      | false =>
          simp [hChecked] at hPrepare
      | true =>
          simp [hChecked] at hPrepare
          rcases hPrepare with ⟨rfl, rfl⟩
          exact hRel
  | succ fuel ih =>
      intro layout prep finalLayout hPrepare hRel hBaseDepth
      unfold loopAboveSuffix at hPrepare
      cases hChecked : checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hPrepare
          rcases hPrepare with ⟨rfl, rfl⟩
          exact hRel
      | false =>
          simp [hChecked] at hPrepare
          cases hPromote :
              promoteBlockedAboveSuffix? protectedDepth layout reqs with
          | none =>
              simp [hPromote] at hPrepare
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promotedLayout⟩
              simp [hPromote] at hPrepare
              cases hRest :
                  loopAboveSuffix protectedDepth returns live stmt reqs fuel
                    promotedLayout with
              | none =>
                  simp [hRest] at hPrepare
              | some restPair =>
                  rcases restPair with ⟨restPrep, restLayout⟩
                  simp [hRest] at hPrepare
                  rcases hPrepare with ⟨rfl, rfl⟩
                  rcases promoteBlockedAboveSuffix?_eq_some hPromote with
                    ⟨name, idx, _hPromoteStmt, hPromoteLayout, hIdx⟩
                  have hPromotedRel :
                      SourceDirect.CleanupLayoutRel promotedLayout base :=
                    cleanupLayoutRel_promoteName_of_idx_lt_protected hRel
                      hPromoteLayout hIdx hBaseDepth
                  exact ih hRest hPromotedRel hBaseDepth

theorem forStmtAboveSuffix?_cleanupLayoutRel_of_baseDepth
    {protectedDepth : Nat}
    {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout base : List Name}
    (hPrepare :
      forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout))
    (hRel : SourceDirect.CleanupLayoutRel layout base)
    (hBaseDepth : base.length ≤ protectedDepth) :
    SourceDirect.CleanupLayoutRel finalLayout base := by
  unfold forStmtAboveSuffix? at hPrepare
  exact
    loopAboveSuffix_cleanupLayoutRel_of_baseDepth hPrepare hRel hBaseDepth

end Prepare

namespace SourceDirectBridge

def LiveHandlerRel (_layout : List Name) :
    Option (List Name) → Option Nat → Prop
  | none, none => True
  | some _scope, some _depth => True
  | _, _ => False

def LiveCtxRel (retc : Nat) (source : Source.Ctx)
    (target : Locals.Ctx) : Prop :=
  (∀ {name : Name}, name ∈ target.layout → name ∈ source.scope) ∧
    LiveHandlerRel target.layout source.breakScope? target.breakDepth? ∧
    LiveHandlerRel target.layout source.continueScope? target.continueDepth? ∧
    target.leaveDepth? = source.leaveScope?.map (fun _scope => 0) ∧
    target.leaveRetc = retc

def LiveControlRel (live : Ctx) (source : Source.Ctx) : Prop :=
  (∀ scope, source.breakScope? = some scope →
    SourceDirect.SameScope live.breakLive scope) ∧
    (∀ scope, source.continueScope? = some scope →
      SourceDirect.SameScope live.continueLive scope) ∧
      (∀ name, name ∈ live.returns →
        ∀ leaveScope, source.leaveScope? = some leaveScope →
          name ∈ leaveScope)

def LiveHandlerScopeRel (live : Ctx) (source : Source.Ctx) : Prop :=
  (∀ breakScope, source.breakScope? = some breakScope →
    ∀ name, name ∈ live.breakLive → name ∈ source.scope) ∧
    (∀ continueScope, source.continueScope? = some continueScope →
      ∀ name, name ∈ live.continueLive → name ∈ source.scope)

def LiveReturnScopeRel (live : Ctx) (source : Source.Ctx) : Prop :=
  ∀ name, name ∈ live.returns →
    ∀ leaveScope, source.leaveScope? = some leaveScope → name ∈ leaveScope

namespace LiveHandlerScopeRel

theorem initial {live : Ctx} : LiveHandlerScopeRel live Source.Ctx.initial := by
  constructor
  · intro scope hScope
    simp [Source.Ctx.initial] at hScope
  · intro scope hScope
    simp [Source.Ctx.initial] at hScope

theorem withLoop {live : Ctx} {source : Source.Ctx}
    {breakLive continueLive breakScope continueScope : List Name}
    (hBreakScope : ∀ name, name ∈ breakLive → name ∈ source.scope)
    (hContinueScope : ∀ name, name ∈ continueLive → name ∈ source.scope) :
    LiveHandlerScopeRel (live.withLoop breakLive continueLive)
      (source.withLoopControl breakScope continueScope) := by
  constructor
  · intro scope hScope name hName
    simp [Source.Ctx.withLoopControl] at hScope
    cases hScope
    exact hBreakScope name hName
  · intro scope hScope name hName
    simp [Source.Ctx.withLoopControl] at hScope
    cases hScope
    exact hContinueScope name hName

theorem withLoop_sameScope {live : Ctx} {source : Source.Ctx}
    {breakLive continueLive breakScope continueScope : List Name}
    (hBreak : SourceDirect.SameScope breakLive breakScope)
    (hContinue : SourceDirect.SameScope continueLive continueScope)
    (hBreakScope : ∀ name, name ∈ breakScope → name ∈ source.scope)
    (hContinueScope : ∀ name, name ∈ continueScope → name ∈ source.scope) :
    LiveHandlerScopeRel (live.withLoop breakLive continueLive)
      (source.withLoopControl breakScope continueScope) := by
  exact withLoop
    (live := live) (source := source)
    (breakScope := breakScope) (continueScope := continueScope)
    (fun name hName =>
      hBreakScope name ((hBreak.2 name).mp hName))
    (fun name hName =>
      hContinueScope name ((hContinue.2 name).mp hName))

theorem withLoop_self {live : Ctx} {source : Source.Ctx}
    {breakLive continueLive : List Name}
    (hBreak : SourceDirect.SameScope breakLive source.scope)
    (hContinue : SourceDirect.SameScope continueLive source.scope) :
    LiveHandlerScopeRel (live.withLoop breakLive continueLive)
      (source.withLoopControl source.scope source.scope) := by
  exact withLoop_sameScope
    (live := live) (source := source) hBreak hContinue
    (fun _ hName => hName) (fun _ hName => hName)

theorem withoutLoopControl {live : Ctx} {source : Source.Ctx} :
    LiveHandlerScopeRel live source.withoutLoopControl := by
  constructor
  · intro scope hScope
    simp [Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope
    simp [Source.Ctx.withoutLoopControl] at hScope

theorem withScopePrepend {live : Ctx} {source : Source.Ctx}
    (names : List Name)
    (hRel : LiveHandlerScopeRel live source) :
    LiveHandlerScopeRel live { source with scope := names ++ source.scope } := by
  constructor
  · intro breakScope hBreak name hName
    exact List.mem_append_right names (hRel.1 breakScope hBreak name hName)
  · intro continueScope hContinue name hName
    exact List.mem_append_right names
      (hRel.2 continueScope hContinue name hName)

theorem stmt_regular {prim : Source.PrimitiveSemantics}
    {program : Program} {live : Ctx} {source sourceOut : Source.Ctx}
    {fuel : Nat} {stmt : Stmt} {state sourceAfter : Source.State}
    (hRel : LiveHandlerScopeRel live source)
    (hRun :
      Source.Stmt.run prim program source fuel stmt state =
        .ok (Source.Outcome.regular sourceAfter, sourceOut)) :
    LiveHandlerScopeRel live sourceOut := by
  constructor
  · intro breakScope hBreak name hName
    have hBreakBase : source.breakScope? = some breakScope := by
      rw [← SourceDirect.SourceRun.stmt_regular_breakScope hRun]
      exact hBreak
    have hScopeBase : name ∈ source.scope :=
      hRel.1 breakScope hBreakBase name hName
    have hScope :
        sourceOut.scope = Scope.Stmt.outEnv source.scope stmt :=
      SourceDirect.SourceRun.stmt_regular_scope hRun
    rw [hScope]
    exact SourceDirect.SourceScope.stmt_outEnv_contains_of_contains
      (stmt := stmt) hScopeBase
  · intro continueScope hContinue name hName
    have hContinueBase :
        source.continueScope? = some continueScope := by
      rw [← SourceDirect.SourceRun.stmt_regular_continueScope hRun]
      exact hContinue
    have hScopeBase : name ∈ source.scope :=
      hRel.2 continueScope hContinueBase name hName
    have hScope :
        sourceOut.scope = Scope.Stmt.outEnv source.scope stmt :=
      SourceDirect.SourceRun.stmt_regular_scope hRun
    rw [hScope]
    exact SourceDirect.SourceScope.stmt_outEnv_contains_of_contains
      (stmt := stmt) hScopeBase

theorem block_regular {prim : Source.PrimitiveSemantics}
    {program : Program} {live : Ctx} {source sourceOut : Source.Ctx}
    {fuel : Nat} {block : Block} {state sourceAfter : Source.State}
    (hRel : LiveHandlerScopeRel live source)
    (hRun :
      Source.Block.runOpen prim program source fuel block state =
        .ok (Source.Outcome.regular sourceAfter, sourceOut)) :
    LiveHandlerScopeRel live sourceOut := by
  constructor
  · intro breakScope hBreak name hName
    have hBreakBase : source.breakScope? = some breakScope := by
      rw [← SourceDirect.SourceRun.block_runOpen_regular_breakScope hRun]
      exact hBreak
    have hScopeBase : name ∈ source.scope :=
      hRel.1 breakScope hBreakBase name hName
    have hScope :
        sourceOut.scope = Scope.Block.outEnv source.scope block :=
      SourceDirect.SourceRun.block_runOpen_regular_scope hRun
    rw [hScope]
    exact SourceDirect.SourceScope.block_outEnv_contains_of_contains
      (block := block) hScopeBase
  · intro continueScope hContinue name hName
    have hContinueBase :
        source.continueScope? = some continueScope := by
      rw [← SourceDirect.SourceRun.block_runOpen_regular_continueScope hRun]
      exact hContinue
    have hScopeBase : name ∈ source.scope :=
      hRel.2 continueScope hContinueBase name hName
    have hScope :
        sourceOut.scope = Scope.Block.outEnv source.scope block :=
      SourceDirect.SourceRun.block_runOpen_regular_scope hRun
    rw [hScope]
    exact SourceDirect.SourceScope.block_outEnv_contains_of_contains
      (block := block) hScopeBase

theorem breakLive_subset_let_liveBefore_of_scoped
    {live : Ctx} {source : Source.Ctx} {after : List Name}
    {declared : Name} {value : Expr 1} {breakScope : List Name}
    (hRel : LiveHandlerScopeRel live source)
    (hBreak : source.breakScope? = some breakScope)
    (hScoped : Scope.Stmt.Scoped source.scope (.let_ declared value))
    (hAfter :
      ∀ {name : Name}, name ∈ live.breakLive → name ∈ after) :
    ∀ {name : Name}, name ∈ live.breakLive →
      name ∈ Stmt.liveBefore live after (.let_ declared value) := by
  intro name hName
  exact
    LiveBefore.let_after_of_scoped_scope hScoped
      (hRel.1 breakScope hBreak name hName) (hAfter hName)

theorem continueLive_subset_let_liveBefore_of_scoped
    {live : Ctx} {source : Source.Ctx} {after : List Name}
    {declared : Name} {value : Expr 1} {continueScope : List Name}
    (hRel : LiveHandlerScopeRel live source)
    (hContinue : source.continueScope? = some continueScope)
    (hScoped : Scope.Stmt.Scoped source.scope (.let_ declared value))
    (hAfter :
      ∀ {name : Name}, name ∈ live.continueLive → name ∈ after) :
    ∀ {name : Name}, name ∈ live.continueLive →
      name ∈ Stmt.liveBefore live after (.let_ declared value) := by
  intro name hName
  exact
    LiveBefore.let_after_of_scoped_scope hScoped
      (hRel.2 continueScope hContinue name hName) (hAfter hName)

end LiveHandlerScopeRel

namespace LiveReturnScopeRel

theorem initial {live : Ctx} :
    LiveReturnScopeRel live Source.Ctx.initial := by
  intro name hName leaveScope hLeave
  simp [Source.Ctx.initial] at hLeave

theorem of_liveControl {live : Ctx} {source : Source.Ctx}
    (hRel : LiveControlRel live source) :
    LiveReturnScopeRel live source := by
  intro name hName leaveScope hLeave
  exact hRel.2.2 name hName leaveScope hLeave

theorem withLoop {live : Ctx} {source : Source.Ctx}
    {breakLive continueLive breakScope continueScope : List Name}
    (hRel : LiveReturnScopeRel live source) :
    LiveReturnScopeRel (live.withLoop breakLive continueLive)
      (source.withLoopControl breakScope continueScope) := by
  intro name hName leaveScope hLeave
  exact hRel name (by simpa [Ctx.withLoop] using hName) leaveScope (by
    simpa [Source.Ctx.withLoopControl] using hLeave)

theorem withoutLoopControl {live : Ctx} {source : Source.Ctx}
    (hRel : LiveReturnScopeRel live source) :
    LiveReturnScopeRel live source.withoutLoopControl := by
  intro name hName leaveScope hLeave
  exact hRel name hName leaveScope (by
    simpa [Source.Ctx.withoutLoopControl] using hLeave)

theorem withProtectedLayout {live : Ctx} {source : Source.Ctx}
    (layout : List Name)
    (hRel : LiveReturnScopeRel live source) :
    LiveReturnScopeRel (live.withProtectedLayout layout) source := by
  intro name hName leaveScope hLeave
  exact hRel name (by
    simpa [Ctx.withProtectedLayout, Ctx.withProtectedSuffixDepth] using hName)
    leaveScope hLeave

theorem stmt_regular {prim : Source.PrimitiveSemantics}
    {program : Program} {live : Ctx} {source sourceOut : Source.Ctx}
    {fuel : Nat} {stmt : Stmt} {state sourceAfter : Source.State}
    (hRel : LiveReturnScopeRel live source)
    (hRun :
      Source.Stmt.run prim program source fuel stmt state =
        .ok (Source.Outcome.regular sourceAfter, sourceOut)) :
    LiveReturnScopeRel live sourceOut := by
  intro name hName leaveScope hLeave
  exact hRel name hName leaveScope (by
    rw [SourceDirect.SourceRun.stmt_regular_leaveScope hRun] at hLeave
    exact hLeave)

theorem block_regular {prim : Source.PrimitiveSemantics}
    {program : Program} {live : Ctx} {source sourceOut : Source.Ctx}
    {fuel : Nat} {block : Block} {state sourceAfter : Source.State}
    (hRel : LiveReturnScopeRel live source)
    (hRun :
      Source.Block.runOpen prim program source fuel block state =
        .ok (Source.Outcome.regular sourceAfter, sourceOut)) :
    LiveReturnScopeRel live sourceOut := by
  intro name hName leaveScope hLeave
  exact hRel name hName leaveScope (by
    rw [SourceDirect.SourceRun.block_runOpen_regular_leaveScope hRun] at hLeave
    exact hLeave)

theorem returnScope_of_returns_eq {live : Ctx} {source : Source.Ctx}
    {returns : List Name}
    (hRel : LiveReturnScopeRel live source)
    (hReturns : live.returns = returns) :
    ∀ {leaveScope},
      source.leaveScope? = some leaveScope →
        ∀ name, name ∈ returns → name ∈ leaveScope := by
  intro leaveScope hLeave name hName
  exact hRel name (by simpa [hReturns] using hName) leaveScope hLeave

end LiveReturnScopeRel

namespace LiveControlRel

theorem initial : LiveControlRel {} Source.Ctx.initial := by
  constructor
  · intro scope hScope
    simp [Source.Ctx.initial] at hScope
  constructor
  · intro scope hScope
    simp [Source.Ctx.initial] at hScope
  · intro name hName
    simp at hName

theorem withLoop {live : Ctx} {source : Source.Ctx}
    {breakLive continueLive breakScope continueScope : List Name}
    (hRel : LiveControlRel live source)
    (hBreak : SourceDirect.SameScope breakLive breakScope)
    (hContinue : SourceDirect.SameScope continueLive continueScope) :
    LiveControlRel (live.withLoop breakLive continueLive)
      (source.withLoopControl breakScope continueScope) := by
  rcases hRel with ⟨_hBreakOld, _hContinueOld, hLeave⟩
  constructor
  · intro scope hScope
    simp [Source.Ctx.withLoopControl] at hScope
    cases hScope
    exact hBreak
  constructor
  · intro scope hScope
    simp [Source.Ctx.withLoopControl] at hScope
    cases hScope
    exact hContinue
  · intro name hName leaveScope hLeaveScope
    exact hLeave name hName leaveScope (by
      simpa [Source.Ctx.withLoopControl] using hLeaveScope)

theorem withoutLoopControl {live : Ctx} {source : Source.Ctx}
    (hRel : LiveControlRel live source) :
    LiveControlRel live source.withoutLoopControl := by
  rcases hRel with ⟨_hBreak, _hContinue, hLeave⟩
  constructor
  · intro scope hScope
    simp [Source.Ctx.withoutLoopControl] at hScope
  constructor
  · intro scope hScope
    simp [Source.Ctx.withoutLoopControl] at hScope
  · intro name hName leaveScope hLeaveScope
    exact hLeave name hName leaveScope (by
      simpa [Source.Ctx.withoutLoopControl] using hLeaveScope)

theorem stmt_regular {prim : Source.PrimitiveSemantics}
    {program : Program} {live : Ctx} {source sourceOut : Source.Ctx}
    {fuel : Nat} {stmt : Stmt} {state sourceAfter : Source.State}
    (hRel : LiveControlRel live source)
    (hRun :
      Source.Stmt.run prim program source fuel stmt state =
        .ok (Source.Outcome.regular sourceAfter, sourceOut)) :
    LiveControlRel live sourceOut := by
  constructor
  · intro scope hScope
    exact hRel.1 scope (by
      rw [SourceDirect.SourceRun.stmt_regular_breakScope hRun] at hScope
      exact hScope)
  constructor
  · intro scope hScope
    exact hRel.2.1 scope (by
      rw [SourceDirect.SourceRun.stmt_regular_continueScope hRun] at hScope
      exact hScope)
  · intro name hName leaveScope hLeave
    exact hRel.2.2 name hName leaveScope (by
      rw [SourceDirect.SourceRun.stmt_regular_leaveScope hRun] at hLeave
      exact hLeave)

theorem block_regular {prim : Source.PrimitiveSemantics}
    {program : Program} {live : Ctx} {source sourceOut : Source.Ctx}
    {fuel : Nat} {block : Block} {state sourceAfter : Source.State}
    (hRel : LiveControlRel live source)
    (hRun :
      Source.Block.runOpen prim program source fuel block state =
        .ok (Source.Outcome.regular sourceAfter, sourceOut)) :
    LiveControlRel live sourceOut := by
  constructor
  · intro scope hScope
    exact hRel.1 scope (by
      rw [SourceDirect.SourceRun.block_runOpen_regular_breakScope hRun]
        at hScope
      exact hScope)
  constructor
  · intro scope hScope
    exact hRel.2.1 scope (by
      rw [SourceDirect.SourceRun.block_runOpen_regular_continueScope hRun]
        at hScope
      exact hScope)
  · intro name hName leaveScope hLeave
    exact hRel.2.2 name hName leaveScope (by
      rw [SourceDirect.SourceRun.block_runOpen_regular_leaveScope hRun]
        at hLeave
      exact hLeave)

theorem breakCleanup_trimDeadPrefix {live : Ctx} {source : Source.Ctx}
    {layout scope : List Name} {depth : Nat}
    (hRel : LiveControlRel live source)
    (hBreak : source.breakScope? = some scope)
    (hCleanup : LiveCleanupScopeRel layout depth scope) :
    LiveCleanupScopeRel (Layout.trimDeadPrefix layout live.breakLive) depth
      scope :=
  LiveCleanupScopeRel.trimDeadPrefix_of_sameScope hCleanup
    (hRel.1 scope hBreak)

theorem continueCleanup_trimDeadPrefix {live : Ctx} {source : Source.Ctx}
    {layout scope : List Name} {depth : Nat}
    (hRel : LiveControlRel live source)
    (hContinue : source.continueScope? = some scope)
    (hCleanup : LiveCleanupScopeRel layout depth scope) :
    LiveCleanupScopeRel (Layout.trimDeadPrefix layout live.continueLive) depth
      scope :=
  LiveCleanupScopeRel.trimDeadPrefix_of_sameScope hCleanup
    (hRel.2.1 scope hContinue)

theorem returnScope_of_returns_eq {live : Ctx} {source : Source.Ctx}
    {returns : List Name}
    (hRel : LiveControlRel live source)
    (hReturns : live.returns = returns) :
    ∀ {leaveScope},
      source.leaveScope? = some leaveScope →
        ∀ name, name ∈ returns → name ∈ leaveScope := by
  intro leaveScope hLeave name hName
  exact hRel.2.2 name (by simpa [hReturns] using hName) leaveScope hLeave

end LiveControlRel

def LiveTargetControlRel (live : Ctx) (target : Locals.Ctx) : Prop :=
  (∀ {depth : Nat},
      target.breakDepth? = some depth →
        depth ≤ live.protectedDepth ∧
          ∀ {name : Name},
            name ∈ target.layout.drop (target.layout.length - depth) →
              name ∈ live.breakLive) ∧
    (∀ {depth : Nat},
      target.continueDepth? = some depth →
        depth ≤ live.protectedDepth ∧
          ∀ {name : Name},
            name ∈ target.layout.drop (target.layout.length - depth) →
              name ∈ live.continueLive)

def LiveTargetHandlerScopeRel (source : Source.Ctx)
    (target : Locals.Ctx) : Prop :=
  (∀ {depth : Nat},
      target.breakDepth? = some depth →
        ∀ {name : Name},
          name ∈ target.layout.drop (target.layout.length - depth) →
            name ∈ source.scope) ∧
    (∀ {depth : Nat},
      target.continueDepth? = some depth →
        ∀ {name : Name},
          name ∈ target.layout.drop (target.layout.length - depth) →
            name ∈ source.scope)

namespace LiveTargetControlRel

theorem withoutLoopControl {live : Ctx} {target : Locals.Ctx} :
    LiveTargetControlRel live target.withoutLoopControl := by
  constructor
  · intro depth hDepth
    simp [Locals.Ctx.withoutLoopControl] at hDepth
  · intro depth hDepth
    simp [Locals.Ctx.withoutLoopControl] at hDepth

theorem withProtectedLayout {live : Ctx} {target : Locals.Ctx}
    (layout : List Name)
    (hRel : LiveTargetControlRel live target) :
    LiveTargetControlRel (live.withProtectedLayout layout) target := by
  have hProtectedMono :
      live.protectedDepth ≤
        (live.withProtectedLayout layout).protectedDepth := by
    change
      max live.protectedSuffixDepth
          (max live.breakLive.length live.continueLive.length) ≤
        max (max live.protectedSuffixDepth layout.length)
          (max live.breakLive.length live.continueLive.length)
    exact
      Nat.max_le.mpr
        ⟨Nat.le_trans
          (Nat.le_max_left live.protectedSuffixDepth layout.length)
          (Nat.le_max_left (max live.protectedSuffixDepth layout.length)
            (max live.breakLive.length live.continueLive.length)),
        Nat.le_max_right (max live.protectedSuffixDepth layout.length)
          (max live.breakLive.length live.continueLive.length)⟩
  constructor
  · intro depth hDepth
    rcases hRel.1 hDepth with ⟨hDepthLe, hKeep⟩
    constructor
    · exact Nat.le_trans hDepthLe hProtectedMono
    · exact hKeep
  · intro depth hDepth
    rcases hRel.2 hDepth with ⟨hDepthLe, hKeep⟩
    constructor
    · exact Nat.le_trans hDepthLe hProtectedMono
    · exact hKeep

theorem withLoopControl_self_scopedAfter {live : Ctx}
    {target : Locals.Ctx} {breakAfter continueAfter : List Name}
    (hNoDup : target.layout.Nodup) :
    LiveTargetControlRel
      (live.withLoop (Checked.scopedAfter target.layout breakAfter)
        (Checked.scopedAfter target.layout continueAfter))
      (target.withLoopControl target.layout.length) := by
  have hBreakLen :
      target.layout.length ≤
        (Checked.scopedAfter target.layout breakAfter).length := by
    exact
      List.Subperm.length_le
        (List.subperm_of_subset hNoDup (by
          intro name hName
          exact Checked.mem_scopedAfter_of_mem_layout hName))
  have hContinueLen :
      target.layout.length ≤
        (Checked.scopedAfter target.layout continueAfter).length := by
    exact
      List.Subperm.length_le
        (List.subperm_of_subset hNoDup (by
          intro name hName
          exact Checked.mem_scopedAfter_of_mem_layout hName))
  constructor
  · intro depth hDepth
    have hDepthEq : depth = target.layout.length := by
      simpa [Locals.Ctx.withLoopControl] using hDepth.symm
    subst depth
    constructor
    · simp [Ctx.protectedDepth, Ctx.withLoop]
      omega
    · intro name hName
      have hLayoutMem : name ∈ target.layout := by
        simpa [Locals.Ctx.withLoopControl] using hName
      simpa [Ctx.withLoop, Checked.scopedAfter] using
        Checked.mem_scopedAfter_of_mem_layout
          (layout := target.layout) (after := breakAfter) hLayoutMem
  · intro depth hDepth
    have hDepthEq : depth = target.layout.length := by
      simpa [Locals.Ctx.withLoopControl] using hDepth.symm
    subst depth
    constructor
    · simp [Ctx.protectedDepth, Ctx.withLoop]
      omega
    · intro name hName
      have hLayoutMem : name ∈ target.layout := by
        simpa [Locals.Ctx.withLoopControl] using hName
      simpa [Ctx.withLoop, Checked.scopedAfter] using
        Checked.mem_scopedAfter_of_mem_layout
          (layout := target.layout) (after := continueAfter) hLayoutMem

theorem forStmtAboveSuffix {live : Ctx} {target : Locals.Ctx}
    {returns stmtLive : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {preparedLayout : List Name}
    (hPrepare :
      Prepare.forStmtAboveSuffix? live.protectedDepth returns target.layout
          stmtLive stmt =
        some (prep, preparedLayout))
    (hBreakLayout :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ target.layout.length)
    (hContinueLayout :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ target.layout.length)
    (hRel : LiveTargetControlRel live target) :
    LiveTargetControlRel (live.withProtectedLayout preparedLayout)
      (target.withLayout preparedLayout) := by
  have hProtectedMono :
      live.protectedDepth ≤
        (live.withProtectedLayout preparedLayout).protectedDepth := by
    change
      max live.protectedSuffixDepth
          (max live.breakLive.length live.continueLive.length) ≤
        max (max live.protectedSuffixDepth preparedLayout.length)
          (max live.breakLive.length live.continueLive.length)
    exact
      Nat.max_le.mpr
        ⟨Nat.le_trans
          (Nat.le_max_left live.protectedSuffixDepth preparedLayout.length)
          (Nat.le_max_left
            (max live.protectedSuffixDepth preparedLayout.length)
            (max live.breakLive.length live.continueLive.length)),
        Nat.le_max_right
          (max live.protectedSuffixDepth preparedLayout.length)
          (max live.breakLive.length live.continueLive.length)⟩
  constructor
  · intro depth hDepth
    have hDepthBase : target.breakDepth? = some depth := by
      simpa [Locals.Ctx.withLayout] using hDepth
    rcases hRel.1 hDepthBase with ⟨hDepthProtected, hKeep⟩
    have hBase :
        LiveCleanupScopeRel target.layout depth
          (target.layout.drop (target.layout.length - depth)) := by
      constructor
      · exact hBreakLayout hDepthBase
      · intro name hName
        exact hName
    have hPrepared :
        LiveCleanupScopeRel preparedLayout depth
          (target.layout.drop (target.layout.length - depth)) :=
      LiveCleanupScopeRel.forStmtAboveSuffix_of_depth_bound
        hPrepare hBase hDepthProtected
    constructor
    · exact Nat.le_trans hDepthProtected hProtectedMono
    · intro name hName
      exact hKeep (hPrepared.2 hName)
  · intro depth hDepth
    have hDepthBase : target.continueDepth? = some depth := by
      simpa [Locals.Ctx.withLayout] using hDepth
    rcases hRel.2 hDepthBase with ⟨hDepthProtected, hKeep⟩
    have hBase :
        LiveCleanupScopeRel target.layout depth
          (target.layout.drop (target.layout.length - depth)) := by
      constructor
      · exact hContinueLayout hDepthBase
      · intro name hName
        exact hName
    have hPrepared :
        LiveCleanupScopeRel preparedLayout depth
          (target.layout.drop (target.layout.length - depth)) :=
      LiveCleanupScopeRel.forStmtAboveSuffix_of_depth_bound
        hPrepare hBase hDepthProtected
    constructor
    · exact Nat.le_trans hDepthProtected hProtectedMono
    · intro name hName
      exact hKeep (hPrepared.2 hName)

theorem breakDepth_le_protectedDepth {live : Ctx} {target : Locals.Ctx}
    (hRel : LiveTargetControlRel live target)
    {depth : Nat}
    (hDepth : target.breakDepth? = some depth) :
    depth ≤ live.protectedDepth :=
  (hRel.1 hDepth).1

theorem continueDepth_le_protectedDepth {live : Ctx} {target : Locals.Ctx}
    (hRel : LiveTargetControlRel live target)
    {depth : Nat}
    (hDepth : target.continueDepth? = some depth) :
    depth ≤ live.protectedDepth :=
  (hRel.2 hDepth).1

end LiveTargetControlRel

namespace FunDef

theorem liveControlRel_bodyCtx (fn : FunDef) :
    LiveControlRel { returns := fn.returns }
      (SourceDirect.FunDef.sourceBodyCtx fn) := by
  constructor
  · intro scope hScope
    simp [SourceDirect.FunDef.sourceBodyCtx, Source.FunDef.bodyCtx,
      Source.Ctx.initial, Source.Ctx.withLeaveScope] at hScope
  constructor
  · intro scope hScope
    simp [SourceDirect.FunDef.sourceBodyCtx, Source.FunDef.bodyCtx,
      Source.Ctx.initial, Source.Ctx.withLeaveScope] at hScope
  · intro name hName leaveScope hLeave
    simp [SourceDirect.FunDef.sourceBodyCtx, Source.FunDef.bodyCtx,
      Source.Ctx.initial, Source.Ctx.withLeaveScope] at hName hLeave ⊢
    subst leaveScope
    exact List.mem_append.mpr (Or.inl hName)

theorem bodyCtx_breakCleanupScope (fn : FunDef) :
    ∀ {breakScope targetDepth},
      (SourceDirect.FunDef.sourceBodyCtx fn).breakScope? = some breakScope →
      (SourceDirect.FunDef.targetBodyCtx fn).breakDepth? = some targetDepth →
        LiveCleanupScopeRel (SourceDirect.FunDef.targetBodyCtx fn).layout
          targetDepth breakScope := by
  intro breakScope targetDepth hBreak _hTargetDepth
  simp [SourceDirect.FunDef.sourceBodyCtx, Source.FunDef.bodyCtx,
    Source.Ctx.initial, Source.Ctx.withLeaveScope] at hBreak

theorem bodyCtx_continueCleanupScope (fn : FunDef) :
    ∀ {continueScope targetDepth},
      (SourceDirect.FunDef.sourceBodyCtx fn).continueScope? =
        some continueScope →
      (SourceDirect.FunDef.targetBodyCtx fn).continueDepth? =
        some targetDepth →
        LiveCleanupScopeRel (SourceDirect.FunDef.targetBodyCtx fn).layout
          targetDepth continueScope := by
  intro continueScope targetDepth hContinue _hTargetDepth
  simp [SourceDirect.FunDef.sourceBodyCtx, Source.FunDef.bodyCtx,
    Source.Ctx.initial, Source.Ctx.withLeaveScope] at hContinue

end FunDef

namespace LiveCtxRel

theorem of_ctxRel {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx}
    (hRel : SourceDirect.CtxRel retc source target) :
    LiveCtxRel retc source target := by
  rcases hRel with
    ⟨hScope, hBreak, hContinue, hLeave, hRetc, _hBreakScope,
      _hContinueScope⟩
  refine ⟨?_, ?_, ?_, hLeave, hRetc⟩
  · intro name hName
    exact (hScope.2 name).mp hName
  · cases hSourceBreak : source.breakScope? with
    | none =>
        cases hTarget : target.breakDepth? <;>
          simp [LiveHandlerRel, hSourceBreak, hTarget] at hBreak ⊢
    | some breakScope =>
        cases hTarget : target.breakDepth? <;>
          simp [LiveHandlerRel, hSourceBreak, hTarget] at hBreak ⊢
  · cases hSourceContinue : source.continueScope? with
    | none =>
        cases hTarget : target.continueDepth? <;>
          simp [LiveHandlerRel, hSourceContinue, hTarget] at hContinue ⊢
    | some continueScope =>
        cases hTarget : target.continueDepth? <;>
          simp [LiveHandlerRel, hSourceContinue, hTarget] at hContinue ⊢

theorem initial :
    LiveCtxRel 0 Source.Ctx.initial Locals.Ctx.initial :=
  of_ctxRel SourceDirect.CtxRel.initial

theorem bodyCtx (fn : FunDef) :
    LiveCtxRel fn.returns.length (SourceDirect.FunDef.sourceBodyCtx fn)
      (SourceDirect.FunDef.targetBodyCtx fn) :=
  of_ctxRel (SourceDirect.FunDef.bodyCtxRel fn)

theorem withLayout_of_subset {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {layout : List Name}
    (hRel : LiveCtxRel retc source target)
    (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ target.layout) :
    LiveCtxRel retc source (target.withLayout layout) := by
  rcases hRel with
    ⟨hSourceSubset, hBreakDepth, hContinueDepth, hLeaveDepth, hRetc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro name hName
    exact hSourceSubset (hSubset hName)
  · simpa [Locals.Ctx.withLayout] using hBreakDepth
  · simpa [Locals.Ctx.withLayout] using hContinueDepth
  · simpa [Locals.Ctx.withLayout] using hLeaveDepth
  · simpa [Locals.Ctx.withLayout] using hRetc

theorem cleanupTo_trimDeadPrefix {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {live : List Name}
    (hRel : LiveCtxRel retc source target) :
    LiveCtxRel retc source
      (target.withLayout (Layout.trimDeadPrefix target.layout live)) :=
  withLayout_of_subset hRel
    (fun hMem => Layout.mem_trimDeadPrefix hMem)

theorem withoutLoopControl {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    (hRel : LiveCtxRel retc source target) :
    LiveCtxRel retc source.withoutLoopControl target.withoutLoopControl := by
  rcases hRel with
    ⟨hSourceSubset, _hBreakDepth, _hContinueDepth, hLeaveDepth, hRetc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro name hMem
    exact hSourceSubset (by
      simpa [Locals.Ctx.withoutLoopControl] using hMem)
  · simp [LiveHandlerRel, Source.Ctx.withoutLoopControl,
      Locals.Ctx.withoutLoopControl]
  · simp [LiveHandlerRel, Source.Ctx.withoutLoopControl,
      Locals.Ctx.withoutLoopControl]
  · simpa [Source.Ctx.withoutLoopControl, Locals.Ctx.withoutLoopControl] using
      hLeaveDepth
  · simpa [Locals.Ctx.withoutLoopControl] using hRetc

theorem withScopeCons {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {name : Name}
    (hRel : LiveCtxRel retc source target) :
    LiveCtxRel retc { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) := by
  rcases hRel with
    ⟨hSourceSubset, hBreakDepth, hContinueDepth, hLeaveDepth, hRetc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro other hMem
    simp [Locals.Ctx.withLayout] at hMem
    rcases hMem with hEq | hTail
    · simp [hEq]
    · exact List.mem_cons_of_mem name (hSourceSubset hTail)
  · simpa [Locals.Ctx.withLayout] using hBreakDepth
  · simpa [Locals.Ctx.withLayout] using hContinueDepth
  · simpa [Locals.Ctx.withLayout] using hLeaveDepth
  · simpa [Locals.Ctx.withLayout] using hRetc

theorem withScopePrepend {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} (names : List Name)
    (hRel : LiveCtxRel retc source target) :
    LiveCtxRel retc { source with scope := names ++ source.scope }
      (target.withLayout (names ++ target.layout)) := by
  induction names with
  | nil =>
      simpa [Locals.Ctx.withLayout] using hRel
  | cons name rest ih =>
      simpa [List.cons_append, Locals.Ctx.withLayout] using
        withScopeCons (name := name) ih

theorem withLoopControl_self {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    (hRel : LiveCtxRel retc source target) :
    LiveCtxRel retc
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) := by
  rcases hRel with
    ⟨hSourceSubset, _hBreakDepth, _hContinueDepth, hLeaveDepth, hRetc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro name hName
    simpa [Source.Ctx.withLoopControl] using hSourceSubset hName
  · simp [LiveHandlerRel, Source.Ctx.withLoopControl,
      Locals.Ctx.withLoopControl]
  · simp [LiveHandlerRel, Source.Ctx.withLoopControl,
      Locals.Ctx.withLoopControl]
  · simpa [Source.Ctx.withLoopControl, Locals.Ctx.withLoopControl] using
      hLeaveDepth
  · simpa [Locals.Ctx.withLoopControl] using hRetc

end LiveCtxRel

namespace LiveTargetHandlerScopeRel

theorem of_liveCtxRel {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx}
    (hRel : LiveCtxRel retc source target) :
    LiveTargetHandlerScopeRel source target := by
  constructor
  · intro depth _hDepth name hName
    exact hRel.1 (List.mem_of_mem_drop hName)
  · intro depth _hDepth name hName
    exact hRel.1 (List.mem_of_mem_drop hName)

theorem withoutLoopControl {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx}
    (hRel : LiveCtxRel retc source target) :
    LiveTargetHandlerScopeRel source.withoutLoopControl
      target.withoutLoopControl := by
  exact of_liveCtxRel (LiveCtxRel.withoutLoopControl hRel)

theorem withLoopControl_self {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx}
    (hRel : LiveCtxRel retc source target) :
    LiveTargetHandlerScopeRel
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) := by
  exact of_liveCtxRel (LiveCtxRel.withLoopControl_self hRel)

end LiveTargetHandlerScopeRel

structure LiveCtxCleanupRel (retc : Nat) (source : Source.Ctx)
    (target : Locals.Ctx) : Prop where
  ctxRel : LiveCtxRel retc source target
  breakCleanup :
    ∀ {breakScope targetDepth},
      source.breakScope? = some breakScope →
        target.breakDepth? = some targetDepth →
          LiveCleanupScopeRel target.layout targetDepth breakScope
  continueCleanup :
    ∀ {continueScope targetDepth},
      source.continueScope? = some continueScope →
        target.continueDepth? = some targetDepth →
          LiveCleanupScopeRel target.layout targetDepth continueScope

namespace LiveCtxCleanupRel

theorem of_ctxRel {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx}
    (hRel : SourceDirect.CtxRel retc source target) :
    LiveCtxCleanupRel retc source target := by
  refine
    { ctxRel := LiveCtxRel.of_ctxRel hRel
      breakCleanup := ?_
      continueCleanup := ?_ }
  · intro breakScope targetDepth hBreak hTargetDepth
    exact LiveCleanupScopeRel.break_of_ctxRel hRel hBreak hTargetDepth
  · intro continueScope targetDepth hContinue hTargetDepth
    exact LiveCleanupScopeRel.continue_of_ctxRel hRel hContinue hTargetDepth

theorem withoutLoopControl {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    (hRel : LiveCtxCleanupRel retc source target) :
    LiveCtxCleanupRel retc source.withoutLoopControl
      target.withoutLoopControl := by
  refine
    { ctxRel := LiveCtxRel.withoutLoopControl hRel.ctxRel
      breakCleanup := ?_
      continueCleanup := ?_ }
  · intro breakScope targetDepth hBreak _hTargetDepth
    simp [Source.Ctx.withoutLoopControl] at hBreak
  · intro continueScope targetDepth hContinue _hTargetDepth
    simp [Source.Ctx.withoutLoopControl] at hContinue

theorem withScopePrepend {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} (names : List Name)
    (hRel : LiveCtxCleanupRel retc source target) :
    LiveCtxCleanupRel retc { source with scope := names ++ source.scope }
      (target.withLayout (names ++ target.layout)) := by
  refine
    { ctxRel := LiveCtxRel.withScopePrepend names hRel.ctxRel
      breakCleanup := ?_
      continueCleanup := ?_ }
  · intro breakScope targetDepth hBreak hTargetDepth
    have hBreakBase : source.breakScope? = some breakScope := by
      simpa using hBreak
    have hTargetDepthBase : target.breakDepth? = some targetDepth := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    exact
      LiveCleanupScopeRel.prepend names
        (hRel.breakCleanup hBreakBase hTargetDepthBase)
  · intro continueScope targetDepth hContinue hTargetDepth
    have hContinueBase : source.continueScope? = some continueScope := by
      simpa using hContinue
    have hTargetDepthBase : target.continueDepth? = some targetDepth := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    exact
      LiveCleanupScopeRel.prepend names
        (hRel.continueCleanup hContinueBase hTargetDepthBase)

theorem withLayout_of_source_subset_cleanupLayoutRel {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {layout : List Name}
    (hRel : LiveCtxCleanupRel retc source target)
    (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ source.scope)
    (hCleanupLayout : SourceDirect.CleanupLayoutRel layout target.layout) :
    LiveCtxCleanupRel retc source (target.withLayout layout) := by
  rcases hRel.ctxRel with
    ⟨_hSourceSubset, hBreakDepth, hContinueDepth, hLeaveDepth, hRetc⟩
  refine
    { ctxRel := ?_
      breakCleanup := ?_
      continueCleanup := ?_ }
  · exact
      ⟨hSubset,
        by simpa [Locals.Ctx.withLayout] using hBreakDepth,
        by simpa [Locals.Ctx.withLayout] using hContinueDepth,
        by simpa [Locals.Ctx.withLayout] using hLeaveDepth,
        by simpa [Locals.Ctx.withLayout] using hRetc⟩
  · intro breakScope targetDepth hBreak hTargetDepth
    have hTargetDepthBase : target.breakDepth? = some targetDepth := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    exact
      LiveCleanupScopeRel.of_cleanupLayoutRel hCleanupLayout
        (hRel.breakCleanup hBreak hTargetDepthBase)
  · intro continueScope targetDepth hContinue hTargetDepth
    have hTargetDepthBase : target.continueDepth? = some targetDepth := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    exact
      LiveCleanupScopeRel.of_cleanupLayoutRel hCleanupLayout
        (hRel.continueCleanup hContinue hTargetDepthBase)

theorem promoteName_of_idx_lt_protectedDepth {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {promoted : List Name} {idx protectedDepth : Nat} {name : Name}
    (hRel : LiveCtxCleanupRel retc source target)
    (hPromote :
      Layout.promoteName? target.layout name = some (promoted, idx))
    (hIdx : idx < target.layout.length - protectedDepth)
    (hBreakDepth :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth)
    (hContinueDepth :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) :
    LiveCtxCleanupRel retc source (target.withLayout promoted) := by
  rcases Layout.promoteName?_eq_some hPromote with
    ⟨hIndex, _hBound, hPromoted, _hTop, _hLength⟩
  refine
    { ctxRel := ?_
      breakCleanup := ?_
      continueCleanup := ?_ }
  · exact
      LiveCtxRel.withLayout_of_subset hRel.ctxRel
        (by
          intro needle hNeedle
          rw [hPromoted] at hNeedle
          exact Layout.mem_of_mem_promoteAt hNeedle)
  · intro breakScope targetDepth hBreak hTargetDepth
    have hTargetDepthBase :
        target.breakDepth? = some targetDepth := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    have hBase :
        LiveCleanupScopeRel target.layout targetDepth breakScope :=
      hRel.breakCleanup hBreak hTargetDepthBase
    have hIdxDepth : idx < target.layout.length - targetDepth := by
      have hDepthLe := hBreakDepth hTargetDepthBase
      omega
    exact
      LiveCleanupScopeRel.promoteName_of_idx_lt_suffix
        hBase hPromote hIdxDepth
  · intro continueScope targetDepth hContinue hTargetDepth
    have hTargetDepthBase :
        target.continueDepth? = some targetDepth := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    have hBase :
        LiveCleanupScopeRel target.layout targetDepth continueScope :=
      hRel.continueCleanup hContinue hTargetDepthBase
    have hIdxDepth : idx < target.layout.length - targetDepth := by
      have hDepthLe := hContinueDepth hTargetDepthBase
      omega
    exact
      LiveCleanupScopeRel.promoteName_of_idx_lt_suffix
        hBase hPromote hIdxDepth

theorem prepareLoopAboveSuffix_of_depth_bounds {retc protectedDepth : Nat}
    {source : Source.Ctx} {returns live : List Name} {stmt : Stmt}
    {reqs : List Prepare.NameReq} :
    ∀ {fuel target prep finalLayout},
      Prepare.loopAboveSuffix protectedDepth returns live stmt reqs fuel
          target.layout =
        some (prep, finalLayout) →
      LiveCtxCleanupRel retc source target →
      (∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth) →
      (∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) →
      LiveCtxCleanupRel retc source (target.withLayout finalLayout) := by
  intro fuel
  induction fuel with
  | zero =>
      intro target prep finalLayout hPrepare hRel _hBreakDepth
        _hContinueDepth
      unfold Prepare.loopAboveSuffix at hPrepare
      cases hChecked : Prepare.checked? returns live target.layout stmt with
      | false =>
          simp [hChecked] at hPrepare
      | true =>
          simp [hChecked] at hPrepare
          rcases hPrepare with ⟨rfl, rfl⟩
          simpa [Locals.Ctx.withLayout] using hRel
  | succ fuel ih =>
      intro target prep finalLayout hPrepare hRel hBreakDepth hContinueDepth
      unfold Prepare.loopAboveSuffix at hPrepare
      cases hChecked : Prepare.checked? returns live target.layout stmt with
      | true =>
          simp [hChecked] at hPrepare
          rcases hPrepare with ⟨rfl, rfl⟩
          simpa [Locals.Ctx.withLayout] using hRel
      | false =>
          simp [hChecked] at hPrepare
          cases hPromote :
              Prepare.promoteBlockedAboveSuffix? protectedDepth target.layout
                reqs with
          | none =>
              simp [hPromote] at hPrepare
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promotedLayout⟩
              simp [hPromote] at hPrepare
              cases hRest :
                  Prepare.loopAboveSuffix protectedDepth returns live stmt reqs
                    fuel promotedLayout with
              | none =>
                  simp [hRest] at hPrepare
              | some restPair =>
                  rcases restPair with ⟨restPrep, restLayout⟩
                  simp [hRest] at hPrepare
                  rcases hPrepare with ⟨rfl, rfl⟩
                  rcases Prepare.promoteBlockedAboveSuffix?_eq_some hPromote
                    with ⟨name, idx, hPromoteStmt, hPromoteLayout, hIdx⟩
                  have hPromotedRel :
                      LiveCtxCleanupRel retc source
                        (target.withLayout promotedLayout) :=
                    promoteName_of_idx_lt_protectedDepth hRel hPromoteLayout
                      hIdx hBreakDepth hContinueDepth
                  exact
                    ih (target := target.withLayout promotedLayout)
                      (prep := restPrep) (finalLayout := restLayout)
                      (by simpa [Locals.Ctx.withLayout] using hRest)
                      hPromotedRel
                      (fun hDepth =>
                        hBreakDepth
                          (by
                            simpa [Locals.Ctx.withLayout] using hDepth))
                      (fun hDepth =>
                        hContinueDepth
                          (by
                            simpa [Locals.Ctx.withLayout] using hDepth))

theorem forStmtAboveSuffix_of_depth_bounds {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns target.layout live
          stmt =
        some (prep, finalLayout))
    (hRel : LiveCtxCleanupRel retc source target)
    (hBreakDepth :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth)
    (hContinueDepth :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) :
    LiveCtxCleanupRel retc source (target.withLayout finalLayout) := by
  unfold Prepare.forStmtAboveSuffix? at hPrepare
  exact
    prepareLoopAboveSuffix_of_depth_bounds hPrepare hRel hBreakDepth
      hContinueDepth

theorem withLoopControl_self {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    (hRel : LiveCtxCleanupRel retc source target) :
    LiveCtxCleanupRel retc
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) := by
  refine
    { ctxRel := LiveCtxRel.withLoopControl_self hRel.ctxRel
      breakCleanup := ?_
      continueCleanup := ?_ }
  · intro breakScope targetDepth hBreak hTargetDepth
    have hBreakScope : breakScope = source.scope := by
      simpa [Source.Ctx.withLoopControl] using hBreak.symm
    have hTargetDepthEq : targetDepth = target.layout.length := by
      simpa [Locals.Ctx.withLoopControl] using hTargetDepth.symm
    subst breakScope
    subst targetDepth
    exact LiveCleanupScopeRel.full_layout hRel.ctxRel.1
  · intro continueScope targetDepth hContinue hTargetDepth
    have hContinueScope : continueScope = source.scope := by
      simpa [Source.Ctx.withLoopControl] using hContinue.symm
    have hTargetDepthEq : targetDepth = target.layout.length := by
      simpa [Locals.Ctx.withLoopControl] using hTargetDepth.symm
    subst continueScope
    subst targetDepth
    exact LiveCleanupScopeRel.full_layout hRel.ctxRel.1

theorem withLoopControl_self_of_liveCtxRel {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    (hRel : LiveCtxRel retc source target) :
    LiveCtxCleanupRel retc
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) := by
  refine
    { ctxRel := LiveCtxRel.withLoopControl_self hRel
      breakCleanup := ?_
      continueCleanup := ?_ }
  · intro breakScope targetDepth hBreak hTargetDepth
    have hBreakScope : breakScope = source.scope := by
      simpa [Source.Ctx.withLoopControl] using hBreak.symm
    have hTargetDepthEq : targetDepth = target.layout.length := by
      simpa [Locals.Ctx.withLoopControl] using hTargetDepth.symm
    subst breakScope
    subst targetDepth
    exact LiveCleanupScopeRel.full_layout hRel.1
  · intro continueScope targetDepth hContinue hTargetDepth
    have hContinueScope : continueScope = source.scope := by
      simpa [Source.Ctx.withLoopControl] using hContinue.symm
    have hTargetDepthEq : targetDepth = target.layout.length := by
      simpa [Locals.Ctx.withLoopControl] using hTargetDepth.symm
    subst continueScope
    subst targetDepth
    exact LiveCleanupScopeRel.full_layout hRel.1

structure LiveCtxHandlerCleanupRel (retc : Nat) (source : Source.Ctx)
    (target : Locals.Ctx) (protectedDepth : Nat) : Prop where
  cleanup : LiveCtxCleanupRel retc source target
  breakDepth :
    ∀ {depth : Nat}, target.breakDepth? = some depth →
      depth ≤ protectedDepth
  continueDepth :
    ∀ {depth : Nat}, target.continueDepth? = some depth →
      depth ≤ protectedDepth

namespace LiveCtxHandlerCleanupRel

theorem of_cleanupRel {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    (hRel : LiveCtxCleanupRel retc source target)
    (hBreakDepth :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth)
    (hContinueDepth :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) :
    LiveCtxHandlerCleanupRel retc source target protectedDepth :=
  { cleanup := hRel
    breakDepth := hBreakDepth
    continueDepth := hContinueDepth }

theorem withLoopControl_self_of_liveCtxRel {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    (hRel : LiveCtxRel retc source target)
    (hDepth : target.layout.length ≤ protectedDepth) :
    LiveCtxHandlerCleanupRel retc
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) protectedDepth := by
  refine
    { cleanup := LiveCtxCleanupRel.withLoopControl_self_of_liveCtxRel hRel
      breakDepth := ?_
      continueDepth := ?_ }
  · intro depth hBreakDepth
    have hDepthEq : depth = target.layout.length := by
      simpa [Locals.Ctx.withLoopControl] using hBreakDepth.symm
    simpa [hDepthEq] using hDepth
  · intro depth hContinueDepth
    have hDepthEq : depth = target.layout.length := by
      simpa [Locals.Ctx.withLoopControl] using hContinueDepth.symm
    simpa [hDepthEq] using hDepth

theorem withoutLoopControl {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    (hRel : LiveCtxHandlerCleanupRel retc source target protectedDepth) :
    LiveCtxHandlerCleanupRel retc source.withoutLoopControl
      target.withoutLoopControl protectedDepth := by
  refine
    { cleanup := LiveCtxCleanupRel.withoutLoopControl hRel.cleanup
      breakDepth := ?_
      continueDepth := ?_ }
  · intro depth hDepth
    simp [Locals.Ctx.withoutLoopControl] at hDepth
  · intro depth hDepth
    simp [Locals.Ctx.withoutLoopControl] at hDepth

theorem forStmtAboveSuffix {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns target.layout live
          stmt =
        some (prep, finalLayout))
    (hRel : LiveCtxHandlerCleanupRel retc source target protectedDepth) :
    LiveCtxHandlerCleanupRel retc source (target.withLayout finalLayout)
      protectedDepth := by
  refine
    { cleanup :=
        LiveCtxCleanupRel.forStmtAboveSuffix_of_depth_bounds hPrepare
          hRel.cleanup hRel.breakDepth hRel.continueDepth
      breakDepth := ?_
      continueDepth := ?_ }
  · intro depth hDepth
    exact hRel.breakDepth (by simpa [Locals.Ctx.withLayout] using hDepth)
  · intro depth hDepth
    exact hRel.continueDepth (by simpa [Locals.Ctx.withLayout] using hDepth)

theorem forStmtAboveSuffix_of_trimDeadPrefix_all_mem {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {returns stmtLive liveLayout : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {preparedLayout : List Name}
    (hLiveLayout :
      liveLayout = Layout.trimDeadPrefix target.layout stmtLive)
    (hAllLive :
      ∀ {name : Name}, name ∈ target.layout → name ∈ stmtLive)
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns liveLayout stmtLive
          stmt =
        some (prep, preparedLayout))
    (hRel : LiveCtxHandlerCleanupRel retc source target protectedDepth) :
    LiveCtxHandlerCleanupRel retc source (target.withLayout preparedLayout)
      protectedDepth := by
  have hCleanupLayout :
      SourceDirect.CleanupLayoutRel liveLayout target.layout := by
    rw [hLiveLayout]
    exact Layout.cleanupLayoutRel_trimDeadPrefix_of_all_mem hAllLive
  have hLiveSubset :
      ∀ {name : Name}, name ∈ liveLayout → name ∈ source.scope := by
    intro name hMem
    exact hRel.cleanup.ctxRel.1 (by
      rw [hLiveLayout] at hMem
      exact Layout.mem_trimDeadPrefix hMem)
  have hTrimRel :
      LiveCtxHandlerCleanupRel retc source (target.withLayout liveLayout)
        protectedDepth := by
    refine
      { cleanup :=
          LiveCtxCleanupRel.withLayout_of_source_subset_cleanupLayoutRel
            hRel.cleanup hLiveSubset hCleanupLayout
        breakDepth := ?_
        continueDepth := ?_ }
    · intro depth hDepth
      exact hRel.breakDepth (by simpa [Locals.Ctx.withLayout] using hDepth)
    · intro depth hDepth
      exact hRel.continueDepth (by simpa [Locals.Ctx.withLayout] using hDepth)
  exact
    forStmtAboveSuffix
      (target := target.withLayout liveLayout)
      (by simpa [Locals.Ctx.withLayout] using hPrepare)
      hTrimRel

end LiveCtxHandlerCleanupRel

theorem trimDeadPrefix_of_handler_live_subset {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {live : Ctx} {keepLive : List Name}
    (hRel : LiveCtxCleanupRel retc source target)
    (hControl : LiveControlRel live source)
    (hBreakLiveSubset :
      ∀ {name : Name}, name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      ∀ {name : Name}, name ∈ live.continueLive → name ∈ keepLive) :
    LiveCtxCleanupRel retc source
      (target.withLayout (Layout.trimDeadPrefix target.layout keepLive)) := by
  let cleanedLayout := Layout.trimDeadPrefix target.layout keepLive
  refine
    { ctxRel := ?_
      breakCleanup := ?_
      continueCleanup := ?_ }
  · exact
      LiveCtxRel.withLayout_of_subset hRel.ctxRel
        (fun hMem => Layout.mem_trimDeadPrefix hMem)
  · intro breakScope targetDepth hBreak hTargetDepth
    have hTargetDepthBase : target.breakDepth? = some targetDepth := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    have hBase :
        LiveCleanupScopeRel target.layout targetDepth breakScope :=
      hRel.breakCleanup hBreak hTargetDepthBase
    exact
      LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
        (by
          intro name hName
          exact hBreakLiveSubset
            ((hControl.1 breakScope hBreak).2 name |>.mpr
              (hBase.2 hName)))
  · intro continueScope targetDepth hContinue hTargetDepth
    have hTargetDepthBase : target.continueDepth? = some targetDepth := by
      simpa [Locals.Ctx.withLayout] using hTargetDepth
    have hBase :
        LiveCleanupScopeRel target.layout targetDepth continueScope :=
      hRel.continueCleanup hContinue hTargetDepthBase
    exact
      LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
        (by
          intro name hName
          exact hContinueLiveSubset
            ((hControl.2.1 continueScope hContinue).2 name |>.mpr
              (hBase.2 hName)))

end LiveCtxCleanupRel

namespace LiveCtxCleanupRel

theorem breakDepth_le_protectedDepth {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {live : Ctx}
    (hRel : LiveCtxCleanupRel retc source target)
    (hControl : LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    {targetDepth : Nat}
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth := by
  rcases hRel with ⟨hCtxRel, hBreakCleanup, _hContinueCleanup⟩
  rcases hCtxRel with
    ⟨_hSubset, hBreakHandler, _hContinueHandler, _hLeaveDepth, _hRetc⟩
  cases hBreak : source.breakScope? with
  | none =>
      simp [LiveHandlerRel, hBreak, hTargetDepth] at hBreakHandler
  | some breakScope =>
      have hCleanup :
          LiveCleanupScopeRel target.layout targetDepth breakScope :=
        hBreakCleanup hBreak hTargetDepth
      have hDepthLive :
          targetDepth ≤ live.breakLive.length :=
        LiveCleanupScopeRel.depth_le_live_length_of_nodup_sameScope
          hCleanup hNoDup (hControl.1 breakScope hBreak)
      simp [Ctx.protectedDepth]
      omega

theorem continueDepth_le_protectedDepth {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {live : Ctx}
    (hRel : LiveCtxCleanupRel retc source target)
    (hControl : LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    {targetDepth : Nat}
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth := by
  rcases hRel with ⟨hCtxRel, _hBreakCleanup, hContinueCleanup⟩
  rcases hCtxRel with
    ⟨_hSubset, _hBreakHandler, hContinueHandler, _hLeaveDepth, _hRetc⟩
  cases hContinue : source.continueScope? with
  | none =>
      simp [LiveHandlerRel, hContinue, hTargetDepth] at hContinueHandler
  | some continueScope =>
      have hCleanup :
          LiveCleanupScopeRel target.layout targetDepth continueScope :=
        hContinueCleanup hContinue hTargetDepth
      have hDepthLive :
          targetDepth ≤ live.continueLive.length :=
        LiveCleanupScopeRel.depth_le_live_length_of_nodup_sameScope
          hCleanup hNoDup (hControl.2.1 continueScope hContinue)
      simp [Ctx.protectedDepth]
      omega

theorem forStmtAboveSuffix_of_liveControl {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {liveCtx : Ctx}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      Prepare.forStmtAboveSuffix? liveCtx.protectedDepth returns
          target.layout live stmt =
        some (prep, finalLayout))
    (hRel : LiveCtxCleanupRel retc source target)
    (hControl : LiveControlRel liveCtx source)
    (hNoDup : target.layout.Nodup) :
    LiveCtxCleanupRel retc source (target.withLayout finalLayout) := by
  exact
    forStmtAboveSuffix_of_depth_bounds hPrepare hRel
      (fun hDepth =>
        breakDepth_le_protectedDepth hRel hControl hNoDup hDepth)
      (fun hDepth =>
        continueDepth_le_protectedDepth hRel hControl hNoDup hDepth)

end LiveCtxCleanupRel

def LiveCtxOutcomeCleanupRel (retc : Nat) (source : Source.Ctx)
    (target : Locals.Ctx) (sourceOutcome : Source.Outcome) : Prop :=
  LiveCtxRel retc source target ∧
    match sourceOutcome.mode with
    | .brk =>
        ∀ {breakScope targetDepth},
          source.breakScope? = some breakScope →
            target.breakDepth? = some targetDepth →
              LiveCleanupScopeRel target.layout targetDepth breakScope
    | .cont =>
        ∀ {continueScope targetDepth},
          source.continueScope? = some continueScope →
            target.continueDepth? = some targetDepth →
              LiveCleanupScopeRel target.layout targetDepth continueScope
    | .regular | .leave | .halt _ => True

namespace LiveCtxOutcomeCleanupRel

theorem of_cleanupRel {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxCleanupRel retc source target) :
    LiveCtxOutcomeCleanupRel retc source target sourceOutcome := by
  constructor
  · exact hRel.ctxRel
  · cases sourceOutcome with
    | mk _sourceState sourceMode =>
        cases sourceMode <;> simp
        · intro breakScope targetDepth hBreak hTargetDepth
          exact hRel.breakCleanup hBreak hTargetDepth
        · intro continueScope targetDepth hContinue hTargetDepth
          exact hRel.continueCleanup hContinue hTargetDepth

theorem ctxRel {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxOutcomeCleanupRel retc source target sourceOutcome) :
    LiveCtxRel retc source target :=
  hRel.1

theorem breakCleanup {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxOutcomeCleanupRel retc source target sourceOutcome)
    (hMode : sourceOutcome.mode = .brk)
    {breakScope targetDepth}
    (hBreak : source.breakScope? = some breakScope)
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    LiveCleanupScopeRel target.layout targetDepth breakScope := by
  rcases hRel with ⟨_hCtx, hCleanup⟩
  cases sourceOutcome with
  | mk _sourceState sourceMode =>
      cases sourceMode <;> simp at hMode hCleanup
      exact hCleanup hBreak hTargetDepth

theorem continueCleanup {retc : Nat} {source : Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxOutcomeCleanupRel retc source target sourceOutcome)
    (hMode : sourceOutcome.mode = .cont)
    {continueScope targetDepth}
    (hContinue : source.continueScope? = some continueScope)
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    LiveCleanupScopeRel target.layout targetDepth continueScope := by
  rcases hRel with ⟨_hCtx, hCleanup⟩
  cases sourceOutcome with
  | mk _sourceState sourceMode =>
      cases sourceMode <;> simp at hMode hCleanup
      exact hCleanup hContinue hTargetDepth

theorem withLayout_of_cleanupLayoutRel {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {layout : List Name} {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxOutcomeCleanupRel retc source target sourceOutcome)
    (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ source.scope)
    (hLayout : SourceDirect.CleanupLayoutRel layout target.layout) :
    LiveCtxOutcomeCleanupRel retc source (target.withLayout layout)
      sourceOutcome := by
  have hCtx :
      LiveCtxRel retc source (target.withLayout layout) := by
    rcases hRel.1 with
      ⟨_hSourceSubset, hBreakDepth, hContinueDepth, hLeaveDepth, hRetc⟩
    exact
      ⟨ hSubset
      , by simpa [Locals.Ctx.withLayout] using hBreakDepth
      , by simpa [Locals.Ctx.withLayout] using hContinueDepth
      , by simpa [Locals.Ctx.withLayout] using hLeaveDepth
      , by simpa [Locals.Ctx.withLayout] using hRetc ⟩
  refine ⟨hCtx, ?_⟩
  cases sourceOutcome with
  | mk _sourceState sourceMode =>
      cases sourceMode <;> simp
      · intro breakScope targetDepth hBreak hTargetDepth
        have hTargetDepthBase : target.breakDepth? = some targetDepth := by
          simpa [Locals.Ctx.withLayout] using hTargetDepth
        exact
          LiveCleanupScopeRel.of_cleanupLayoutRel hLayout
            (LiveCtxOutcomeCleanupRel.breakCleanup hRel rfl hBreak
              hTargetDepthBase)
      · intro continueScope targetDepth hContinue hTargetDepth
        have hTargetDepthBase :
            target.continueDepth? = some targetDepth := by
          simpa [Locals.Ctx.withLayout] using hTargetDepth
        exact
          LiveCleanupScopeRel.of_cleanupLayoutRel hLayout
            (LiveCtxOutcomeCleanupRel.continueCleanup hRel rfl hContinue
              hTargetDepthBase)

theorem trimDeadPrefix_of_mode_live_subset {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {live : Ctx} {keepLive : List Name}
    {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxCleanupRel retc source target)
    (hControl : LiveControlRel live source)
    (hBreakLiveSubset :
      sourceOutcome.mode = .brk →
        ∀ {name : Name}, name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      sourceOutcome.mode = .cont →
        ∀ {name : Name}, name ∈ live.continueLive → name ∈ keepLive) :
    LiveCtxOutcomeCleanupRel retc source
      (target.withLayout (Layout.trimDeadPrefix target.layout keepLive))
      sourceOutcome := by
  let cleanedLayout := Layout.trimDeadPrefix target.layout keepLive
  refine ⟨?_, ?_⟩
  · exact
      LiveCtxRel.withLayout_of_subset hRel.ctxRel
        (fun hMem => Layout.mem_trimDeadPrefix hMem)
  · cases sourceOutcome with
    | mk _sourceState sourceMode =>
        cases sourceMode <;> simp
        · intro breakScope targetDepth hBreak hTargetDepth
          have hTargetDepthBase : target.breakDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout, cleanedLayout] using hTargetDepth
          have hBase :
              LiveCleanupScopeRel target.layout targetDepth breakScope :=
            hRel.breakCleanup hBreak hTargetDepthBase
          exact
            LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
              (by
                intro name hName
                exact hBreakLiveSubset rfl
                  ((hControl.1 breakScope hBreak).2 name |>.mpr
                    (hBase.2 hName)))
        · intro continueScope targetDepth hContinue hTargetDepth
          have hTargetDepthBase :
              target.continueDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout, cleanedLayout] using hTargetDepth
          have hBase :
              LiveCleanupScopeRel target.layout targetDepth continueScope :=
            hRel.continueCleanup hContinue hTargetDepthBase
          exact
            LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
              (by
                intro name hName
                exact hContinueLiveSubset rfl
                  ((hControl.2.1 continueScope hContinue).2 name |>.mpr
                    (hBase.2 hName)))

theorem trimDeadPrefix_of_mode_target_control {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {live : Ctx} {keepLive : List Name}
    {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxCleanupRel retc source target)
    (hControl : LiveTargetControlRel live target)
    (hBreakLiveSubset :
      sourceOutcome.mode = .brk →
        ∀ {name : Name}, name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      sourceOutcome.mode = .cont →
        ∀ {name : Name}, name ∈ live.continueLive → name ∈ keepLive) :
    LiveCtxOutcomeCleanupRel retc source
      (target.withLayout (Layout.trimDeadPrefix target.layout keepLive))
      sourceOutcome := by
  let cleanedLayout := Layout.trimDeadPrefix target.layout keepLive
  refine ⟨?_, ?_⟩
  · exact
      LiveCtxRel.withLayout_of_subset hRel.ctxRel
        (fun hMem => Layout.mem_trimDeadPrefix hMem)
  · cases sourceOutcome with
    | mk _sourceState sourceMode =>
        cases sourceMode <;> simp
        · intro breakScope targetDepth hBreak hTargetDepth
          have hTargetDepthBase : target.breakDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout, cleanedLayout] using hTargetDepth
          have hBase :
              LiveCleanupScopeRel target.layout targetDepth breakScope :=
            hRel.breakCleanup hBreak hTargetDepthBase
          exact
            LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
              (by
                intro name hName
                exact hBreakLiveSubset rfl
                  ((hControl.1 hTargetDepthBase).2 hName))
        · intro continueScope targetDepth hContinue hTargetDepth
          have hTargetDepthBase :
              target.continueDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout, cleanedLayout] using hTargetDepth
          have hBase :
              LiveCleanupScopeRel target.layout targetDepth continueScope :=
            hRel.continueCleanup hContinue hTargetDepthBase
          exact
            LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
              (by
                intro name hName
                exact hContinueLiveSubset rfl
                  ((hControl.2 hTargetDepthBase).2 hName))

theorem trimDeadPrefix_of_outer_mode_live_subset {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {live : Ctx} {keepLive : List Name}
    {outerOutcome sourceOutcome : Source.Outcome}
    (hRel :
      LiveCtxOutcomeCleanupRel retc source target outerOutcome)
    (hControl : LiveControlRel live source)
    (hBreakMode :
      sourceOutcome.mode = .brk → outerOutcome.mode = .brk)
    (hContinueMode :
      sourceOutcome.mode = .cont → outerOutcome.mode = .cont)
    (hBreakLiveSubset :
      sourceOutcome.mode = .brk →
        ∀ {name : Name}, name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      sourceOutcome.mode = .cont →
        ∀ {name : Name}, name ∈ live.continueLive → name ∈ keepLive) :
    LiveCtxOutcomeCleanupRel retc source
      (target.withLayout (Layout.trimDeadPrefix target.layout keepLive))
      sourceOutcome := by
  let cleanedLayout := Layout.trimDeadPrefix target.layout keepLive
  refine ⟨?_, ?_⟩
  · exact
      LiveCtxRel.withLayout_of_subset hRel.1
        (fun hMem => Layout.mem_trimDeadPrefix hMem)
  · cases sourceOutcome with
    | mk _sourceState sourceMode =>
        cases sourceMode <;> simp
        · intro breakScope targetDepth hBreak hTargetDepth
          have hTargetDepthBase : target.breakDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout, cleanedLayout] using hTargetDepth
          have hBase :
              LiveCleanupScopeRel target.layout targetDepth breakScope :=
            LiveCtxOutcomeCleanupRel.breakCleanup hRel
              (hBreakMode rfl) hBreak hTargetDepthBase
          exact
            LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
              (by
                intro name hName
                exact hBreakLiveSubset rfl
                  ((hControl.1 breakScope hBreak).2 name |>.mpr
                    (hBase.2 hName)))
        · intro continueScope targetDepth hContinue hTargetDepth
          have hTargetDepthBase :
              target.continueDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout, cleanedLayout] using hTargetDepth
          have hBase :
              LiveCleanupScopeRel target.layout targetDepth continueScope :=
            LiveCtxOutcomeCleanupRel.continueCleanup hRel
              (hContinueMode rfl) hContinue hTargetDepthBase
          exact
            LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
              (by
                intro name hName
                exact hContinueLiveSubset rfl
                  ((hControl.2.1 continueScope hContinue).2 name |>.mpr
                    (hBase.2 hName)))

theorem trimDeadPrefix_of_outer_mode_target_suffix {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {keepLive : List Name}
    {outerOutcome sourceOutcome : Source.Outcome}
    (hRel :
      LiveCtxOutcomeCleanupRel retc source target outerOutcome)
    (hBreakMode :
      sourceOutcome.mode = .brk → outerOutcome.mode = .brk)
    (hContinueMode :
      sourceOutcome.mode = .cont → outerOutcome.mode = .cont)
    (hBreakTargetLive :
      sourceOutcome.mode = .brk →
        ∀ {depth : Nat}, target.breakDepth? = some depth →
          ∀ {name : Name},
            name ∈ target.layout.drop (target.layout.length - depth) →
              name ∈ keepLive)
    (hContinueTargetLive :
      sourceOutcome.mode = .cont →
        ∀ {depth : Nat}, target.continueDepth? = some depth →
          ∀ {name : Name},
            name ∈ target.layout.drop (target.layout.length - depth) →
              name ∈ keepLive) :
    LiveCtxOutcomeCleanupRel retc source
      (target.withLayout (Layout.trimDeadPrefix target.layout keepLive))
      sourceOutcome := by
  let cleanedLayout := Layout.trimDeadPrefix target.layout keepLive
  refine ⟨?_, ?_⟩
  · exact
      LiveCtxRel.withLayout_of_subset hRel.1
        (fun hMem => Layout.mem_trimDeadPrefix hMem)
  · cases sourceOutcome with
    | mk _sourceState sourceMode =>
        cases sourceMode <;> simp
        · intro breakScope targetDepth hBreak hTargetDepth
          have hTargetDepthBase : target.breakDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout, cleanedLayout] using hTargetDepth
          have hBase :
              LiveCleanupScopeRel target.layout targetDepth breakScope :=
            LiveCtxOutcomeCleanupRel.breakCleanup hRel
              (hBreakMode rfl) hBreak hTargetDepthBase
          exact
            LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
              (by
                intro name hName
                exact hBreakTargetLive rfl hTargetDepthBase hName)
        · intro continueScope targetDepth hContinue hTargetDepth
          have hTargetDepthBase :
              target.continueDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout, cleanedLayout] using hTargetDepth
          have hBase :
              LiveCleanupScopeRel target.layout targetDepth continueScope :=
            LiveCtxOutcomeCleanupRel.continueCleanup hRel
              (hContinueMode rfl) hContinue hTargetDepthBase
          exact
            LiveCleanupScopeRel.trimDeadPrefix_of_keep hBase
              (by
                intro name hName
                exact hContinueTargetLive rfl hTargetDepthBase hName)

theorem forStmtAboveSuffix_of_depth_bounds {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    {sourceOutcome : Source.Outcome}
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns target.layout live
          stmt =
        some (prep, finalLayout))
    (hRel : LiveCtxOutcomeCleanupRel retc source target sourceOutcome)
    (hBreakDepth :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth)
    (hContinueDepth :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) :
    LiveCtxOutcomeCleanupRel retc source (target.withLayout finalLayout)
      sourceOutcome := by
  refine ⟨?_, ?_⟩
  · exact
      LiveCtxRel.withLayout_of_subset hRel.1
        (fun hMem => Prepare.forStmtAboveSuffix?_mem hPrepare hMem)
  · cases sourceOutcome with
    | mk _sourceState sourceMode =>
        cases sourceMode <;> simp
        · intro breakScope targetDepth hBreak hTargetDepth
          have hTargetDepthBase :
              target.breakDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout] using hTargetDepth
          exact
            LiveCleanupScopeRel.forStmtAboveSuffix_of_depth_bound hPrepare
              (LiveCtxOutcomeCleanupRel.breakCleanup hRel rfl hBreak
                hTargetDepthBase)
              (hBreakDepth hTargetDepthBase)
        · intro continueScope targetDepth hContinue hTargetDepth
          have hTargetDepthBase :
              target.continueDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout] using hTargetDepth
          exact
            LiveCleanupScopeRel.forStmtAboveSuffix_of_depth_bound hPrepare
              (LiveCtxOutcomeCleanupRel.continueCleanup hRel rfl hContinue
                hTargetDepthBase)
              (hContinueDepth hTargetDepthBase)

theorem forStmtAboveSuffix_of_mode_depth_bounds {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Name}
    {sourceOutcome : Source.Outcome}
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns target.layout live
          stmt =
        some (prep, finalLayout))
    (hRel : LiveCtxOutcomeCleanupRel retc source target sourceOutcome)
    (hBreakDepth :
      sourceOutcome.mode = .brk →
        ∀ {depth : Nat}, target.breakDepth? = some depth →
          depth ≤ protectedDepth)
    (hContinueDepth :
      sourceOutcome.mode = .cont →
        ∀ {depth : Nat}, target.continueDepth? = some depth →
          depth ≤ protectedDepth) :
    LiveCtxOutcomeCleanupRel retc source (target.withLayout finalLayout)
      sourceOutcome := by
  refine ⟨?_, ?_⟩
  · exact
      LiveCtxRel.withLayout_of_subset hRel.1
        (fun hMem => Prepare.forStmtAboveSuffix?_mem hPrepare hMem)
  · cases sourceOutcome with
    | mk _sourceState sourceMode =>
        cases sourceMode <;> simp
        · intro breakScope targetDepth hBreak hTargetDepth
          have hTargetDepthBase :
              target.breakDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout] using hTargetDepth
          exact
            LiveCleanupScopeRel.forStmtAboveSuffix_of_depth_bound hPrepare
              (LiveCtxOutcomeCleanupRel.breakCleanup hRel rfl hBreak
                hTargetDepthBase)
              (hBreakDepth rfl hTargetDepthBase)
        · intro continueScope targetDepth hContinue hTargetDepth
          have hTargetDepthBase :
              target.continueDepth? = some targetDepth := by
            simpa [Locals.Ctx.withLayout] using hTargetDepth
          exact
            LiveCleanupScopeRel.forStmtAboveSuffix_of_depth_bound hPrepare
              (LiveCtxOutcomeCleanupRel.continueCleanup hRel rfl hContinue
                hTargetDepthBase)
              (hContinueDepth rfl hTargetDepthBase)

theorem forStmtAboveSuffix_of_outer_mode_target_suffix
    {retc protectedDepth : Nat}
    {source : Source.Ctx} {target : Locals.Ctx}
    {returns live : List Name} {stmt : Stmt}
    {prep : List Locals.Stmt} {liveLayout finalLayout : List Name}
    {outerOutcome sourceOutcome : Source.Outcome}
    (hLiveLayout : liveLayout = Layout.trimDeadPrefix target.layout live)
    (hPrepare :
      Prepare.forStmtAboveSuffix? protectedDepth returns liveLayout live stmt =
        some (prep, finalLayout))
    (hRel :
      LiveCtxOutcomeCleanupRel retc source target outerOutcome)
    (hBreakMode :
      sourceOutcome.mode = .brk → outerOutcome.mode = .brk)
    (hContinueMode :
      sourceOutcome.mode = .cont → outerOutcome.mode = .cont)
    (hBreakDepth :
      sourceOutcome.mode = .brk →
        ∀ {depth : Nat}, target.breakDepth? = some depth →
          depth ≤ protectedDepth)
    (hContinueDepth :
      sourceOutcome.mode = .cont →
        ∀ {depth : Nat}, target.continueDepth? = some depth →
          depth ≤ protectedDepth)
    (hBreakTargetLive :
      sourceOutcome.mode = .brk →
        ∀ {depth : Nat}, target.breakDepth? = some depth →
          ∀ {name : Name},
            name ∈ target.layout.drop (target.layout.length - depth) →
              name ∈ live)
    (hContinueTargetLive :
      sourceOutcome.mode = .cont →
        ∀ {depth : Nat}, target.continueDepth? = some depth →
          ∀ {name : Name},
            name ∈ target.layout.drop (target.layout.length - depth) →
              name ∈ live) :
    LiveCtxOutcomeCleanupRel retc source (target.withLayout finalLayout)
      sourceOutcome := by
  have hTrim :
      LiveCtxOutcomeCleanupRel retc source
        (target.withLayout (Layout.trimDeadPrefix target.layout live))
        sourceOutcome :=
    trimDeadPrefix_of_outer_mode_target_suffix hRel hBreakMode hContinueMode
      hBreakTargetLive hContinueTargetLive
  have hPrepared :
      LiveCtxOutcomeCleanupRel retc source
        ((target.withLayout liveLayout).withLayout finalLayout)
        sourceOutcome :=
    forStmtAboveSuffix_of_mode_depth_bounds
      (target := target.withLayout liveLayout)
      (hPrepare := by
        simpa [Locals.Ctx.withLayout] using hPrepare)
      (by simpa [hLiveLayout] using hTrim)
      (by
        intro hMode depth hDepth
        exact hBreakDepth hMode
          (by simpa [Locals.Ctx.withLayout] using hDepth))
      (by
        intro hMode depth hDepth
        exact hContinueDepth hMode
          (by simpa [Locals.Ctx.withLayout] using hDepth))
  simpa [Locals.Ctx.withLayout] using hPrepared

theorem breakDepth_le_protectedDepth {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {live : Ctx}
    {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxOutcomeCleanupRel retc source target sourceOutcome)
    (hMode : sourceOutcome.mode = .brk)
    (hControl : LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    {targetDepth : Nat}
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth := by
  rcases hRel.1 with
    ⟨_hSubset, hBreakHandler, _hContinueHandler, _hLeaveDepth, _hRetc⟩
  cases hBreak : source.breakScope? with
  | none =>
      simp [LiveHandlerRel, hBreak, hTargetDepth] at hBreakHandler
  | some breakScope =>
      have hCleanup :
          LiveCleanupScopeRel target.layout targetDepth breakScope :=
        LiveCtxOutcomeCleanupRel.breakCleanup hRel hMode hBreak hTargetDepth
      have hDepthLive :
          targetDepth ≤ live.breakLive.length :=
        LiveCleanupScopeRel.depth_le_live_length_of_nodup_sameScope
          hCleanup hNoDup (hControl.1 breakScope hBreak)
      simp [Ctx.protectedDepth]
      omega

theorem continueDepth_le_protectedDepth {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {live : Ctx}
    {sourceOutcome : Source.Outcome}
    (hRel : LiveCtxOutcomeCleanupRel retc source target sourceOutcome)
    (hMode : sourceOutcome.mode = .cont)
    (hControl : LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    {targetDepth : Nat}
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth := by
  rcases hRel.1 with
    ⟨_hSubset, _hBreakHandler, hContinueHandler, _hLeaveDepth, _hRetc⟩
  cases hContinue : source.continueScope? with
  | none =>
      simp [LiveHandlerRel, hContinue, hTargetDepth] at hContinueHandler
  | some continueScope =>
      have hCleanup :
          LiveCleanupScopeRel target.layout targetDepth continueScope :=
        LiveCtxOutcomeCleanupRel.continueCleanup hRel hMode hContinue
          hTargetDepth
      have hDepthLive :
          targetDepth ≤ live.continueLive.length :=
        LiveCleanupScopeRel.depth_le_live_length_of_nodup_sameScope
          hCleanup hNoDup (hControl.2.1 continueScope hContinue)
      simp [Ctx.protectedDepth]
      omega

end LiveCtxOutcomeCleanupRel

theorem LiveCtxRel.breakDepth_some {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {scope : List Name}
    (hRel : LiveCtxRel retc source target)
    (hBreak : source.breakScope? = some scope) :
    ∃ depth, target.breakDepth? = some depth := by
  rcases hRel with
    ⟨_hSubset, hBreakRel, _hContinueRel, _hLeaveDepth, _hRetc⟩
  cases hTarget : target.breakDepth? with
  | none =>
      simp [LiveHandlerRel, hBreak, hTarget] at hBreakRel
  | some depth =>
      exact ⟨depth, rfl⟩

theorem LiveCtxRel.breakScope_some_of_target {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {depth : Nat}
    (hRel : LiveCtxRel retc source target)
    (hDepth : target.breakDepth? = some depth) :
    ∃ scope, source.breakScope? = some scope := by
  rcases hRel with
    ⟨_hSubset, hBreakRel, _hContinueRel, _hLeaveDepth, _hRetc⟩
  cases hBreak : source.breakScope? with
  | none =>
      simp [LiveHandlerRel, hBreak, hDepth] at hBreakRel
  | some scope =>
      exact ⟨scope, rfl⟩

theorem LiveCtxRel.continueDepth_some {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {scope : List Name}
    (hRel : LiveCtxRel retc source target)
    (hContinue : source.continueScope? = some scope) :
    ∃ depth, target.continueDepth? = some depth := by
  rcases hRel with
    ⟨_hSubset, _hBreakRel, hContinueRel, _hLeaveDepth, _hRetc⟩
  cases hTarget : target.continueDepth? with
  | none =>
      simp [LiveHandlerRel, hContinue, hTarget] at hContinueRel
  | some depth =>
      exact ⟨depth, rfl⟩

theorem LiveCtxRel.continueScope_some_of_target {retc : Nat}
    {source : Source.Ctx} {target : Locals.Ctx} {depth : Nat}
    (hRel : LiveCtxRel retc source target)
    (hDepth : target.continueDepth? = some depth) :
    ∃ scope, source.continueScope? = some scope := by
  rcases hRel with
    ⟨_hSubset, _hBreakRel, hContinueRel, _hLeaveDepth, _hRetc⟩
  cases hContinue : source.continueScope? with
  | none =>
      simp [LiveHandlerRel, hContinue, hDepth] at hContinueRel
  | some scope =>
      exact ⟨scope, rfl⟩

def LiveStmtRunResultRel (retc : Nat) (returns : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match sourceResult.1.mode, targetResult.1.mode with
  | .regular, .regular =>
      SourceDirect.StateRel targetResult.2.layout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | _, _ =>
      ∃ outcomeLayout,
        SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
          sourceResult.1 targetResult.1 ∧
          LiveCtxRel retc sourceResult.2 targetResult.2

namespace LiveStmtRunResultRel

theorem regular {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel : SourceDirect.StateRel targetCtx.layout hiddenReturns source target)
    (hCtx : LiveCtxRel retc sourceCtx targetCtx) :
    LiveStmtRunResultRel retc returns hiddenReturns
      (Source.Outcome.regular source, sourceCtx)
      (Structured.Outcome.regular target, targetCtx) := by
  exact ⟨hRel, hCtx⟩

theorem of_sourceDirect {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      SourceDirect.StmtRunResultRel retc returns hiddenReturns sourceResult
        targetResult) :
    LiveStmtRunResultRel retc returns hiddenReturns sourceResult
      targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp only [SourceDirect.StmtRunResultRel,
              LiveStmtRunResultRel] at hRel ⊢
          · exact ⟨hRel.1, LiveCtxRel.of_ctxRel hRel.2⟩
          all_goals
            rcases hRel with ⟨outcomeLayout, hOutcomeRel, hCtxRel⟩
            exact ⟨outcomeLayout, hOutcomeRel, LiveCtxRel.of_ctxRel hCtxRel⟩

theorem regular_stateRel {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns
        (Source.Outcome.regular source, sourceCtx)
        (Structured.Outcome.regular target, targetCtx)) :
    SourceDirect.StateRel targetCtx.layout hiddenReturns source target ∧
      LiveCtxRel retc sourceCtx targetCtx := by
  simpa [LiveStmtRunResultRel, Source.Outcome.regular,
    Structured.Outcome.regular] using hRel

theorem source_regular_target_regular {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns
        (Source.Outcome.regular source, sourceCtx)
        (targetOutcome, targetCtx)) :
    ∃ target,
      targetOutcome = Structured.Outcome.regular target ∧
        SourceDirect.StateRel targetCtx.layout hiddenReturns source target ∧
        LiveCtxRel retc sourceCtx targetCtx := by
  cases targetOutcome with
  | mk targetState targetMode =>
      cases targetMode with
      | regular =>
          exact ⟨targetState, rfl, hRel.1, hRel.2⟩
      | brk =>
          simp [LiveStmtRunResultRel, SourceDirect.StmtOutcomeRel,
            Source.Outcome.regular, Locals.Source.Outcome.regular] at hRel
      | cont =>
          simp [LiveStmtRunResultRel, SourceDirect.StmtOutcomeRel,
            Source.Outcome.regular, Locals.Source.Outcome.regular] at hRel
      | leave =>
          simp [LiveStmtRunResultRel, SourceDirect.StmtOutcomeRel,
            Source.Outcome.regular, Locals.Source.Outcome.regular] at hRel
      | halt kind =>
          simp [LiveStmtRunResultRel, SourceDirect.StmtOutcomeRel,
            Source.Outcome.regular, Locals.Source.Outcome.regular] at hRel

theorem outcomeRel_of_nonregular {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns
        (sourceOutcome, sourceCtx) (targetOutcome, targetCtx))
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    ∃ outcomeLayout,
      SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
        sourceOutcome targetOutcome := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveStmtRunResultRel] at hRel hNonregular ⊢
          all_goals exact hRel.1

theorem of_nonregular {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hOutcome :
      ∃ outcomeLayout,
        SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
          sourceOutcome targetOutcome)
    (hCtx : LiveCtxRel retc sourceCtx targetCtx)
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    LiveStmtRunResultRel retc returns hiddenReturns
      (sourceOutcome, sourceCtx) (targetOutcome, targetCtx) := by
  rcases hOutcome with ⟨outcomeLayout, hOutcomeRel⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases sourceMode with
      | regular =>
          exact False.elim (hNonregular rfl)
      | brk =>
          simpa [LiveStmtRunResultRel] using
            (show ∃ outcomeLayout,
              SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
                { state := sourceState, mode := Locals.Source.Mode.brk }
                targetOutcome ∧
                LiveCtxRel retc sourceCtx targetCtx from
              ⟨outcomeLayout, hOutcomeRel, hCtx⟩)
      | cont =>
          simpa [LiveStmtRunResultRel] using
            (show ∃ outcomeLayout,
              SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
                { state := sourceState, mode := Locals.Source.Mode.cont }
                targetOutcome ∧
                LiveCtxRel retc sourceCtx targetCtx from
              ⟨outcomeLayout, hOutcomeRel, hCtx⟩)
      | leave =>
          simpa [LiveStmtRunResultRel] using
            (show ∃ outcomeLayout,
              SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
                { state := sourceState, mode := Locals.Source.Mode.leave }
                targetOutcome ∧
                LiveCtxRel retc sourceCtx targetCtx from
              ⟨outcomeLayout, hOutcomeRel, hCtx⟩)
      | halt kind =>
          simpa [LiveStmtRunResultRel] using
            (show ∃ outcomeLayout,
              SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
                (Source.Outcome.halt kind sourceState) targetOutcome ∧
                LiveCtxRel retc sourceCtx targetCtx from
              ⟨outcomeLayout, hOutcomeRel, hCtx⟩)

theorem target_nonregular_of_source_nonregular {retc : Nat}
    {returns : List Name} {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns
        (sourceOutcome, sourceCtx) (targetOutcome, targetCtx))
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    targetOutcome.mode ≠ .regular := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveStmtRunResultRel, SourceDirect.StmtOutcomeRel] at hRel hNonregular ⊢

end LiveStmtRunResultRel

def LiveBlockOpenResultRel (retc : Nat) (returns : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match sourceResult.1.mode, targetResult.1.mode with
  | .regular, .regular =>
      SourceDirect.StateRel targetResult.2.layout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | _, _ =>
      ∃ outcomeLayout,
        SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
          sourceResult.1 targetResult.1 ∧
          LiveCtxRel retc sourceResult.2 targetResult.2

namespace LiveBlockOpenResultRel

theorem regular {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel : SourceDirect.StateRel targetCtx.layout hiddenReturns source target)
    (hCtx : LiveCtxRel retc sourceCtx targetCtx) :
    LiveBlockOpenResultRel retc returns hiddenReturns
      (Source.Outcome.regular source, sourceCtx)
      (Structured.Outcome.regular target, targetCtx) := by
  exact ⟨hRel, hCtx⟩

theorem of_sourceDirect {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      SourceDirect.BlockOpenResultRel retc returns hiddenReturns sourceResult
        targetResult) :
    LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
      targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp only [SourceDirect.BlockOpenResultRel,
              LiveBlockOpenResultRel] at hRel ⊢
          · exact ⟨hRel.1, LiveCtxRel.of_ctxRel hRel.2⟩
          all_goals
            rcases hRel with ⟨outcomeLayout, hOutcomeRel, hCtxRel⟩
            exact ⟨outcomeLayout, hOutcomeRel, LiveCtxRel.of_ctxRel hCtxRel⟩

theorem regular_stateRel {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns
        (Source.Outcome.regular source, sourceCtx)
        (Structured.Outcome.regular target, targetCtx)) :
    SourceDirect.StateRel targetCtx.layout hiddenReturns source target ∧
      LiveCtxRel retc sourceCtx targetCtx := by
  simpa [LiveBlockOpenResultRel, Source.Outcome.regular,
    Structured.Outcome.regular] using hRel

theorem ctxRel {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
        targetResult) :
    LiveCtxRel retc sourceResult.2 targetResult.2 := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp only [LiveBlockOpenResultRel, SourceDirect.StmtOutcomeRel]
              at hRel
          · exact hRel.2
          all_goals
            first
            | contradiction
            | rcases hRel with ⟨_outcomeLayout, _hOutcome, hCtx⟩
              exact hCtx

theorem source_regular_target_regular {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns
        (Source.Outcome.regular source, sourceCtx)
        (targetOutcome, targetCtx)) :
    ∃ target,
      targetOutcome = Structured.Outcome.regular target ∧
        SourceDirect.StateRel targetCtx.layout hiddenReturns source target ∧
        LiveCtxRel retc sourceCtx targetCtx := by
  cases targetOutcome with
  | mk targetState targetMode =>
      cases targetMode with
      | regular =>
          exact ⟨targetState, rfl, hRel.1, hRel.2⟩
      | brk =>
          simp [LiveBlockOpenResultRel, SourceDirect.StmtOutcomeRel,
            Source.Outcome.regular, Locals.Source.Outcome.regular] at hRel
      | cont =>
          simp [LiveBlockOpenResultRel, SourceDirect.StmtOutcomeRel,
            Source.Outcome.regular, Locals.Source.Outcome.regular] at hRel
      | leave =>
          simp [LiveBlockOpenResultRel, SourceDirect.StmtOutcomeRel,
            Source.Outcome.regular, Locals.Source.Outcome.regular] at hRel
      | halt kind =>
          simp [LiveBlockOpenResultRel, SourceDirect.StmtOutcomeRel,
            Source.Outcome.regular, Locals.Source.Outcome.regular] at hRel

theorem outcomeRel_of_nonregular {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns
        (sourceOutcome, sourceCtx) (targetOutcome, targetCtx))
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    ∃ outcomeLayout,
      SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
        sourceOutcome targetOutcome := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveBlockOpenResultRel] at hRel hNonregular ⊢
          all_goals exact hRel.1

theorem target_nonregular_of_source_nonregular {retc : Nat}
    {returns : List Name} {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns
        (sourceOutcome, sourceCtx) (targetOutcome, targetCtx))
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    targetOutcome.mode ≠ .regular := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveBlockOpenResultRel, SourceDirect.StmtOutcomeRel]
              at hRel hNonregular ⊢

theorem outcomeCleanup_of_not_break_continue {retc : Nat}
    {returns : List Name} {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
        targetResult)
    (hNotBreak : sourceResult.1.mode ≠ .brk)
    (hNotContinue : sourceResult.1.mode ≠ .cont) :
    LiveCtxOutcomeCleanupRel retc sourceResult.2 targetResult.2
      sourceResult.1 := by
  refine ⟨ctxRel hRel, ?_⟩
  rcases sourceResult with ⟨sourceOutcome, _sourceCtx⟩
  cases sourceOutcome with
  | mk _sourceState sourceMode =>
      cases sourceMode <;> simp at hNotBreak hNotContinue ⊢

theorem of_stmt_nonregular {retc : Nat} {returns : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx stmtSourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns
        (sourceOutcome, stmtSourceCtx) (targetOutcome, targetCtx))
    (hSourceCtx : stmtSourceCtx = sourceCtx)
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    LiveBlockOpenResultRel retc returns hiddenReturns
      (sourceOutcome, sourceCtx) (targetOutcome, targetCtx) := by
  subst stmtSourceCtx
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveStmtRunResultRel, LiveBlockOpenResultRel] at hRel hNonregular ⊢
          all_goals exact hRel

end LiveBlockOpenResultRel

def LiveLoopStmtRunResultRel (retc : Nat) (returns loopLayout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match sourceResult.1.mode, targetResult.1.mode with
  | .regular, .regular =>
      SourceDirect.StateRel targetResult.2.layout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | .brk, .brk
  | .cont, .cont =>
      SourceDirect.StateRel loopLayout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | .leave, .leave
  | .halt _, .halt _ =>
      SourceDirect.StmtOutcomeRel returns loopLayout hiddenReturns
        sourceResult.1 targetResult.1 ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | _, _ => False

namespace LiveLoopStmtRunResultRel

theorem to_liveStmtRunResultRel {retc : Nat} {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
        sourceResult targetResult) :
    LiveStmtRunResultRel retc returns hiddenReturns sourceResult
      targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveLoopStmtRunResultRel, LiveStmtRunResultRel,
              SourceDirect.StmtOutcomeRel] at hRel ⊢
          all_goals
            first
            | exact hRel
            | exact ⟨⟨loopLayout, hRel.1⟩, hRel.2⟩

theorem regular_stateRel {retc : Nat} {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
        (Source.Outcome.regular source, sourceCtx)
        (Structured.Outcome.regular target, targetCtx)) :
    SourceDirect.StateRel targetCtx.layout hiddenReturns source target ∧
      LiveCtxRel retc sourceCtx targetCtx := by
  simpa [LiveLoopStmtRunResultRel, Source.Outcome.regular,
    Locals.Source.Outcome.regular, Structured.Outcome.regular] using hRel

theorem of_stmtOutcomeRel_same_ctx {retc : Nat}
    {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hLoopLayout : loopLayout = targetCtx.layout)
    (hCtx : LiveCtxRel retc sourceCtx targetCtx)
    (hRel :
      SourceDirect.StmtOutcomeRel returns loopLayout hiddenReturns
        sourceOutcome targetOutcome) :
    LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
      (sourceOutcome, sourceCtx) (targetOutcome, targetCtx) := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveLoopStmtRunResultRel, SourceDirect.StmtOutcomeRel]
              at hRel ⊢
          all_goals
            first
            | exact False.elim hRel
            | exact ⟨by simpa [hLoopLayout] using hRel, hCtx⟩

theorem of_liveStmtRunResultRel_of_loop_stateRel {retc : Nat}
    {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns sourceResult
        targetResult)
    (hBreak :
      sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
      sourceResult targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveStmtRunResultRel, LiveLoopStmtRunResultRel,
              SourceDirect.StmtOutcomeRel] at hRel hBreak hContinue ⊢
          all_goals
            first
            | exact False.elim hRel
            | exact hRel
            | exact ⟨hBreak, hRel.2⟩
            | exact ⟨hContinue, hRel.2⟩

theorem of_liveStmtRunResultRel_not_break_continue {retc : Nat}
    {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns sourceResult
        targetResult)
    (hNotBreak : sourceResult.1.mode ≠ .brk)
    (hNotContinue : sourceResult.1.mode ≠ .cont) :
    LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
      sourceResult targetResult := by
  exact
    of_liveStmtRunResultRel_of_loop_stateRel hRel
      (fun hMode => False.elim (hNotBreak hMode))
      (fun hMode => False.elim (hNotContinue hMode))

theorem to_stmtOutcomeRel_of_target_layout {retc : Nat}
    {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
        (sourceOutcome, sourceCtx) (targetOutcome, targetCtx))
    (hLayout : targetCtx.layout = loopLayout) :
    SourceDirect.StmtOutcomeRel returns loopLayout hiddenReturns
      sourceOutcome targetOutcome := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveLoopStmtRunResultRel, SourceDirect.StmtOutcomeRel]
              at hRel ⊢
          all_goals
            first
            | exact False.elim hRel
            | exact hRel.1
            | exact by simpa [hLayout] using hRel.1

end LiveLoopStmtRunResultRel

def LiveLoopBlockOpenResultRel (retc : Nat) (returns loopLayout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match sourceResult.1.mode, targetResult.1.mode with
  | .regular, .regular =>
      SourceDirect.StateRel targetResult.2.layout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | .brk, .brk
  | .cont, .cont =>
      SourceDirect.StateRel loopLayout hiddenReturns
        sourceResult.1.state targetResult.1.state ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | .leave, .leave
  | .halt _, .halt _ =>
      SourceDirect.StmtOutcomeRel returns loopLayout hiddenReturns
        sourceResult.1 targetResult.1 ∧
        LiveCtxRel retc sourceResult.2 targetResult.2
  | _, _ => False

namespace LiveLoopBlockOpenResultRel

theorem to_liveBlockOpenResultRel {retc : Nat}
    {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
        sourceResult targetResult) :
    LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
      targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveLoopBlockOpenResultRel, LiveBlockOpenResultRel,
              SourceDirect.StmtOutcomeRel] at hRel ⊢
          all_goals
            first
            | exact hRel
            | exact ⟨⟨loopLayout, hRel.1⟩, hRel.2⟩

theorem of_liveLoopStmtRunResultRel {retc : Nat}
    {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
        sourceResult targetResult) :
    LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
      sourceResult targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveLoopStmtRunResultRel,
              LiveLoopBlockOpenResultRel] at hRel ⊢
          all_goals exact hRel

theorem of_stmt_nonregular {retc : Nat} {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx stmtSourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
        (sourceOutcome, stmtSourceCtx) (targetOutcome, targetCtx))
    (hSourceCtx : stmtSourceCtx = sourceCtx)
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
      (sourceOutcome, sourceCtx) (targetOutcome, targetCtx) := by
  subst stmtSourceCtx
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveLoopStmtRunResultRel, LiveLoopBlockOpenResultRel,
              SourceDirect.StmtOutcomeRel] at hRel hNonregular ⊢
          all_goals exact hRel

theorem of_stmtOutcomeRel_same_ctx {retc : Nat}
    {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Source.Outcome} {targetOutcome : Locals.Outcome}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    (hLoopLayout : loopLayout = targetCtx.layout)
    (hCtx : LiveCtxRel retc sourceCtx targetCtx)
    (hRel :
      SourceDirect.StmtOutcomeRel returns loopLayout hiddenReturns
        sourceOutcome targetOutcome) :
    LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
      (sourceOutcome, sourceCtx) (targetOutcome, targetCtx) := by
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveLoopBlockOpenResultRel, SourceDirect.StmtOutcomeRel]
              at hRel ⊢
          all_goals
            first
            | exact False.elim hRel
            | exact ⟨by simpa [hLoopLayout] using hRel, hCtx⟩

theorem of_liveBlockOpenResultRel_of_loop_stateRel {retc : Nat}
    {returns loopLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
        targetResult)
    (hBreak :
      sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
      sourceResult targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveBlockOpenResultRel, LiveLoopBlockOpenResultRel,
              SourceDirect.StmtOutcomeRel] at hRel hBreak hContinue ⊢
          all_goals
            first
            | exact False.elim hRel
            | exact hRel
            | exact ⟨hBreak, hRel.2⟩
            | exact ⟨hContinue, hRel.2⟩

end LiveLoopBlockOpenResultRel

def LiveBlockScopedOutcomeRel (returns layout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (source : Source.Outcome) (target : Locals.Outcome) : Prop :=
  match source.mode, target.mode with
  | .regular, .regular =>
      SourceDirect.StateRel layout hiddenReturns source.state target.state
  | _, _ =>
      ∃ outcomeLayout,
        SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
          source target

namespace LiveBlockScopedOutcomeRel

theorem regular {returns layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    (hRel : SourceDirect.StateRel layout hiddenReturns source target) :
    LiveBlockScopedOutcomeRel returns layout hiddenReturns
      (Source.Outcome.regular source) (Structured.Outcome.regular target) := by
  exact hRel

theorem nonregular {returns layout outcomeLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.Outcome} {target : Locals.Outcome}
    (hRel :
      SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
        source target)
    (hNonregular : source.mode ≠ .regular) :
    LiveBlockScopedOutcomeRel returns layout hiddenReturns source target := by
  cases source with
  | mk sourceState sourceMode =>
      cases sourceMode with
      | regular =>
          exact False.elim (hNonregular rfl)
      | brk =>
          simpa [LiveBlockScopedOutcomeRel] using
            (show ∃ outcomeLayout,
              SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
                { state := sourceState, mode := Locals.Source.Mode.brk }
                target from
              ⟨outcomeLayout, hRel⟩)
      | cont =>
          simpa [LiveBlockScopedOutcomeRel] using
            (show ∃ outcomeLayout,
              SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
                { state := sourceState, mode := Locals.Source.Mode.cont }
                target from
              ⟨outcomeLayout, hRel⟩)
      | leave =>
          simpa [LiveBlockScopedOutcomeRel] using
            (show ∃ outcomeLayout,
              SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
                { state := sourceState, mode := Locals.Source.Mode.leave }
                target from
              ⟨outcomeLayout, hRel⟩)
      | halt kind =>
          simpa [LiveBlockScopedOutcomeRel] using
            (show ∃ outcomeLayout,
              SourceDirect.StmtOutcomeRel returns outcomeLayout hiddenReturns
                (Source.Outcome.halt kind sourceState) target from
              ⟨outcomeLayout, hRel⟩)

theorem regular_stateRel {returns layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    (hRel :
      LiveBlockScopedOutcomeRel returns layout hiddenReturns
        (Source.Outcome.regular source)
        (Structured.Outcome.regular target)) :
    SourceDirect.StateRel layout hiddenReturns source target := by
  simpa [LiveBlockScopedOutcomeRel, Source.Outcome.regular,
    Locals.Source.Outcome.regular, Structured.Outcome.regular] using hRel

theorem to_stmtOutcomeRel_of_not_break_continue
    {returns layout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.Outcome} {target : Locals.Outcome}
    (hRel :
      LiveBlockScopedOutcomeRel returns layout hiddenReturns source target)
    (hNotBreak : source.mode ≠ .brk)
    (hNotContinue : source.mode ≠ .cont) :
    SourceDirect.StmtOutcomeRel returns layout hiddenReturns source target := by
  cases source with
  | mk sourceState sourceMode =>
      cases target with
      | mk targetState targetMode =>
          cases sourceMode with
          | regular =>
              cases targetMode <;>
                simp [LiveBlockScopedOutcomeRel,
                  SourceDirect.StmtOutcomeRel] at hRel ⊢
              all_goals exact hRel
          | brk =>
              exact False.elim (hNotBreak rfl)
          | cont =>
              exact False.elim (hNotContinue rfl)
          | leave =>
              cases targetMode <;>
                simp [LiveBlockScopedOutcomeRel,
                  SourceDirect.StmtOutcomeRel] at hRel ⊢
              all_goals exact hRel
          | halt kind =>
              cases targetMode <;>
                simp [LiveBlockScopedOutcomeRel,
                  SourceDirect.StmtOutcomeRel] at hRel ⊢
              all_goals exact hRel

end LiveBlockScopedOutcomeRel

def LiveStmtRunBridge (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (hiddenReturns : List Structured.ReturnDest)
    (stmt : Stmt) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  ∃ sourceResult targetFuel targetResult,
    Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
      .ok sourceResult ∧
    Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel targetBlock
      target =
      .ok targetResult ∧
    LiveStmtRunResultRel retc returns hiddenReturns sourceResult targetResult

def LiveStmtRegularLayoutRelTo (baseLayout : List Name)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match sourceResult.1.mode, targetResult.1.mode with
  | .regular, .regular =>
      SourceDirect.CleanupLayoutRel targetResult.2.layout baseLayout
  | _, _ => True

def LiveStmtRegularLayoutRel (targetCtx : Locals.Ctx)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  LiveStmtRegularLayoutRelTo targetCtx.layout sourceResult targetResult

def LiveStmtTargetRegularOutputLayoutRel (outLayout : List Name)
    (_sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match targetResult.1.mode with
  | .regular => targetResult.2.layout = outLayout
  | _ => True

def LiveStmtRunBridgeWithLayoutTo (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx) (baseLayout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (stmt : Stmt) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  ∃ sourceResult targetFuel targetResult,
    Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
      .ok sourceResult ∧
    Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel targetBlock
      target =
      .ok targetResult ∧
    LiveStmtRunResultRel retc returns hiddenReturns sourceResult targetResult ∧
    LiveStmtRegularLayoutRelTo baseLayout sourceResult targetResult

def LiveStmtRunBridgeWithLayout (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (hiddenReturns : List Structured.ReturnDest)
    (stmt : Stmt) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  LiveStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram returns retc
    sourceFuel sourceCtx targetCtx targetCtx.layout hiddenReturns stmt
    targetBlock source target

namespace LiveStmtRunBridgeWithLayoutTo

theorem to_stmt {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx} {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
        retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns stmt
        targetBlock source target) :
    LiveStmtRunBridge prim sourceProgram targetProgram returns retc
      sourceFuel sourceCtx targetCtx hiddenReturns stmt targetBlock source
      target := by
  rcases hBridge with
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel,
      _hLayout⟩
  exact ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel⟩

theorem target_result_of_source {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx} {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      LiveStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
        retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns stmt
        targetBlock source target)
    (hSource :
      Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
        .ok sourceResult) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult ∧
      LiveStmtRunResultRel retc returns hiddenReturns sourceResult
        targetResult ∧
      LiveStmtRegularLayoutRelTo baseLayout sourceResult targetResult := by
  rcases hBridge with
    ⟨sourceResult', targetFuel, targetResult, hSource', hTarget, hRel,
      hLayout⟩
  rw [hSource] at hSource'
  cases hSource'
  exact ⟨targetFuel, targetResult, hTarget, hRel, hLayout⟩

end LiveStmtRunBridgeWithLayoutTo

namespace LiveStmtRunBridgeWithLayout

theorem to_stmt {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveStmtRunBridgeWithLayout prim sourceProgram targetProgram returns
        retc sourceFuel sourceCtx targetCtx hiddenReturns stmt targetBlock
        source target) :
    LiveStmtRunBridge prim sourceProgram targetProgram returns retc
      sourceFuel sourceCtx targetCtx hiddenReturns stmt targetBlock source
      target := by
  exact LiveStmtRunBridgeWithLayoutTo.to_stmt hBridge

end LiveStmtRunBridgeWithLayout

def LiveBlockOpenRunBridge (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (hiddenReturns : List Structured.ReturnDest)
    (block : Block) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  ∃ sourceResult targetFuel targetResult,
    Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block source =
      .ok sourceResult ∧
    Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel targetBlock
      target =
      .ok targetResult ∧
    LiveBlockOpenResultRel retc returns hiddenReturns sourceResult targetResult

def LiveBlockOpenRegularLayoutRelTo (baseLayout : List Name)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match sourceResult.1.mode, targetResult.1.mode with
  | .regular, .regular =>
      SourceDirect.CleanupLayoutRel targetResult.2.layout baseLayout
  | _, _ => True

def LiveBlockOpenRegularLayoutRel (targetCtx : Locals.Ctx)
    (sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  LiveBlockOpenRegularLayoutRelTo targetCtx.layout sourceResult targetResult

def LiveBlockOpenTargetRegularOutputLayoutRel (outLayout : List Name)
    (_sourceResult : Source.Outcome × Source.Ctx)
    (targetResult : Locals.Outcome × Locals.Ctx) : Prop :=
  match targetResult.1.mode with
  | .regular => targetResult.2.layout = outLayout
  | _ => True

namespace LiveBlockOpenTargetRegularOutputLayoutRel

theorem namesAccessible_of_regular {outLayout returns : List Name}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetState : Locals.RunState} {targetCtx : Locals.Ctx}
    (hLayout :
      LiveBlockOpenTargetRegularOutputLayoutRel outLayout sourceResult
        (Structured.Outcome.regular targetState, targetCtx))
    (hAccess : NamesAccess.Accessible outLayout 0 returns) :
    NamesAccess.Accessible targetCtx.layout 0 returns := by
  have hEq : targetCtx.layout = outLayout := by
    simpa [LiveBlockOpenTargetRegularOutputLayoutRel,
      Structured.Outcome.regular] using hLayout
  rw [hEq]
  exact hAccess

theorem returnValuesAccessible_of_regular {outLayout returns : List Name}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetState : Locals.RunState} {targetCtx : Locals.Ctx}
    (hLayout :
      LiveBlockOpenTargetRegularOutputLayoutRel outLayout sourceResult
        (Structured.Outcome.regular targetState, targetCtx))
    (hAccess : NamesAccess.Accessible outLayout 0 returns) :
    SourceDirect.ReturnValuesRel.Accessible targetCtx.layout 0 returns :=
  NamesAccess.to_returnValuesAccessible
    (namesAccessible_of_regular hLayout hAccess)

end LiveBlockOpenTargetRegularOutputLayoutRel

namespace LiveBlockOpenRegularLayoutRelTo

theorem trans_cleanup {entryLayout baseLayout : List Name}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      LiveBlockOpenRegularLayoutRelTo entryLayout sourceResult targetResult)
    (hCleanup : SourceDirect.CleanupLayoutRel entryLayout baseLayout) :
    LiveBlockOpenRegularLayoutRelTo baseLayout sourceResult targetResult := by
  rcases sourceResult with ⟨sourceOutcome, sourceCtx⟩
  rcases targetResult with ⟨targetOutcome, targetCtx⟩
  cases sourceOutcome with
  | mk sourceState sourceMode =>
      cases targetOutcome with
      | mk targetState targetMode =>
          cases sourceMode <;> cases targetMode <;>
            simp [LiveBlockOpenRegularLayoutRelTo] at hRel ⊢
          exact SourceDirect.CleanupLayoutRel.trans hRel hCleanup

end LiveBlockOpenRegularLayoutRelTo

def LiveBlockOpenRunBridgeWithLayoutTo (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx) (baseLayout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (block : Block) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  ∃ sourceResult targetFuel targetResult,
    Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block source =
      .ok sourceResult ∧
    Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel targetBlock
      target =
      .ok targetResult ∧
    LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
      targetResult ∧
    LiveBlockOpenRegularLayoutRelTo baseLayout sourceResult targetResult

def LiveBlockOpenRunBridgeWithLayout (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (hiddenReturns : List Structured.ReturnDest)
    (block : Block) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  LiveBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
    retc sourceFuel sourceCtx targetCtx targetCtx.layout hiddenReturns block
    targetBlock source target

namespace LiveBlockOpenRunBridgeWithLayoutTo

theorem to_open {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx} {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns
        block targetBlock source target) :
    LiveBlockOpenRunBridge prim sourceProgram targetProgram returns retc
      sourceFuel sourceCtx targetCtx hiddenReturns block targetBlock source
      target := by
  rcases hBridge with
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel,
      _hLayout⟩
  exact ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel⟩

theorem source_mono {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns : List Name} {retc sourceFuel sourceFuel' : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx} {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hFuel : sourceFuel ≤ sourceFuel')
    (hBridge :
      LiveBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns
        block targetBlock source target) :
    LiveBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
      returns retc sourceFuel' sourceCtx targetCtx baseLayout hiddenReturns
      block targetBlock source target := by
  rcases hBridge with
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel,
      hLayout⟩
  exact
    ⟨sourceResult, targetFuel, targetResult,
      Source.Block.runOpen_mono prim sourceProgram hFuel hSource, hTarget,
      hRel, hLayout⟩

theorem target_result_of_source {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx} {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      LiveBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns
        block targetBlock source target)
    (hSource :
      Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block source =
        .ok sourceResult) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult ∧
      LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
        targetResult ∧
      LiveBlockOpenRegularLayoutRelTo baseLayout sourceResult
        targetResult := by
  rcases hBridge with
    ⟨sourceResult', targetFuel, targetResult, hSource', hTarget, hRel,
      hLayout⟩
  rw [hSource] at hSource'
  cases hSource'
  exact ⟨targetFuel, targetResult, hTarget, hRel, hLayout⟩

theorem target_result_with_noncontrol_outcome_cleanup_of_source
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx} {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      LiveBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns
        block targetBlock source target)
    (hSource :
      Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block source =
        .ok sourceResult)
    (hNotBreak : sourceResult.1.mode ≠ .brk)
    (hNotContinue : sourceResult.1.mode ≠ .cont) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult ∧
      LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
        targetResult ∧
      LiveCtxOutcomeCleanupRel retc sourceResult.2 targetResult.2
        sourceResult.1 ∧
      LiveBlockOpenRegularLayoutRelTo baseLayout sourceResult
        targetResult := by
  rcases target_result_of_source hBridge hSource with
    ⟨targetFuel, targetResult, hTarget, hRel, hLayout⟩
  exact
    ⟨targetFuel, targetResult, hTarget, hRel,
      LiveBlockOpenResultRel.outcomeCleanup_of_not_break_continue
        hRel hNotBreak hNotContinue,
      hLayout⟩

end LiveBlockOpenRunBridgeWithLayoutTo

namespace LiveBlockOpenRunBridgeWithLayout

theorem to_open {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveBlockOpenRunBridgeWithLayout prim sourceProgram targetProgram
        returns retc sourceFuel sourceCtx targetCtx hiddenReturns block
        targetBlock source target) :
    LiveBlockOpenRunBridge prim sourceProgram targetProgram returns retc
      sourceFuel sourceCtx targetCtx hiddenReturns block targetBlock source
      target := by
  exact LiveBlockOpenRunBridgeWithLayoutTo.to_open hBridge

end LiveBlockOpenRunBridgeWithLayout

def LiveLoopStmtRunBridgeWithLayoutTo (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns loopLayout : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (baseLayout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (stmt : Stmt) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  ∃ sourceResult targetFuel targetResult,
    Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
      .ok sourceResult ∧
    Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel targetBlock
      target =
      .ok targetResult ∧
    LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
      sourceResult targetResult ∧
    LiveStmtRegularLayoutRelTo baseLayout sourceResult targetResult

def LiveLoopStmtRunBridgeWithLayout (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns loopLayout : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (hiddenReturns : List Structured.ReturnDest)
    (stmt : Stmt) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  LiveLoopStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
    loopLayout retc sourceFuel sourceCtx targetCtx targetCtx.layout
    hiddenReturns stmt targetBlock source target

namespace LiveLoopStmtRunBridgeWithLayoutTo

theorem to_stmt_with_layout {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveLoopStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns loopLayout retc sourceFuel sourceCtx targetCtx baseLayout
        hiddenReturns stmt targetBlock source target) :
    LiveStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
      retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns stmt
      targetBlock source target := by
  rcases hBridge with
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel,
      hLayout⟩
  exact
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget,
      LiveLoopStmtRunResultRel.to_liveStmtRunResultRel hRel, hLayout⟩

theorem of_stmt_with_layout_of_loop_stateRel
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
        retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns stmt
        targetBlock source target)
    (hBreak :
      ∀ {sourceResult : Source.Outcome × Source.Ctx}
        {targetFuel : Nat}
        {targetResult : Locals.Outcome × Locals.Ctx},
        Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
          .ok sourceResult →
        Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
            targetBlock target =
          .ok targetResult →
        sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      ∀ {sourceResult : Source.Outcome × Source.Ctx}
        {targetFuel : Nat}
        {targetResult : Locals.Outcome × Locals.Ctx},
        Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
          .ok sourceResult →
        Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
            targetBlock target =
          .ok targetResult →
        sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
      loopLayout retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns
      stmt targetBlock source target := by
  rcases hBridge with
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel,
      hLayout⟩
  exact
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget,
      LiveLoopStmtRunResultRel.of_liveStmtRunResultRel_of_loop_stateRel
        hRel
        (fun hMode => hBreak hSource hTarget hMode)
        (fun hMode => hContinue hSource hTarget hMode),
      hLayout⟩

theorem target_result_of_source {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      LiveLoopStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns loopLayout retc sourceFuel sourceCtx targetCtx baseLayout
        hiddenReturns stmt targetBlock source target)
    (hSource :
      Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
        .ok sourceResult) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult ∧
      LiveLoopStmtRunResultRel retc returns loopLayout hiddenReturns
        sourceResult targetResult ∧
      LiveStmtRegularLayoutRelTo baseLayout sourceResult targetResult := by
  rcases hBridge with
    ⟨sourceResult', targetFuel, targetResult, hSource', hTarget, hRel,
      hLayout⟩
  rw [hSource] at hSource'
  cases hSource'
  exact ⟨targetFuel, targetResult, hTarget, hRel, hLayout⟩

theorem of_target_result_with_loop_stateRel
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetFuel : Nat}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hSource :
      Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
        .ok sourceResult)
    (hTarget :
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult)
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns sourceResult
        targetResult)
    (hLayout :
      LiveStmtRegularLayoutRelTo baseLayout sourceResult targetResult)
    (hBreak :
      sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopStmtRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
      loopLayout retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns
      stmt targetBlock source target := by
  exact
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget,
      LiveLoopStmtRunResultRel.of_liveStmtRunResultRel_of_loop_stateRel
        hRel hBreak hContinue,
      hLayout⟩

end LiveLoopStmtRunBridgeWithLayoutTo

namespace LiveLoopStmtRunBridgeWithLayout

theorem to_stmt_with_layout {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveLoopStmtRunBridgeWithLayout prim sourceProgram targetProgram
        returns loopLayout retc sourceFuel sourceCtx targetCtx hiddenReturns
        stmt targetBlock source target) :
    LiveStmtRunBridgeWithLayout prim sourceProgram targetProgram returns retc
      sourceFuel sourceCtx targetCtx hiddenReturns stmt targetBlock source
      target :=
  LiveLoopStmtRunBridgeWithLayoutTo.to_stmt_with_layout hBridge

theorem of_stmt_with_layout_of_loop_stateRel
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveStmtRunBridgeWithLayout prim sourceProgram targetProgram returns
        retc sourceFuel sourceCtx targetCtx hiddenReturns stmt targetBlock
        source target)
    (hBreak :
      ∀ {sourceResult : Source.Outcome × Source.Ctx}
        {targetFuel : Nat}
        {targetResult : Locals.Outcome × Locals.Ctx},
        Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
          .ok sourceResult →
        Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
            targetBlock target =
          .ok targetResult →
        sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      ∀ {sourceResult : Source.Outcome × Source.Ctx}
        {targetFuel : Nat}
        {targetResult : Locals.Outcome × Locals.Ctx},
        Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
          .ok sourceResult →
        Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
            targetBlock target =
          .ok targetResult →
        sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopStmtRunBridgeWithLayout prim sourceProgram targetProgram returns
      loopLayout retc sourceFuel sourceCtx targetCtx hiddenReturns stmt
      targetBlock source target :=
  LiveLoopStmtRunBridgeWithLayoutTo.of_stmt_with_layout_of_loop_stateRel
    hBridge hBreak hContinue

theorem of_stmt_with_layout_not_break_continue
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveStmtRunBridgeWithLayout prim sourceProgram targetProgram returns
        retc sourceFuel sourceCtx targetCtx hiddenReturns stmt targetBlock
        source target)
    (hNotBreak :
      ∀ {sourceResult},
        Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
          .ok sourceResult →
        sourceResult.1.mode ≠ .brk)
    (hNotContinue :
      ∀ {sourceResult},
        Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
          .ok sourceResult →
        sourceResult.1.mode ≠ .cont) :
    LiveLoopStmtRunBridgeWithLayout prim sourceProgram targetProgram returns
      loopLayout retc sourceFuel sourceCtx targetCtx hiddenReturns stmt
      targetBlock source target := by
  rcases hBridge with
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel,
      hLayout⟩
  exact
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget,
      LiveLoopStmtRunResultRel.of_liveStmtRunResultRel_not_break_continue
        hRel (hNotBreak hSource) (hNotContinue hSource),
      hLayout⟩

theorem of_target_result_with_loop_stateRel
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Stmt} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetFuel : Nat}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hSource :
      Source.Stmt.run prim sourceProgram sourceCtx sourceFuel stmt source =
        .ok sourceResult)
    (hTarget :
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult)
    (hRel :
      LiveStmtRunResultRel retc returns hiddenReturns sourceResult
        targetResult)
    (hLayout :
      LiveStmtRegularLayoutRel targetCtx sourceResult targetResult)
    (hBreak :
      sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopStmtRunBridgeWithLayout prim sourceProgram targetProgram returns
      loopLayout retc sourceFuel sourceCtx targetCtx hiddenReturns stmt
      targetBlock source target :=
  LiveLoopStmtRunBridgeWithLayoutTo.of_target_result_with_loop_stateRel
    hSource hTarget hRel hLayout hBreak hContinue

end LiveLoopStmtRunBridgeWithLayout

def LiveLoopBlockOpenRunBridgeWithLayoutTo
    (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns loopLayout : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (baseLayout : List Name)
    (hiddenReturns : List Structured.ReturnDest)
    (block : Block) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  ∃ sourceResult targetFuel targetResult,
    Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block source =
      .ok sourceResult ∧
    Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel targetBlock
      target =
      .ok targetResult ∧
    LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
      sourceResult targetResult ∧
    LiveBlockOpenRegularLayoutRelTo baseLayout sourceResult targetResult

def LiveLoopBlockOpenRunBridgeWithLayout
    (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns loopLayout : List Name) (retc sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (hiddenReturns : List Structured.ReturnDest)
    (block : Block) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  LiveLoopBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
    returns loopLayout retc sourceFuel sourceCtx targetCtx targetCtx.layout
    hiddenReturns block targetBlock source target

namespace LiveLoopBlockOpenRunBridgeWithLayoutTo

theorem to_open_with_layout {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveLoopBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns loopLayout retc sourceFuel sourceCtx targetCtx baseLayout
        hiddenReturns block targetBlock source target) :
    LiveBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram returns
      retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns block
      targetBlock source target := by
  rcases hBridge with
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel,
      hLayout⟩
  exact
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget,
      LiveLoopBlockOpenResultRel.to_liveBlockOpenResultRel hRel, hLayout⟩

theorem of_open_with_layout_of_loop_stateRel
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns retc sourceFuel sourceCtx targetCtx baseLayout hiddenReturns
        block targetBlock source target)
    (hBreak :
      ∀ {sourceResult : Source.Outcome × Source.Ctx}
        {targetFuel : Nat}
        {targetResult : Locals.Outcome × Locals.Ctx},
        Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block
            source =
          .ok sourceResult →
        Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
            targetBlock target =
          .ok targetResult →
        sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      ∀ {sourceResult : Source.Outcome × Source.Ctx}
        {targetFuel : Nat}
        {targetResult : Locals.Outcome × Locals.Ctx},
        Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block
            source =
          .ok sourceResult →
        Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
            targetBlock target =
          .ok targetResult →
        sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
      returns loopLayout retc sourceFuel sourceCtx targetCtx baseLayout
      hiddenReturns block targetBlock source target := by
  rcases hBridge with
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget, hRel,
      hLayout⟩
  exact
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget,
      LiveLoopBlockOpenResultRel.of_liveBlockOpenResultRel_of_loop_stateRel
        hRel
        (fun hMode => hBreak hSource hTarget hMode)
        (fun hMode => hContinue hSource hTarget hMode),
      hLayout⟩

theorem of_target_result_with_loop_stateRel
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetFuel : Nat}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hSource :
      Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block
          source =
        .ok sourceResult)
    (hTarget :
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult)
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
        targetResult)
    (hLayout :
      LiveBlockOpenRegularLayoutRelTo baseLayout sourceResult targetResult)
    (hBreak :
      sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
      returns loopLayout retc sourceFuel sourceCtx targetCtx baseLayout
      hiddenReturns block targetBlock source target := by
  exact
    ⟨sourceResult, targetFuel, targetResult, hSource, hTarget,
      LiveLoopBlockOpenResultRel.of_liveBlockOpenResultRel_of_loop_stateRel
        hRel hBreak hContinue,
      hLayout⟩

theorem target_result_of_source {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {baseLayout : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      LiveLoopBlockOpenRunBridgeWithLayoutTo prim sourceProgram targetProgram
        returns loopLayout retc sourceFuel sourceCtx targetCtx baseLayout
        hiddenReturns block targetBlock source target)
    (hSource :
      Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block source =
        .ok sourceResult) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult ∧
      LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
        sourceResult targetResult ∧
      LiveBlockOpenRegularLayoutRelTo baseLayout sourceResult targetResult := by
  rcases hBridge with
    ⟨sourceResult', targetFuel, targetResult, hSource', hTarget, hRel,
      hLayout⟩
  rw [hSource] at hSource'
  cases hSource'
  exact ⟨targetFuel, targetResult, hTarget, hRel, hLayout⟩

end LiveLoopBlockOpenRunBridgeWithLayoutTo

namespace LiveLoopBlockOpenRunBridgeWithLayout

theorem to_open_with_layout {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveLoopBlockOpenRunBridgeWithLayout prim sourceProgram targetProgram
        returns loopLayout retc sourceFuel sourceCtx targetCtx hiddenReturns
        block targetBlock source target) :
    LiveBlockOpenRunBridgeWithLayout prim sourceProgram targetProgram returns
      retc sourceFuel sourceCtx targetCtx hiddenReturns block targetBlock
      source target :=
  LiveLoopBlockOpenRunBridgeWithLayoutTo.to_open_with_layout hBridge

theorem target_result_of_source {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    (hBridge :
      LiveLoopBlockOpenRunBridgeWithLayout prim sourceProgram targetProgram
        returns loopLayout retc sourceFuel sourceCtx targetCtx hiddenReturns
        block targetBlock source target)
    (hSource :
      Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block source =
        .ok sourceResult) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult ∧
      LiveLoopBlockOpenResultRel retc returns loopLayout hiddenReturns
        sourceResult targetResult ∧
      LiveBlockOpenRegularLayoutRel targetCtx sourceResult targetResult :=
  LiveLoopBlockOpenRunBridgeWithLayoutTo.target_result_of_source hBridge
    hSource

theorem of_open_with_layout_of_loop_stateRel
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    (hBridge :
      LiveBlockOpenRunBridgeWithLayout prim sourceProgram targetProgram
        returns retc sourceFuel sourceCtx targetCtx hiddenReturns block
        targetBlock source target)
    (hBreak :
      ∀ {sourceResult : Source.Outcome × Source.Ctx}
        {targetFuel : Nat}
        {targetResult : Locals.Outcome × Locals.Ctx},
        Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block
            source =
          .ok sourceResult →
        Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
            targetBlock target =
          .ok targetResult →
        sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      ∀ {sourceResult : Source.Outcome × Source.Ctx}
        {targetFuel : Nat}
        {targetResult : Locals.Outcome × Locals.Ctx},
        Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block
            source =
          .ok sourceResult →
        Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
            targetBlock target =
          .ok targetResult →
        sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopBlockOpenRunBridgeWithLayout prim sourceProgram targetProgram
      returns loopLayout retc sourceFuel sourceCtx targetCtx hiddenReturns
      block targetBlock source target :=
  LiveLoopBlockOpenRunBridgeWithLayoutTo.of_open_with_layout_of_loop_stateRel
    hBridge hBreak hContinue

theorem of_target_result_with_loop_stateRel
    {prim : Source.PrimitiveSemantics}
    {sourceProgram : Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Name} {retc sourceFuel : Nat}
    {sourceCtx : Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Block} {targetBlock : Locals.Block}
    {source : Source.State} {target : Locals.RunState}
    {sourceResult : Source.Outcome × Source.Ctx}
    {targetFuel : Nat}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hSource :
      Source.Block.runOpen prim sourceProgram sourceCtx sourceFuel block
          source =
        .ok sourceResult)
    (hTarget :
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel
          targetBlock target =
        .ok targetResult)
    (hRel :
      LiveBlockOpenResultRel retc returns hiddenReturns sourceResult
        targetResult)
    (hLayout :
      LiveBlockOpenRegularLayoutRel targetCtx sourceResult targetResult)
    (hBreak :
      sourceResult.1.mode = .brk →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state)
    (hContinue :
      sourceResult.1.mode = .cont →
        SourceDirect.StateRel loopLayout hiddenReturns
          sourceResult.1.state targetResult.1.state) :
    LiveLoopBlockOpenRunBridgeWithLayout prim sourceProgram targetProgram
      returns loopLayout retc sourceFuel sourceCtx targetCtx hiddenReturns
      block targetBlock source target :=
  LiveLoopBlockOpenRunBridgeWithLayoutTo.of_target_result_with_loop_stateRel
    hSource hTarget hRel hLayout hBreak hContinue

end LiveLoopBlockOpenRunBridgeWithLayout

def LiveBlockScopedRunBridge (prim : Source.PrimitiveSemantics)
    (sourceProgram : Program) (targetProgram : Locals.Program)
    (returns : List Name) (sourceFuel : Nat)
    (sourceCtx : Source.Ctx) (targetCtx : Locals.Ctx)
    (hiddenReturns : List Structured.ReturnDest)
    (block : Block) (targetBlock : Locals.Block)
    (source : Source.State) (target : Locals.RunState) : Prop :=
  ∃ sourceOutcome targetFuel targetOutcome,
    Source.Block.runScoped prim sourceProgram sourceCtx block sourceFuel
      source =
      .ok sourceOutcome ∧
    Locals.Direct.Block.runScoped targetProgram targetCtx targetBlock
      targetFuel target =
      .ok targetOutcome ∧
    LiveBlockScopedOutcomeRel returns targetCtx.layout hiddenReturns
      sourceOutcome targetOutcome

theorem stateRel_cleanupTo_trimDeadPrefix {ctx : Locals.Ctx}
    {live : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx
          (Layout.trimDeadPrefix ctx.layout live).length target =
        .ok cleaned)
    (hRel : SourceDirect.StateRel ctx.layout hiddenReturns source target) :
    SourceDirect.StateRel (Layout.trimDeadPrefix ctx.layout live)
      hiddenReturns source cleaned := by
  rcases hRel with ⟨hLowerRel, hReturns⟩
  rcases Drop.cleanupTo_trimDeadPrefix_stateRel hRun hLowerRel with
    ⟨hCleanRel, hCleanReturns⟩
  exact ⟨hCleanRel, hCleanReturns.trans hReturns⟩

theorem stateRel_cleanupTo_layout_subset {ctx : Locals.Ctx}
    {outer scope : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target cleaned : Locals.RunState}
    (hRel : SourceDirect.StateRel ctx.layout hiddenReturns source target)
    (hLayout : SourceDirect.CleanupLayoutRel ctx.layout outer)
    (hSubset : ∀ {name : Name}, name ∈ outer → name ∈ scope)
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx outer.length target = .ok cleaned) :
    SourceDirect.StateRel outer hiddenReturns
      (Locals.Source.State.restrictTo scope source) cleaned := by
  rcases hRel with ⟨⟨hSharedRel, hStackRel⟩, hReturns⟩
  rcases hStackRel with ⟨hStackLen, hStackLookup⟩
  rcases Locals.Direct.Ctx.runCleanupTo_stack_drop hRun with
    ⟨_hDepth, hCleanStack, hCleanShared, hCleanReturns⟩
  constructor
  · constructor
    · simp [Locals.Source.State.restrictTo, hCleanShared, hSharedRel]
    · constructor
      · rw [hCleanStack]
        have hLayoutLen := congrArg List.length hLayout
        simp at hLayoutLen
        simp [List.length_drop, hStackLen]
        omega
      · intro idx name hOuter
        have hCombined :
            ctx.layout[ctx.layout.length - outer.length + idx]? =
              some name := by
          rw [← hLayout] at hOuter
          rw [← List.getElem?_drop]
          exact hOuter
        have hStackAt := hStackLookup hCombined
        rw [hCleanStack, List.getElem?_drop]
        have hNameMem : name ∈ scope :=
          hSubset (List.mem_of_getElem? hOuter)
        simpa [Locals.Source.State.restrictTo,
          Locals.Source.Store.restrictTo, hNameMem] using hStackAt
  · exact hCleanReturns.trans hReturns

theorem stateRel_cleanupTo_liveScope {ctx : Locals.Ctx}
    {depth : Nat} {scope : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target cleaned : Locals.RunState}
    (hRel : SourceDirect.StateRel ctx.layout hiddenReturns source target)
    (hScope : LiveCleanupScopeRel ctx.layout depth scope)
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx depth target = .ok cleaned) :
    SourceDirect.StateRel (ctx.layout.drop (ctx.layout.length - depth))
      hiddenReturns (Locals.Source.State.restrictTo scope source) cleaned := by
  rcases hScope with ⟨hDepth, hSubset⟩
  have hOuterLen :
      (ctx.layout.drop (ctx.layout.length - depth)).length = depth := by
    simp [List.length_drop]
    omega
  have hLayout :
      SourceDirect.CleanupLayoutRel ctx.layout
        (ctx.layout.drop (ctx.layout.length - depth)) := by
    simp [SourceDirect.CleanupLayoutRel, hOuterLen]
  have hRunOuter :
      Locals.Direct.Ctx.runCleanupTo ctx
          (ctx.layout.drop (ctx.layout.length - depth)).length target =
        .ok cleaned := by
    simpa [hOuterLen] using hRun
  exact
    stateRel_cleanupTo_layout_subset
      (ctx := ctx) (outer := ctx.layout.drop (ctx.layout.length - depth))
      (scope := scope) (hiddenReturns := hiddenReturns) (source := source)
      (target := target) (cleaned := cleaned) hRel hLayout hSubset hRunOuter

theorem stateRel_restrictTo_layout_subset {layout scope : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    (hRel : SourceDirect.StateRel layout hiddenReturns source target)
    (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ scope) :
    SourceDirect.StateRel layout hiddenReturns
      (Locals.Source.State.restrictTo scope source) target := by
  rcases hRel with ⟨⟨hSharedRel, hStackRel⟩, hReturns⟩
  rcases hStackRel with ⟨hStackLen, hStackLookup⟩
  constructor
  · constructor
    · simpa [Locals.Source.State.restrictTo] using hSharedRel
    · constructor
      · exact hStackLen
      · intro idx name hLayout
        have hNameMem : name ∈ scope :=
          hSubset (List.mem_of_getElem? hLayout)
        simpa [Locals.Source.State.restrictTo,
          Locals.Source.Store.restrictTo, hNameMem] using
          hStackLookup hLayout
  · exact hReturns

theorem cleanupTo_trimDeadPrefix_exists {ctx : Locals.Ctx}
    {live : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    (hRel : SourceDirect.StateRel ctx.layout hiddenReturns source target) :
    ∃ cleaned,
      Locals.Direct.Ctx.runCleanupTo ctx
          (Layout.trimDeadPrefix ctx.layout live).length target =
        .ok cleaned ∧
      SourceDirect.StateRel (Layout.trimDeadPrefix ctx.layout live)
        hiddenReturns source cleaned := by
  rcases hRel with ⟨⟨hSharedRel, hStackRel⟩, hReturns⟩
  have hStackLen := hStackRel.1
  have hDepth :
      (Layout.trimDeadPrefix ctx.layout live).length ≤ ctx.layout.length := by
    have hCount := Layout.trimDeadPrefixCount_add_length ctx.layout live
    omega
  rcases SourceDirect.Cleanup.runCleanupTo_exists
      (ctx := ctx)
      (targetDepth := (Layout.trimDeadPrefix ctx.layout live).length)
      (state := target) hDepth hStackLen with
    ⟨cleaned, hRun⟩
  exact
    ⟨cleaned, hRun,
      stateRel_cleanupTo_trimDeadPrefix hRun ⟨⟨hSharedRel, hStackRel⟩,
        hReturns⟩⟩

theorem cleanupStmt_trimDeadPrefix_exists {program : Locals.Program}
    {ctx : Locals.Ctx} {fuel : Nat} {live : List Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Source.State} {target : Locals.RunState}
    (hRel : SourceDirect.StateRel ctx.layout hiddenReturns source target) :
    ∃ cleaned,
      Locals.Direct.Stmt.run program ctx fuel
          (.cleanupTo (Layout.trimDeadPrefix ctx.layout live)) target =
        .ok (Structured.Outcome.regular cleaned,
          ctx.withLayout (Layout.trimDeadPrefix ctx.layout live)) ∧
      SourceDirect.StateRel (Layout.trimDeadPrefix ctx.layout live)
        hiddenReturns source cleaned := by
  rcases cleanupTo_trimDeadPrefix_exists
      (ctx := ctx) (live := live) hRel with
    ⟨cleaned, hRun, hCleanRel⟩
  have hTarget :
      Layout.trimDeadPrefix ctx.layout live =
        ctx.layout.drop
          (ctx.layout.length -
            (Layout.trimDeadPrefix ctx.layout live).length) := by
    rw [Layout.length_sub_trimDeadPrefix_eq_count,
      Layout.drop_trimDeadPrefixCount_eq_trimDeadPrefix]
  refine ⟨cleaned, ?_, hCleanRel⟩
  cases fuel
  all_goals
    unfold Locals.Direct.Stmt.run
    change
      (if Layout.trimDeadPrefix ctx.layout live =
          ctx.layout.drop
            (ctx.layout.length -
              (Layout.trimDeadPrefix ctx.layout live).length) then
        (do
          let stateAfterCleanup ←
            Locals.Direct.Ctx.runCleanupTo ctx
              (Layout.trimDeadPrefix ctx.layout live).length target
          .ok (Structured.Outcome.regular stateAfterCleanup,
            ctx.withLayout (Layout.trimDeadPrefix ctx.layout live)))
      else Locals.invalid) =
        .ok (Structured.Outcome.regular cleaned,
          ctx.withLayout (Layout.trimDeadPrefix ctx.layout live))
    rw [if_pos hTarget]
    simp [hRun]

end SourceDirectBridge

end LiveLayout
end Functions
end EvmCompiler
