import EvmCompiler.Yul.ObjectSemantics

namespace EvmCompiler
namespace Yul
namespace ObjectModel

/-!
Preservation bricks for the Yul object layer.

The full layer theorem will be a mutual induction over object expressions,
statements, function bodies, and dispatcher execution.  This file starts at the
new object constructs: layout-stable constants for `datasize`/`dataoffset` and
the `datacopy` lowering to core-Yul `codecopy`.
-/

namespace Preservation

abbrev CodeOverride := Option AstContract

def codecopyPrim : PrimOp :=
  (.Env .CODECOPY : EvmYul.Operation .Yul)

theorem patchStmt_toAst?
    {mode : LayoutMode} {reference : ImmutableReference}
    {base value : Expr} {baseAst valueAst : AstExpr}
    {stmt : Stmt} {stmtAst : AstStmt}
    (hBase : Expr.toAst? mode base = some baseAst)
    (hValue : Expr.toAst? mode value = some valueAst)
    (hSource :
      Source.patchStmt? reference base value = some stmt)
    (hAst :
      ImmutableReference.patchAstStmt? reference baseAst valueAst =
        some stmtAst) :
    Stmt.toAst? mode stmt = some stmtAst := by
  unfold Source.patchStmt? at hSource
  unfold ImmutableReference.patchAstStmt? at hAst
  cases hPatch : reference.isPatchable <;> simp [hPatch] at hSource hAst
  cases hSource
  cases hAst
  simp [Stmt.toAst?, Expr.toAst?, Expr.List.toAst?, hBase, hValue]

theorem patchStmts_toAst?
    {mode : LayoutMode} {references : List ImmutableReference}
    {base value : Expr} {baseAst valueAst : AstExpr}
    {stmts : List Stmt} {stmtAsts : List AstStmt}
    (hBase : Expr.toAst? mode base = some baseAst)
    (hValue : Expr.toAst? mode value = some valueAst)
    (hSource :
      Source.ImmutableReferenceList.patchStmts? references base value =
        some stmts)
    (hAst :
      ImmutableReference.List.patchAstStmts? references baseAst valueAst =
        some stmtAsts) :
    Stmt.List.toAst? mode stmts = some stmtAsts := by
  induction references generalizing stmts stmtAsts with
  | nil =>
      simp [Source.ImmutableReferenceList.patchStmts?,
        ImmutableReference.List.patchAstStmts?] at hSource hAst
      cases hSource
      cases hAst
      rfl
  | cons reference rest ih =>
      simp [Source.ImmutableReferenceList.patchStmts?,
        ImmutableReference.List.patchAstStmts?] at hSource hAst
      cases hSourceHead : Source.patchStmt? reference base value with
      | none =>
          simp [hSourceHead] at hSource
      | some sourceHead =>
          cases hSourceTail :
              Source.ImmutableReferenceList.patchStmts? rest base value with
          | none =>
              simp [hSourceHead, hSourceTail] at hSource
          | some sourceTail =>
              cases hAstHead :
                  ImmutableReference.patchAstStmt? reference baseAst valueAst
              with
              | none =>
                  simp [hAstHead] at hAst
              | some astHead =>
                  cases hAstTail :
                      ImmutableReference.List.patchAstStmts? rest baseAst
                        valueAst with
                  | none =>
                      simp [hAstHead, hAstTail] at hAst
                  | some astTail =>
                      simp [hSourceHead, hSourceTail] at hSource
                      simp [hAstHead, hAstTail] at hAst
                      cases hSource
                      cases hAst
                      simp [Stmt.List.toAst?,
                        patchStmt_toAst? hBase hValue hSourceHead hAstHead,
                        ih hSourceTail hAstTail]

theorem exists_source_patchStmt_of_patchAstStmt?
    {mode : LayoutMode} {reference : ImmutableReference}
    {base value : Expr} {baseAst valueAst : AstExpr}
    {stmtAst : AstStmt}
    (hBase : Expr.toAst? mode base = some baseAst)
    (hValue : Expr.toAst? mode value = some valueAst)
    (hAst :
      ImmutableReference.patchAstStmt? reference baseAst valueAst =
        some stmtAst) :
    ∃ stmt : Stmt,
      Source.patchStmt? reference base value = some stmt ∧
        Stmt.toAst? mode stmt = some stmtAst := by
  unfold ImmutableReference.patchAstStmt? at hAst
  cases hPatch : reference.isPatchable <;> simp [hPatch] at hAst
  cases hAst
  exact
    ⟨ .exprStmtCall
        (.call (.inl ((.StackMemFlow .MSTORE : EvmYul.Operation .Yul)))
          [ .call (.inl ((.StopArith .ADD : EvmYul.Operation .Yul)))
              [base, .lit (EvmYul.UInt256.ofNat reference.start)]
          , value ])
    , by simp [Source.patchStmt?, hPatch]
    , by simp [Stmt.toAst?, Expr.toAst?, Expr.List.toAst?, hBase, hValue] ⟩

theorem exists_source_patchStmts_of_patchAstStmts?
    {mode : LayoutMode} {references : List ImmutableReference}
    {base value : Expr} {baseAst valueAst : AstExpr}
    {stmtAsts : List AstStmt}
    (hBase : Expr.toAst? mode base = some baseAst)
    (hValue : Expr.toAst? mode value = some valueAst)
    (hAst :
      ImmutableReference.List.patchAstStmts? references baseAst valueAst =
        some stmtAsts) :
    ∃ stmts : List Stmt,
      Source.ImmutableReferenceList.patchStmts? references base value =
        some stmts ∧
        Stmt.List.toAst? mode stmts = some stmtAsts := by
  induction references generalizing stmtAsts with
  | nil =>
      simp [ImmutableReference.List.patchAstStmts?] at hAst
      cases hAst
      exact
        ⟨[], by simp [Source.ImmutableReferenceList.patchStmts?], rfl⟩
  | cons reference rest ih =>
      simp [ImmutableReference.List.patchAstStmts?] at hAst
      cases hAstHead :
          ImmutableReference.patchAstStmt? reference baseAst valueAst with
      | none =>
          simp [hAstHead] at hAst
      | some astHead =>
          cases hAstTail :
              ImmutableReference.List.patchAstStmts? rest baseAst valueAst with
          | none =>
              simp [hAstHead, hAstTail] at hAst
          | some astTail =>
              simp [hAstHead, hAstTail] at hAst
              cases hAst
              rcases
                  exists_source_patchStmt_of_patchAstStmt?
                    hBase hValue hAstHead with
                ⟨sourceHead, hSourceHead, hHeadAst⟩
              rcases ih hAstTail with
                ⟨sourceTail, hSourceTail, hTailAst⟩
              exact
                ⟨ sourceHead :: sourceTail
                , by
                    simp [Source.ImmutableReferenceList.patchStmts?,
                      hSourceHead, hSourceTail]
                , by simp [Stmt.List.toAst?, hHeadAst, hTailAst] ⟩

theorem reverseResult_eq_reverse'
    (result : Except Source.Exception (Source.State × List Word)) :
    Source.reverseResult result = EvmYul.Yul.reverse' result := by
  cases result with
  | ok pair =>
      cases pair
      rfl
  | error exception =>
      rfl

theorem headResult_eq_head'
    (result : Except Source.Exception (Source.State × List Word)) :
    Source.headResult result = EvmYul.Yul.head' result := by
  cases result with
  | ok pair =>
      cases pair
      rfl
  | error exception =>
      rfl

theorem multifillResult_eq_multifill'
    (vars : List Name)
    (result : Except Source.Exception (Source.State × List Word)) :
    Source.multifillResult vars result = EvmYul.Yul.multifill' vars result := by
  cases result with
  | ok pair =>
      cases pair
      rfl
  | error exception =>
      rfl

theorem word_zero_ofNat_eq_literal :
    EvmYul.UInt256.ofNat 0 = ({ val := 0 } : Word) := by
  rfl

theorem exprList_toAst?_append {mode : LayoutMode}
    {left right : List Expr} {leftAst rightAst : List AstExpr}
    (hLeft : Expr.List.toAst? mode left = some leftAst)
    (hRight : Expr.List.toAst? mode right = some rightAst) :
    Expr.List.toAst? mode (left ++ right) =
      some (leftAst ++ rightAst) := by
  induction left generalizing leftAst with
  | nil =>
      simp [Expr.List.toAst?] at hLeft
      cases hLeft
      simpa using hRight
  | cons head tail ih =>
      cases hHead : Expr.toAst? mode head with
      | none =>
          simp [Expr.List.toAst?, hHead] at hLeft
      | some headAst =>
          cases hTail : Expr.List.toAst? mode tail with
          | none =>
              simp [Expr.List.toAst?, hHead, hTail] at hLeft
          | some tailAst =>
              simp [Expr.List.toAst?, hHead, hTail] at hLeft
              cases hLeft
              simp [Expr.List.toAst?, hHead, ih hTail]

theorem exprList_toAst?_reverse {mode : LayoutMode}
    {args : List Expr} {argsAst : List AstExpr}
    (hArgs : Expr.List.toAst? mode args = some argsAst) :
    Expr.List.toAst? mode args.reverse = some argsAst.reverse := by
  induction args generalizing argsAst with
  | nil =>
      simp [Expr.List.toAst?] at hArgs
      cases hArgs
      simp [Expr.List.toAst?]
  | cons head tail ih =>
      cases hHead : Expr.toAst? mode head with
      | none =>
          simp [Expr.List.toAst?, hHead] at hArgs
      | some headAst =>
          cases hTail : Expr.List.toAst? mode tail with
          | none =>
              simp [Expr.List.toAst?, hHead, hTail] at hArgs
          | some tailAst =>
              simp [Expr.List.toAst?, hHead, hTail] at hArgs
              cases hArgs
              have hTailRev :
                  Expr.List.toAst? mode tail.reverse =
                    some tailAst.reverse :=
                ih hTail
              have hHeadList :
                  Expr.List.toAst? mode [head] = some [headAst] := by
                simp [Expr.List.toAst?, hHead]
              simpa using
                exprList_toAst?_append hTailRev hHeadList

theorem evalArgs_zero_to_core {runtime : Source.Runtime}
    {args : List Expr} {argsAst : List AstExpr}
    {state : Source.State} {codeOverride : CodeOverride} :
    Source.evalArgs 0 runtime args state =
      EvmYul.Yul.evalArgs 0 argsAst codeOverride state := by
  simp [Source.evalArgs, EvmYul.Yul.evalArgs]

theorem evalTail_zero_to_core {runtime : Source.Runtime}
    {args : List Expr} {argsAst : List AstExpr}
    {input : Except Source.Exception (Source.State × Word)}
    {codeOverride : CodeOverride} :
    Source.evalTail 0 runtime args input =
      EvmYul.Yul.evalTail 0 argsAst codeOverride input := by
  cases input with
  | error exception =>
      unfold Source.evalTail EvmYul.Yul.evalTail
      rfl
  | ok pair =>
      cases pair
      unfold Source.evalTail EvmYul.Yul.evalTail
      rfl

theorem evalTail_succ_to_core_of_evalArgs
    {runtime : Source.Runtime} {fuel : Nat}
    {args : List Expr} {argsAst : List AstExpr}
    {input : Except Source.Exception (Source.State × Word)}
    {codeOverride : CodeOverride}
    (hArgs :
      ∀ state : Source.State,
        Source.evalArgs fuel runtime args state =
          EvmYul.Yul.evalArgs fuel argsAst codeOverride state) :
    Source.evalTail (fuel + 1) runtime args input =
      EvmYul.Yul.evalTail (fuel + 1) argsAst codeOverride input := by
  cases input with
  | error exception =>
      unfold Source.evalTail EvmYul.Yul.evalTail
      rfl
  | ok pair =>
      cases pair with
      | mk state value =>
          simp [Source.evalTail, EvmYul.Yul.evalTail, Source.consResult,
            EvmYul.Yul.cons']
          rw [hArgs state]
          cases hCore :
              EvmYul.Yul.evalArgs fuel argsAst codeOverride state with
          | error exception =>
              rfl
          | ok pair =>
              cases pair
              rfl

theorem evalArgs_nil_succ_to_core {runtime : Source.Runtime}
    {fuel : Nat} {state : Source.State} {codeOverride : CodeOverride} :
    Source.evalArgs (fuel + 1) runtime [] state =
      EvmYul.Yul.evalArgs (fuel + 1) [] codeOverride state := by
  simp [Source.evalArgs, EvmYul.Yul.evalArgs]

theorem evalArgs_cons_succ_to_core_of_eval_tail
    {runtime : Source.Runtime} {fuel : Nat}
    {arg : Expr} {argAst : AstExpr}
    {rest : List Expr} {restAst : List AstExpr}
    {state : Source.State} {codeOverride : CodeOverride}
    (hEval :
      Source.eval fuel runtime arg state =
        EvmYul.Yul.eval fuel argAst codeOverride state)
    (hTail :
      ∀ input : Except Source.Exception (Source.State × Word),
        Source.evalTail fuel runtime rest input =
          EvmYul.Yul.evalTail fuel restAst codeOverride input) :
    Source.evalArgs (fuel + 1) runtime (arg :: rest) state =
      EvmYul.Yul.evalArgs (fuel + 1) (argAst :: restAst) codeOverride
        state := by
  simp [Source.evalArgs, EvmYul.Yul.evalArgs, hEval]
  exact hTail (EvmYul.Yul.eval fuel argAst codeOverride state)

theorem evalTail_succ_toAst?_checked_core_of_evalArgs
    {runtime : Source.Runtime} {fuel : Nat}
    {args : List Expr} {argsAst : List AstExpr}
    {input : Except Source.Exception (Source.State × Word)}
    {coreContract : AstContract}
    (hArgs :
      ∀ state : Source.State,
        Source.evalArgs fuel runtime args state =
          EvmYul.Yul.evalArgs fuel argsAst (some coreContract) state) :
    Source.evalTail (fuel + 1) runtime args input =
      EvmYul.Yul.evalTail (fuel + 1) argsAst (some coreContract) input := by
  exact
    evalTail_succ_to_core_of_evalArgs
      (runtime := runtime) (fuel := fuel) (args := args)
      (argsAst := argsAst) (input := input)
      (codeOverride := some coreContract) hArgs

theorem evalArgs_succ_toAst?_checked_core_of_evalValues_and_tail
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {args : List Expr} {argsAst : List AstExpr}
    {coreContract : AstContract}
    (hArgsAst :
      Expr.List.toAst? (runtime.checkedMode) args = some argsAst)
    (hEvalValues :
      ∀ (expr : Expr) (exprAst : AstExpr) (state : Source.State),
        Expr.toAst? (runtime.checkedMode) expr = some exprAst →
          Source.evalValues fuel runtime expr state =
            EvmYul.Yul.evalValues fuel exprAst (some coreContract) state)
    (hTail :
      ∀ (tail : List Expr) (tailAst : List AstExpr)
        (input : Except Source.Exception (Source.State × Word)),
        Expr.List.toAst? (runtime.checkedMode) tail = some tailAst →
          Source.evalTail fuel runtime tail input =
            EvmYul.Yul.evalTail fuel tailAst (some coreContract) input) :
    Source.evalArgs (fuel + 1) runtime args state =
      EvmYul.Yul.evalArgs (fuel + 1) argsAst (some coreContract) state := by
  cases args with
  | nil =>
      simp [Expr.List.toAst?] at hArgsAst
      cases hArgsAst
      exact
        evalArgs_nil_succ_to_core
          (runtime := runtime) (fuel := fuel) (state := state)
          (codeOverride := some coreContract)
  | cons arg rest =>
      cases hArgAst :
          Expr.toAst? (runtime.checkedMode) arg with
      | none =>
          simp [Expr.List.toAst?, hArgAst] at hArgsAst
      | some argAst =>
          cases hRestAst :
              Expr.List.toAst? (runtime.checkedMode) rest with
          | none =>
              simp [Expr.List.toAst?, hArgAst, hRestAst] at hArgsAst
          | some restAst =>
              simp [Expr.List.toAst?, hArgAst, hRestAst] at hArgsAst
              cases hArgsAst
              exact
                evalArgs_cons_succ_to_core_of_eval_tail
                  (runtime := runtime) (fuel := fuel) (arg := arg)
                  (argAst := argAst) (rest := rest) (restAst := restAst)
                  (state := state) (codeOverride := some coreContract)
                  (by
                    simp [Source.eval, EvmYul.Yul.eval]
                    rw [hEvalValues arg argAst state hArgAst]
                    exact headResult_eq_head'
                      (EvmYul.Yul.evalValues fuel argAst
                        (some coreContract) state))
                  (fun input => hTail rest restAst input hRestAst)

theorem eval_to_core_of_evalValues_eq {runtime : Source.Runtime}
    {fuel : Nat} {expr : Expr} {ast : AstExpr}
    {state : Source.State} {codeOverride : CodeOverride}
    (hEvalValues :
      Source.evalValues fuel runtime expr state =
        EvmYul.Yul.evalValues fuel ast codeOverride state) :
    Source.eval fuel runtime expr state =
      EvmYul.Yul.eval fuel ast codeOverride state := by
  simp [Source.eval, EvmYul.Yul.eval]
  rw [hEvalValues]
  exact headResult_eq_head'
    (EvmYul.Yul.evalValues fuel ast codeOverride state)

theorem execSeq_zero_to_core {runtime : Source.Runtime}
    {stmts : List Stmt} {stmtsAst : List AstStmt}
    {state : Source.State} {codeOverride : CodeOverride} :
    Source.execSeq 0 runtime stmts state =
      EvmYul.Yul.execSeq 0 stmtsAst codeOverride state := by
  simp [Source.execSeq, EvmYul.Yul.execSeq]

theorem execSeq_nil_succ_to_core {runtime : Source.Runtime}
    {fuel : Nat} {state : Source.State} {codeOverride : CodeOverride} :
    Source.execSeq (fuel + 1) runtime [] state =
      EvmYul.Yul.execSeq (fuel + 1) [] codeOverride state := by
  simp [Source.execSeq, EvmYul.Yul.execSeq]

theorem execSeq_cons_succ_to_core_of_exec_tail
    {runtime : Source.Runtime} {fuel : Nat}
    {stmt : Stmt} {stmtAst : AstStmt}
    {rest : List Stmt} {restAst : List AstStmt}
    {state : Source.State} {codeOverride : CodeOverride}
    (hExec :
      Source.exec fuel runtime stmt state =
        EvmYul.Yul.exec fuel stmtAst codeOverride state)
    (hTail :
      ∀ stateAfterHead : Source.State,
        Source.execSeq fuel runtime rest stateAfterHead =
          EvmYul.Yul.execSeq fuel restAst codeOverride stateAfterHead) :
    Source.execSeq (fuel + 1) runtime (stmt :: rest) state =
      EvmYul.Yul.execSeq (fuel + 1) (stmtAst :: restAst) codeOverride
        state := by
  simp [Source.execSeq, EvmYul.Yul.execSeq, hExec]
  cases hCoreHead : EvmYul.Yul.exec fuel stmtAst codeOverride state with
  | error exception =>
      rfl
  | ok stateAfterHead =>
      cases stateAfterHead with
      | Ok shared store =>
          exact hTail (.Ok shared store)
      | OutOfFuel =>
          rfl
      | Checkpoint jump =>
          rfl

theorem execSeq_succ_toAst?_checked_core_of_exec_tail
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {stmts : List Stmt} {stmtsAst : List AstStmt}
    {coreContract : AstContract}
    (hStmtsAst :
      Stmt.List.toAst? (runtime.checkedMode) stmts = some stmtsAst)
    (hExec :
      ∀ (stmt : Stmt) (stmtAst : AstStmt) (state : Source.State),
        Stmt.toAst? (runtime.checkedMode) stmt = some stmtAst →
          Source.exec fuel runtime stmt state =
            EvmYul.Yul.exec fuel stmtAst (some coreContract) state)
    (hTail :
      ∀ (tail : List Stmt) (tailAst : List AstStmt)
        (state : Source.State),
        Stmt.List.toAst? (runtime.checkedMode) tail = some tailAst →
          Source.execSeq fuel runtime tail state =
            EvmYul.Yul.execSeq fuel tailAst (some coreContract) state) :
    Source.execSeq (fuel + 1) runtime stmts state =
      EvmYul.Yul.execSeq (fuel + 1) stmtsAst (some coreContract) state := by
  cases stmts with
  | nil =>
      simp [Stmt.List.toAst?] at hStmtsAst
      cases hStmtsAst
      exact
        execSeq_nil_succ_to_core
          (runtime := runtime) (fuel := fuel) (state := state)
          (codeOverride := some coreContract)
  | cons stmt rest =>
      cases hStmtAst :
          Stmt.toAst? (runtime.checkedMode) stmt with
      | none =>
          simp [Stmt.List.toAst?, hStmtAst] at hStmtsAst
      | some stmtAst =>
          cases hRestAst :
              Stmt.List.toAst? (runtime.checkedMode) rest with
          | none =>
              simp [Stmt.List.toAst?, hStmtAst, hRestAst] at hStmtsAst
          | some restAst =>
              simp [Stmt.List.toAst?, hStmtAst, hRestAst] at hStmtsAst
              cases hStmtsAst
              exact
                execSeq_cons_succ_to_core_of_exec_tail
                  (runtime := runtime) (fuel := fuel) (stmt := stmt)
                  (stmtAst := stmtAst) (rest := rest) (restAst := restAst)
                  (state := state) (codeOverride := some coreContract)
                  (hExec stmt stmtAst state hStmtAst)
                  (fun stateAfterHead =>
                    hTail rest restAst stateAfterHead hRestAst)

theorem exec_block_toAst?_core_of_execSeq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {body : List Stmt} {bodyAst : List AstStmt}
    {codeOverride : CodeOverride}
    (hBodyAst : Stmt.List.toAst? mode body = some bodyAst)
    (hSeq :
      Source.execSeq fuel runtime body state =
        EvmYul.Yul.execSeq fuel bodyAst codeOverride state) :
    Stmt.toAst? mode (.block body) = some (.Block bodyAst) ∧
      Source.exec (fuel + 1) runtime (.block body) state =
        EvmYul.Yul.exec (fuel + 1) (.Block bodyAst) codeOverride state := by
  constructor
  · simp [Stmt.toAst?, hBodyAst]
  · simp [Source.exec, EvmYul.Yul.exec, hSeq]
    cases EvmYul.Yul.execSeq fuel bodyAst codeOverride state with
    | error exception =>
        rfl
    | ok stateAfter =>
        rfl

theorem exec_continue_toAst?_core {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {codeOverride : CodeOverride} :
    Stmt.toAst? mode .continue = some .Continue ∧
      Source.exec (fuel + 1) runtime .continue state =
        EvmYul.Yul.exec (fuel + 1) .Continue codeOverride state := by
  simp [Stmt.toAst?, Source.exec, EvmYul.Yul.exec]

theorem exec_break_toAst?_core {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {codeOverride : CodeOverride} :
    Stmt.toAst? mode .break = some .Break ∧
      Source.exec (fuel + 1) runtime .break state =
        EvmYul.Yul.exec (fuel + 1) .Break codeOverride state := by
  simp [Stmt.toAst?, Source.exec, EvmYul.Yul.exec]

theorem exec_leave_toAst?_core {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {codeOverride : CodeOverride} :
    Stmt.toAst? mode .leave = some .Leave ∧
      Source.exec (fuel + 1) runtime .leave state =
        EvmYul.Yul.exec (fuel + 1) .Leave codeOverride state := by
  simp [Stmt.toAst?, Source.exec, EvmYul.Yul.exec]

theorem loop_zero_to_core {runtime : Source.Runtime}
    {cond : Expr} {condAst : AstExpr}
    {post body : List Stmt} {postAst bodyAst : List AstStmt}
    {state : Source.State} {codeOverride : CodeOverride} :
    Source.loop 0 runtime cond post body state =
      EvmYul.Yul.loop 0 condAst postAst bodyAst codeOverride state := by
  simp [Source.loop, EvmYul.Yul.loop]

theorem loop_one_to_core {runtime : Source.Runtime}
    {cond : Expr} {condAst : AstExpr}
    {post body : List Stmt} {postAst bodyAst : List AstStmt}
    {state : Source.State} {codeOverride : CodeOverride} :
    Source.loop 1 runtime cond post body state =
      EvmYul.Yul.loop 1 condAst postAst bodyAst codeOverride state := by
  simp [Source.loop, EvmYul.Yul.loop]

theorem loop_succ_succ_to_core_of_parts {runtime : Source.Runtime}
    {fuel : Nat} {cond : Expr} {condAst : AstExpr}
    {post body : List Stmt} {postAst bodyAst : List AstStmt}
    {state : Source.State} {codeOverride : CodeOverride}
    (hEval :
      Source.eval fuel runtime cond (EvmYul.Yul.State.mkOk state) =
        EvmYul.Yul.eval fuel condAst codeOverride
          (EvmYul.Yul.State.mkOk state))
    (hBody :
      ∀ stateAfterCond : Source.State,
        Source.exec fuel runtime (.block body) stateAfterCond =
          EvmYul.Yul.exec fuel (.Block bodyAst) codeOverride
            stateAfterCond)
    (hPost :
      ∀ stateAfterBody : Source.State,
        Source.exec fuel runtime (.block post)
            (EvmYul.Yul.State.reviveJump stateAfterBody) =
          EvmYul.Yul.exec fuel (.Block postAst) codeOverride
            (EvmYul.Yul.State.reviveJump stateAfterBody))
    (hFor :
      ∀ nextState : Source.State,
        Source.exec fuel runtime (.for_ cond post body) nextState =
          EvmYul.Yul.exec fuel (.For condAst postAst bodyAst)
            codeOverride nextState) :
    Source.loop (fuel + 1 + 1) runtime cond post body state =
      EvmYul.Yul.loop (fuel + 1 + 1) condAst postAst bodyAst
        codeOverride state := by
  simp only [Source.loop, EvmYul.Yul.loop, hEval]
  cases hCoreEval :
      EvmYul.Yul.eval fuel condAst codeOverride
        (EvmYul.Yul.State.mkOk state) with
  | error exception =>
      simp
  | ok pair =>
      cases pair with
      | mk stateAfterCond value =>
          simp
          by_cases hZero : value = EvmYul.UInt256.ofNat 0
          · simp [hZero, word_zero_ofNat_eq_literal]
          · have hNonzeroCore : value ≠ ({ val := 0 } : Word) := by
              intro hCoreZero
              exact hZero (by
                simpa [← word_zero_ofNat_eq_literal] using hCoreZero)
            simp [hNonzeroCore, word_zero_ofNat_eq_literal]
            rw [hBody stateAfterCond]
            cases hCoreBody :
                EvmYul.Yul.exec fuel (.Block bodyAst) codeOverride
                  stateAfterCond with
            | error exception =>
                simp
            | ok stateAfterBody =>
                simp
                cases stateAfterBody with
                | OutOfFuel =>
                    rfl
                | Ok shared store =>
                    rw [hPost (.Ok shared store)]
                    cases hCorePost :
                        EvmYul.Yul.exec fuel (.Block postAst) codeOverride
                          (EvmYul.Yul.State.reviveJump
                            (.Ok shared store)) with
                    | error exception =>
                        simp
                    | ok stateAfterPost =>
                        simp
                        cases stateAfterPost with
                        | OutOfFuel =>
                            rfl
                        | Checkpoint jump =>
                            cases jump with
                            | Continue sharedPost storePost =>
                                rw [hFor
                                  (EvmYul.Yul.State.overwrite?
                                    (.Checkpoint
                                      (.Continue sharedPost storePost))
                                    state)]
                                cases EvmYul.Yul.exec fuel
                                    (.For condAst postAst bodyAst)
                                    codeOverride
                                    (EvmYul.Yul.State.overwrite?
                                      (.Checkpoint
                                        (.Continue sharedPost storePost))
                                      state) <;> rfl
                            | Break sharedPost storePost =>
                                rw [hFor
                                  (EvmYul.Yul.State.overwrite?
                                    (.Checkpoint (.Break sharedPost storePost))
                                    state)]
                                cases EvmYul.Yul.exec fuel
                                    (.For condAst postAst bodyAst)
                                    codeOverride
                                    (EvmYul.Yul.State.overwrite?
                                      (.Checkpoint
                                        (.Break sharedPost storePost))
                                      state) <;> rfl
                            | Leave sharedPost storePost =>
                                rfl
                        | Ok sharedPost storePost =>
                            rw [hFor
                              (EvmYul.Yul.State.overwrite?
                                (.Ok sharedPost storePost) state)]
                            cases EvmYul.Yul.exec fuel
                                (.For condAst postAst bodyAst) codeOverride
                                (EvmYul.Yul.State.overwrite?
                                  (.Ok sharedPost storePost) state) <;> rfl
                | Checkpoint jump =>
                    cases jump with
                    | Break sharedJump storeJump =>
                        rfl
                    | Leave sharedJump storeJump =>
                        rfl
                    | Continue sharedJump storeJump =>
                        rw [hPost
                          (.Checkpoint (.Continue sharedJump storeJump))]
                        cases hCorePost :
                            EvmYul.Yul.exec fuel (.Block postAst)
                              codeOverride
                              (EvmYul.Yul.State.reviveJump
                                (.Checkpoint
                                  (.Continue sharedJump storeJump))) with
                        | error exception =>
                            simp
                        | ok stateAfterPost =>
                            simp
                            cases stateAfterPost with
                            | OutOfFuel =>
                                rfl
                            | Checkpoint postJump =>
                                cases postJump with
                                | Continue sharedPost storePost =>
                                    rw [hFor
                                      (EvmYul.Yul.State.overwrite?
                                        (.Checkpoint
                                          (.Continue sharedPost storePost))
                                        state)]
                                    cases EvmYul.Yul.exec fuel
                                        (.For condAst postAst bodyAst)
                                        codeOverride
                                        (EvmYul.Yul.State.overwrite?
                                          (.Checkpoint
                                            (.Continue sharedPost storePost))
                                          state) <;> rfl
                                | Break sharedPost storePost =>
                                    rw [hFor
                                      (EvmYul.Yul.State.overwrite?
                                        (.Checkpoint
                                          (.Break sharedPost storePost))
                                        state)]
                                    cases EvmYul.Yul.exec fuel
                                        (.For condAst postAst bodyAst)
                                        codeOverride
                                        (EvmYul.Yul.State.overwrite?
                                          (.Checkpoint
                                            (.Break sharedPost storePost))
                                          state) <;> rfl
                                | Leave sharedPost storePost =>
                                    rfl
                            | Ok sharedPost storePost =>
                                rw [hFor
                                  (EvmYul.Yul.State.overwrite?
                                    (.Ok sharedPost storePost) state)]
                                cases hCoreFor :
                                    EvmYul.Yul.exec fuel
                                      (.For condAst postAst bodyAst)
                                      codeOverride
                                      (EvmYul.Yul.State.overwrite?
                                        (.Ok sharedPost storePost) state) <;>
                                  rfl

theorem loop_succ_succ_toAst?_checked_core_of_parts
    {runtime : Source.Runtime} {fuel : Nat}
    {cond : Expr} {condAst : AstExpr}
    {post body : List Stmt} {postAst bodyAst : List AstStmt}
    {state : Source.State} {coreContract : AstContract}
    (hCondAst : Expr.toAst? (runtime.checkedMode) cond = some condAst)
    (hPostAst :
      Stmt.List.toAst? (runtime.checkedMode) post = some postAst)
    (hBodyAst :
      Stmt.List.toAst? (runtime.checkedMode) body = some bodyAst)
    (hEvalValues :
      ∀ (expr : Expr) (exprAst : AstExpr) (state : Source.State),
        Expr.toAst? (runtime.checkedMode) expr = some exprAst →
          Source.evalValues fuel runtime expr state =
            EvmYul.Yul.evalValues fuel exprAst (some coreContract) state)
    (hExec :
      ∀ (stmt : Stmt) (stmtAst : AstStmt) (state : Source.State),
        Stmt.toAst? (runtime.checkedMode) stmt = some stmtAst →
          Source.exec fuel runtime stmt state =
            EvmYul.Yul.exec fuel stmtAst (some coreContract) state) :
    Source.loop (fuel + 1 + 1) runtime cond post body state =
      EvmYul.Yul.loop (fuel + 1 + 1) condAst postAst bodyAst
        (some coreContract) state := by
  exact
    loop_succ_succ_to_core_of_parts
      (runtime := runtime) (fuel := fuel) (cond := cond)
      (condAst := condAst) (post := post) (body := body)
      (postAst := postAst) (bodyAst := bodyAst) (state := state)
      (codeOverride := some coreContract)
      (eval_to_core_of_evalValues_eq
        (runtime := runtime) (fuel := fuel) (expr := cond)
        (ast := condAst) (state := EvmYul.Yul.State.mkOk state)
        (codeOverride := some coreContract)
        (hEvalValues cond condAst (EvmYul.Yul.State.mkOk state)
          hCondAst))
      (fun stateAfterCond =>
        hExec (.block body) (.Block bodyAst) stateAfterCond
          (by simp [Stmt.toAst?, hBodyAst]))
      (fun stateAfterBody =>
        hExec (.block post) (.Block postAst)
          (EvmYul.Yul.State.reviveJump stateAfterBody)
          (by simp [Stmt.toAst?, hPostAst]))
      (fun nextState =>
        hExec (.for_ cond post body) (.For condAst postAst bodyAst) nextState
          (by simp [Stmt.toAst?, hCondAst, hPostAst, hBodyAst]))

theorem exec_for_toAst?_core_of_loop {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {cond : Expr} {condAst : AstExpr}
    {post body : List Stmt} {postAst bodyAst : List AstStmt}
    {codeOverride : CodeOverride}
    (hCondAst : Expr.toAst? mode cond = some condAst)
    (hPostAst : Stmt.List.toAst? mode post = some postAst)
    (hBodyAst : Stmt.List.toAst? mode body = some bodyAst)
    (hLoop :
      Source.loop fuel runtime cond post body state =
        EvmYul.Yul.loop fuel condAst postAst bodyAst codeOverride state) :
    Stmt.toAst? mode (.for_ cond post body) =
        some (.For condAst postAst bodyAst) ∧
      Source.exec (fuel + 1) runtime (.for_ cond post body) state =
        EvmYul.Yul.exec (fuel + 1) (.For condAst postAst bodyAst)
          codeOverride state := by
  constructor
  · simp [Stmt.toAst?, hCondAst, hPostAst, hBodyAst]
  · simp [Source.exec, EvmYul.Yul.exec, hLoop]

theorem selectSwitchCase_toAst?_core {mode : LayoutMode}
    {cond : Word} {defaultBody : List Stmt}
    {defaultBodyAst : List AstStmt}
    {cases : List (Word × List Stmt)}
    {casesAst : List (Word × List AstStmt)}
    (hDefault :
      Stmt.List.toAst? mode defaultBody = some defaultBodyAst)
    (hCases : Stmt.Cases.toAst? mode cases = some casesAst) :
    Stmt.List.toAst? mode
        (Source.selectSwitchCase cond defaultBody cases) =
      some (EvmYul.Yul.selectSwitchCase cond defaultBodyAst casesAst) := by
  induction cases generalizing casesAst with
  | nil =>
      simp [Stmt.Cases.toAst?] at hCases
      subst casesAst
      exact hDefault
  | cons head tail ih =>
      cases head with
      | mk value body =>
          unfold Stmt.Cases.toAst? at hCases
          cases hBody : Stmt.List.toAst? mode body with
          | none =>
              simp [hBody] at hCases
          | some bodyAst =>
              cases hTail : Stmt.Cases.toAst? mode tail with
              | none =>
                  simp [hBody, hTail] at hCases
              | some tailAst =>
                  simp [hBody, hTail] at hCases
                  subst casesAst
                  by_cases hEq : value = cond
                  · simp [Source.selectSwitchCase,
                      EvmYul.Yul.selectSwitchCase, hEq, hBody]
                  · simpa [Source.selectSwitchCase,
                      EvmYul.Yul.selectSwitchCase, hEq] using
                      ih hTail

theorem call_zero_to_core {runtime : Source.Runtime} {args : List Word}
    {functionName? : Option AstFunctionName} {state : Source.State}
    {codeOverride : CodeOverride} :
    Source.call 0 runtime args functionName? state =
      EvmYul.Yul.call 0 args functionName? codeOverride state := by
  simp [Source.call, EvmYul.Yul.call]

theorem callDispatcher_zero_to_core {runtime : Source.Runtime}
    {state : Source.State} {codeOverride : CodeOverride} :
    Source.callDispatcher 0 runtime state =
      EvmYul.Yul.callDispatcher 0 codeOverride state := by
  simp [Source.callDispatcher, EvmYul.Yul.callDispatcher]

theorem call_user_missing_contract_to_core {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {codeOverride : CodeOverride}
    (hMissing :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner = none) :
    Source.call (fuel + 1) runtime args (some functionName) state =
      EvmYul.Yul.call (fuel + 1) args (some functionName) codeOverride
        state := by
  simp [Source.call, EvmYul.Yul.call, hMissing]

theorem evalCall_user_missing_contract_to_core {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {codeOverride : CodeOverride}
    (hMissing :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner = none) :
    Source.evalCall (fuel + 2) runtime functionName (.ok (state, args)) =
      EvmYul.Yul.evalCall (fuel + 2) functionName codeOverride
        (.ok (state, args)) := by
  simp [Source.evalCall, EvmYul.Yul.evalCall]
  rw [call_user_missing_contract_to_core (runtime := runtime)
      (fuel := fuel) (args := args) (functionName := functionName)
      (state := state) (codeOverride := codeOverride) hMissing]
  simp [Source.headResult, EvmYul.Yul.head']
  cases EvmYul.Yul.call (fuel + 1) args (some functionName) codeOverride state
    <;> rfl

theorem stable_payloadLayout_eq {prelim final : Objects.Object}
    {prelimLayout finalLayout : ObjectLayout}
    (hStable : Object.layoutStable? prelim final = true)
    (hPrelim : Objects.Object.payloadLayout? prelim = some prelimLayout)
    (hFinal : Objects.Object.payloadLayout? final = some finalLayout) :
    prelimLayout = finalLayout :=
  Object.layoutStable?_payloadLayout_eq hStable hPrelim hFinal

theorem toRootCoreProgram?_uses_runtime_layout {program : Program}
    {runtime : Source.Runtime} {core : Yul.Program}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core) :
    program.root.code.toCoreProgram? (runtime.checkedMode) = some core := by
  rcases Source.Runtime.ofCheckedProgram?_checked hRuntime with
    ⟨lower, hLower, hRuntimeLayout, _hImage, _hContract,
      _hRuntimeContract, hLinker, hImmutableValues, hImmutableReferences⟩
  rcases Program.toObjects?_checked hLower with
    ⟨prelim, hPrelim, hFinal, hStable⟩
  rcases Program.toRootCoreProgram?_checked hCore with
    ⟨corePrelim, coreFinal, coreLayout, hCorePrelim, hCoreLayout,
      hCoreLower, hCoreFinal, hCoreStable⟩
  have hPrelimEq : corePrelim = prelim := by
    have h := hCorePrelim
    rw [hPrelim] at h
    injection h with hEq
    exact hEq.symm
  subst corePrelim
  have hFinalEq : coreFinal = lower.root := by
    have h := hCoreFinal
    rw [hFinal] at h
    injection h with hEq
    exact hEq.symm
  subst coreFinal
  have hRuntimeLayoutRoot :
      Objects.Object.payloadLayout? lower.root = some runtime.layout := by
    simpa [Objects.Program.payloadLayout?] using hRuntimeLayout
  have hLayoutEq : coreLayout = runtime.layout :=
    stable_payloadLayout_eq hCoreStable hCoreLayout hRuntimeLayoutRoot
  subst coreLayout
  have hMode :
      Program.checkedMode program runtime.layout = runtime.checkedMode := by
    simp [Program.checkedMode, Source.Runtime.checkedMode, hLinker,
      hImmutableValues, hImmutableReferences]
  simpa [hMode] using hCoreLower

theorem toRootCoreProgram?_installedContract {program : Program}
    {runtime : Source.Runtime} {core : Yul.Program}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core) :
    core.contract = runtime.installedContract := by
  have hCoreLower :
      program.root.code.toCoreProgram? (runtime.checkedMode) =
        some core :=
    toRootCoreProgram?_uses_runtime_layout
      (program := program) (runtime := runtime) (core := core)
      hRuntime hCore
  rcases Source.Runtime.ofCheckedProgram?_checked hRuntime with
    ⟨_lower, _hLower, _hRuntimeLayout, _hImage, hInstalled,
      _hContract, hLinker, hImmutableValues, hImmutableReferences⟩
  have hMode :
      Program.checkedMode program runtime.layout = runtime.checkedMode := by
    simp [Program.checkedMode, Source.Runtime.checkedMode, hLinker,
      hImmutableValues, hImmutableReferences]
  unfold Contract.toCoreProgram? at hCoreLower
  rw [← hMode] at hCoreLower
  rw [hInstalled] at hCoreLower
  simp at hCoreLower
  rw [← hCoreLower]

theorem installCodeImage_eq_installContractWithCodeImage
    {runtime : Source.Runtime} {core : Yul.Program}
    (hContract : core.contract = runtime.installedContract)
    (state : Source.State) :
    Source.installCodeImage runtime state =
      Yul.Program.installContractWithCodeImage core runtime.codeImage state := by
  cases state <;> simp [Source.installCodeImage,
    Yul.Program.installContractWithCodeImage, hContract]

theorem installCodeImage_eq_installContractWithCodeImage_of_checked
    {program : Program} {runtime : Source.Runtime} {core : Yul.Program}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core)
    (state : Source.State) :
    Source.installCodeImage runtime state =
      Yul.Program.installContractWithCodeImage core runtime.codeImage state := by
  exact
    installCodeImage_eq_installContractWithCodeImage
      (runtime := runtime) (core := core)
      (toRootCoreProgram?_installedContract
        (program := program) (runtime := runtime) (core := core)
        hRuntime hCore)
      state

theorem runContract_to_runWithCodeImage_of_dispatcher
    {runtime : Source.Runtime} {core : Yul.Program}
    {fuel : Nat} {state : Source.State}
    (hInstall :
      Source.installCodeImage runtime state =
        Yul.Program.installContractWithCodeImage core runtime.codeImage state)
    (hDispatcher :
      Source.callDispatcher fuel runtime
          (Source.installCodeImage runtime state) =
        EvmYul.Yul.callDispatcher fuel (some core.contract)
          (Source.installCodeImage runtime state)) :
    Source.runContract runtime fuel state =
      Yul.Program.runWithCodeImage fuel core runtime.codeImage state := by
  have hDispatcher' :
      Source.callDispatcher fuel runtime
          (Source.installCodeImage runtime state) =
        EvmYul.Yul.callDispatcher fuel (some core.contract)
          (Yul.Program.installContractWithCodeImage core runtime.codeImage
            state) := by
    simpa [hInstall] using hDispatcher
  unfold Source.runContract Yul.Program.runWithCodeImage
  rw [hDispatcher']
  cases hCall :
      EvmYul.Yul.callDispatcher fuel (some core.contract)
        (Yul.Program.installContractWithCodeImage core runtime.codeImage
          state) with
  | ok result =>
      cases result
      rfl
  | error exception =>
      cases exception <;> rfl

theorem runContract_to_runWithCodeImage_of_checked_dispatcher
    {program : Program} {runtime : Source.Runtime} {core : Yul.Program}
    {fuel : Nat} {state : Source.State}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core)
    (hDispatcher :
      Source.callDispatcher fuel runtime
          (Source.installCodeImage runtime state) =
        EvmYul.Yul.callDispatcher fuel (some core.contract)
          (Source.installCodeImage runtime state)) :
    Source.runContract runtime fuel state =
      Yul.Program.runWithCodeImage fuel core runtime.codeImage state := by
  exact
    runContract_to_runWithCodeImage_of_dispatcher
      (runtime := runtime) (core := core) (fuel := fuel) (state := state)
      (installCodeImage_eq_installContractWithCodeImage_of_checked
        (program := program) (runtime := runtime) (core := core)
        hRuntime hCore state)
      hDispatcher

theorem list_find?_predicate_true {α : Type} {items : List α}
    {predicate : α → Bool} {item : α}
    (hFind : items.find? predicate = some item) :
    predicate item = true := by
  induction items with
  | nil =>
      simp at hFind
  | cons head tail ih =>
      cases hHead : predicate head
      · simp [List.find?, hHead] at hFind
        exact ih hFind
      · simp [List.find?, hHead] at hFind
        cases hFind
        exact hHead

theorem functionMapUnchecked?_lookup_of_find?
    {mode : LayoutMode}
    {entries : List (AstFunctionName × FunctionDefinition)}
    {functions : Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)}
    {functionName : AstFunctionName} {fn : FunctionDefinition}
    {fnAst : AstFunctionDefinition}
    (hNodup : (entries.map Prod.fst).Nodup)
    (hMap : Contract.functionMapUnchecked? mode entries = some functions)
    (hFind :
      entries.find? (fun entry => entry.1 == functionName) =
        some (functionName, fn))
    (hFn : fn.toAst? mode = some fnAst) :
    functions.lookup functionName = some fnAst := by
  induction entries generalizing functions with
  | nil =>
      simp at hFind
  | cons head tail ih =>
      cases head with
      | mk headName headFn =>
          have hTailNodup : (tail.map Prod.fst).Nodup := by
            simpa using hNodup.tail
          unfold Contract.functionMapUnchecked? at hMap
          cases hHeadAst : headFn.toAst? mode with
          | none =>
              simp [hHeadAst] at hMap
          | some headFnAst =>
              cases hTailMap :
                  Contract.functionMapUnchecked? mode tail with
              | none =>
                  simp [hHeadAst, hTailMap] at hMap
              | some tailFunctions =>
                  simp [hHeadAst, hTailMap] at hMap
                  subst functions
                  cases hHeadBeq : (headName == functionName)
                  · have hFindTail :
                        tail.find? (fun entry => entry.1 == functionName) =
                          some (functionName, fn) := by
                      simpa [List.find?, hHeadBeq] using hFind
                    have hTailLookup :
                        tailFunctions.lookup functionName = some fnAst :=
                      ih hTailNodup hTailMap hFindTail
                    have hNe : functionName ≠ headName := by
                      intro hEq
                      subst functionName
                      simp at hHeadBeq
                    rw [Finmap.lookup_insert_of_ne
                      (a := headName) (a' := functionName)
                      (b := headFnAst) tailFunctions hNe]
                    exact hTailLookup
                  · have hHeadEq :
                        (headName, headFn) = (functionName, fn) := by
                      simpa [List.find?, hHeadBeq] using hFind
                    injection hHeadEq with hNameEq hFnEq
                    subst headName
                    subst headFn
                    have hAstEq : headFnAst = fnAst := by
                      rw [hFn] at hHeadAst
                      injection hHeadAst with hEq
                      exact hEq.symm
                    subst headFnAst
                    exact Finmap.lookup_insert tailFunctions

theorem functionMap?_lookup_of_find?
    {mode : LayoutMode}
    {entries : List (AstFunctionName × FunctionDefinition)}
    {functions : Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)}
    {functionName : AstFunctionName} {fn : FunctionDefinition}
    {fnAst : AstFunctionDefinition}
    (hMap : Contract.functionMap? mode entries = some functions)
    (hFind :
      entries.find? (fun entry => entry.1 == functionName) =
        some (functionName, fn))
    (hFn : fn.toAst? mode = some fnAst) :
    functions.lookup functionName = some fnAst := by
  unfold Contract.functionMap? at hMap
  cases hNodupCheck :
      decide ((entries.map Prod.fst).Nodup) <;> simp [hNodupCheck] at hMap
  have hNodup : (entries.map Prod.fst).Nodup :=
    of_decide_eq_true hNodupCheck
  exact
    functionMapUnchecked?_lookup_of_find?
      (mode := mode) (entries := entries) (functions := functions)
      (functionName := functionName) (fn := fn) (fnAst := fnAst)
      hNodup hMap hFind hFn

theorem functionMap?_lookup_of_source_lookup
    {mode : LayoutMode} {contract : Contract}
    {functions : Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)}
    {functionName : AstFunctionName} {fn : FunctionDefinition}
    {fnAst : AstFunctionDefinition}
    (hMap : Contract.functionMap? mode contract.functions = some functions)
    (hLookup : Source.lookupFunction? contract functionName = some fn)
    (hFn : fn.toAst? mode = some fnAst) :
    functions.lookup functionName = some fnAst := by
  unfold Source.lookupFunction? at hLookup
  cases hFind :
      contract.functions.find? (fun entry => entry.1 == functionName) with
  | none =>
      simp [hFind] at hLookup
  | some entry =>
      cases entry with
      | mk foundName foundFn =>
          have hPred : (foundName == functionName) = true :=
            list_find?_predicate_true
              (items := contract.functions)
              (predicate := fun entry => entry.1 == functionName)
              (item := (foundName, foundFn)) hFind
          have hName : foundName = functionName := beq_iff_eq.mp hPred
          have hFnEq : foundFn = fn := by
            simpa [hFind] using hLookup
          simp at hName hFnEq
          subst foundName
          subst foundFn
          exact
            functionMap?_lookup_of_find?
              (mode := mode) (entries := contract.functions)
              (functions := functions) (functionName := functionName)
              (fn := fn) (fnAst := fnAst) hMap hFind hFn

theorem functionMapUnchecked?_toAst?_of_find?
    {mode : LayoutMode}
    {entries : List (AstFunctionName × FunctionDefinition)}
    {functions : Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)}
    {functionName : AstFunctionName} {fn : FunctionDefinition}
    (hMap : Contract.functionMapUnchecked? mode entries = some functions)
    (hFind :
      entries.find? (fun entry => entry.1 == functionName) =
        some (functionName, fn)) :
    ∃ fnAst : AstFunctionDefinition, fn.toAst? mode = some fnAst := by
  induction entries generalizing functions with
  | nil =>
      simp at hFind
  | cons head tail ih =>
      cases head with
      | mk headName headFn =>
          unfold Contract.functionMapUnchecked? at hMap
          cases hHeadAst : headFn.toAst? mode with
          | none =>
              simp [hHeadAst] at hMap
          | some headFnAst =>
              cases hTailMap :
                  Contract.functionMapUnchecked? mode tail with
              | none =>
                  simp [hHeadAst, hTailMap] at hMap
              | some tailFunctions =>
                  cases hHeadBeq : (headName == functionName)
                  · have hFindTail :
                        tail.find? (fun entry => entry.1 == functionName) =
                          some (functionName, fn) := by
                      simpa [List.find?, hHeadBeq] using hFind
                    exact ih hTailMap hFindTail
                  · have hHeadEq :
                        (headName, headFn) = (functionName, fn) := by
                      simpa [List.find?, hHeadBeq] using hFind
                    injection hHeadEq with hNameEq hFnEq
                    subst headName
                    subst headFn
                    exact ⟨headFnAst, hHeadAst⟩

theorem functionMap?_toAst?_of_source_lookup
    {mode : LayoutMode} {contract : Contract}
    {functions : Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)}
    {functionName : AstFunctionName} {fn : FunctionDefinition}
    (hMap : Contract.functionMap? mode contract.functions = some functions)
    (hLookup : Source.lookupFunction? contract functionName = some fn) :
    ∃ fnAst : AstFunctionDefinition, fn.toAst? mode = some fnAst := by
  unfold Contract.functionMap? at hMap
  cases hNodupCheck :
      decide ((contract.functions.map Prod.fst).Nodup) <;>
      simp [hNodupCheck] at hMap
  unfold Source.lookupFunction? at hLookup
  cases hFind :
      contract.functions.find? (fun entry => entry.1 == functionName) with
  | none =>
      simp [hFind] at hLookup
  | some entry =>
      cases entry with
      | mk foundName foundFn =>
          have hPred : (foundName == functionName) = true :=
            list_find?_predicate_true
              (items := contract.functions)
              (predicate := fun entry => entry.1 == functionName)
              (item := (foundName, foundFn)) hFind
          have hName : foundName = functionName := beq_iff_eq.mp hPred
          have hFnEq : foundFn = fn := by
            simpa [hFind] using hLookup
          simp at hName hFnEq
          subst foundName
          subst foundFn
          exact
            functionMapUnchecked?_toAst?_of_find?
              (mode := mode) (entries := contract.functions)
              (functions := functions) (functionName := functionName)
              (fn := fn) hMap hFind

theorem functionMapUnchecked?_lookup_none_of_find?_none
    {mode : LayoutMode}
    {entries : List (AstFunctionName × FunctionDefinition)}
    {functions : Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)}
    {functionName : AstFunctionName}
    (hNodup : (entries.map Prod.fst).Nodup)
    (hMap : Contract.functionMapUnchecked? mode entries = some functions)
    (hFind :
      entries.find? (fun entry => entry.1 == functionName) = none) :
    functions.lookup functionName = none := by
  induction entries generalizing functions with
  | nil =>
      unfold Contract.functionMapUnchecked? at hMap
      simp at hMap
      subst functions
      rfl
  | cons head tail ih =>
      cases head with
      | mk headName headFn =>
          have hTailNodup : (tail.map Prod.fst).Nodup := by
            simpa using hNodup.tail
          unfold Contract.functionMapUnchecked? at hMap
          cases hHeadAst : headFn.toAst? mode with
          | none =>
              simp [hHeadAst] at hMap
          | some headFnAst =>
              cases hTailMap :
                  Contract.functionMapUnchecked? mode tail with
              | none =>
                  simp [hHeadAst, hTailMap] at hMap
              | some tailFunctions =>
                  simp [hHeadAst, hTailMap] at hMap
                  subst functions
                  cases hHeadBeq : (headName == functionName)
                  · have hFindTail :
                        tail.find? (fun entry => entry.1 == functionName) =
                          none := by
                      simpa [List.find?, hHeadBeq] using hFind
                    have hTailLookup :
                        tailFunctions.lookup functionName = none :=
                      ih hTailNodup hTailMap hFindTail
                    have hNe : functionName ≠ headName := by
                      intro hEq
                      subst functionName
                      simp at hHeadBeq
                    rw [Finmap.lookup_insert_of_ne
                      (a := headName) (a' := functionName)
                      (b := headFnAst) tailFunctions hNe]
                    exact hTailLookup
                  · simp [List.find?, hHeadBeq] at hFind

theorem functionMap?_lookup_none_of_find?_none
    {mode : LayoutMode}
    {entries : List (AstFunctionName × FunctionDefinition)}
    {functions : Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)}
    {functionName : AstFunctionName}
    (hMap : Contract.functionMap? mode entries = some functions)
    (hFind :
      entries.find? (fun entry => entry.1 == functionName) = none) :
    functions.lookup functionName = none := by
  unfold Contract.functionMap? at hMap
  cases hNodupCheck :
      decide ((entries.map Prod.fst).Nodup) <;> simp [hNodupCheck] at hMap
  have hNodup : (entries.map Prod.fst).Nodup :=
    of_decide_eq_true hNodupCheck
  exact
    functionMapUnchecked?_lookup_none_of_find?_none
      (mode := mode) (entries := entries) (functions := functions)
      (functionName := functionName) hNodup hMap hFind

theorem functionMap?_lookup_none_of_source_lookup_none
    {mode : LayoutMode} {contract : Contract}
    {functions : Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)}
    {functionName : AstFunctionName}
    (hMap : Contract.functionMap? mode contract.functions = some functions)
    (hLookup : Source.lookupFunction? contract functionName = none) :
    functions.lookup functionName = none := by
  unfold Source.lookupFunction? at hLookup
  cases hFind :
      contract.functions.find? (fun entry => entry.1 == functionName) with
  | none =>
      exact
        functionMap?_lookup_none_of_find?_none
          (mode := mode) (entries := contract.functions)
          (functions := functions) (functionName := functionName)
          hMap hFind
  | some entry =>
      cases entry
      simp [hFind] at hLookup

theorem contract_toAst?_parts {mode : LayoutMode} {contract : Contract}
    {coreContract : AstContract}
    (hContract : Contract.toAst? mode contract = some coreContract) :
    ∃ dispatcherAst : AstStmt,
      ∃ functions : Finmap (fun (_ : AstFunctionName) =>
          AstFunctionDefinition),
        Stmt.toAst? mode contract.dispatcher = some dispatcherAst ∧
          Contract.functionMap? mode contract.functions = some functions ∧
            coreContract =
              { dispatcher := dispatcherAst, functions := functions } := by
  unfold Contract.toAst? at hContract
  cases hDispatcher : Stmt.toAst? mode contract.dispatcher with
  | none =>
      simp [hDispatcher] at hContract
  | some dispatcherAst =>
      cases hFunctions : Contract.functionMap? mode contract.functions with
      | none =>
          simp [hDispatcher, hFunctions] at hContract
      | some functions =>
          simp [hDispatcher, hFunctions] at hContract
          subst coreContract
          exact ⟨dispatcherAst, functions, rfl, rfl, rfl⟩

theorem contract_toAst?_dispatcher {mode : LayoutMode} {contract : Contract}
    {coreContract : AstContract}
    (hContract : Contract.toAst? mode contract = some coreContract) :
    ∃ dispatcherAst : AstStmt,
      Stmt.toAst? mode contract.dispatcher = some dispatcherAst ∧
        coreContract.dispatcher = dispatcherAst := by
  rcases contract_toAst?_parts hContract with
    ⟨dispatcherAst, functions, hDispatcher, _hFunctions, hCore⟩
  subst coreContract
  exact ⟨dispatcherAst, hDispatcher, rfl⟩

theorem contract_toAst?_lookup_of_source_lookup
    {mode : LayoutMode} {contract : Contract}
    {coreContract : AstContract} {functionName : AstFunctionName}
    {fn : FunctionDefinition}
    (hContract : Contract.toAst? mode contract = some coreContract)
    (hLookup : Source.lookupFunction? contract functionName = some fn) :
    ∃ bodyAst : List AstStmt,
      Stmt.List.toAst? mode fn.body = some bodyAst ∧
        coreContract.functions.lookup functionName =
          some (.Def fn.params fn.returns bodyAst) := by
  rcases contract_toAst?_parts hContract with
    ⟨dispatcherAst, functions, _hDispatcher, hFunctions, hCore⟩
  rcases functionMap?_toAst?_of_source_lookup hFunctions hLookup with
    ⟨fnAst, hFnAst⟩
  unfold FunctionDefinition.toAst? at hFnAst
  cases hBody : Stmt.List.toAst? mode fn.body with
  | none =>
      simp [hBody] at hFnAst
  | some bodyAst =>
      have hFnDef :
          fn.toAst? mode =
            some (.Def fn.params fn.returns bodyAst) := by
        simp [FunctionDefinition.toAst?, hBody]
      have hCoreLookup :
          functions.lookup functionName =
            some (.Def fn.params fn.returns bodyAst) :=
        functionMap?_lookup_of_source_lookup
          (mode := mode) (contract := contract) (functions := functions)
          (functionName := functionName) (fn := fn)
          (fnAst := .Def fn.params fn.returns bodyAst)
          hFunctions hLookup hFnDef
      subst coreContract
      exact ⟨bodyAst, rfl, hCoreLookup⟩

theorem contract_toAst?_lookup_none_of_source_lookup_none
    {mode : LayoutMode} {contract : Contract}
    {coreContract : AstContract} {functionName : AstFunctionName}
    (hContract : Contract.toAst? mode contract = some coreContract)
    (hLookup : Source.lookupFunction? contract functionName = none) :
    coreContract.functions.lookup functionName = none := by
  rcases contract_toAst?_parts hContract with
    ⟨dispatcherAst, functions, _hDispatcher, hFunctions, hCore⟩
  have hCoreLookup :
      functions.lookup functionName = none :=
    functionMap?_lookup_none_of_source_lookup_none
      (mode := mode) (contract := contract) (functions := functions)
      (functionName := functionName) hFunctions hLookup
  subst coreContract
  exact hCoreLookup

theorem call_user_missing_function_to_core_of_contractAst
    {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {account : EvmYul.Account .Yul}
    {coreContract : AstContract}
    (hAccount :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner =
        some account)
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract)
    (hSourceLookup :
      Source.lookupFunction? runtime.contract functionName = none) :
    Source.call (fuel + 1) runtime args (some functionName) state =
      EvmYul.Yul.call (fuel + 1) args (some functionName)
        (some coreContract) state := by
  have hCoreLookup :
      coreContract.functions.lookup functionName = none :=
    contract_toAst?_lookup_none_of_source_lookup_none
      (mode := runtime.checkedMode) (contract := runtime.contract)
      (coreContract := coreContract) (functionName := functionName)
      hContract hSourceLookup
  simp [Source.call, EvmYul.Yul.call, hAccount, hSourceLookup, hCoreLookup]

theorem evalCall_user_missing_function_to_core_of_contractAst
    {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {account : EvmYul.Account .Yul}
    {coreContract : AstContract}
    (hAccount :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner =
        some account)
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract)
    (hSourceLookup :
      Source.lookupFunction? runtime.contract functionName = none) :
    Source.evalCall (fuel + 2) runtime functionName (.ok (state, args)) =
      EvmYul.Yul.evalCall (fuel + 2) functionName (some coreContract)
        (.ok (state, args)) := by
  simp [Source.evalCall, EvmYul.Yul.evalCall]
  rw [call_user_missing_function_to_core_of_contractAst
    (runtime := runtime) (fuel := fuel) (args := args)
    (functionName := functionName) (state := state) (account := account)
    (coreContract := coreContract) hAccount hContract hSourceLookup]
  simp [Source.headResult, EvmYul.Yul.head']
  cases EvmYul.Yul.call (fuel + 1) args (some functionName)
      (some coreContract) state <;> rfl

theorem call_user_present_to_core_of_bodyAst {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {account : EvmYul.Account .Yul}
    {coreContract : AstContract} {fn : FunctionDefinition}
    {bodyAst : List AstStmt}
    (hAccount :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner =
        some account)
    (hSourceLookup :
      Source.lookupFunction? runtime.contract functionName = some fn)
    (hCoreLookup :
      coreContract.functions.lookup functionName =
        some (.Def fn.params fn.returns bodyAst))
    (hBody :
      Source.exec fuel runtime (.block fn.body)
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall fn.params fn.returns args state)) =
        EvmYul.Yul.exec fuel (.Block bodyAst) (some coreContract)
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall fn.params fn.returns args state))) :
    Source.call (fuel + 1) runtime args (some functionName) state =
      EvmYul.Yul.call (fuel + 1) args (some functionName)
        (some coreContract) state := by
  simp [Source.call, EvmYul.Yul.call, hAccount, hSourceLookup, hCoreLookup]
  have hBody' :
      Source.exec fuel runtime (.block fn.body)
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall fn.params fn.returns args state)) =
        EvmYul.Yul.exec fuel
          (.Block
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              fn.params fn.returns bodyAst).body)
          (some coreContract)
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall
              (EvmYul.Yul.Ast.FunctionDefinition.Def
                fn.params fn.returns bodyAst).params
              (EvmYul.Yul.Ast.FunctionDefinition.Def
                fn.params fn.returns bodyAst).rets
              args state)) := by
    simpa using hBody
  rw [hBody']
  cases hExec : EvmYul.Yul.exec fuel
      (.Block
        (EvmYul.Yul.Ast.FunctionDefinition.Def
          fn.params fn.returns bodyAst).body)
      (some coreContract)
      (EvmYul.Yul.State.mkOk
        (EvmYul.Yul.State.initcall
        (EvmYul.Yul.Ast.FunctionDefinition.Def
          fn.params fn.returns bodyAst).params
        (EvmYul.Yul.Ast.FunctionDefinition.Def
          fn.params fn.returns bodyAst).rets
        args state))
  · rfl
  · simp
    rfl

theorem evalCall_user_present_to_core_of_bodyAst {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {account : EvmYul.Account .Yul}
    {coreContract : AstContract} {fn : FunctionDefinition}
    {bodyAst : List AstStmt}
    (hAccount :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner =
        some account)
    (hSourceLookup :
      Source.lookupFunction? runtime.contract functionName = some fn)
    (hCoreLookup :
      coreContract.functions.lookup functionName =
        some (.Def fn.params fn.returns bodyAst))
    (hBody :
      Source.exec fuel runtime (.block fn.body)
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall fn.params fn.returns args state)) =
        EvmYul.Yul.exec fuel (.Block bodyAst) (some coreContract)
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall fn.params fn.returns args state))) :
    Source.evalCall (fuel + 2) runtime functionName (.ok (state, args)) =
      EvmYul.Yul.evalCall (fuel + 2) functionName (some coreContract)
        (.ok (state, args)) := by
  simp [Source.evalCall, EvmYul.Yul.evalCall]
  rw [call_user_present_to_core_of_bodyAst
    (runtime := runtime) (fuel := fuel) (args := args)
    (functionName := functionName) (state := state) (account := account)
    (coreContract := coreContract) (fn := fn) (bodyAst := bodyAst)
    hAccount hSourceLookup hCoreLookup hBody]
  simp [Source.headResult, EvmYul.Yul.head']
  cases EvmYul.Yul.call (fuel + 1) args (some functionName)
      (some coreContract) state <;> rfl

theorem call_user_present_to_core_of_contractAst {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {account : EvmYul.Account .Yul}
    {coreContract : AstContract} {fn : FunctionDefinition}
    (hAccount :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner =
        some account)
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract)
    (hSourceLookup :
      Source.lookupFunction? runtime.contract functionName = some fn)
    (hBody :
      ∀ bodyAst : List AstStmt,
        Stmt.List.toAst? (runtime.checkedMode) fn.body = some bodyAst →
          Source.exec fuel runtime (.block fn.body)
              (EvmYul.Yul.State.mkOk
                (EvmYul.Yul.State.initcall fn.params fn.returns args state)) =
            EvmYul.Yul.exec fuel (.Block bodyAst) (some coreContract)
              (EvmYul.Yul.State.mkOk
                (EvmYul.Yul.State.initcall
                  fn.params fn.returns args state))) :
    Source.call (fuel + 1) runtime args (some functionName) state =
      EvmYul.Yul.call (fuel + 1) args (some functionName)
        (some coreContract) state := by
  rcases
      contract_toAst?_lookup_of_source_lookup
        (mode := runtime.checkedMode) (contract := runtime.contract)
        (coreContract := coreContract) (functionName := functionName)
        (fn := fn) hContract hSourceLookup with
    ⟨bodyAst, hBodyAst, hCoreLookup⟩
  exact
    call_user_present_to_core_of_bodyAst
      (runtime := runtime) (fuel := fuel) (args := args)
      (functionName := functionName) (state := state) (account := account)
      (coreContract := coreContract) (fn := fn) (bodyAst := bodyAst)
      hAccount hSourceLookup hCoreLookup (hBody bodyAst hBodyAst)

theorem evalCall_user_present_to_core_of_contractAst {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {account : EvmYul.Account .Yul}
    {coreContract : AstContract} {fn : FunctionDefinition}
    (hAccount :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner =
        some account)
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract)
    (hSourceLookup :
      Source.lookupFunction? runtime.contract functionName = some fn)
    (hBody :
      ∀ bodyAst : List AstStmt,
        Stmt.List.toAst? (runtime.checkedMode) fn.body = some bodyAst →
          Source.exec fuel runtime (.block fn.body)
              (EvmYul.Yul.State.mkOk
                (EvmYul.Yul.State.initcall fn.params fn.returns args state)) =
            EvmYul.Yul.exec fuel (.Block bodyAst) (some coreContract)
              (EvmYul.Yul.State.mkOk
                (EvmYul.Yul.State.initcall
                  fn.params fn.returns args state))) :
    Source.evalCall (fuel + 2) runtime functionName (.ok (state, args)) =
      EvmYul.Yul.evalCall (fuel + 2) functionName (some coreContract)
        (.ok (state, args)) := by
  simp [Source.evalCall, EvmYul.Yul.evalCall]
  rw [call_user_present_to_core_of_contractAst
    (runtime := runtime) (fuel := fuel) (args := args)
    (functionName := functionName) (state := state) (account := account)
    (coreContract := coreContract) (fn := fn)
    hAccount hContract hSourceLookup hBody]
  simp [Source.headResult, EvmYul.Yul.head']
  cases EvmYul.Yul.call (fuel + 1) args (some functionName)
      (some coreContract) state <;> rfl

theorem call_user_succ_toAst?_checked_core_of_contract_and_blocks
    {runtime : Source.Runtime}
    {fuel : Nat} {args : List Word} {functionName : AstFunctionName}
    {state : Source.State} {coreContract : AstContract}
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract)
    (hExecBlock :
      ∀ (body : List Stmt) (bodyAst : List AstStmt)
        (state : Source.State),
        Stmt.List.toAst? (runtime.checkedMode) body = some bodyAst →
          Source.exec fuel runtime (.block body) state =
            EvmYul.Yul.exec fuel (.Block bodyAst) (some coreContract) state) :
    Source.call (fuel + 1) runtime args (some functionName) state =
      EvmYul.Yul.call (fuel + 1) args (some functionName)
        (some coreContract) state := by
  cases hAccount :
      state.sharedState.accountMap.find? state.executionEnv.codeOwner with
  | none =>
      exact
        call_user_missing_contract_to_core
          (runtime := runtime) (fuel := fuel) (args := args)
          (functionName := functionName) (state := state)
          (codeOverride := some coreContract) hAccount
  | some account =>
      cases hLookup :
          Source.lookupFunction? runtime.contract functionName with
      | none =>
          exact
            call_user_missing_function_to_core_of_contractAst
              (runtime := runtime) (fuel := fuel) (args := args)
              (functionName := functionName) (state := state)
              (account := account) (coreContract := coreContract)
              hAccount hContract hLookup
      | some fn =>
          exact
            call_user_present_to_core_of_contractAst
              (runtime := runtime) (fuel := fuel) (args := args)
              (functionName := functionName) (state := state)
              (account := account) (coreContract := coreContract)
              (fn := fn) hAccount hContract hLookup
              (fun bodyAst hBodyAst =>
                hExecBlock fn.body bodyAst
                  (EvmYul.Yul.State.mkOk
                    (EvmYul.Yul.State.initcall
                      fn.params fn.returns args state))
                  hBodyAst)

theorem callDispatcher_to_core_of_contractAst {runtime : Source.Runtime}
    {fuel : Nat} {state : Source.State} {coreContract : AstContract}
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract)
    (hStateCode : state.executionEnv.code = coreContract)
    (hBody :
      ∀ dispatcherAst : AstStmt,
        Stmt.toAst? (runtime.checkedMode) runtime.contract.dispatcher =
          some dispatcherAst →
          Source.exec fuel runtime (.block [runtime.contract.dispatcher])
              (EvmYul.Yul.State.mkOk
                (EvmYul.Yul.State.initcall [] [] [] state)) =
            EvmYul.Yul.exec fuel (.Block [dispatcherAst])
              (some coreContract)
              (EvmYul.Yul.State.mkOk
                (EvmYul.Yul.State.initcall [] [] [] state))) :
    Source.callDispatcher (fuel + 1) runtime state =
      EvmYul.Yul.callDispatcher (fuel + 1) (some coreContract) state := by
  rcases contract_toAst?_dispatcher hContract with
    ⟨dispatcherAst, hDispatcher, hCoreDispatcher⟩
  have hStateDispatcher :
      state.executionEnv.code.dispatcher = dispatcherAst := by
    rw [hStateCode, hCoreDispatcher]
  simp [Source.callDispatcher, EvmYul.Yul.callDispatcher, hStateDispatcher]
  have hBody' :
      Source.exec fuel runtime (.block [runtime.contract.dispatcher])
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall [] [] [] state)) =
        EvmYul.Yul.exec fuel
          (.Block
            (EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [dispatcherAst]).body)
          (some coreContract)
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall
              (EvmYul.Yul.Ast.FunctionDefinition.Def
                [] [] [dispatcherAst]).params
              (EvmYul.Yul.Ast.FunctionDefinition.Def
                [] [] [dispatcherAst]).rets
              [] state)) := by
    simpa using hBody dispatcherAst hDispatcher
  rw [hBody']
  cases EvmYul.Yul.exec fuel
      (.Block
        (EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [dispatcherAst]).body)
      (some coreContract)
      (EvmYul.Yul.State.mkOk
        (EvmYul.Yul.State.initcall
          (EvmYul.Yul.Ast.FunctionDefinition.Def
            [] [] [dispatcherAst]).params
          (EvmYul.Yul.Ast.FunctionDefinition.Def
            [] [] [dispatcherAst]).rets
          [] state)) <;> rfl

theorem callDispatcher_succ_toAst?_checked_core_of_contract_and_blocks
    {runtime : Source.Runtime}
    {fuel : Nat} {state : Source.State} {coreContract : AstContract}
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract)
    (hStateCode : state.executionEnv.code = coreContract)
    (hExecBlock :
      ∀ (body : List Stmt) (bodyAst : List AstStmt)
        (state : Source.State),
        Stmt.List.toAst? (runtime.checkedMode) body = some bodyAst →
          Source.exec fuel runtime (.block body) state =
            EvmYul.Yul.exec fuel (.Block bodyAst) (some coreContract) state) :
    Source.callDispatcher (fuel + 1) runtime state =
      EvmYul.Yul.callDispatcher (fuel + 1) (some coreContract) state := by
  exact
    callDispatcher_to_core_of_contractAst
      (runtime := runtime) (fuel := fuel) (state := state)
      (coreContract := coreContract) hContract hStateCode
      (fun dispatcherAst hDispatcher =>
        hExecBlock [runtime.contract.dispatcher] [dispatcherAst]
          (EvmYul.Yul.State.mkOk
            (EvmYul.Yul.State.initcall [] [] [] state))
          (by simp [Stmt.List.toAst?, hDispatcher]))

theorem evalValues_var_toAst?_core {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {name : Name} {codeOverride : CodeOverride} :
    Expr.toAst? mode (.var name) = some (.Var name) ∧
      Source.evalValues fuel runtime (.var name) state =
        EvmYul.Yul.evalValues fuel (.Var name) codeOverride state := by
  constructor
  · rfl
  · cases fuel with
    | zero =>
        simp [Source.evalValues, EvmYul.Yul.evalValues]
    | succ fuel' =>
        simp [Source.evalValues, EvmYul.Yul.evalValues]
        cases EvmYul.Yul.State.lookup? name state <;> rfl

theorem evalValues_lit_toAst?_core {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {value : Word} {codeOverride : CodeOverride} :
    Expr.toAst? mode (.lit value) = some (.Lit value) ∧
      Source.evalValues fuel runtime (.lit value) state =
        EvmYul.Yul.evalValues fuel (.Lit value) codeOverride state := by
  constructor
  · rfl
  · cases fuel <;> simp [Source.evalValues, EvmYul.Yul.evalValues]

theorem evalValues_primCall_toAst?_core_of_args_eq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {prim : PrimOp} {args : List Expr} {argsAst : List AstExpr}
    {codeOverride : CodeOverride}
    (hArgsAst : Expr.List.toAst? mode args = some argsAst)
    (hArgsEq :
      Source.reverseResult
          (Source.evalArgs fuel runtime args.reverse state) =
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel argsAst.reverse codeOverride state)) :
    Expr.toAst? mode (.call (.inl prim) args) =
        some (.Call (.inl prim) argsAst) ∧
      Source.evalValues (fuel + 1) runtime (.call (.inl prim) args) state =
        EvmYul.Yul.evalValues (fuel + 1)
          (.Call (.inl prim) argsAst) codeOverride state := by
  constructor
  · simp [Expr.toAst?, hArgsAst]
  · simp [Source.evalValues, EvmYul.Yul.evalValues]
    rw [hArgsEq]
    cases hCoreArgs :
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel argsAst.reverse codeOverride state) with
    | error exception =>
        rfl
    | ok pair =>
        cases pair
        rfl

theorem evalValues_userCall_toAst?_core_of_args_eq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {functionName : AstFunctionName} {args : List Expr}
    {argsAst : List AstExpr} {codeOverride : CodeOverride}
    (hArgsAst : Expr.List.toAst? mode args = some argsAst)
    (hArgsEq :
      Source.reverseResult
          (Source.evalArgs fuel runtime args.reverse state) =
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel argsAst.reverse codeOverride state))
    (hCall :
      ∀ stateAfterArgs values,
        Source.call fuel runtime values (some functionName) stateAfterArgs =
          EvmYul.Yul.call fuel values (some functionName) codeOverride
            stateAfterArgs) :
    Expr.toAst? mode (.call (.inr functionName) args) =
        some (.Call (.inr functionName) argsAst) ∧
      Source.evalValues (fuel + 1) runtime
          (.call (.inr functionName) args) state =
        EvmYul.Yul.evalValues (fuel + 1)
          (.Call (.inr functionName) argsAst) codeOverride state := by
  constructor
  · simp [Expr.toAst?, hArgsAst]
  · simp [Source.evalValues, EvmYul.Yul.evalValues]
    rw [hArgsEq]
    cases hCoreArgs :
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel argsAst.reverse codeOverride state) with
    | error exception =>
        rfl
    | ok pair =>
        cases pair with
        | mk stateAfterArgs values =>
            simpa using hCall stateAfterArgs values

theorem exec_exprStmt_primCall_toAst?_core_of_args_eq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {prim : PrimOp} {args : List Expr} {argsAst : List AstExpr}
    {codeOverride : CodeOverride}
    (hArgsAst : Expr.List.toAst? mode args = some argsAst)
    (hArgsEq :
      Source.reverseResult
          (Source.evalArgs fuel runtime args.reverse state) =
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel argsAst.reverse codeOverride state)) :
    Stmt.toAst? mode (.exprStmtCall (.call (.inl prim) args)) =
        some (.ExprStmtCall (.Call (.inl prim) argsAst)) ∧
      Source.exec (fuel + 1) runtime
          (.exprStmtCall (.call (.inl prim) args)) state =
        EvmYul.Yul.exec (fuel + 1)
          (.ExprStmtCall (.Call (.inl prim) argsAst)) codeOverride state := by
  constructor
  · simp [Stmt.toAst?, Expr.toAst?, hArgsAst]
  · simp [Source.exec, EvmYul.Yul.exec, Source.execPrimCall]
    rw [hArgsEq]
    cases hCoreArgs :
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel argsAst.reverse codeOverride state) with
    | error exception =>
        simp [EvmYul.Yul.execPrimCall]
    | ok pair =>
        cases pair with
        | mk stateAfterArgs values =>
            simp [EvmYul.Yul.execPrimCall, multifillResult_eq_multifill']

theorem exec_exprStmt_userCall_toAst?_core_of_args_eq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {functionName : AstFunctionName} {args : List Expr}
    {argsAst : List AstExpr} {codeOverride : CodeOverride}
    (hArgsAst : Expr.List.toAst? mode args = some argsAst)
    (hArgsEq :
      Source.reverseResult
          (Source.evalArgs fuel runtime args.reverse state) =
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel argsAst.reverse codeOverride state))
    (hCall :
      ∀ callFuel stateAfterArgs values,
        callFuel < fuel →
        Source.call callFuel runtime values (some functionName)
            stateAfterArgs =
          EvmYul.Yul.call callFuel values (some functionName) codeOverride
            stateAfterArgs) :
    Stmt.toAst? mode (.exprStmtCall (.call (.inr functionName) args)) =
        some (.ExprStmtCall (.Call (.inr functionName) argsAst)) ∧
      Source.exec (fuel + 1) runtime
          (.exprStmtCall (.call (.inr functionName) args)) state =
        EvmYul.Yul.exec (fuel + 1)
          (.ExprStmtCall (.Call (.inr functionName) argsAst)) codeOverride
          state := by
  constructor
  · simp [Stmt.toAst?, Expr.toAst?, hArgsAst]
  · simp [Source.exec, EvmYul.Yul.exec]
    rw [hArgsEq]
    cases hCoreArgs :
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel argsAst.reverse codeOverride state) with
    | error exception =>
        simp [Source.execCall, EvmYul.Yul.execCall]
    | ok pair =>
        cases pair with
        | mk stateAfterArgs values =>
            cases fuel with
            | zero =>
                simp [Source.execCall, EvmYul.Yul.execCall]
            | succ fuel' =>
                simp [Source.execCall, EvmYul.Yul.execCall,
                  multifillResult_eq_multifill']
                rw [hCall fuel' stateAfterArgs values (Nat.lt_succ_self fuel')]

theorem exec_let_none_toAst?_core {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {vars : List Name} {codeOverride : CodeOverride} :
    Stmt.toAst? mode (.let_ vars none) = some (.Let vars none) ∧
      Source.exec (fuel + 1) runtime (.let_ vars none) state =
        EvmYul.Yul.exec (fuel + 1) (.Let vars none) codeOverride state := by
  constructor
  · rfl
  · simp [Source.exec, EvmYul.Yul.exec]
    cases EvmYul.Yul.checkDeclaration state vars <;> rfl

theorem exec_let_some_toAst?_core_of_evalValues_eq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {vars : List Name} {value : Expr} {valueAst : AstExpr}
    {codeOverride : CodeOverride}
    (hValueAst : Expr.toAst? mode value = some valueAst)
    (hEvalValues :
      Source.evalValues fuel runtime value state =
        EvmYul.Yul.evalValues fuel valueAst codeOverride state) :
    Stmt.toAst? mode (.let_ vars (some value)) =
        some (.Let vars (some valueAst)) ∧
      Source.exec (fuel + 1) runtime (.let_ vars (some value)) state =
        EvmYul.Yul.exec (fuel + 1) (.Let vars (some valueAst))
          codeOverride state := by
  constructor
  · simp [Stmt.toAst?, hValueAst]
  · simp [Source.exec, EvmYul.Yul.exec, hEvalValues]
    cases EvmYul.Yul.checkDeclaration state vars with
    | error exception =>
        rfl
    | ok _ =>
        rw [multifillResult_eq_multifill']

theorem exec_assign_toAst?_core_of_evalValues_eq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {vars : List Name} {value : Expr} {valueAst : AstExpr}
    {codeOverride : CodeOverride}
    (hValueAst : Expr.toAst? mode value = some valueAst)
    (hEvalValues :
      Source.evalValues fuel runtime value state =
        EvmYul.Yul.evalValues fuel valueAst codeOverride state) :
    Stmt.toAst? mode (.assign vars value) =
        some (.Assign vars valueAst) ∧
      Source.exec (fuel + 1) runtime (.assign vars value) state =
        EvmYul.Yul.exec (fuel + 1) (.Assign vars valueAst)
          codeOverride state := by
  constructor
  · simp [Stmt.toAst?, hValueAst]
  · simp [Source.exec, EvmYul.Yul.exec, hEvalValues]
    cases EvmYul.Yul.checkAssignment state vars with
    | error exception =>
        rfl
    | ok _ =>
        rw [multifillResult_eq_multifill']

theorem exec_if_toAst?_core_of_eval_body {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {cond : Expr} {condAst : AstExpr}
    {body : List Stmt} {bodyAst : List AstStmt}
    {codeOverride : CodeOverride}
    (hCondAst : Expr.toAst? mode cond = some condAst)
    (hBodyAst : Stmt.List.toAst? mode body = some bodyAst)
    (hEval :
      Source.eval fuel runtime cond state =
        EvmYul.Yul.eval fuel condAst codeOverride state)
    (hBody :
      ∀ stateAfterCond : Source.State,
        Source.exec fuel runtime (.block body) stateAfterCond =
          EvmYul.Yul.exec fuel (.Block bodyAst) codeOverride
            stateAfterCond) :
    Stmt.toAst? mode (.if_ cond body) = some (.If condAst bodyAst) ∧
      Source.exec (fuel + 1) runtime (.if_ cond body) state =
        EvmYul.Yul.exec (fuel + 1) (.If condAst bodyAst) codeOverride
          state := by
  constructor
  · simp [Stmt.toAst?, hCondAst, hBodyAst]
  · simp [Source.exec, EvmYul.Yul.exec, hEval]
    cases hCoreEval : EvmYul.Yul.eval fuel condAst codeOverride state with
    | error exception =>
        rfl
    | ok pair =>
        cases pair with
        | mk stateAfterCond condValue =>
            by_cases hZero : condValue = EvmYul.UInt256.ofNat 0
            · have hZeroCore : condValue = ({ val := 0 } : Word) := by
                simpa [← word_zero_ofNat_eq_literal] using hZero
              simp [hZero, word_zero_ofNat_eq_literal]
            · have hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0 := hZero
              have hNonzeroCore : condValue ≠ ({ val := 0 } : Word) := by
                intro hCoreZero
                exact hZero (by
                  simpa [← word_zero_ofNat_eq_literal] using hCoreZero)
              simp [hNonzeroCore, hBody stateAfterCond,
                word_zero_ofNat_eq_literal]

theorem exec_switch_toAst?_core_of_eval_selected {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {scrutinee : Expr} {scrutineeAst : AstExpr}
    {cases : List (Word × List Stmt)}
    {casesAst : List (Word × List AstStmt)}
    {defaultBody : List Stmt} {defaultBodyAst : List AstStmt}
    {codeOverride : CodeOverride}
    (hScrutineeAst : Expr.toAst? mode scrutinee = some scrutineeAst)
    (hCasesAst : Stmt.Cases.toAst? mode cases = some casesAst)
    (hDefaultAst : Stmt.List.toAst? mode defaultBody = some defaultBodyAst)
    (hEval :
      Source.eval fuel runtime scrutinee state =
        EvmYul.Yul.eval fuel scrutineeAst codeOverride state)
    (hSelected :
      ∀ (stateAfterCond : Source.State)
        (selectedBody : List Stmt) (selectedBodyAst : List AstStmt),
        Stmt.List.toAst? mode selectedBody = some selectedBodyAst →
          Source.exec fuel runtime (.block selectedBody) stateAfterCond =
            EvmYul.Yul.exec fuel (.Block selectedBodyAst) codeOverride
              stateAfterCond) :
    Stmt.toAst? mode (.switch scrutinee cases defaultBody) =
        some (.Switch scrutineeAst casesAst defaultBodyAst) ∧
      Source.exec (fuel + 1) runtime
          (.switch scrutinee cases defaultBody) state =
        EvmYul.Yul.exec (fuel + 1)
          (.Switch scrutineeAst casesAst defaultBodyAst) codeOverride
          state := by
  constructor
  · simp [Stmt.toAst?, hScrutineeAst, hCasesAst, hDefaultAst]
  · simp [Source.exec, EvmYul.Yul.exec, hEval]
    cases hCoreEval : EvmYul.Yul.eval fuel scrutineeAst codeOverride state with
    | error exception =>
        rfl
    | ok pair =>
        cases pair with
        | mk stateAfterCond condValue =>
            have hSelect :
                Stmt.List.toAst? mode
                    (Source.selectSwitchCase condValue defaultBody cases) =
                  some
                    (EvmYul.Yul.selectSwitchCase condValue defaultBodyAst
                      casesAst) :=
              selectSwitchCase_toAst?_core
                (mode := mode) (cond := condValue)
                (defaultBody := defaultBody)
                (defaultBodyAst := defaultBodyAst)
                (cases := cases) (casesAst := casesAst)
                hDefaultAst hCasesAst
            exact
              hSelected stateAfterCond
                (Source.selectSwitchCase condValue defaultBody cases)
                (EvmYul.Yul.selectSwitchCase condValue defaultBodyAst
                  casesAst)
                hSelect

theorem evalValues_datasize_toAst?_checked_core {runtime : Source.Runtime}
    {fuel : Nat} {state : Source.State} {name : Name} {value : Word}
    {codeOverride : CodeOverride}
    (hLookup : Objects.ObjectLayout.size? runtime.layout name = some value) :
    ∃ ast : AstExpr,
      Expr.toAst? (runtime.checkedMode) (.datasize name) = some ast ∧
        Source.evalValues (fuel + 1) runtime (.datasize name) state =
          EvmYul.Yul.evalValues (fuel + 1) ast codeOverride state := by
  refine
    ⟨.Lit value,
      Expr.toAst?_datasize_checked hLookup,
      ?_⟩
  rw [Source.evalValues_datasize (runtime := runtime) (fuel := fuel)
    (state := state) (name := name) (value := value)]
  · simp [EvmYul.Yul.evalValues]
  · simpa [Source.layoutSize?] using hLookup

theorem evalValues_dataoffset_toAst?_checked_core {runtime : Source.Runtime}
    {fuel : Nat} {state : Source.State} {name : Name} {value : Word}
    {codeOverride : CodeOverride}
    (hLookup : Objects.ObjectLayout.offset? runtime.layout name = some value) :
    ∃ ast : AstExpr,
      Expr.toAst? (runtime.checkedMode) (.dataoffset name) = some ast ∧
        Source.evalValues (fuel + 1) runtime (.dataoffset name) state =
          EvmYul.Yul.evalValues (fuel + 1) ast codeOverride state := by
  refine
    ⟨.Lit value,
      Expr.toAst?_dataoffset_checked hLookup,
      ?_⟩
  rw [Source.evalValues_dataoffset (runtime := runtime) (fuel := fuel)
    (state := state) (name := name) (value := value)]
  · simp [EvmYul.Yul.evalValues]
  · simpa [Source.layoutOffset?] using hLookup

theorem evalValues_datacopy_toAst?_core_of_args_eq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {dst offset size : Expr} {dstAst offsetAst sizeAst : AstExpr}
    {codeOverride : CodeOverride}
    (hDst : Expr.toAst? mode dst = some dstAst)
    (hOffset : Expr.toAst? mode offset = some offsetAst)
    (hSize : Expr.toAst? mode size = some sizeAst)
    (hArgsEq :
      Source.reverseResult
          (Source.evalArgs fuel runtime [dst, offset, size].reverse state) =
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel
            [dstAst, offsetAst, sizeAst].reverse codeOverride state)) :
    Expr.toAst? mode (.datacopy dst offset size) =
        some (.Call (.inl codecopyPrim) [dstAst, offsetAst, sizeAst]) ∧
      Source.evalValues (fuel + 1) runtime (.datacopy dst offset size) state =
        EvmYul.Yul.evalValues (fuel + 1)
          (.Call (.inl codecopyPrim) [dstAst, offsetAst, sizeAst])
          codeOverride state := by
  constructor
  · exact Expr.toAst?_datacopy_checked hDst hOffset hSize
  · simp [Source.evalValues, EvmYul.Yul.evalValues, codecopyPrim]
    have hArgsEq' :
        Source.reverseResult
            (Source.evalArgs fuel runtime [size, offset, dst] state) =
          EvmYul.Yul.reverse'
            (EvmYul.Yul.evalArgs fuel
              [sizeAst, offsetAst, dstAst] codeOverride state) := by
      simpa using hArgsEq
    rw [hArgsEq']
    cases EvmYul.Yul.reverse'
        (EvmYul.Yul.evalArgs fuel
          [sizeAst, offsetAst, dstAst] codeOverride state) with
    | error exception =>
        rfl
    | ok pair =>
        cases pair
        rfl

theorem evalValues_succ_toAst?_checked_core_of_args_and_calls
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {expr : Expr} {ast : AstExpr} {coreContract : AstContract}
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract)
    (hExprAst :
      Expr.toAst? (runtime.checkedMode) expr = some ast)
    (hArgs :
      ∀ (args : List Expr) (argsAst : List AstExpr)
        (state : Source.State),
        Expr.List.toAst? (runtime.checkedMode) args = some argsAst →
          Source.evalArgs fuel runtime args state =
            EvmYul.Yul.evalArgs fuel argsAst (some coreContract) state)
    (hCall :
      ∀ (functionName : AstFunctionName)
        (stateAfterArgs : Source.State) (values : List Word),
        Source.call fuel runtime values (some functionName) stateAfterArgs =
          EvmYul.Yul.call fuel values (some functionName)
            (some coreContract) stateAfterArgs) :
    Source.evalValues (fuel + 1) runtime expr state =
      EvmYul.Yul.evalValues (fuel + 1) ast (some coreContract) state := by
  have _ :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract := hContract
  cases expr with
  | call functionName args =>
      cases hArgsAst : Expr.List.toAst? (runtime.checkedMode) args with
      | none =>
          simp [Expr.toAst?, hArgsAst] at hExprAst
      | some argsAst =>
          simp [Expr.toAst?, hArgsAst] at hExprAst
          cases hExprAst
          have hArgsRevAst :
              Expr.List.toAst? (runtime.checkedMode) args.reverse =
                some argsAst.reverse :=
            exprList_toAst?_reverse hArgsAst
          have hEvalArgsRev :
              Source.evalArgs fuel runtime args.reverse state =
                EvmYul.Yul.evalArgs fuel argsAst.reverse
                  (some coreContract) state :=
            hArgs args.reverse argsAst.reverse state hArgsRevAst
          have hArgsEq :
              Source.reverseResult
                  (Source.evalArgs fuel runtime args.reverse state) =
                EvmYul.Yul.reverse'
                  (EvmYul.Yul.evalArgs fuel argsAst.reverse
                    (some coreContract) state) := by
            rw [hEvalArgsRev]
            exact reverseResult_eq_reverse' _
          cases functionName with
          | inl prim =>
              exact
                (evalValues_primCall_toAst?_core_of_args_eq
                  (mode := runtime.checkedMode) (runtime := runtime)
                  (fuel := fuel) (state := state) (prim := prim)
                  (args := args) (argsAst := argsAst)
                  (codeOverride := some coreContract) hArgsAst hArgsEq).2
          | inr functionName =>
              exact
                (evalValues_userCall_toAst?_core_of_args_eq
                  (mode := runtime.checkedMode) (runtime := runtime)
                  (fuel := fuel) (state := state)
                  (functionName := functionName) (args := args)
                  (argsAst := argsAst) (codeOverride := some coreContract)
                  hArgsAst hArgsEq
                  (fun stateAfterArgs values =>
                    hCall functionName stateAfterArgs values)).2
  | var name =>
      simp [Expr.toAst?] at hExprAst
      cases hExprAst
      exact
        (evalValues_var_toAst?_core
          (mode := runtime.checkedMode) (runtime := runtime)
          (fuel := fuel + 1) (state := state) (name := name)
          (codeOverride := some coreContract)).2
  | lit value =>
      simp [Expr.toAst?] at hExprAst
      cases hExprAst
      exact
        (evalValues_lit_toAst?_core
          (mode := runtime.checkedMode) (runtime := runtime)
          (fuel := fuel + 1) (state := state) (value := value)
          (codeOverride := some coreContract)).2
  | datasize name =>
      cases hLookup :
          Objects.ObjectLayout.size? runtime.layout name with
      | none =>
          simp [Expr.toAst?, LayoutMode.size?, Source.Runtime.checkedMode,
            hLookup] at hExprAst
      | some value =>
          simp [Expr.toAst?, LayoutMode.size?, Source.Runtime.checkedMode,
            hLookup] at hExprAst
          cases hExprAst
          rw [Source.evalValues_datasize
            (runtime := runtime) (fuel := fuel) (state := state)
            (name := name) (value := value)]
          · simp [EvmYul.Yul.evalValues]
          · simpa [Source.layoutSize?] using hLookup
  | dataoffset name =>
      cases hLookup :
          Objects.ObjectLayout.offset? runtime.layout name with
      | none =>
          simp [Expr.toAst?, LayoutMode.offset?, Source.Runtime.checkedMode,
            hLookup] at hExprAst
      | some value =>
          simp [Expr.toAst?, LayoutMode.offset?, Source.Runtime.checkedMode,
            hLookup] at hExprAst
          cases hExprAst
          rw [Source.evalValues_dataoffset
            (runtime := runtime) (fuel := fuel) (state := state)
            (name := name) (value := value)]
          · simp [EvmYul.Yul.evalValues]
          · simpa [Source.layoutOffset?] using hLookup
  | datacopy dst offset size =>
      cases hDst : Expr.toAst? (runtime.checkedMode) dst with
      | none =>
          simp [Expr.toAst?, hDst] at hExprAst
      | some dstAst =>
          cases hOffset : Expr.toAst? (runtime.checkedMode) offset with
          | none =>
              simp [Expr.toAst?, hDst, hOffset] at hExprAst
          | some offsetAst =>
              cases hSize :
                  Expr.toAst? (runtime.checkedMode) size with
              | none =>
                  simp [Expr.toAst?, hDst, hOffset, hSize] at hExprAst
              | some sizeAst =>
                  simp [Expr.toAst?, hDst, hOffset, hSize] at hExprAst
                  cases hExprAst
                  have hTripleAst :
                      Expr.List.toAst? (runtime.checkedMode)
                          [dst, offset, size].reverse =
                        some [dstAst, offsetAst, sizeAst].reverse := by
                    simp [Expr.List.toAst?, hDst, hOffset, hSize]
                  have hEvalArgsTriple :
                      Source.evalArgs fuel runtime
                          [dst, offset, size].reverse state =
                        EvmYul.Yul.evalArgs fuel
                          [dstAst, offsetAst, sizeAst].reverse
                          (some coreContract) state :=
                    hArgs [dst, offset, size].reverse
                      [dstAst, offsetAst, sizeAst].reverse state hTripleAst
                  have hArgsEq :
                      Source.reverseResult
                          (Source.evalArgs fuel runtime
                            [dst, offset, size].reverse state) =
                        EvmYul.Yul.reverse'
                          (EvmYul.Yul.evalArgs fuel
                            [dstAst, offsetAst, sizeAst].reverse
                            (some coreContract) state) := by
                    rw [hEvalArgsTriple]
                    exact reverseResult_eq_reverse' _
                  exact
                    (evalValues_datacopy_toAst?_core_of_args_eq
                      (mode := runtime.checkedMode) (runtime := runtime)
                      (fuel := fuel) (state := state) (dst := dst)
                      (offset := offset) (size := size) (dstAst := dstAst)
                      (offsetAst := offsetAst) (sizeAst := sizeAst)
                      (codeOverride := some coreContract)
                      hDst hOffset hSize hArgsEq).2
  | linkersymbol name =>
      cases hLookup : findNamed? runtime.linkerSymbols name with
      | none =>
          simp [Expr.toAst?, LayoutMode.linkerSymbol?,
            Source.Runtime.checkedMode, hLookup]
            at hExprAst
      | some value =>
          simp [Expr.toAst?, LayoutMode.linkerSymbol?,
            Source.Runtime.checkedMode, hLookup]
            at hExprAst
          cases hExprAst
          simp [Source.evalValues, EvmYul.Yul.evalValues,
            Source.linkerSymbol?, hLookup]
  | loadimmutable name =>
      cases hLookup : findNamed? runtime.immutableValues name with
      | none =>
          simp [Expr.toAst?, LayoutMode.immutableValue?,
            Source.Runtime.checkedMode, hLookup]
            at hExprAst
      | some value =>
          simp [Expr.toAst?, LayoutMode.immutableValue?,
            Source.Runtime.checkedMode, hLookup]
            at hExprAst
          cases hExprAst
          simp [Source.evalValues, EvmYul.Yul.evalValues,
            Source.immutableValue?, hLookup]
  | memoryguard size =>
      simp [Expr.toAst?] at hExprAst
      cases hExprAst
      simp [Source.evalValues, EvmYul.Yul.evalValues]

theorem evalValues_datacopy_toAst?_core_of_args {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state stateAfterArgs : Source.State}
    {dst offset size : Expr} {dstAst offsetAst sizeAst : AstExpr}
    {args : List Word} {codeOverride : CodeOverride}
    (hDst : Expr.toAst? mode dst = some dstAst)
    (hOffset : Expr.toAst? mode offset = some offsetAst)
    (hSize : Expr.toAst? mode size = some sizeAst)
    (hSourceArgs :
      Source.reverseResult
        (Source.evalArgs fuel runtime [dst, offset, size].reverse state) =
          .ok (stateAfterArgs, args))
    (hCoreArgs :
      EvmYul.Yul.reverse'
        (EvmYul.Yul.evalArgs fuel
          [dstAst, offsetAst, sizeAst].reverse codeOverride state) =
          .ok (stateAfterArgs, args)) :
    ∃ ast : AstExpr,
      Expr.toAst? mode (.datacopy dst offset size) = some ast ∧
        Source.evalValues (fuel + 1) runtime (.datacopy dst offset size) state =
          EvmYul.Yul.evalValues (fuel + 1) ast codeOverride state := by
  refine
    ⟨.Call (.inl codecopyPrim) [dstAst, offsetAst, sizeAst],
      Expr.toAst?_datacopy_checked hDst hOffset hSize,
      ?_⟩
  have hCoreArgs' :
      EvmYul.Yul.reverse'
        (EvmYul.Yul.evalArgs fuel
          [sizeAst, offsetAst, dstAst] codeOverride state) =
          .ok (stateAfterArgs, args) := by
    simpa using hCoreArgs
  rw [Source.evalValues_datacopy
    (runtime := runtime) (fuel := fuel) (state := state)
    (dst := dst) (offset := offset) (size := size)
    (stateAfterArgs := stateAfterArgs) (args := args) hSourceArgs]
  simp [EvmYul.Yul.evalValues, codecopyPrim, hCoreArgs']

theorem exec_exprStmt_datacopy_toAst?_core_of_args_eq {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {dst offset size : Expr} {dstAst offsetAst sizeAst : AstExpr}
    {codeOverride : CodeOverride}
    (hDst : Expr.toAst? mode dst = some dstAst)
    (hOffset : Expr.toAst? mode offset = some offsetAst)
    (hSize : Expr.toAst? mode size = some sizeAst)
    (hArgsEq :
      Source.reverseResult
          (Source.evalArgs fuel runtime [dst, offset, size].reverse state) =
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs fuel
            [dstAst, offsetAst, sizeAst].reverse codeOverride state)) :
    Stmt.toAst? mode (.exprStmtCall (.datacopy dst offset size)) =
        some (.ExprStmtCall
          (.Call (.inl codecopyPrim) [dstAst, offsetAst, sizeAst])) ∧
      Source.exec (fuel + 1) runtime
          (.exprStmtCall (.datacopy dst offset size)) state =
        EvmYul.Yul.exec (fuel + 1)
          (.ExprStmtCall
            (.Call (.inl codecopyPrim) [dstAst, offsetAst, sizeAst]))
          codeOverride state := by
  constructor
  · simp [Stmt.toAst?, Expr.toAst?, hDst, hOffset, hSize, codecopyPrim]
  · simp [Source.exec, EvmYul.Yul.exec, Source.execPrimCall, codecopyPrim]
    have hArgsEq' :
        Source.reverseResult
            (Source.evalArgs fuel runtime [size, offset, dst] state) =
          EvmYul.Yul.reverse'
            (EvmYul.Yul.evalArgs fuel
              [sizeAst, offsetAst, dstAst] codeOverride state) := by
      simpa using hArgsEq
    rw [hArgsEq']
    cases EvmYul.Yul.reverse'
        (EvmYul.Yul.evalArgs fuel
          [sizeAst, offsetAst, dstAst] codeOverride state) with
    | error exception =>
        simp [EvmYul.Yul.execPrimCall]
    | ok pair =>
        cases pair with
        | mk stateAfterArgs args =>
            simp [EvmYul.Yul.execPrimCall, multifillResult_eq_multifill']

theorem exec_succ_toAst?_checked_core_of_parts
    {runtime : Source.Runtime} {fuel : Nat} {state : Source.State}
    {stmt : Stmt} {stmtAst : AstStmt} {coreContract : AstContract}
    (hStmtAst :
      Stmt.toAst? (runtime.checkedMode) stmt = some stmtAst)
    (hEvalValues :
      ∀ (expr : Expr) (exprAst : AstExpr) (state : Source.State),
        Expr.toAst? (runtime.checkedMode) expr = some exprAst →
          Source.evalValues fuel runtime expr state =
            EvmYul.Yul.evalValues fuel exprAst (some coreContract) state)
    (hArgs :
      ∀ (args : List Expr) (argsAst : List AstExpr)
        (state : Source.State),
        Expr.List.toAst? (runtime.checkedMode) args = some argsAst →
          Source.evalArgs fuel runtime args state =
            EvmYul.Yul.evalArgs fuel argsAst (some coreContract) state)
    (hCall :
      ∀ (callFuel : Nat) (functionName : AstFunctionName)
        (stateAfterArgs : Source.State) (values : List Word),
        callFuel < fuel →
        Source.call callFuel runtime values (some functionName) stateAfterArgs =
          EvmYul.Yul.call callFuel values (some functionName)
            (some coreContract) stateAfterArgs)
    (hExecSeq :
      ∀ (body : List Stmt) (bodyAst : List AstStmt)
        (state : Source.State),
        Stmt.List.toAst? (runtime.checkedMode) body = some bodyAst →
          Source.execSeq fuel runtime body state =
            EvmYul.Yul.execSeq fuel bodyAst (some coreContract) state)
    (hExecBlock :
      ∀ (body : List Stmt) (bodyAst : List AstStmt)
        (state : Source.State),
        Stmt.List.toAst? (runtime.checkedMode) body = some bodyAst →
          Source.exec fuel runtime (.block body) state =
            EvmYul.Yul.exec fuel (.Block bodyAst) (some coreContract) state)
    (hLoop :
      ∀ (cond : Expr) (condAst : AstExpr)
        (post body : List Stmt) (postAst bodyAst : List AstStmt)
        (state : Source.State),
        Expr.toAst? (runtime.checkedMode) cond = some condAst →
          Stmt.List.toAst? (runtime.checkedMode) post = some postAst →
            Stmt.List.toAst? (runtime.checkedMode) body = some bodyAst →
              Source.loop fuel runtime cond post body state =
                EvmYul.Yul.loop fuel condAst postAst bodyAst
                  (some coreContract) state) :
    Source.exec (fuel + 1) runtime stmt state =
      EvmYul.Yul.exec (fuel + 1) stmtAst (some coreContract) state := by
  cases stmt with
  | block body =>
      cases hBodyAst :
          Stmt.List.toAst? (runtime.checkedMode) body with
      | none =>
          simp [Stmt.toAst?, hBodyAst] at hStmtAst
      | some bodyAst =>
          simp [Stmt.toAst?, hBodyAst] at hStmtAst
          cases hStmtAst
          exact
            (exec_block_toAst?_core_of_execSeq
              (mode := runtime.checkedMode) (runtime := runtime)
              (fuel := fuel) (state := state) (body := body)
              (bodyAst := bodyAst) (codeOverride := some coreContract)
              hBodyAst (hExecSeq body bodyAst state hBodyAst)).2
  | let_ vars value? =>
      cases value? with
      | none =>
          simp [Stmt.toAst?] at hStmtAst
          cases hStmtAst
          exact
            (exec_let_none_toAst?_core
              (mode := runtime.checkedMode) (runtime := runtime)
              (fuel := fuel) (state := state) (vars := vars)
              (codeOverride := some coreContract)).2
      | some value =>
          cases hValueAst :
              Expr.toAst? (runtime.checkedMode) value with
          | none =>
              simp [Stmt.toAst?, hValueAst] at hStmtAst
          | some valueAst =>
              simp [Stmt.toAst?, hValueAst] at hStmtAst
              cases hStmtAst
              exact
                (exec_let_some_toAst?_core_of_evalValues_eq
                  (mode := runtime.checkedMode) (runtime := runtime)
                  (fuel := fuel) (state := state) (vars := vars)
                  (value := value) (valueAst := valueAst)
                  (codeOverride := some coreContract) hValueAst
                  (hEvalValues value valueAst state hValueAst)).2
  | assign vars value =>
      cases hValueAst :
          Expr.toAst? (runtime.checkedMode) value with
      | none =>
          simp [Stmt.toAst?, hValueAst] at hStmtAst
      | some valueAst =>
          simp [Stmt.toAst?, hValueAst] at hStmtAst
          cases hStmtAst
          exact
            (exec_assign_toAst?_core_of_evalValues_eq
              (mode := runtime.checkedMode) (runtime := runtime)
              (fuel := fuel) (state := state) (vars := vars)
              (value := value) (valueAst := valueAst)
              (codeOverride := some coreContract) hValueAst
              (hEvalValues value valueAst state hValueAst)).2
  | exprStmtCall expr =>
      cases expr with
      | call functionName args =>
          cases hArgsAst :
              Expr.List.toAst? (runtime.checkedMode) args with
          | none =>
              simp [Stmt.toAst?, Expr.toAst?, hArgsAst] at hStmtAst
          | some argsAst =>
              simp [Stmt.toAst?, Expr.toAst?, hArgsAst] at hStmtAst
              cases hStmtAst
              have hArgsRevAst :
                  Expr.List.toAst? (runtime.checkedMode) args.reverse =
                    some argsAst.reverse :=
                exprList_toAst?_reverse hArgsAst
              have hEvalArgsRev :
                  Source.evalArgs fuel runtime args.reverse state =
                    EvmYul.Yul.evalArgs fuel argsAst.reverse
                      (some coreContract) state :=
                hArgs args.reverse argsAst.reverse state hArgsRevAst
              have hArgsEq :
                  Source.reverseResult
                      (Source.evalArgs fuel runtime args.reverse state) =
                    EvmYul.Yul.reverse'
                      (EvmYul.Yul.evalArgs fuel argsAst.reverse
                        (some coreContract) state) := by
                rw [hEvalArgsRev]
                exact reverseResult_eq_reverse' _
              cases functionName with
              | inl prim =>
                  exact
                    (exec_exprStmt_primCall_toAst?_core_of_args_eq
                      (mode := runtime.checkedMode) (runtime := runtime)
                      (fuel := fuel) (state := state) (prim := prim)
                      (args := args) (argsAst := argsAst)
                      (codeOverride := some coreContract) hArgsAst hArgsEq).2
              | inr functionName =>
                  exact
                    (exec_exprStmt_userCall_toAst?_core_of_args_eq
                      (mode := runtime.checkedMode) (runtime := runtime)
                      (fuel := fuel) (state := state)
                      (functionName := functionName) (args := args)
                      (argsAst := argsAst) (codeOverride := some coreContract)
                      hArgsAst hArgsEq
                      (fun callFuel stateAfterArgs values =>
                        hCall callFuel functionName stateAfterArgs values)).2
      | var name =>
          simp [Stmt.toAst?, Expr.toAst?] at hStmtAst
          cases hStmtAst
          simp [Source.exec, EvmYul.Yul.exec]
      | lit value =>
          simp [Stmt.toAst?, Expr.toAst?] at hStmtAst
          cases hStmtAst
          simp [Source.exec, EvmYul.Yul.exec]
      | datasize name =>
          cases hLookup :
              Objects.ObjectLayout.size? runtime.layout name with
          | none =>
              simp [Stmt.toAst?, Expr.toAst?, LayoutMode.size?,
                Source.Runtime.checkedMode, hLookup]
                at hStmtAst
          | some value =>
              simp [Stmt.toAst?, Expr.toAst?, LayoutMode.size?,
                Source.Runtime.checkedMode, hLookup]
                at hStmtAst
              cases hStmtAst
              simp [Source.exec, EvmYul.Yul.exec]
      | dataoffset name =>
          cases hLookup :
              Objects.ObjectLayout.offset? runtime.layout name with
          | none =>
              simp [Stmt.toAst?, Expr.toAst?, LayoutMode.offset?,
                Source.Runtime.checkedMode, hLookup]
                at hStmtAst
          | some value =>
              simp [Stmt.toAst?, Expr.toAst?, LayoutMode.offset?,
                Source.Runtime.checkedMode, hLookup]
                at hStmtAst
              cases hStmtAst
              simp [Source.exec, EvmYul.Yul.exec]
      | datacopy dst offset size =>
          cases hDst : Expr.toAst? (runtime.checkedMode) dst with
          | none =>
              simp [Stmt.toAst?, Expr.toAst?, hDst] at hStmtAst
          | some dstAst =>
              cases hOffset :
                  Expr.toAst? (runtime.checkedMode) offset with
              | none =>
                  simp [Stmt.toAst?, Expr.toAst?, hDst, hOffset] at hStmtAst
              | some offsetAst =>
                  cases hSize :
                      Expr.toAst? (runtime.checkedMode) size with
                  | none =>
                      simp [Stmt.toAst?, Expr.toAst?, hDst, hOffset, hSize]
                        at hStmtAst
                  | some sizeAst =>
                      simp [Stmt.toAst?, Expr.toAst?, hDst, hOffset, hSize]
                        at hStmtAst
                      cases hStmtAst
                      have hTripleAst :
                          Expr.List.toAst? (runtime.checkedMode)
                              [dst, offset, size].reverse =
                            some [dstAst, offsetAst, sizeAst].reverse := by
                        simp [Expr.List.toAst?, hDst, hOffset, hSize]
                      have hEvalArgsTriple :
                          Source.evalArgs fuel runtime
                              [dst, offset, size].reverse state =
                            EvmYul.Yul.evalArgs fuel
                              [dstAst, offsetAst, sizeAst].reverse
                              (some coreContract) state :=
                        hArgs [dst, offset, size].reverse
                          [dstAst, offsetAst, sizeAst].reverse state
                          hTripleAst
                      have hArgsEq :
                          Source.reverseResult
                              (Source.evalArgs fuel runtime
                                [dst, offset, size].reverse state) =
                            EvmYul.Yul.reverse'
                              (EvmYul.Yul.evalArgs fuel
                                [dstAst, offsetAst, sizeAst].reverse
                                (some coreContract) state) := by
                        rw [hEvalArgsTriple]
                        exact reverseResult_eq_reverse' _
                      exact
                        (exec_exprStmt_datacopy_toAst?_core_of_args_eq
                          (mode := runtime.checkedMode)
                          (runtime := runtime) (fuel := fuel)
                          (state := state) (dst := dst) (offset := offset)
                          (size := size) (dstAst := dstAst)
                          (offsetAst := offsetAst) (sizeAst := sizeAst)
                          (codeOverride := some coreContract)
                        hDst hOffset hSize hArgsEq).2
      | linkersymbol name =>
          cases hLookup : findNamed? runtime.linkerSymbols name with
          | none =>
              simp [Stmt.toAst?, Expr.toAst?, LayoutMode.linkerSymbol?,
                Source.Runtime.checkedMode, hLookup]
                at hStmtAst
          | some value =>
              simp [Stmt.toAst?, Expr.toAst?, LayoutMode.linkerSymbol?,
                Source.Runtime.checkedMode, hLookup]
                at hStmtAst
              cases hStmtAst
              simp [Source.exec, EvmYul.Yul.exec]
      | loadimmutable name =>
          cases hLookup : findNamed? runtime.immutableValues name with
          | none =>
              simp [Stmt.toAst?, Expr.toAst?, LayoutMode.immutableValue?,
                Source.Runtime.checkedMode, hLookup]
                at hStmtAst
          | some value =>
              simp [Stmt.toAst?, Expr.toAst?, LayoutMode.immutableValue?,
                Source.Runtime.checkedMode, hLookup]
                at hStmtAst
              cases hStmtAst
              simp [Source.exec, EvmYul.Yul.exec]
      | memoryguard size =>
          simp [Stmt.toAst?, Expr.toAst?] at hStmtAst
          cases hStmtAst
          simp [Source.exec, EvmYul.Yul.exec]
  | switch scrutinee cases defaultBody =>
      cases hScrutineeAst :
          Expr.toAst? (runtime.checkedMode) scrutinee with
      | none =>
          simp [Stmt.toAst?, hScrutineeAst] at hStmtAst
      | some scrutineeAst =>
          cases hCasesAst :
              Stmt.Cases.toAst? (runtime.checkedMode) cases with
          | none =>
              simp [Stmt.toAst?, hScrutineeAst, hCasesAst] at hStmtAst
          | some casesAst =>
              cases hDefaultAst :
                  Stmt.List.toAst? (runtime.checkedMode) defaultBody with
              | none =>
                  simp [Stmt.toAst?, hScrutineeAst, hCasesAst, hDefaultAst]
                    at hStmtAst
              | some defaultBodyAst =>
                  simp [Stmt.toAst?, hScrutineeAst, hCasesAst, hDefaultAst]
                    at hStmtAst
                  cases hStmtAst
                  have hEval :
                      Source.eval fuel runtime scrutinee state =
                        EvmYul.Yul.eval fuel scrutineeAst
                          (some coreContract) state :=
                    eval_to_core_of_evalValues_eq
                      (hEvalValues scrutinee scrutineeAst state hScrutineeAst)
                  exact
                    (exec_switch_toAst?_core_of_eval_selected
                      (mode := runtime.checkedMode) (runtime := runtime)
                      (fuel := fuel) (state := state)
                      (scrutinee := scrutinee)
                      (scrutineeAst := scrutineeAst) (cases := cases)
                      (casesAst := casesAst) (defaultBody := defaultBody)
                      (defaultBodyAst := defaultBodyAst)
                      (codeOverride := some coreContract) hScrutineeAst
                      hCasesAst hDefaultAst hEval
                      (fun stateAfterCond selectedBody selectedBodyAst hAst =>
                        hExecBlock selectedBody selectedBodyAst
                          stateAfterCond hAst)).2
  | for_ cond post body =>
      cases hCondAst :
          Expr.toAst? (runtime.checkedMode) cond with
      | none =>
          simp [Stmt.toAst?, hCondAst] at hStmtAst
      | some condAst =>
          cases hPostAst :
              Stmt.List.toAst? (runtime.checkedMode) post with
          | none =>
              simp [Stmt.toAst?, hCondAst, hPostAst] at hStmtAst
          | some postAst =>
              cases hBodyAst :
                  Stmt.List.toAst? (runtime.checkedMode) body with
              | none =>
                  simp [Stmt.toAst?, hCondAst, hPostAst, hBodyAst] at hStmtAst
              | some bodyAst =>
                  simp [Stmt.toAst?, hCondAst, hPostAst, hBodyAst] at hStmtAst
                  cases hStmtAst
                  exact
                    (exec_for_toAst?_core_of_loop
                      (mode := runtime.checkedMode) (runtime := runtime)
                      (fuel := fuel) (state := state) (cond := cond)
                      (condAst := condAst) (post := post) (body := body)
                      (postAst := postAst) (bodyAst := bodyAst)
                      (codeOverride := some coreContract) hCondAst hPostAst
                      hBodyAst
                      (hLoop cond condAst post body postAst bodyAst state
                        hCondAst hPostAst hBodyAst)).2
  | if_ cond body =>
      cases hCondAst :
          Expr.toAst? (runtime.checkedMode) cond with
      | none =>
          simp [Stmt.toAst?, hCondAst] at hStmtAst
      | some condAst =>
          cases hBodyAst :
              Stmt.List.toAst? (runtime.checkedMode) body with
          | none =>
              simp [Stmt.toAst?, hCondAst, hBodyAst] at hStmtAst
          | some bodyAst =>
              simp [Stmt.toAst?, hCondAst, hBodyAst] at hStmtAst
              cases hStmtAst
              have hEval :
                  Source.eval fuel runtime cond state =
                    EvmYul.Yul.eval fuel condAst (some coreContract) state :=
                eval_to_core_of_evalValues_eq
                  (hEvalValues cond condAst state hCondAst)
              exact
                (exec_if_toAst?_core_of_eval_body
                  (mode := runtime.checkedMode) (runtime := runtime)
                  (fuel := fuel) (state := state) (cond := cond)
                  (condAst := condAst) (body := body) (bodyAst := bodyAst)
                  (codeOverride := some coreContract) hCondAst hBodyAst hEval
                  (fun stateAfterCond =>
                    hExecBlock body bodyAst stateAfterCond hBodyAst)).2
  | setimmutable offset name value =>
      cases hOffsetAst :
          Expr.toAst? (runtime.checkedMode) offset with
      | none =>
          simp [Stmt.toAst?, hOffsetAst] at hStmtAst
      | some offsetAst =>
          cases hValueAst :
              Expr.toAst? (runtime.checkedMode) value with
          | none =>
              simp [Stmt.toAst?, hOffsetAst, hValueAst] at hStmtAst
          | some valueAst =>
              cases hRefs :
                  LayoutMode.immutableReferences? runtime.checkedMode name with
              | none =>
                  simp [Stmt.toAst?, hOffsetAst, hValueAst, hRefs] at hStmtAst
              | some references =>
                  cases hPatchAst :
                      ImmutableReference.List.patchAstStmts? references
                        offsetAst valueAst with
                  | none =>
                      simp [Stmt.toAst?, hOffsetAst, hValueAst, hRefs,
                        hPatchAst] at hStmtAst
                  | some patchAsts =>
                      simp [Stmt.toAst?, hOffsetAst, hValueAst, hRefs,
                        hPatchAst] at hStmtAst
                      cases hStmtAst
                      have hSourceRefs :
                          Source.immutableReferences? runtime name =
                            some references := by
                        simpa [Source.immutableReferences?,
                          LayoutMode.immutableReferences?,
                          Source.Runtime.checkedMode] using hRefs
                      rcases
                          exists_source_patchStmts_of_patchAstStmts?
                            (mode := runtime.checkedMode) hOffsetAst hValueAst
                            hPatchAst with
                        ⟨patchStmts, hPatchSource, hPatchToAst⟩
                      have hBlock :
                          Source.exec (fuel + 1) runtime
                              (.block patchStmts) state =
                            EvmYul.Yul.exec (fuel + 1) (.Block patchAsts)
                              (some coreContract) state :=
                        (exec_block_toAst?_core_of_execSeq
                          (mode := runtime.checkedMode) (runtime := runtime)
                          (fuel := fuel) (state := state) (body := patchStmts)
                          (bodyAst := patchAsts)
                          (codeOverride := some coreContract) hPatchToAst
                          (hExecSeq patchStmts patchAsts state
                            hPatchToAst)).2
                      simpa [Source.exec, hSourceRefs, hPatchSource] using
                        hBlock
  | «continue» =>
      simp [Stmt.toAst?] at hStmtAst
      cases hStmtAst
      exact
        (exec_continue_toAst?_core
          (mode := runtime.checkedMode) (runtime := runtime)
          (fuel := fuel) (state := state)
          (codeOverride := some coreContract)).2
  | «break» =>
      simp [Stmt.toAst?] at hStmtAst
      cases hStmtAst
      exact
        (exec_break_toAst?_core
          (mode := runtime.checkedMode) (runtime := runtime)
          (fuel := fuel) (state := state)
          (codeOverride := some coreContract)).2
  | «leave» =>
      simp [Stmt.toAst?] at hStmtAst
      cases hStmtAst
      exact
        (exec_leave_toAst?_core
          (mode := runtime.checkedMode) (runtime := runtime)
          (fuel := fuel) (state := state)
          (codeOverride := some coreContract)).2

theorem exec_exprStmt_datacopy_toAst?_core_of_args {mode : LayoutMode}
    {runtime : Source.Runtime} {fuel : Nat} {state stateAfterArgs : Source.State}
    {dst offset size : Expr} {dstAst offsetAst sizeAst : AstExpr}
    {args : List Word} {codeOverride : CodeOverride}
    (hDst : Expr.toAst? mode dst = some dstAst)
    (hOffset : Expr.toAst? mode offset = some offsetAst)
    (hSize : Expr.toAst? mode size = some sizeAst)
    (hSourceArgs :
      Source.reverseResult
        (Source.evalArgs (fuel + 1) runtime
          [dst, offset, size].reverse state) =
          .ok (stateAfterArgs, args))
    (hCoreArgs :
      EvmYul.Yul.reverse'
        (EvmYul.Yul.evalArgs (fuel + 1)
          [dstAst, offsetAst, sizeAst].reverse codeOverride state) =
          .ok (stateAfterArgs, args)) :
    ∃ ast : AstStmt,
      Stmt.toAst? mode (.exprStmtCall (.datacopy dst offset size)) =
          some ast ∧
        Source.exec (fuel + 2) runtime
            (.exprStmtCall (.datacopy dst offset size)) state =
          EvmYul.Yul.exec (fuel + 2) ast codeOverride state := by
  refine
    ⟨.ExprStmtCall (.Call (.inl codecopyPrim)
        [dstAst, offsetAst, sizeAst]),
      ?_,
      ?_⟩
  · simp [Stmt.toAst?, Expr.toAst?, hDst, hOffset, hSize, codecopyPrim]
  · have hSourceArgs' :
        Source.reverseResult
          (Source.evalArgs (fuel + 1) runtime
            [size, offset, dst] state) =
            .ok (stateAfterArgs, args) := by
      simpa using hSourceArgs
    have hCoreArgs' :
        EvmYul.Yul.reverse'
          (EvmYul.Yul.evalArgs (fuel + 1)
            [sizeAst, offsetAst, dstAst] codeOverride state) =
            .ok (stateAfterArgs, args) := by
      simpa using hCoreArgs
    simp [Source.exec, Source.execPrimCall, EvmYul.Yul.exec,
      EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill',
      Source.multifillResult, codecopyPrim,
      hSourceArgs', hCoreArgs']
    cases
      EvmYul.Yul.primCall (fuel + 1) stateAfterArgs codecopyPrim args
      <;> rfl

structure CheckedPreservationAt (runtime : Source.Runtime)
    (coreContract : AstContract) (fuel : Nat) : Prop where
  evalValues :
    ∀ (expr : Expr) (exprAst : AstExpr) (state : Source.State),
      Expr.toAst? (runtime.checkedMode) expr = some exprAst →
        Source.evalValues fuel runtime expr state =
          EvmYul.Yul.evalValues fuel exprAst (some coreContract) state
  evalArgs :
    ∀ (args : List Expr) (argsAst : List AstExpr)
      (state : Source.State),
      Expr.List.toAst? (runtime.checkedMode) args = some argsAst →
        Source.evalArgs fuel runtime args state =
          EvmYul.Yul.evalArgs fuel argsAst (some coreContract) state
  evalTail :
    ∀ (args : List Expr) (argsAst : List AstExpr)
      (input : Except Source.Exception (Source.State × Word)),
      Expr.List.toAst? (runtime.checkedMode) args = some argsAst →
        Source.evalTail fuel runtime args input =
          EvmYul.Yul.evalTail fuel argsAst (some coreContract) input
  call :
    ∀ (functionName : AstFunctionName) (values : List Word)
      (state : Source.State),
      Source.call fuel runtime values (some functionName) state =
        EvmYul.Yul.call fuel values (some functionName)
          (some coreContract) state
  exec :
    ∀ (stmt : Stmt) (stmtAst : AstStmt) (state : Source.State),
      Stmt.toAst? (runtime.checkedMode) stmt = some stmtAst →
        Source.exec fuel runtime stmt state =
          EvmYul.Yul.exec fuel stmtAst (some coreContract) state
  execSeq :
    ∀ (stmts : List Stmt) (stmtsAst : List AstStmt)
      (state : Source.State),
      Stmt.List.toAst? (runtime.checkedMode) stmts = some stmtsAst →
        Source.execSeq fuel runtime stmts state =
          EvmYul.Yul.execSeq fuel stmtsAst (some coreContract) state
  loop :
    ∀ (cond : Expr) (condAst : AstExpr)
      (post body : List Stmt) (postAst bodyAst : List AstStmt)
      (state : Source.State),
      Expr.toAst? (runtime.checkedMode) cond = some condAst →
        Stmt.List.toAst? (runtime.checkedMode) post = some postAst →
          Stmt.List.toAst? (runtime.checkedMode) body = some bodyAst →
            Source.loop fuel runtime cond post body state =
              EvmYul.Yul.loop fuel condAst postAst bodyAst
                (some coreContract) state
  callDispatcher :
    ∀ state : Source.State,
      state.executionEnv.code = coreContract →
        Source.callDispatcher fuel runtime state =
          EvmYul.Yul.callDispatcher fuel (some coreContract) state

theorem checkedPreservationAt_zero {runtime : Source.Runtime}
    {coreContract : AstContract} :
    CheckedPreservationAt runtime coreContract 0 := by
  refine
    { evalValues := ?_,
      evalArgs := ?_,
      evalTail := ?_,
      call := ?_,
      exec := ?_,
      execSeq := ?_,
      loop := ?_,
      callDispatcher := ?_ }
  · intro expr exprAst state hExprAst
    simp [Source.evalValues, EvmYul.Yul.evalValues]
  · intro args argsAst state hArgsAst
    exact
      evalArgs_zero_to_core
        (runtime := runtime) (args := args) (argsAst := argsAst)
        (state := state) (codeOverride := some coreContract)
  · intro args argsAst input hArgsAst
    exact
      evalTail_zero_to_core
        (runtime := runtime) (args := args) (argsAst := argsAst)
        (input := input) (codeOverride := some coreContract)
  · intro functionName values state
    exact
      call_zero_to_core
        (runtime := runtime) (args := values)
        (functionName? := some functionName) (state := state)
        (codeOverride := some coreContract)
  · intro stmt stmtAst state hStmtAst
    simp [Source.exec, EvmYul.Yul.exec]
  · intro stmts stmtsAst state hStmtsAst
    exact
      execSeq_zero_to_core
        (runtime := runtime) (stmts := stmts) (stmtsAst := stmtsAst)
        (state := state) (codeOverride := some coreContract)
  · intro cond condAst post body postAst bodyAst state
      hCondAst hPostAst hBodyAst
    exact
      loop_zero_to_core
        (runtime := runtime) (cond := cond) (condAst := condAst)
        (post := post) (body := body) (postAst := postAst)
        (bodyAst := bodyAst) (state := state)
        (codeOverride := some coreContract)
  · intro state hStateCode
    exact
      callDispatcher_zero_to_core
        (runtime := runtime) (state := state)
        (codeOverride := some coreContract)

theorem checkedPreservationAt_of_contractAst {runtime : Source.Runtime}
    {coreContract : AstContract}
    (hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some coreContract) :
    ∀ fuel : Nat, CheckedPreservationAt runtime coreContract fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      cases fuel with
      | zero =>
          exact checkedPreservationAt_zero
      | succ fuelPred =>
          have hPrev :
              CheckedPreservationAt runtime coreContract fuelPred :=
            ih fuelPred (Nat.lt_succ_self fuelPred)
          refine
            { evalValues := ?_,
              evalArgs := ?_,
              evalTail := ?_,
              call := ?_,
              exec := ?_,
              execSeq := ?_,
              loop := ?_,
              callDispatcher := ?_ }
          · intro expr exprAst state hExprAst
            exact
              evalValues_succ_toAst?_checked_core_of_args_and_calls
                (runtime := runtime) (fuel := fuelPred) (state := state)
                (expr := expr) (ast := exprAst)
                (coreContract := coreContract) hContract hExprAst
                hPrev.evalArgs
                (fun functionName stateAfterArgs values =>
                  hPrev.call functionName values stateAfterArgs)
          · intro args argsAst state hArgsAst
            exact
              evalArgs_succ_toAst?_checked_core_of_evalValues_and_tail
                (runtime := runtime) (fuel := fuelPred) (state := state)
                (args := args) (argsAst := argsAst)
                (coreContract := coreContract) hArgsAst
                hPrev.evalValues hPrev.evalTail
          · intro args argsAst input hArgsAst
            exact
              evalTail_succ_toAst?_checked_core_of_evalArgs
                (runtime := runtime) (fuel := fuelPred) (args := args)
                (argsAst := argsAst) (input := input)
                (coreContract := coreContract)
                (fun state => hPrev.evalArgs args argsAst state hArgsAst)
          · intro functionName values state
            exact
              call_user_succ_toAst?_checked_core_of_contract_and_blocks
                (runtime := runtime) (fuel := fuelPred)
                (args := values) (functionName := functionName)
                (state := state) (coreContract := coreContract)
                hContract
                (fun body bodyAst state hBodyAst =>
                  hPrev.exec (.block body) (.Block bodyAst) state
                    (by simp [Stmt.toAst?, hBodyAst]))
          · intro stmt stmtAst state hStmtAst
            exact
              exec_succ_toAst?_checked_core_of_parts
                (runtime := runtime) (fuel := fuelPred) (state := state)
                (stmt := stmt) (stmtAst := stmtAst)
                (coreContract := coreContract) hStmtAst
                hPrev.evalValues hPrev.evalArgs
                (fun callFuel functionName stateAfterArgs values hLt =>
                  (ih callFuel
                    (Nat.lt_trans hLt
                      (Nat.lt_succ_self fuelPred))).call
                    functionName values stateAfterArgs)
                hPrev.execSeq
                (fun body bodyAst state hBodyAst =>
                  hPrev.exec (.block body) (.Block bodyAst) state
                    (by simp [Stmt.toAst?, hBodyAst]))
                hPrev.loop
          · intro stmts stmtsAst state hStmtsAst
            exact
              execSeq_succ_toAst?_checked_core_of_exec_tail
                (runtime := runtime) (fuel := fuelPred) (state := state)
                (stmts := stmts) (stmtsAst := stmtsAst)
                (coreContract := coreContract) hStmtsAst
                hPrev.exec hPrev.execSeq
          · intro cond condAst post body postAst bodyAst state
              hCondAst hPostAst hBodyAst
            cases fuelPred with
            | zero =>
                exact
                  loop_one_to_core
                    (runtime := runtime) (cond := cond)
                    (condAst := condAst) (post := post) (body := body)
                    (postAst := postAst) (bodyAst := bodyAst)
                    (state := state) (codeOverride := some coreContract)
            | succ fuelPrev =>
                have hLoopPrev :
                    CheckedPreservationAt runtime coreContract fuelPrev :=
                  ih fuelPrev
                    (Nat.lt_trans (Nat.lt_succ_self fuelPrev)
                      (Nat.lt_succ_self (fuelPrev + 1)))
                exact
                  loop_succ_succ_toAst?_checked_core_of_parts
                    (runtime := runtime) (fuel := fuelPrev)
                    (cond := cond) (condAst := condAst)
                    (post := post) (body := body)
                    (postAst := postAst) (bodyAst := bodyAst)
                    (state := state) (coreContract := coreContract)
                    hCondAst hPostAst hBodyAst
                    hLoopPrev.evalValues hLoopPrev.exec
          · intro state hStateCode
            exact
              callDispatcher_succ_toAst?_checked_core_of_contract_and_blocks
                (runtime := runtime) (fuel := fuelPred)
                (state := state) (coreContract := coreContract)
                hContract hStateCode
                (fun body bodyAst state hBodyAst =>
                  hPrev.exec (.block body) (.Block bodyAst) state
                    (by simp [Stmt.toAst?, hBodyAst]))

theorem runtime_contract_toAst?_of_checked {program : Program}
    {runtime : Source.Runtime}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime) :
    Contract.toAst? (runtime.checkedMode) runtime.contract =
      some runtime.installedContract := by
  rcases Source.Runtime.ofCheckedProgram?_checked hRuntime with
    ⟨_lower, _hLower, _hLayout, _hImage, hInstalled, hRuntimeContract,
      hLinker, hImmutableValues, hImmutableReferences⟩
  have hMode :
      Program.checkedMode program runtime.layout = runtime.checkedMode := by
    simp [Program.checkedMode, Source.Runtime.checkedMode, hLinker,
      hImmutableValues, hImmutableReferences]
  rw [hRuntimeContract]
  simpa [hMode] using hInstalled

theorem toRootCoreProgram?_of_runtime_checked {program : Program}
    {runtime : Source.Runtime}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime) :
    Program.toRootCoreProgram? program =
      some { contract := runtime.installedContract } := by
  rcases Source.Runtime.ofCheckedProgram?_checked hRuntime with
    ⟨lower, hLower, hRuntimeLayout, _hImage, hInstalled,
      hRuntimeContract, hLinker, hImmutableValues, hImmutableReferences⟩
  rcases Program.toObjects?_checked hLower with
    ⟨prelim, hPrelim, hFinal, hStable⟩
  unfold Program.toRootCoreProgram?
  rw [hPrelim]
  cases hPrelimLayout : Objects.Object.payloadLayout? prelim with
  | none =>
      have hNoFinal :
          Object.toObjectsWithPrelayoutWith? program.checkedMode
              program.root prelim = none := by
        cases program.root
        cases prelim
        simp [Object.toObjectsWithPrelayoutWith?, hPrelimLayout]
      rw [hNoFinal] at hFinal
      contradiction
  | some prelimLayout =>
      have hFinalLayout :
          Objects.Object.payloadLayout? lower.root = some runtime.layout := by
        simpa [Objects.Program.payloadLayout?] using hRuntimeLayout
      have hLayoutEq : prelimLayout = runtime.layout :=
        Object.layoutStable?_payloadLayout_eq
          hStable hPrelimLayout hFinalLayout
      subst prelimLayout
      simp [hPrelimLayout, Contract.toCoreProgram?, hInstalled, hFinal,
        hStable]

theorem runContract_to_runWithCodeImage_of_checked_ok
    {program : Program} {runtime : Source.Runtime} {core : Yul.Program}
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core) :
    Source.runContract runtime fuel (.Ok shared store) =
      Yul.Program.runWithCodeImage fuel core runtime.codeImage
        (.Ok shared store) := by
  have hCoreContract :
      core.contract = runtime.installedContract :=
    toRootCoreProgram?_installedContract
      (program := program) (runtime := runtime) (core := core)
      hRuntime hCore
  have hRuntimeContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some runtime.installedContract :=
    runtime_contract_toAst?_of_checked
      (program := program) (runtime := runtime) hRuntime
  have hContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some core.contract := by
    rw [hCoreContract]
    exact hRuntimeContract
  have hAt :
      CheckedPreservationAt runtime core.contract fuel :=
    checkedPreservationAt_of_contractAst hContract fuel
  exact
    runContract_to_runWithCodeImage_of_checked_dispatcher
      (program := program) (runtime := runtime) (core := core)
      (fuel := fuel) (state := .Ok shared store) hRuntime hCore
      (hAt.callDispatcher
        (Source.installCodeImage runtime (.Ok shared store))
      (by
          simp [Source.installCodeImage, EvmYul.Yul.State.executionEnv,
            hCoreContract]))

theorem runContract_to_runWithCodeImage_of_checked_ok_withCodeImage
    {program : Program} {runtime : Source.Runtime} {core : Yul.Program}
    {fuel : Nat} {codeImage : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core) :
    Source.runContract (Source.Runtime.withCodeImage runtime codeImage) fuel
        (.Ok shared store) =
      Yul.Program.runWithCodeImage fuel core codeImage (.Ok shared store) := by
  let runtimeWithImage : Source.Runtime :=
    Source.Runtime.withCodeImage runtime codeImage
  have hCoreContract :
      core.contract = runtime.installedContract :=
    toRootCoreProgram?_installedContract
      (program := program) (runtime := runtime) (core := core)
      hRuntime hCore
  have hCoreContractWithImage :
      core.contract = runtimeWithImage.installedContract := by
    simpa [runtimeWithImage, Source.Runtime.withCodeImage] using
      hCoreContract
  have hRuntimeContract :
      Contract.toAst? (runtime.checkedMode) runtime.contract =
        some runtime.installedContract :=
    runtime_contract_toAst?_of_checked
      (program := program) (runtime := runtime) hRuntime
  have hContract :
      Contract.toAst? runtimeWithImage.checkedMode runtimeWithImage.contract =
        some core.contract := by
    rw [hCoreContract]
    simpa [runtimeWithImage, Source.Runtime.withCodeImage] using
      hRuntimeContract
  have hAt :
      CheckedPreservationAt runtimeWithImage core.contract fuel :=
    checkedPreservationAt_of_contractAst hContract fuel
  have hRun :=
    runContract_to_runWithCodeImage_of_dispatcher
      (runtime := runtimeWithImage) (core := core)
      (fuel := fuel) (state := .Ok shared store)
      (installCodeImage_eq_installContractWithCodeImage
        (runtime := runtimeWithImage) (core := core)
        hCoreContractWithImage (.Ok shared store))
      (hAt.callDispatcher
        (Source.installCodeImage runtimeWithImage (.Ok shared store))
        (by
          simp [runtimeWithImage, Source.Runtime.withCodeImage,
            Source.installCodeImage, EvmYul.Yul.State.executionEnv,
            hCoreContract]))
  simpa [runtimeWithImage, Source.Runtime.withCodeImage] using hRun

theorem sourceRun?_to_runWithCodeImage_of_checked_ok
    {program : Program} {runtime : Source.Runtime} {core : Yul.Program}
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core) :
    Source.Program.sourceRun? fuel program (.Ok shared store) =
      some
        (Yul.Program.runWithCodeImage fuel core runtime.codeImage
          (.Ok shared store)) := by
  unfold Source.Program.sourceRun?
  rw [hRuntime]
  simp [runContract_to_runWithCodeImage_of_checked_ok
    (program := program) (runtime := runtime) (core := core)
    (fuel := fuel) (shared := shared) (store := store) hRuntime hCore]

theorem sourceRunWithCodeImage?_to_runWithCodeImage_of_checked_ok
    {program : Program} {runtime : Source.Runtime} {core : Yul.Program}
    {fuel : Nat} {codeImage : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core) :
    Source.Program.sourceRunWithCodeImage? fuel program codeImage
        (.Ok shared store) =
      some
        (Yul.Program.runWithCodeImage fuel core codeImage
          (.Ok shared store)) := by
  unfold Source.Program.sourceRunWithCodeImage?
  rw [hRuntime]
  simp [runContract_to_runWithCodeImage_of_checked_ok_withCodeImage
    (program := program) (runtime := runtime) (core := core)
    (fuel := fuel) (codeImage := codeImage)
    (shared := shared) (store := store) hRuntime hCore]

theorem sourceRun?_eq_sourceRunChecked?_of_checked_ok
    {program : Program} {runtime : Source.Runtime} {core : Yul.Program}
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    (hRuntime : Source.Runtime.ofCheckedProgram? program = some runtime)
    (hCore : Program.toRootCoreProgram? program = some core) :
    Source.Program.sourceRun? fuel program (.Ok shared store) =
      Program.sourceRunChecked? fuel program (.Ok shared store) := by
  have hImage : Program.bytecodeImage? program = some runtime.codeImage := by
    rcases Source.Runtime.ofCheckedProgram?_checked hRuntime with
      ⟨lower, hLower, _hLayout, hImage, _hContract, _hRuntimeContract⟩
    simp [Program.bytecodeImage?, hLower, hImage]
  rw [sourceRun?_to_runWithCodeImage_of_checked_ok
    (program := program) (runtime := runtime) (core := core)
    (fuel := fuel) (shared := shared) (store := store) hRuntime hCore]
  simp [Program.sourceRunChecked?, hCore, hImage]

theorem sourceRun?_success_to_sourceRunChecked?_ok
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hRun :
      Source.Program.sourceRun? fuel program (.Ok shared store) =
        some result) :
    Program.sourceRunChecked? fuel program (.Ok shared store) =
      some result := by
  rcases Source.Program.sourceRun?_checked hRun with
    ⟨runtime, hRuntime, hRunContract⟩
  let core : Yul.Program := { contract := runtime.installedContract }
  have hCore :
      Program.toRootCoreProgram? program = some core := by
    simpa [core] using
      toRootCoreProgram?_of_runtime_checked
        (program := program) (runtime := runtime) hRuntime
  have hImage : Program.bytecodeImage? program = some runtime.codeImage := by
    rcases Source.Runtime.ofCheckedProgram?_checked hRuntime with
      ⟨lower, hLower, _hLayout, hImage, _hContract, _hRuntimeContract⟩
    simp [Program.bytecodeImage?, hLower, hImage]
  unfold Program.sourceRunChecked?
  rw [hCore, hImage]
  exact
    congrArg some
      ((runContract_to_runWithCodeImage_of_checked_ok
        (program := program) (runtime := runtime) (core := core)
        (fuel := fuel) (shared := shared) (store := store)
        hRuntime hCore).symm.trans hRunContract)

theorem sourceRun?_success_exists_runWithCodeImage_ok
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hRun :
      Source.Program.sourceRun? fuel program (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program, ∃ image : ByteArray,
      Program.toRootCoreProgram? program = some core ∧
        Program.bytecodeImage? program = some image ∧
          Yul.Program.runWithCodeImage fuel core image (.Ok shared store) =
            result := by
  rcases Source.Program.sourceRun?_checked hRun with
    ⟨runtime, hRuntime, hRunContract⟩
  let core : Yul.Program := { contract := runtime.installedContract }
  have hCore :
      Program.toRootCoreProgram? program = some core := by
    simpa [core] using
      toRootCoreProgram?_of_runtime_checked
        (program := program) (runtime := runtime) hRuntime
  have hImage : Program.bytecodeImage? program = some runtime.codeImage := by
    rcases Source.Runtime.ofCheckedProgram?_checked hRuntime with
      ⟨lower, hLower, _hLayout, hImage, _hContract, _hRuntimeContract⟩
    simp [Program.bytecodeImage?, hLower, hImage]
  refine ⟨core, runtime.codeImage, hCore, hImage, ?_⟩
  exact
    (runContract_to_runWithCodeImage_of_checked_ok
      (program := program) (runtime := runtime) (core := core)
      (fuel := fuel) (shared := shared) (store := store)
      hRuntime hCore).symm.trans hRunContract

theorem sourceRunWithCodeImage?_success_exists_runWithCodeImage_ok
    {program : Program} {fuel : Nat} {codeImage : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hRun :
      Source.Program.sourceRunWithCodeImage? fuel program codeImage
          (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program,
      Program.toRootCoreProgram? program = some core ∧
        Yul.Program.runWithCodeImage fuel core codeImage (.Ok shared store) =
          result := by
  rcases Source.Program.sourceRunWithCodeImage?_checked hRun with
    ⟨runtime, hRuntime, hRunContract⟩
  let core : Yul.Program := { contract := runtime.installedContract }
  have hCore :
      Program.toRootCoreProgram? program = some core := by
    simpa [core] using
      toRootCoreProgram?_of_runtime_checked
        (program := program) (runtime := runtime) hRuntime
  refine ⟨core, hCore, ?_⟩
  exact
    (runContract_to_runWithCodeImage_of_checked_ok_withCodeImage
      (program := program) (runtime := runtime) (core := core)
      (fuel := fuel) (codeImage := codeImage)
      (shared := shared) (store := store)
      hRuntime hCore).symm.trans hRunContract

theorem sourceRunWithCodeSuffix?_success_exists_runWithCodeImage_ok
    {program : Program} {fuel : Nat} {suffix : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hRun :
      Source.Program.sourceRunWithCodeSuffix? fuel program suffix
          (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program, ∃ image : ByteArray,
      Program.toRootCoreProgram? program = some core ∧
        Program.bytecodeImage? program = some image ∧
          Yul.Program.runWithCodeImage fuel core (image ++ suffix)
              (.Ok shared store) =
            result := by
  unfold Source.Program.sourceRunWithCodeSuffix? at hRun
  cases hImage : Program.bytecodeImage? program with
  | none =>
      simp [hImage] at hRun
  | some image =>
      have hRunImage :
          Source.Program.sourceRunWithCodeImage? fuel program (image ++ suffix)
              (.Ok shared store) =
            some result := by
        simpa [hImage] using hRun
      rcases
          sourceRunWithCodeImage?_success_exists_runWithCodeImage_ok
            hRunImage with
        ⟨core, hCore, hCoreRun⟩
      exact ⟨core, image, hCore, rfl, hCoreRun⟩

theorem runWithCodeImage_eq_run_of_initial_codeBytes_ok
    {core : Yul.Program} {image : ByteArray} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    (hCodeBytes : shared.executionEnv.codeBytes = image) :
    Yul.Program.runWithCodeImage fuel core image (.Ok shared store) =
      Yul.Program.run fuel core (.Ok shared store) := by
  subst image
  simp [Yul.Program.runWithCodeImage, Yul.Program.run,
    Yul.Program.installContractWithCodeImage, Yul.Program.installContract]

theorem sourceRun?_success_exists_coreRun_ok_of_initial_codeBytes
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hInitialCodeBytes :
      Program.bytecodeImage? program =
        some shared.executionEnv.codeBytes)
    (hRun :
      Source.Program.sourceRun? fuel program (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program,
      Program.toRootCoreProgram? program = some core ∧
        Yul.Program.run fuel core (.Ok shared store) = result := by
  rcases Source.Program.sourceRun?_checked hRun with
    ⟨runtime, hRuntime, hRunContract⟩
  let core : Yul.Program := { contract := runtime.installedContract }
  have hCore :
      Program.toRootCoreProgram? program = some core := by
    simpa [core] using
      toRootCoreProgram?_of_runtime_checked
        (program := program) (runtime := runtime) hRuntime
  have hImage : Program.bytecodeImage? program = some runtime.codeImage := by
    rcases Source.Runtime.ofCheckedProgram?_checked hRuntime with
      ⟨lower, hLower, _hLayout, hImage, _hContract, _hRuntimeContract⟩
    simp [Program.bytecodeImage?, hLower, hImage]
  have hRuntimeImage :
      shared.executionEnv.codeBytes = runtime.codeImage := by
    rw [hInitialCodeBytes] at hImage
    injection hImage with hEq
  refine ⟨core, hCore, ?_⟩
  rw [← runWithCodeImage_eq_run_of_initial_codeBytes_ok
    (core := core) (image := runtime.codeImage) (fuel := fuel)
    (shared := shared) (store := store) hRuntimeImage]
  exact
    (runContract_to_runWithCodeImage_of_checked_ok
      (program := program) (runtime := runtime) (core := core)
      (fuel := fuel) (shared := shared) (store := store)
      hRuntime hCore).symm.trans hRunContract

theorem sourceRunWithCodeImage?_success_exists_coreRun_ok_of_initial_codeBytes
    {program : Program} {fuel : Nat} {codeImage : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hInitialCodeBytes : shared.executionEnv.codeBytes = codeImage)
    (hRun :
      Source.Program.sourceRunWithCodeImage? fuel program codeImage
          (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program,
      Program.toRootCoreProgram? program = some core ∧
        Yul.Program.run fuel core (.Ok shared store) = result := by
  rcases
      sourceRunWithCodeImage?_success_exists_runWithCodeImage_ok hRun with
    ⟨core, hCore, hRunCoreImage⟩
  refine ⟨core, hCore, ?_⟩
  rw [← runWithCodeImage_eq_run_of_initial_codeBytes_ok
    (core := core) (image := codeImage) (fuel := fuel)
    (shared := shared) (store := store) hInitialCodeBytes]
  exact hRunCoreImage

theorem sourceRunWithCodeSuffix?_success_exists_coreRun_ok_of_initial_codeBytes
    {program : Program} {fuel : Nat} {suffix : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hInitialCodeBytes :
      ∃ image : ByteArray,
        Program.bytecodeImage? program = some image ∧
          shared.executionEnv.codeBytes = image ++ suffix)
    (hRun :
      Source.Program.sourceRunWithCodeSuffix? fuel program suffix
          (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program,
      Program.toRootCoreProgram? program = some core ∧
        Yul.Program.run fuel core (.Ok shared store) = result := by
  rcases hInitialCodeBytes with ⟨initialImage, hInitialImage, hCodeBytes⟩
  rcases
      sourceRunWithCodeSuffix?_success_exists_runWithCodeImage_ok hRun with
    ⟨core, runImage, hCore, hRunImage, hCoreRunImage⟩
  have hImageEq : runImage = initialImage := by
    rw [hInitialImage] at hRunImage
    injection hRunImage with hEq
    exact hEq.symm
  subst runImage
  refine ⟨core, hCore, ?_⟩
  rw [← runWithCodeImage_eq_run_of_initial_codeBytes_ok
    (core := core) (image := initialImage ++ suffix) (fuel := fuel)
    (shared := shared) (store := store) hCodeBytes]
  exact hCoreRunImage

end Preservation

namespace Program

theorem sourceRunChecked?_of_sourceRun?_ok
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hRun :
      Source.Program.sourceRun? fuel program (.Ok shared store) =
        some result) :
    sourceRunChecked? fuel program (.Ok shared store) = some result :=
  Preservation.sourceRun?_success_to_sourceRunChecked?_ok hRun

theorem exists_runWithCodeImage_of_sourceRun?_ok
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hRun :
      Source.Program.sourceRun? fuel program (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program, ∃ image : ByteArray,
      toRootCoreProgram? program = some core ∧
        bytecodeImage? program = some image ∧
          Yul.Program.runWithCodeImage fuel core image (.Ok shared store) =
            result :=
  Preservation.sourceRun?_success_exists_runWithCodeImage_ok hRun

theorem exists_runWithCodeImage_of_sourceRunWithCodeImage?_ok
    {program : Program} {fuel : Nat} {codeImage : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hRun :
      Source.Program.sourceRunWithCodeImage? fuel program codeImage
          (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program,
      toRootCoreProgram? program = some core ∧
        Yul.Program.runWithCodeImage fuel core codeImage (.Ok shared store) =
          result :=
  Preservation.sourceRunWithCodeImage?_success_exists_runWithCodeImage_ok hRun

theorem exists_runWithCodeImage_of_sourceRunWithCodeSuffix?_ok
    {program : Program} {fuel : Nat} {suffix : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hRun :
      Source.Program.sourceRunWithCodeSuffix? fuel program suffix
          (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program, ∃ image : ByteArray,
      toRootCoreProgram? program = some core ∧
        bytecodeImage? program = some image ∧
          Yul.Program.runWithCodeImage fuel core (image ++ suffix)
              (.Ok shared store) =
            result :=
  Preservation.sourceRunWithCodeSuffix?_success_exists_runWithCodeImage_ok
    hRun

theorem exists_coreRun_of_sourceRun?_ok_initial_codeBytes
    {program : Program} {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hInitialCodeBytes :
      bytecodeImage? program = some shared.executionEnv.codeBytes)
    (hRun :
      Source.Program.sourceRun? fuel program (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program,
      toRootCoreProgram? program = some core ∧
        Yul.Program.run fuel core (.Ok shared store) = result :=
  Preservation.sourceRun?_success_exists_coreRun_ok_of_initial_codeBytes
    hInitialCodeBytes hRun

theorem exists_coreRun_of_sourceRunWithCodeImage?_ok_initial_codeBytes
    {program : Program} {fuel : Nat} {codeImage : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hInitialCodeBytes : shared.executionEnv.codeBytes = codeImage)
    (hRun :
      Source.Program.sourceRunWithCodeImage? fuel program codeImage
          (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program,
      toRootCoreProgram? program = some core ∧
        Yul.Program.run fuel core (.Ok shared store) = result :=
  Preservation.sourceRunWithCodeImage?_success_exists_coreRun_ok_of_initial_codeBytes
    hInitialCodeBytes hRun

theorem exists_coreRun_of_sourceRunWithCodeSuffix?_ok_initial_codeBytes
    {program : Program} {fuel : Nat} {suffix : ByteArray}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {result : Except Source.Exception ReferenceResult}
    (hInitialCodeBytes :
      ∃ image : ByteArray,
        bytecodeImage? program = some image ∧
          shared.executionEnv.codeBytes = image ++ suffix)
    (hRun :
      Source.Program.sourceRunWithCodeSuffix? fuel program suffix
          (.Ok shared store) =
        some result) :
    ∃ core : Yul.Program,
      toRootCoreProgram? program = some core ∧
        Yul.Program.run fuel core (.Ok shared store) = result :=
  Preservation.sourceRunWithCodeSuffix?_success_exists_coreRun_ok_of_initial_codeBytes
    hInitialCodeBytes hRun

end Program

end ObjectModel
end Yul
end EvmCompiler
