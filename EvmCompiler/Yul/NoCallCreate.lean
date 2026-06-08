import EvmCompiler.Yul.Reference

namespace EvmCompiler
namespace Yul

namespace NoCallCreate

theorem expr_cast {m n : Nat} (h : m = n) (expr : Locals.Expr m)
    (hExpr : expr.usesCallCreate = false) :
    (Expr.cast h expr).usesCallCreate = false := by
  cases h
  exact hExpr

theorem exprSeq_cast {m n : Nat} (h : m = n)
    (exprs : Locals.ExprSeq m)
    (hExprs : exprs.usesCallCreate = false) :
    (Expr.seqCast h exprs).usesCallCreate = false := by
  cases h
  exact hExprs

theorem functionsStmtList_append {left right : List Functions.Stmt}
    (hLeft : Functions.StmtList.usesCallCreate left = false)
    (hRight : Functions.StmtList.usesCallCreate right = false) :
    Functions.StmtList.usesCallCreate (left ++ right) = false := by
  induction left with
  | nil => simpa using hRight
  | cons head tail ih =>
      have hParts :
          head.usesCallCreate = false ∧
            Functions.StmtList.usesCallCreate tail = false := by
        simpa [Functions.StmtList.usesCallCreate] using hLeft
      simp [Functions.StmtList.usesCallCreate, hParts.1, ih hParts.2]

theorem toSeq?_noCallCreate :
    ∀ {exprs : List (Locals.Expr 1)} {results : Nat}
      {lower : Locals.ExprSeq results},
      (∀ expr ∈ exprs, expr.usesCallCreate = false) →
        Expr.List.toSeq? exprs results = some lower →
          lower.usesCallCreate = false
  := by
    intro exprs
    induction exprs with
    | nil =>
        intro results lower hExprs hLower
        cases results <;> simp [Expr.List.toSeq?] at hLower
        cases hLower
        rfl
    | cons expr rest ih =>
      intro results lower hExprs hLower
      cases results with
      | zero =>
          simp [Expr.List.toSeq?] at hLower
      | succ results =>
      cases hTail : Expr.List.toSeq? rest results with
      | none =>
          simp [Expr.List.toSeq?, hTail] at hLower
      | some tail =>
      simp [Expr.List.toSeq?, hTail] at hLower
      have hExpr : expr.usesCallCreate = false := hExprs expr (by simp)
      have hRest :
          ∀ e ∈ rest, e.usesCallCreate = false := by
        intro e hMem
        exact hExprs e (by simp [hMem])
      have hTailNo : tail.usesCallCreate = false :=
        ih hRest hTail
      rw [← hLower]
      apply exprSeq_cast
      simp [Locals.ExprSeq.usesCallCreate, hExpr, hTailNo]

theorem toStackSeq?_noCallCreate {exprs : List (Locals.Expr 1)}
    {results : Nat} {lower : Locals.ExprSeq results}
    (hExprs : ∀ expr ∈ exprs, expr.usesCallCreate = false)
    (hLower : Expr.List.toStackSeq? exprs results = some lower) :
    lower.usesCallCreate = false := by
  unfold Expr.List.toStackSeq? at hLower
  exact toSeq?_noCallCreate
    (exprs := exprs.reverse)
    (by
      intro expr hMem
      exact hExprs expr (List.mem_reverse.mp hMem))
    hLower

theorem localsExprList_all_noCallCreate :
    ∀ {exprs : List (Locals.Expr 1)},
      (∀ expr ∈ exprs, expr.usesCallCreate = false) →
        Functions.ExprList.usesCallCreate exprs = false
  | [], _h => rfl
  | expr :: rest, h => by
      have hHead : expr.usesCallCreate = false := h expr (by simp)
      have hRest :
          Functions.ExprList.usesCallCreate rest = false :=
        localsExprList_all_noCallCreate (exprs := rest) (by
          intro e hMem
          exact h e (by simp [hMem]))
      simp [Functions.ExprList.usesCallCreate, hHead, hRest]

set_option maxHeartbeats 800000 in
mutual
  theorem expr_toLocals?_noCallCreate
      {safeExpr : AstExpr} {results : Nat} {lower : Locals.Expr results}
      (hSafe : Reference.Safe.expr safeExpr)
      (hLower : Expr.toLocals? results safeExpr = some lower) :
      lower.usesCallCreate = false := by
    cases safeExpr with
    | Lit value =>
        unfold Expr.toLocals? at hLower
        split_ifs at hLower with h
        · cases hLower
          exact expr_cast h (.lit value) rfl
    | Var name =>
        unfold Expr.toLocals? at hLower
        split_ifs at hLower with h
        · cases hLower
          exact expr_cast h (.var (identName name)) rfl
    | Call callee args =>
        cases callee with
        | inr functionName =>
            simp [Expr.toLocals?] at hLower
        | inl prim =>
            rcases hSafe with ⟨hPrimSafe, hArgsSafe⟩
            simp [Expr.toLocals?] at hLower
            cases hOp : Prim.toBasicOp? prim with
            | none => simp [hOp] at hLower
            | some op =>
                simp [hOp] at hLower
                cases hArgs : Expr.List.toLocals1? args with
                | none => simp [hArgs] at hLower
                | some lowerArgs =>
                    simp [hArgs] at hLower
                    cases hSeq :
                        Expr.List.toStackSeq? lowerArgs
                          (Expressions.Structured.BasicOp.inputs op) with
                    | none => simp [hSeq] at hLower
                    | some seq =>
                        simp [hSeq] at hLower
                        rcases hLower with ⟨hResults, hLower⟩
                        cases hLower
                        have hArgsNo :
                            ∀ expr ∈ lowerArgs,
                              expr.usesCallCreate = false :=
                          exprList_toLocals1?_all_noCallCreate hArgsSafe hArgs
                        have hSeqNo :
                            seq.usesCallCreate = false :=
                          toStackSeq?_noCallCreate hArgsNo hSeq
                        have hOpNo :
                            op.toPrimOp.isCallCreate = false :=
                          Reference.Safe.lowered_basicOp_not_callCreate
                            hPrimSafe hOp
                        exact expr_cast hResults (.prim op seq) (by
                          simp [Locals.Expr.usesCallCreate, hSeqNo, hOpNo])

  theorem exprList_toLocals1?_all_noCallCreate
      {safeExprs : List AstExpr} {lower : List (Locals.Expr 1)}
      (hSafe : Reference.Safe.exprs safeExprs)
      (hLower : Expr.List.toLocals1? safeExprs = some lower) :
      ∀ expr ∈ lower, expr.usesCallCreate = false := by
    cases safeExprs with
    | nil =>
        simp [Expr.List.toLocals1?] at hLower
        cases hLower
        intro expr hMem
        simp at hMem
    | cons head rest =>
        rcases hSafe with ⟨hHeadSafe, hRestSafe⟩
        simp [Expr.List.toLocals1?] at hLower
        cases hHead : Expr.toLocals? 1 head with
        | none => simp [hHead] at hLower
        | some lowerHead =>
            simp [hHead] at hLower
            cases hRest : Expr.List.toLocals1? rest with
            | none => simp [hRest] at hLower
            | some lowerRest =>
                simp [hRest] at hLower
                cases hLower
                intro expr hMem
                simp at hMem
                cases hMem with
                | inl hEq =>
                    subst expr
                    exact expr_toLocals?_noCallCreate hHeadSafe hHead
                | inr hMem =>
                    exact
                      exprList_toLocals1?_all_noCallCreate
                        hRestSafe hRest expr hMem
end

set_option maxHeartbeats 1600000 in
mutual
  theorem expr_lower?_noCallCreate
      {safeExpr : AstExpr} {results : Nat} {state state' : Fresh.State}
      {pre : List Functions.Stmt} {lower : Locals.Expr results}
      (hSafe : Reference.Safe.expr safeExpr)
      (hLower :
        Expr.lower? results state safeExpr = some (pre, lower, state')) :
      Functions.StmtList.usesCallCreate pre = false ∧
        lower.usesCallCreate = false := by
    cases safeExpr with
    | Lit value =>
        by_cases hResults : 1 = results
        · simp [Expr.lower?, Expr.cast, hResults] at hLower
          rcases hLower with ⟨hPre, hLowerExpr, _hState⟩
          subst pre
          subst lower
          exact ⟨rfl, expr_cast hResults (.lit value) rfl⟩
        · simp [Expr.lower?, Expr.cast, hResults] at hLower
    | Var name =>
        by_cases hResults : 1 = results
        · simp [Expr.lower?, Expr.cast, hResults] at hLower
          rcases hLower with ⟨hPre, hLowerExpr, _hState⟩
          subst pre
          subst lower
          exact ⟨rfl, expr_cast hResults (.var (identName name)) rfl⟩
        · simp [Expr.lower?, Expr.cast, hResults] at hLower
    | Call callee args =>
        cases callee with
        | inl prim =>
            rcases hSafe with ⟨hPrimSafe, hArgsSafe⟩
            cases hOp : Prim.toBasicOp? prim with
            | none =>
                simp [Expr.lower?, hOp] at hLower
            | some op =>
                cases hArgs :
                    Expr.List.lowerBound1? state args with
                | none =>
                    simp [Expr.lower?, hOp, hArgs] at hLower
                | some argResult =>
                    rcases argResult with ⟨preArgs, lowerArgs, stateAfterArgs⟩
                    have hArgsNo :=
                      exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
                    cases hSeq :
                        Expr.List.toStackSeq? lowerArgs
                          (Expressions.Structured.BasicOp.inputs op) with
                    | none =>
                        simp [Expr.lower?, hOp, hArgs, hSeq] at hLower
                    | some seq =>
                        by_cases hOutputs :
                            Expressions.Structured.BasicOp.outputs op =
                              results
                        · simp [Expr.lower?, hOp, hArgs, hSeq, hOutputs]
                            at hLower
                          rcases hLower with ⟨hPre, hLowerExpr, _hState⟩
                          subst pre
                          subst lower
                          have hSeqNo : seq.usesCallCreate = false :=
                            toStackSeq?_noCallCreate hArgsNo.2 hSeq
                          have hOpNo :
                              op.toPrimOp.isCallCreate = false :=
                            Reference.Safe.lowered_basicOp_not_callCreate
                              hPrimSafe hOp
                          exact
                            ⟨hArgsNo.1,
                              expr_cast hOutputs (.prim op seq) (by
                                simp [Locals.Expr.usesCallCreate, hSeqNo,
                                  hOpNo])⟩
                        · simp [Expr.lower?, hOp, hArgs, hSeq, hOutputs]
                            at hLower
        | inr functionName =>
            rcases hSafe with ⟨hUnsupportedSafe, hArgsSafe⟩
            by_cases hUnsupported :
                ObjectBuiltin.unsupported? functionName
            · simp [Expr.lower?, hUnsupported] at hLower
            · by_cases hResults : 1 = results
              · by_cases hDirect :
                    Expr.List.directCallArgsSafe? args
                · cases hDirectArgs : Expr.List.toLocals1? args with
                  | none =>
                      simp [Expr.lower?, hUnsupported, hResults, hDirect,
                        hDirectArgs] at hLower
                  | some lowerArgs =>
                      cases hFresh : Fresh.fresh? state with
                      | none =>
                          simp [Expr.lower?, hUnsupported, hResults, hDirect,
                            hDirectArgs, hFresh] at hLower
                      | some freshResult =>
                          rcases freshResult with ⟨tmp, stateFresh⟩
                          simp [Expr.lower?, hUnsupported, hResults, hDirect,
                            hDirectArgs, hFresh] at hLower
                          rcases hLower with ⟨hPre, hLowerExpr, _hState⟩
                          subst pre
                          subst lower
                          have hArgsNo :
                              ∀ expr ∈ lowerArgs,
                                expr.usesCallCreate = false :=
                            exprList_toLocals1?_all_noCallCreate
                              hArgsSafe hDirectArgs
                          have hArgListNo :
                              Functions.ExprList.usesCallCreate lowerArgs =
                                false :=
                            localsExprList_all_noCallCreate hArgsNo
                          exact
                            ⟨by
                              simp [Functions.StmtList.usesCallCreate,
                                Functions.Stmt.usesCallCreate,
                                Locals.Expr.usesCallCreate, hArgListNo],
                              expr_cast hResults (.var tmp) rfl⟩
                · cases hArgs :
                      Expr.List.lowerBound1? state args with
                  | none =>
                      simp [Expr.lower?, hUnsupported, hResults, hDirect,
                        hArgs] at hLower
                  | some argResult =>
                      rcases argResult with ⟨preArgs, lowerArgs, stateAfterArgs⟩
                      have hArgsNo :=
                        exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
                      cases hFresh : Fresh.fresh? stateAfterArgs with
                      | none =>
                          simp [Expr.lower?, hUnsupported, hResults, hDirect,
                            hArgs, hFresh] at hLower
                      | some freshResult =>
                          rcases freshResult with ⟨tmp, stateFresh⟩
                          simp [Expr.lower?, hUnsupported, hResults, hDirect,
                            hArgs, hFresh] at hLower
                          rcases hLower with ⟨hPre, hLowerExpr, _hState⟩
                          subst pre
                          subst lower
                          have hArgListNo :
                              Functions.ExprList.usesCallCreate lowerArgs =
                                false :=
                            localsExprList_all_noCallCreate hArgsNo.2
                          exact
                            ⟨functionsStmtList_append hArgsNo.1 (by
                              simp [Functions.StmtList.usesCallCreate,
                                Functions.Stmt.usesCallCreate,
                                Locals.Expr.usesCallCreate, hArgListNo]),
                              expr_cast hResults (.var tmp) rfl⟩
              · simp [Expr.lower?, hUnsupported, hResults] at hLower

  theorem exprList_lowerBound1?_noCallCreate
      {safeExprs : List AstExpr} {state state' : Fresh.State}
      {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
      (hSafe : Reference.Safe.exprs safeExprs)
      (hLower :
        Expr.List.lowerBound1? state safeExprs =
          some (pre, lowerArgs, state')) :
      Functions.StmtList.usesCallCreate pre = false ∧
        ∀ expr ∈ lowerArgs, expr.usesCallCreate = false := by
    cases safeExprs with
    | nil =>
        simp [Expr.List.lowerBound1?] at hLower
        rcases hLower with ⟨hPre, hArgs, _hState⟩
        subst pre
        subst lowerArgs
        exact ⟨rfl, by intro expr hMem; simp at hMem⟩
    | cons head rest =>
        rcases hSafe with ⟨hHeadSafe, hRestSafe⟩
        cases hRest :
            Expr.List.lowerBound1? state rest with
        | none =>
            simp [Expr.List.lowerBound1?, hRest] at hLower
        | some restResult =>
            rcases restResult with ⟨preRest, lowerRest, stateRest⟩
            have hRestNo :=
              exprList_lowerBound1?_noCallCreate hRestSafe hRest
            cases hHead :
                Expr.lower? 1 stateRest head with
            | none =>
                simp [Expr.List.lowerBound1?, hRest, hHead] at hLower
            | some headResult =>
                rcases headResult with ⟨preHead, lowerHead, stateHead⟩
                have hHeadNo :=
                  expr_lower?_noCallCreate hHeadSafe hHead
                cases hFresh : Fresh.fresh? stateHead with
                | none =>
                    simp [Expr.List.lowerBound1?, hRest, hHead, hFresh]
                      at hLower
                | some freshResult =>
                    rcases freshResult with ⟨tmp, stateFresh⟩
                    simp [Expr.List.lowerBound1?, hRest, hHead, hFresh]
                      at hLower
                    rcases hLower with ⟨hPre, hLowerArgs, _hState⟩
                    subst pre
                    subst lowerArgs
                    constructor
                    · simpa [List.append_assoc] using
                        functionsStmtList_append
                          (left := preRest ++ preHead)
                          (right := [Functions.Stmt.let_ tmp lowerHead])
                          (functionsStmtList_append hRestNo.1 hHeadNo.1)
                          (show
                            Functions.StmtList.usesCallCreate
                              [Functions.Stmt.let_ tmp lowerHead] = false by
                            simp [Functions.StmtList.usesCallCreate,
                              Functions.Stmt.usesCallCreate, hHeadNo.2])
                    · intro expr hMem
                      simp at hMem
                      cases hMem with
                      | inl hEq =>
                          subst expr
                          simp [Locals.Expr.usesCallCreate]
                      | inr hMem =>
                          exact hRestNo.2 expr hMem
end

theorem expr_lower1?_noCallCreate
    {safeExpr : AstExpr} {state state' : Fresh.State}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    (hSafe : Reference.Safe.expr safeExpr)
    (hLower : Expr.lower1? state safeExpr = some (pre, lower, state')) :
    Functions.StmtList.usesCallCreate pre = false ∧
      lower.usesCallCreate = false :=
  expr_lower?_noCallCreate hSafe hLower

theorem expr_lower0?_noCallCreate
    {safeExpr : AstExpr} {state state' : Fresh.State}
    {pre : List Functions.Stmt} {lower : Locals.Expr 0}
    (hSafe : Reference.Safe.expr safeExpr)
    (hLower : Expr.lower0? state safeExpr = some (pre, lower, state')) :
    Functions.StmtList.usesCallCreate pre = false ∧
      lower.usesCallCreate = false :=
  expr_lower?_noCallCreate hSafe hLower

theorem initNames_noCallCreate :
    ∀ names : List Name,
      Functions.StmtList.usesCallCreate (Stmt.initNames names) = false
  | [] => rfl
  | _name :: rest => by
      simp [Stmt.initNames, Functions.StmtList.usesCallCreate,
        Functions.Stmt.usesCallCreate]
      exact ⟨rfl, by simpa [Stmt.initNames] using initNames_noCallCreate rest⟩

theorem directOrBoundArgs_noCallCreate
    {safeArgs : List AstExpr} {state state' : Fresh.State}
    {preArgs : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hSafe : Reference.Safe.exprs safeArgs)
    (hArgs :
      (if Expr.List.directCallArgsSafe? safeArgs then do
        let lowerArgs ← Expr.List.toLocals1? safeArgs
        some ([], lowerArgs, state)
      else
        Expr.List.lowerBound1? state safeArgs) =
        some (preArgs, lowerArgs, state')) :
    Functions.StmtList.usesCallCreate preArgs = false ∧
      ∀ expr ∈ lowerArgs, expr.usesCallCreate = false := by
  by_cases hDirect : Expr.List.directCallArgsSafe? safeArgs
  · cases hLocals : Expr.List.toLocals1? safeArgs with
    | none =>
        simp [hDirect, hLocals] at hArgs
    | some directArgs =>
        simp [hDirect, hLocals] at hArgs
        rcases hArgs with ⟨hPre, hArgsEq, _hState⟩
        subst preArgs
        subst lowerArgs
        exact
          ⟨rfl,
            exprList_toLocals1?_all_noCallCreate hSafe hLocals⟩
  · simp [hDirect] at hArgs
    exact exprList_lowerBound1?_noCallCreate hSafe hArgs

theorem block_of_stmts_noCallCreate {stmts : List Functions.Stmt}
    (hStmts : Functions.StmtList.usesCallCreate stmts = false) :
    (Functions.Block.mk stmts).usesCallCreate = false := by
  simpa [Functions.Block.usesCallCreate] using hStmts

theorem singleton_noCallCreate {stmt : Functions.Stmt}
    (hStmt : stmt.usesCallCreate = false) :
    Functions.StmtList.usesCallCreate [stmt] = false := by
  simp [Functions.StmtList.usesCallCreate, hStmt]

theorem terminalArgs_noCallCreate {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    (hArgs : args.usesCallCreate = false) :
    (Functions.Stmt.terminalArgs kind args).usesCallCreate = false := by
  simpa [Functions.Stmt.usesCallCreate] using hArgs

set_option maxHeartbeats 1400000 in
theorem exprStmtCall_toFunctionsListFuel?_noCallCreate
    {expr : AstExpr} {fuel : Nat} {state state' : Fresh.State}
    {lower : List Functions.Stmt}
    (hSafe : Reference.Safe.expr expr)
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state (.ExprStmtCall expr) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  cases expr with
  | Lit value =>
      simp [Stmt.toFunctionsListFuel?] at hLower
      cases hValue : Expr.lower0? state (.Lit value) with
      | none => simp [hValue] at hLower
      | some valueResult =>
          rcases valueResult with ⟨pre, lowerExpr, stateValue⟩
          simp [hValue] at hLower
          rcases hLower with ⟨hLowerList, _hState⟩
          subst lower
          have hValueNo :=
            expr_lower0?_noCallCreate (by trivial) hValue
          exact functionsStmtList_append hValueNo.1 (by
            simp [Functions.StmtList.usesCallCreate,
              Functions.Stmt.usesCallCreate, hValueNo.2])
  | Var name =>
      simp [Stmt.toFunctionsListFuel?] at hLower
      cases hValue : Expr.lower0? state (.Var name) with
      | none => simp [hValue] at hLower
      | some valueResult =>
          rcases valueResult with ⟨pre, lowerExpr, stateValue⟩
          simp [hValue] at hLower
          rcases hLower with ⟨hLowerList, _hState⟩
          subst lower
          have hValueNo :=
            expr_lower0?_noCallCreate (by trivial) hValue
          exact functionsStmtList_append hValueNo.1 (by
            simp [Functions.StmtList.usesCallCreate,
              Functions.Stmt.usesCallCreate, hValueNo.2])
  | Call callee args =>
      cases callee with
      | inr functionName =>
          rcases hSafe with ⟨hNameSafe, hArgsSafe⟩
          by_cases hUnsupported :
              ObjectBuiltin.unsupported? functionName
          · simp [Stmt.toFunctionsListFuel?, hUnsupported] at hLower
          · by_cases hDirect : Expr.List.directCallArgsSafe? args
            · cases hArgs : Expr.List.toLocals1? args with
              | none =>
                  simp [Stmt.toFunctionsListFuel?, hUnsupported, hDirect,
                    hArgs] at hLower
              | some lowerArgs =>
                  simp [Stmt.toFunctionsListFuel?, hUnsupported, hDirect,
                    hArgs] at hLower
                  rcases hLower with ⟨hLowerList, _hState⟩
                  subst lower
                  have hArgsNo :
                      ∀ expr ∈ lowerArgs,
                        expr.usesCallCreate = false :=
                    exprList_toLocals1?_all_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo
                  simp [Functions.StmtList.usesCallCreate,
                    Functions.Stmt.usesCallCreate, hArgListNo]
            · cases hArgs : Expr.List.lowerBound1? state args with
              | none =>
                  simp [Stmt.toFunctionsListFuel?, hUnsupported, hDirect,
                    hArgs] at hLower
              | some argResult =>
                  rcases argResult with ⟨preArgs, lowerArgs, stateArgs⟩
                  simp [Stmt.toFunctionsListFuel?, hUnsupported, hDirect,
                    hArgs] at hLower
                  rcases hLower with ⟨hLowerList, _hState⟩
                  subst lower
                  have hArgsNo :=
                    exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo.2
                  exact functionsStmtList_append hArgsNo.1 (by
                    simp [Functions.StmtList.usesCallCreate,
                      Functions.Stmt.usesCallCreate, hArgListNo])
      | inl prim =>
          rcases hSafe with ⟨hPrimSafe, hArgsSafe⟩
          cases hTerminal : Prim.terminal? prim with
          | some kind =>
              cases hArgs : Expr.List.lowerBound1? state args with
              | none =>
                  simp [Stmt.toFunctionsListFuel?, hTerminal, hArgs] at hLower
              | some argResult =>
                  rcases argResult with ⟨preArgs, lowerArgs, stateArgs⟩
                  have hArgsNo :=
                    exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
                  cases hSeq :
                      Expr.List.toStackSeq? lowerArgs kind.argCount with
                  | none =>
                      simp [Stmt.toFunctionsListFuel?, hTerminal, hArgs, hSeq]
                        at hLower
                  | some seq =>
                      simp [Stmt.toFunctionsListFuel?, hTerminal, hArgs, hSeq]
                        at hLower
                      rcases hLower with ⟨hLowerList, _hState⟩
                      subst lower
                      have hSeqNo :=
                        toStackSeq?_noCallCreate hArgsNo.2 hSeq
                      exact functionsStmtList_append hArgsNo.1 (by
                        simp [Functions.StmtList.usesCallCreate,
                          Functions.Stmt.usesCallCreate, hSeqNo])
          | none =>
              cases hValue :
                  Expr.lower0? state (.Call (.inl prim) args) with
              | none =>
                  simp [Stmt.toFunctionsListFuel?, hTerminal, hValue] at hLower
              | some valueResult =>
                  rcases valueResult with ⟨pre, lowerExpr, stateValue⟩
                  simp [Stmt.toFunctionsListFuel?, hTerminal, hValue] at hLower
                  rcases hLower with ⟨hLowerList, _hState⟩
                  subst lower
                  have hValueNo :=
                    expr_lower0?_noCallCreate
                      (by exact ⟨hPrimSafe, hArgsSafe⟩) hValue
                  exact functionsStmtList_append hValueNo.1 (by
                    simp [Functions.StmtList.usesCallCreate,
                      Functions.Stmt.usesCallCreate, hValueNo.2])

theorem letNone_toFunctionsListFuel?_noCallCreate
    {names : List EvmYul.Identifier} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state (.Let names none) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  unfold Stmt.toFunctionsListFuel? at hLower
  simp at hLower
  rcases hLower with ⟨hLower, _hState⟩
  rw [← hLower]
  exact initNames_noCallCreate (identNames names)

theorem letLit_toFunctionsListFuel?_noCallCreate
    {name : EvmYul.Identifier} {value : Word} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state
          (.Let [name] (some (.Lit value))) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  unfold Stmt.toFunctionsListFuel? at hLower
  cases hValue : Expr.lower1? state (.Lit value) with
  | none =>
      simp [hValue] at hLower
  | some valueResult =>
      rcases valueResult with ⟨preValue, lowerValue, stateValue⟩
      simp [hValue] at hLower
      rcases hLower with ⟨hLower, _hState⟩
      rw [← hLower]
      have hValueNo := expr_lower1?_noCallCreate (by trivial) hValue
      exact functionsStmtList_append hValueNo.1 (by
        simp [Functions.StmtList.usesCallCreate,
          Functions.Stmt.usesCallCreate, hValueNo.2])

theorem letVar_toFunctionsListFuel?_noCallCreate
    {name var : EvmYul.Identifier} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state
          (.Let [name] (some (.Var var))) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  unfold Stmt.toFunctionsListFuel? at hLower
  cases hValue : Expr.lower1? state (.Var var) with
  | none =>
      simp [hValue] at hLower
  | some valueResult =>
      rcases valueResult with ⟨preValue, lowerValue, stateValue⟩
      simp [hValue] at hLower
      rcases hLower with ⟨hLower, _hState⟩
      rw [← hLower]
      have hValueNo := expr_lower1?_noCallCreate (by trivial) hValue
      exact functionsStmtList_append hValueNo.1 (by
        simp [Functions.StmtList.usesCallCreate,
          Functions.Stmt.usesCallCreate, hValueNo.2])

theorem letPrimCall_toFunctionsListFuel?_noCallCreate
    {name : EvmYul.Identifier} {prim : EvmYul.Operation .Yul}
    {args : List AstExpr} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hSafe : Reference.Safe.expr (.Call (.inl prim) args))
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state
          (.Let [name] (some (.Call (.inl prim) args))) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  unfold Stmt.toFunctionsListFuel? at hLower
  cases hValue : Expr.lower1? state (.Call (.inl prim) args) with
  | none =>
      simp [hValue] at hLower
  | some valueResult =>
      rcases valueResult with ⟨preValue, lowerValue, stateValue⟩
      simp [hValue] at hLower
      rcases hLower with ⟨hLower, _hState⟩
      rw [← hLower]
      have hValueNo := expr_lower1?_noCallCreate hSafe hValue
      exact functionsStmtList_append hValueNo.1 (by
        simp [Functions.StmtList.usesCallCreate,
          Functions.Stmt.usesCallCreate, hValueNo.2])

theorem letUserCall_toFunctionsListFuel?_noCallCreate
    {names : List EvmYul.Identifier} {functionName : Name}
    {args : List AstExpr} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hSafe : Reference.Safe.expr (.Call (.inr functionName) args))
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state
          (.Let names (some (.Call (.inr functionName) args))) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  rcases hSafe with ⟨hNameSafe, hArgsSafe⟩
  unfold Stmt.toFunctionsListFuel? at hLower
  by_cases hUnsupported : ObjectBuiltin.unsupported? functionName = true
  · simp [hNameSafe] at hUnsupported
  · cases names with
    | nil =>
        by_cases hDirect : Expr.List.directCallArgsSafe? args = true
        · cases hArgs : Expr.List.toLocals1? args with
          | none =>
              simp [hNameSafe, hDirect, hArgs] at hLower
          | some lowerArgs =>
              simp [hNameSafe, hDirect, hArgs] at hLower
              rcases hLower with ⟨hLower, _hState⟩
              rw [← hLower]
              have hArgsNo :
                  ∀ expr ∈ lowerArgs, expr.usesCallCreate = false :=
                exprList_toLocals1?_all_noCallCreate hArgsSafe hArgs
              have hArgListNo :
                  Functions.ExprList.usesCallCreate lowerArgs = false :=
                localsExprList_all_noCallCreate hArgsNo
              simp [Functions.StmtList.usesCallCreate,
                Functions.Stmt.usesCallCreate, hArgListNo]
        · cases hArgs : Expr.List.lowerBound1? state args with
          | none =>
              simp [hNameSafe, hDirect, hArgs] at hLower
          | some argResult =>
              rcases argResult with ⟨preArgs, lowerArgs, stateArgs⟩
              simp [hNameSafe, hDirect, hArgs] at hLower
              rcases hLower with ⟨hLower, _hState⟩
              rw [← hLower]
              have hArgsNo :=
                exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
              have hArgListNo :
                  Functions.ExprList.usesCallCreate lowerArgs = false :=
                localsExprList_all_noCallCreate hArgsNo.2
              exact functionsStmtList_append hArgsNo.1 (by
                simp [Functions.StmtList.usesCallCreate,
                  Functions.Stmt.usesCallCreate, hArgListNo])
    | cons name rest =>
        cases rest with
        | nil =>
            by_cases hDirect : Expr.List.directCallArgsSafe? args = true
            · cases hArgs : Expr.List.toLocals1? args with
              | none =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
              | some lowerArgs =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  have hArgsNo :
                      ∀ expr ∈ lowerArgs, expr.usesCallCreate = false :=
                    exprList_toLocals1?_all_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo
                  exact functionsStmtList_append
                    (initNames_noCallCreate (identNames [name]))
                    (by
                      simp [Functions.StmtList.usesCallCreate,
                        Functions.Stmt.usesCallCreate, hArgListNo])
            · cases hArgs : Expr.List.lowerBound1? state args with
              | none =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
              | some argResult =>
                  rcases argResult with ⟨preArgs, lowerArgs, stateArgs⟩
                  simp [hNameSafe, hDirect, hArgs] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  have hArgsNo :=
                    exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo.2
                  exact functionsStmtList_append
                    (initNames_noCallCreate (identNames [name]))
                    (functionsStmtList_append hArgsNo.1 (by
                      simp [Functions.StmtList.usesCallCreate,
                        Functions.Stmt.usesCallCreate, hArgListNo]))
        | cons next rest =>
            by_cases hDirect : Expr.List.directCallArgsSafe? args = true
            · cases hArgs : Expr.List.toLocals1? args with
              | none =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
              | some lowerArgs =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  have hArgsNo :
                      ∀ expr ∈ lowerArgs, expr.usesCallCreate = false :=
                    exprList_toLocals1?_all_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo
                  exact functionsStmtList_append
                    (initNames_noCallCreate (identNames (name :: next :: rest)))
                    (by
                      simp [Functions.StmtList.usesCallCreate,
                        Functions.Stmt.usesCallCreate, hArgListNo])
            · cases hArgs : Expr.List.lowerBound1? state args with
              | none =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
              | some argResult =>
                  rcases argResult with ⟨preArgs, lowerArgs, stateArgs⟩
                  simp [hNameSafe, hDirect, hArgs] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  have hArgsNo :=
                    exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo.2
                  exact functionsStmtList_append
                    (initNames_noCallCreate (identNames (name :: next :: rest)))
                    (functionsStmtList_append hArgsNo.1 (by
                      simp [Functions.StmtList.usesCallCreate,
                        Functions.Stmt.usesCallCreate, hArgListNo]))

theorem assignLit_toFunctionsListFuel?_noCallCreate
    {name : EvmYul.Identifier} {value : Word} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state
          (.Assign [name] (.Lit value)) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  unfold Stmt.toFunctionsListFuel? at hLower
  cases hValue : Expr.lower1? state (.Lit value) with
  | none =>
      simp [hValue] at hLower
  | some valueResult =>
      rcases valueResult with ⟨preValue, lowerValue, stateValue⟩
      simp [hValue] at hLower
      rcases hLower with ⟨hLower, _hState⟩
      rw [← hLower]
      have hValueNo := expr_lower1?_noCallCreate (by trivial) hValue
      exact functionsStmtList_append hValueNo.1 (by
        simp [Functions.StmtList.usesCallCreate,
          Functions.Stmt.usesCallCreate, hValueNo.2])

theorem assignVar_toFunctionsListFuel?_noCallCreate
    {name var : EvmYul.Identifier} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state
          (.Assign [name] (.Var var)) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  unfold Stmt.toFunctionsListFuel? at hLower
  cases hValue : Expr.lower1? state (.Var var) with
  | none =>
      simp [hValue] at hLower
  | some valueResult =>
      rcases valueResult with ⟨preValue, lowerValue, stateValue⟩
      simp [hValue] at hLower
      rcases hLower with ⟨hLower, _hState⟩
      rw [← hLower]
      have hValueNo := expr_lower1?_noCallCreate (by trivial) hValue
      exact functionsStmtList_append hValueNo.1 (by
        simp [Functions.StmtList.usesCallCreate,
          Functions.Stmt.usesCallCreate, hValueNo.2])

theorem assignPrimCall_toFunctionsListFuel?_noCallCreate
    {name : EvmYul.Identifier} {prim : EvmYul.Operation .Yul}
    {args : List AstExpr} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hSafe : Reference.Safe.expr (.Call (.inl prim) args))
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state
          (.Assign [name] (.Call (.inl prim) args)) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  unfold Stmt.toFunctionsListFuel? at hLower
  cases hValue : Expr.lower1? state (.Call (.inl prim) args) with
  | none =>
      simp [hValue] at hLower
  | some valueResult =>
      rcases valueResult with ⟨preValue, lowerValue, stateValue⟩
      simp [hValue] at hLower
      rcases hLower with ⟨hLower, _hState⟩
      rw [← hLower]
      have hValueNo := expr_lower1?_noCallCreate hSafe hValue
      exact functionsStmtList_append hValueNo.1 (by
        simp [Functions.StmtList.usesCallCreate,
          Functions.Stmt.usesCallCreate, hValueNo.2])

theorem assignUserCall_toFunctionsListFuel?_noCallCreate
    {names : List EvmYul.Identifier} {functionName : Name}
    {args : List AstExpr} {fuel : Nat}
    {state state' : Fresh.State} {lower : List Functions.Stmt}
    (hSafe : Reference.Safe.expr (.Call (.inr functionName) args))
    (hLower :
      Stmt.toFunctionsListFuel? (fuel + 1) state
          (.Assign names (.Call (.inr functionName) args)) =
        some (lower, state')) :
    Functions.StmtList.usesCallCreate lower = false := by
  rcases hSafe with ⟨hNameSafe, hArgsSafe⟩
  unfold Stmt.toFunctionsListFuel? at hLower
  by_cases hUnsupported : ObjectBuiltin.unsupported? functionName = true
  · simp [hNameSafe] at hUnsupported
  · cases names with
    | nil =>
        by_cases hDirect : Expr.List.directCallArgsSafe? args = true
        · cases hArgs : Expr.List.toLocals1? args with
          | none =>
              simp [hNameSafe, hDirect, hArgs] at hLower
          | some lowerArgs =>
              simp [hNameSafe, hDirect, hArgs] at hLower
              rcases hLower with ⟨hLower, _hState⟩
              rw [← hLower]
              have hArgsNo :
                  ∀ expr ∈ lowerArgs, expr.usesCallCreate = false :=
                exprList_toLocals1?_all_noCallCreate hArgsSafe hArgs
              have hArgListNo :
                  Functions.ExprList.usesCallCreate lowerArgs = false :=
                localsExprList_all_noCallCreate hArgsNo
              simp [Functions.StmtList.usesCallCreate,
                Functions.Stmt.usesCallCreate, hArgListNo]
        · cases hArgs : Expr.List.lowerBound1? state args with
          | none =>
              simp [hNameSafe, hDirect, hArgs] at hLower
          | some argResult =>
              rcases argResult with ⟨preArgs, lowerArgs, stateArgs⟩
              simp [hNameSafe, hDirect, hArgs] at hLower
              rcases hLower with ⟨hLower, _hState⟩
              rw [← hLower]
              have hArgsNo :=
                exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
              have hArgListNo :
                  Functions.ExprList.usesCallCreate lowerArgs = false :=
                localsExprList_all_noCallCreate hArgsNo.2
              exact functionsStmtList_append hArgsNo.1 (by
                simp [Functions.StmtList.usesCallCreate,
                  Functions.Stmt.usesCallCreate, hArgListNo])
    | cons name rest =>
        cases rest with
        | nil =>
            by_cases hDirect : Expr.List.directCallArgsSafe? args = true
            · cases hArgs : Expr.List.toLocals1? args with
              | none =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
              | some lowerArgs =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  have hArgsNo :
                      ∀ expr ∈ lowerArgs, expr.usesCallCreate = false :=
                    exprList_toLocals1?_all_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo
                  simp [Functions.StmtList.usesCallCreate,
                    Functions.Stmt.usesCallCreate, hArgListNo]
            · cases hArgs : Expr.List.lowerBound1? state args with
              | none =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
              | some argResult =>
                  rcases argResult with ⟨preArgs, lowerArgs, stateArgs⟩
                  simp [hNameSafe, hDirect, hArgs] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  have hArgsNo :=
                    exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo.2
                  exact functionsStmtList_append hArgsNo.1 (by
                    simp [Functions.StmtList.usesCallCreate,
                      Functions.Stmt.usesCallCreate, hArgListNo])
        | cons next rest =>
            by_cases hDirect : Expr.List.directCallArgsSafe? args = true
            · cases hArgs : Expr.List.toLocals1? args with
              | none =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
              | some lowerArgs =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  have hArgsNo :
                      ∀ expr ∈ lowerArgs, expr.usesCallCreate = false :=
                    exprList_toLocals1?_all_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo
                  simp [Functions.StmtList.usesCallCreate,
                    Functions.Stmt.usesCallCreate, hArgListNo]
            · cases hArgs : Expr.List.lowerBound1? state args with
              | none =>
                  simp [hNameSafe, hDirect, hArgs] at hLower
              | some argResult =>
                  rcases argResult with ⟨preArgs, lowerArgs, stateArgs⟩
                  simp [hNameSafe, hDirect, hArgs] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  have hArgsNo :=
                    exprList_lowerBound1?_noCallCreate hArgsSafe hArgs
                  have hArgListNo :
                      Functions.ExprList.usesCallCreate lowerArgs = false :=
                    localsExprList_all_noCallCreate hArgsNo.2
                  exact functionsStmtList_append hArgsNo.1 (by
                    simp [Functions.StmtList.usesCallCreate,
                      Functions.Stmt.usesCallCreate, hArgListNo])

theorem forCondBlock_noCallCreate
    {preCond : List Functions.Stmt} {lowerCond : Locals.Expr 1}
    {lowerBody : Functions.Block}
    (hCondPre : Functions.StmtList.usesCallCreate preCond = false)
    (hCond : lowerCond.usesCallCreate = false)
    (hBody : lowerBody.usesCallCreate = false) :
    (Functions.Block.mk
      (preCond ++
        [Functions.Stmt.if_
          (Locals.Expr.prim .iszero
            (Locals.ExprSeq.cons lowerCond .nil))
          { stmts := [Functions.Stmt.brk] }] ++
        lowerBody.stmts)).usesCallCreate = false := by
  apply block_of_stmts_noCallCreate
  simpa [List.append_assoc] using
    functionsStmtList_append
      (left := preCond ++
        [Functions.Stmt.if_
          (Locals.Expr.prim .iszero
            (Locals.ExprSeq.cons lowerCond .nil))
          { stmts := [Functions.Stmt.brk] }])
      (right := lowerBody.stmts)
      (functionsStmtList_append hCondPre (by
        simp [Functions.StmtList.usesCallCreate,
          Functions.Stmt.usesCallCreate, Locals.Expr.usesCallCreate,
          Locals.ExprSeq.usesCallCreate, Functions.Block.usesCallCreate,
          Structured.BasicOp.toPrimOp, Assembly.PrimOp.isCallCreate, hCond]))
      (by
        cases lowerBody
        simpa [Functions.Block.usesCallCreate] using hBody)

set_option maxHeartbeats 2600000 in
mutual
  theorem stmt_toFunctionsListFuel?_noCallCreate
      {safeStmt : AstStmt} {fuel : Nat} {state state' : Fresh.State}
      {lower : List Functions.Stmt}
      (hSafe : Reference.Safe.stmt safeStmt)
      (hLower :
        Stmt.toFunctionsListFuel? fuel state safeStmt =
          some (lower, state')) :
      Functions.StmtList.usesCallCreate lower = false := by
    cases fuel with
    | zero =>
        simp [Stmt.toFunctionsListFuel?] at hLower
    | succ fuel =>
      cases safeStmt with
      | Block body =>
          unfold Stmt.toFunctionsListFuel? at hLower
          cases hBody : Stmt.List.toBlockFuel? fuel state body with
          | none =>
              simp [hBody] at hLower
          | some bodyResult =>
              rcases bodyResult with ⟨lowerBody, stateBody⟩
              simp [hBody] at hLower
              rcases hLower with ⟨hLower, _hState⟩
              rw [← hLower]
              have hBodyNo :=
                block_toFunctionsFuel?_noCallCreate
                  (by simpa [Reference.Safe.stmt] using hSafe) hBody
              simp [Functions.StmtList.usesCallCreate,
                Functions.Stmt.usesCallCreate, hBodyNo]
      | Let names opt =>
          cases opt with
          | none =>
              exact letNone_toFunctionsListFuel?_noCallCreate hLower
          | some value =>
              cases value with
              | Lit value =>
                  cases names with
                  | nil =>
                      simp [Stmt.toFunctionsListFuel?] at hLower
                  | cons name rest =>
                      cases rest with
                      | nil =>
                          exact letLit_toFunctionsListFuel?_noCallCreate hLower
                      | cons _ _ =>
                          simp [Stmt.toFunctionsListFuel?] at hLower
              | Var var =>
                  cases names with
                  | nil =>
                      simp [Stmt.toFunctionsListFuel?] at hLower
                  | cons name rest =>
                      cases rest with
                      | nil =>
                          exact letVar_toFunctionsListFuel?_noCallCreate hLower
                      | cons _ _ =>
                          simp [Stmt.toFunctionsListFuel?] at hLower
              | Call callee args =>
                  cases callee with
                  | inr functionName =>
                      exact letUserCall_toFunctionsListFuel?_noCallCreate
                        hSafe hLower
                  | inl prim =>
                      cases names with
                      | nil =>
                          simp [Stmt.toFunctionsListFuel?] at hLower
                      | cons name rest =>
                          cases rest with
                          | nil =>
                              exact letPrimCall_toFunctionsListFuel?_noCallCreate
                                hSafe
                                hLower
                          | cons _ _ =>
                              simp [Stmt.toFunctionsListFuel?] at hLower
      | Assign names value =>
          cases value with
          | Lit value =>
              cases names with
              | nil =>
                  simp [Stmt.toFunctionsListFuel?] at hLower
              | cons name rest =>
                  cases rest with
                  | nil =>
                      exact assignLit_toFunctionsListFuel?_noCallCreate hLower
                  | cons _ _ =>
                      simp [Stmt.toFunctionsListFuel?] at hLower
          | Var var =>
              cases names with
              | nil =>
                  simp [Stmt.toFunctionsListFuel?] at hLower
              | cons name rest =>
                  cases rest with
                  | nil =>
                      exact assignVar_toFunctionsListFuel?_noCallCreate hLower
                  | cons _ _ =>
                      simp [Stmt.toFunctionsListFuel?] at hLower
          | Call callee args =>
              cases callee with
              | inr functionName =>
                  exact assignUserCall_toFunctionsListFuel?_noCallCreate
                    (by simpa [Reference.Safe.stmt] using hSafe) hLower
              | inl prim =>
                  cases names with
                  | nil =>
                      simp [Stmt.toFunctionsListFuel?] at hLower
                  | cons name rest =>
                      cases rest with
                      | nil =>
                          exact assignPrimCall_toFunctionsListFuel?_noCallCreate
                            (by simpa [Reference.Safe.stmt] using hSafe)
                            hLower
                      | cons _ _ =>
                          simp [Stmt.toFunctionsListFuel?] at hLower
      | ExprStmtCall expr =>
          exact exprStmtCall_toFunctionsListFuel?_noCallCreate hSafe hLower
      | Switch scrutinee cases defaultBody =>
          rcases hSafe with ⟨hScrutineeSafe, hCasesSafe, hDefaultSafe⟩
          unfold Stmt.toFunctionsListFuel? at hLower
          cases hScrutinee : Expr.lower1? state scrutinee with
          | none =>
              simp [hScrutinee] at hLower
          | some scrutineeResult =>
              rcases scrutineeResult with
                ⟨preScrutinee, lowerScrutinee, stateScrutinee⟩
              have hScrutineeNo :=
                expr_lower1?_noCallCreate hScrutineeSafe hScrutinee
              cases hCases :
                  Stmt.CaseList.toFunctionsFuel? fuel stateScrutinee cases with
              | none =>
                  simp [hScrutinee, hCases] at hLower
              | some casesResult =>
                  rcases casesResult with ⟨lowerCases, stateCases⟩
                  have hCasesNo :=
                    caseList_toFunctionsFuel?_noCallCreate hCasesSafe hCases
                  cases defaultBody with
                  | nil =>
                      simp [hScrutinee, hCases] at hLower
                      rcases hLower with ⟨hLower, _hState⟩
                      rw [← hLower]
                      exact functionsStmtList_append hScrutineeNo.1 (by
                        simp [Functions.StmtList.usesCallCreate,
                          Functions.Stmt.usesCallCreate,
                          Functions.Default.usesCallCreate, hScrutineeNo.2,
                          hCasesNo])
                  | cons d ds =>
                      cases hDefault :
                          Stmt.List.toBlockFuel? fuel stateCases (d :: ds) with
                      | none =>
                          simp [hScrutinee, hCases, hDefault] at hLower
                      | some defaultResult =>
                          rcases defaultResult with ⟨lowerDefault, stateDefault⟩
                          simp [hScrutinee, hCases, hDefault] at hLower
                          rcases hLower with ⟨hLower, _hState⟩
                          rw [← hLower]
                          have hDefaultNo :=
                            block_toFunctionsFuel?_noCallCreate
                              (by simpa using hDefaultSafe) hDefault
                          exact functionsStmtList_append hScrutineeNo.1 (by
                            simp [Functions.StmtList.usesCallCreate,
                              Functions.Stmt.usesCallCreate,
                              Functions.Default.usesCallCreate, hScrutineeNo.2,
                              hCasesNo, hDefaultNo])
      | For cond post body =>
          rcases hSafe with ⟨hCondSafe, hPostSafe, hBodySafe⟩
          unfold Stmt.toFunctionsListFuel? at hLower
          cases hCond : Expr.lower1? state cond with
          | none =>
              simp [hCond] at hLower
          | some condResult =>
              rcases condResult with ⟨preCond, lowerCond, stateCond⟩
              have hCondNo := expr_lower1?_noCallCreate hCondSafe hCond
              cases hPost : Stmt.List.toBlockFuel? fuel stateCond post with
              | none =>
                  simp [hCond, hPost] at hLower
              | some postResult =>
                  rcases postResult with ⟨lowerPost, statePost⟩
                  have hPostNo :=
                    block_toFunctionsFuel?_noCallCreate hPostSafe hPost
                  cases hBody : Stmt.List.toBlockFuel? fuel statePost body with
                  | none =>
                      simp [hCond, hPost, hBody] at hLower
                  | some bodyResult =>
                      rcases bodyResult with ⟨lowerBody, stateBody⟩
                      simp [hCond, hPost, hBody] at hLower
                      rcases hLower with ⟨hLower, _hState⟩
                      rw [← hLower]
                      have hBodyNo :=
                        block_toFunctionsFuel?_noCallCreate hBodySafe hBody
                      have hBodyWithCond :=
                        forCondBlock_noCallCreate hCondNo.1 hCondNo.2 hBodyNo
                      simp [Functions.StmtList.usesCallCreate,
                        Functions.Stmt.usesCallCreate,
                        Functions.Block.usesCallCreate, hPostNo]
                      exact
                        ⟨rfl,
                          by
                            simpa [Functions.Block.usesCallCreate,
                              List.append_assoc] using hBodyWithCond⟩
      | If cond body =>
          rcases hSafe with ⟨hCondSafe, hBodySafe⟩
          unfold Stmt.toFunctionsListFuel? at hLower
          cases hCond : Expr.lower1? state cond with
          | none =>
              simp [hCond] at hLower
          | some condResult =>
              rcases condResult with ⟨preCond, lowerCond, stateCond⟩
              have hCondNo := expr_lower1?_noCallCreate hCondSafe hCond
              cases hBody : Stmt.List.toBlockFuel? fuel stateCond body with
              | none =>
                  simp [hCond, hBody] at hLower
              | some bodyResult =>
                  rcases bodyResult with ⟨lowerBody, stateBody⟩
                  have hBodyNo :=
                    block_toFunctionsFuel?_noCallCreate hBodySafe hBody
                  simp [hCond, hBody] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  exact functionsStmtList_append hCondNo.1 (by
                    simp [Functions.StmtList.usesCallCreate,
                      Functions.Stmt.usesCallCreate, hCondNo.2, hBodyNo])
      | Continue =>
          unfold Stmt.toFunctionsListFuel? at hLower
          simp at hLower
          rcases hLower with ⟨hLower, _hState⟩
          rw [← hLower]
          rfl
      | Break =>
          unfold Stmt.toFunctionsListFuel? at hLower
          simp at hLower
          rcases hLower with ⟨hLower, _hState⟩
          rw [← hLower]
          rfl
      | Leave =>
          unfold Stmt.toFunctionsListFuel? at hLower
          simp at hLower
          rcases hLower with ⟨hLower, _hState⟩
          rw [← hLower]
          rfl

  theorem stmtList_toFunctionsFuel?_noCallCreate
      {safeStmts : List AstStmt} {fuel : Nat} {state state' : Fresh.State}
      {lower : List Functions.Stmt}
      (hSafe : Reference.Safe.stmts safeStmts)
      (hLower :
        Stmt.List.toFunctionsFuel? fuel state safeStmts =
          some (lower, state')) :
      Functions.StmtList.usesCallCreate lower = false := by
    cases fuel with
    | zero =>
        simp [Stmt.List.toFunctionsFuel?] at hLower
    | succ fuel =>
      cases safeStmts with
      | nil =>
          unfold Stmt.List.toFunctionsFuel? at hLower
          simp at hLower
          rcases hLower with ⟨hLower, _hState⟩
          rw [hLower]
          rfl
      | cons head rest =>
          rcases hSafe with ⟨hHeadSafe, hRestSafe⟩
          unfold Stmt.List.toFunctionsFuel? at hLower
          cases hHead :
              Stmt.toFunctionsListFuel? fuel state head with
          | none =>
              simp [hHead] at hLower
          | some headResult =>
              rcases headResult with ⟨lowerHead, stateHead⟩
              have hHeadNo :=
                stmt_toFunctionsListFuel?_noCallCreate hHeadSafe hHead
              cases hRest :
                  Stmt.List.toFunctionsFuel? fuel stateHead rest with
              | none =>
                  simp [hHead, hRest] at hLower
              | some restResult =>
                  rcases restResult with ⟨lowerRest, stateRest⟩
                  have hRestNo :=
                    stmtList_toFunctionsFuel?_noCallCreate hRestSafe hRest
                  simp [hHead, hRest] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  exact functionsStmtList_append hHeadNo hRestNo

  theorem caseList_toFunctionsFuel?_noCallCreate
      {safeCases : List (Word × List AstStmt)} {fuel : Nat}
      {state state' : Fresh.State}
      {lower : List (Word × Functions.Block)}
      (hSafe : Reference.Safe.casesSafe safeCases)
      (hLower :
        Stmt.CaseList.toFunctionsFuel? fuel state safeCases =
          some (lower, state')) :
      Functions.CaseList.usesCallCreate lower = false := by
    cases fuel with
    | zero =>
        simp [Stmt.CaseList.toFunctionsFuel?] at hLower
    | succ fuel =>
      cases safeCases with
      | nil =>
          unfold Stmt.CaseList.toFunctionsFuel? at hLower
          simp at hLower
          rcases hLower with ⟨hLower, _hState⟩
          rw [hLower]
          rfl
      | cons head rest =>
          rcases head with ⟨value, body⟩
          rcases hSafe with ⟨hBodySafe, hRestSafe⟩
          unfold Stmt.CaseList.toFunctionsFuel? at hLower
          cases hBody : Stmt.List.toBlockFuel? fuel state body with
          | none =>
              simp [hBody] at hLower
          | some bodyResult =>
              rcases bodyResult with ⟨lowerBody, stateBody⟩
              have hBodyNo :=
                block_toFunctionsFuel?_noCallCreate hBodySafe hBody
              cases hRest :
                  Stmt.CaseList.toFunctionsFuel? fuel stateBody rest with
              | none =>
                  simp [hBody, hRest] at hLower
              | some restResult =>
                  rcases restResult with ⟨lowerRest, stateRest⟩
                  have hRestNo :=
                    caseList_toFunctionsFuel?_noCallCreate hRestSafe hRest
                  simp [hBody, hRest] at hLower
                  rcases hLower with ⟨hLower, _hState⟩
                  rw [← hLower]
                  simp [Functions.CaseList.usesCallCreate, hBodyNo, hRestNo]

  theorem block_toFunctionsFuel?_noCallCreate
      {safeStmts : List AstStmt} {fuel : Nat} {state state' : Fresh.State}
      {lower : Functions.Block}
      (hSafe : Reference.Safe.stmts safeStmts)
      (hLower :
        Stmt.List.toBlockFuel? fuel state safeStmts =
          some (lower, state')) :
      lower.usesCallCreate = false := by
    cases fuel with
    | zero =>
        simp [Stmt.List.toBlockFuel?] at hLower
    | succ fuel =>
      unfold Stmt.List.toBlockFuel? at hLower
      cases hList :
          Stmt.List.toFunctionsFuel? fuel state safeStmts with
      | none =>
          simp [hList] at hLower
      | some listResult =>
          rcases listResult with ⟨lowerList, stateList⟩
          simp [hList] at hLower
          rcases hLower with ⟨hLower, _hState⟩
          rw [← hLower]
          exact block_of_stmts_noCallCreate
            (stmtList_toFunctionsFuel?_noCallCreate hSafe hList)
end

theorem functionDefinition_toFunDefFuel?_noCallCreate
    {fn : AstFunctionDefinition} {fuel : Nat} {state state' : Fresh.State}
    {name : Name} {lower : Functions.FunDef}
    (hSafe : Reference.Safe.functionDefinition fn)
    (hLower :
      FunctionDefinition.toFunDefFuel? fuel state name fn =
        some (lower, state')) :
    lower.usesCallCreate = false := by
  cases fn with
  | Def params returns body =>
      unfold FunctionDefinition.toFunDefFuel? at hLower
      cases hBody : Stmt.List.toBlockFuel? fuel state body with
      | none =>
          simp [hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨lowerBody, stateBody⟩
          simp [hBody] at hLower
          rcases hLower with ⟨hLower, _hState⟩
          rw [← hLower]
          simpa [Functions.FunDef.usesCallCreate] using
            block_toFunctionsFuel?_noCallCreate
              (by simpa [Reference.Safe.functionDefinition] using hSafe)
              hBody

theorem functionList_toFunDefsFuel?_noCallCreate :
    ∀ {entries : List (Name × AstFunctionDefinition)} {fuel : Nat}
      {state state' : Fresh.State} {lower : List Functions.FunDef},
      Reference.Safe.functionEntries entries →
        FunctionList.toFunDefsFuel? fuel state entries =
          some (lower, state') →
          Functions.FunList.usesCallCreate lower = false
  | [], _fuel, _state, _state', _lower, _hSafe, hLower => by
      unfold FunctionList.toFunDefsFuel? at hLower
      simp at hLower
      rcases hLower with ⟨hLower, _hState⟩
      rw [hLower]
      rfl
  | (name, fn) :: rest, fuel, state, state', lower, hSafe, hLower => by
      rcases hSafe with ⟨hFnSafe, hRestSafe⟩
      unfold FunctionList.toFunDefsFuel? at hLower
      cases hFn :
          FunctionDefinition.toFunDefFuel? fuel state name fn with
      | none =>
          simp [hFn] at hLower
      | some fnResult =>
          rcases fnResult with ⟨lowerFn, stateFn⟩
          have hFnNo :=
            functionDefinition_toFunDefFuel?_noCallCreate hFnSafe hFn
          cases hRest :
              FunctionList.toFunDefsFuel? fuel stateFn rest with
          | none =>
              simp [hFn, hRest] at hLower
          | some restResult =>
              rcases restResult with ⟨lowerRest, stateRest⟩
              have hRestNo :=
                functionList_toFunDefsFuel?_noCallCreate hRestSafe hRest
              simp [hFn, hRest] at hLower
              rcases hLower with ⟨hLower, _hState⟩
              rw [← hLower]
              simp [Functions.FunList.usesCallCreate, hFnNo, hRestNo]

theorem contract_toObjects?_functions_noCallCreate
    {contract : AstContract} {obj : Objects.Program}
    (hSafe : Reference.Safe.contract contract)
    (hLower : Contract.toObjects? contract = some obj) :
    obj.toFunctions.usesCallCreate = false := by
  unfold Contract.toObjects? at hLower
  cases hBody :
      Stmt.toFunctionsList? (Fresh.initial (Contract.names contract))
        contract.dispatcher with
  | none =>
      simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨bodyStmts, stateAfterBody⟩
      cases hFns :
          FunctionList.toFunDefs? stateAfterBody
            (Contract.functionEntries contract) with
      | none =>
          simp [hBody, hFns] at hLower
      | some fnResult =>
          rcases fnResult with ⟨functions, stateAfterFns⟩
          simp [hBody, hFns] at hLower
          rw [← hLower]
          rcases hSafe with ⟨hDispatcherSafe, hFnsSafe⟩
          have hBodyNo :
              Functions.StmtList.usesCallCreate bodyStmts = false :=
            stmt_toFunctionsListFuel?_noCallCreate hDispatcherSafe hBody
          have hFnsNo :
              Functions.FunList.usesCallCreate functions = false := by
            unfold FunctionList.toFunDefs? at hFns
            exact functionList_toFunDefsFuel?_noCallCreate hFnsSafe hFns
          simp [Objects.Program.toFunctions, Objects.Object.toFunctions,
            Functions.Program.usesCallCreate]
          exact ⟨hFnsNo, block_of_stmts_noCallCreate hBodyNo⟩

theorem program_toObjects?_functions_noCallCreate
    {program : Program} {obj : Objects.Program}
    (hAccepted : Reference.Accepted program)
    (hLower : program.toObjects? = some obj) :
    obj.toFunctions.usesCallCreate = false :=
  contract_toObjects?_functions_noCallCreate
    (by simpa [Reference.Safe.program] using
      Reference.safeProgram_of_accepted hAccepted)
    hLower

theorem compileChecked?_noCallCreate
    {program : Program} {asm : Assembly.Program}
    (hAccepted : Reference.Accepted program)
    (hCompile : Program.compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Program.compileChecked?_noCallCreate_of_loweredFunctions
    (fun obj hLower =>
      program_toObjects?_functions_noCallCreate hAccepted hLower)
    hCompile

end NoCallCreate

end Yul
end EvmCompiler
