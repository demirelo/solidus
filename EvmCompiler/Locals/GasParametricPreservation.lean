import EvmCompiler.Locals.Preservation

namespace EvmCompiler
namespace Locals
namespace Direct

set_option maxHeartbeats 1800000 in
mutual
  theorem Block.runOpenWithGasOracle_toExpressions_exists
      (program : Program) (lower : Expressions.Program)
      (hLower : program.toExpressions? = some lower) :
      ∀ {ctx : Ctx} {fuel : Nat} {block : Block} {state : RunState}
        {outcome : Outcome} {runCtx compileCtx : Ctx}
        {code : List Expressions.Stmt} {oracle : Structured.GasOracle}
        {cursor cursorFinal : Nat},
        Locals.Block.compileOpen ctx block = some (code, compileCtx) →
        Block.runOpenWithGasOracle program ctx oracle fuel block cursor state =
          .ok (outcome, runCtx, cursorFinal) →
        (outcome.mode = .regular → runCtx = compileCtx) ∧
          ∃ lowerFuel,
            Expressions.Block.runWithGasOracle lower oracle lowerFuel
                { stmts := code } cursor state =
              .ok (outcome, cursorFinal) := by
    intro ctx fuel block state outcome runCtx compileCtx code oracle cursor
      cursorFinal hCompile hRun
    cases fuel with
    | zero =>
        simp [Block.runOpenWithGasOracle, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                simp [Locals.Block.compileOpen] at hCompile
                cases hCompile
                simp [Block.runOpenWithGasOracle] at hRun
                cases hRun
                constructor
                · intro _h
                  simp_all
                · exact ⟨1, by simp_all [Expressions.Block.runWithGasOracle]⟩
            | cons stmt rest =>
                simp [Locals.Block.compileOpen] at hCompile
                cases hStmtCompile : Locals.Stmt.compile ctx stmt with
                | none =>
                    simp [hStmtCompile] at hCompile
                | some stmtCompiled =>
                    rcases stmtCompiled with ⟨stmtCode, stmtCtx⟩
                    cases hRestCompile :
                        Locals.Block.compileOpen stmtCtx { stmts := rest } with
                    | none =>
                        simp [hStmtCompile, hRestCompile] at hCompile
                    | some restCompiled =>
                        rcases restCompiled with ⟨restCode, restCtx⟩
                        simp [hStmtCompile, hRestCompile] at hCompile
                        cases hCompile
                        subst code
                        subst compileCtx
                        unfold Block.runOpenWithGasOracle at hRun
                        cases hStmtRun :
                            Stmt.runWithGasOracle program ctx oracle fuel stmt
                              cursor state with
                        | error err =>
                            simp [hStmtRun] at hRun
                        | ok stmtResult =>
                            rcases stmtResult with
                              ⟨stmtOutcome, stmtRunCtx, cursorAfterStmt⟩
                            simp [hStmtRun] at hRun
                            have hStmtBridge :=
                              Stmt.runWithGasOracle_toExpressions_exists program lower hLower
                                hStmtCompile hStmtRun
                            rcases hStmtBridge with
                              ⟨hStmtCtx, hStmtLower⟩
                            cases hMode : stmtOutcome.mode with
                            | regular =>
                                simp [hMode] at hRun
                                have hCtxEq : stmtRunCtx = stmtCtx :=
                                  hStmtCtx hMode
                                subst stmtRunCtx
                                cases hRestRun :
                                    Block.runOpenWithGasOracle program stmtCtx
                                      oracle fuel { stmts := rest }
                                      cursorAfterStmt stmtOutcome.state with
                                | error err =>
                                    simp [hRestRun] at hRun
                                | ok restResult =>
                                    rcases restResult with
                                      ⟨restOutcome, restRunCtx,
                                        cursorAfterRest⟩
                                    simp [hRestRun] at hRun
                                    rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                                    rcases hRestEq with
                                      ⟨hRunCtxEq, hCursorEq⟩
                                    subst outcome
                                    subst runCtx
                                    subst cursorFinal
                                    have hRestBridge :=
                                      Block.runOpenWithGasOracle_toExpressions_exists program
                                        lower hLower hRestCompile hRestRun
                                    rcases hRestBridge with
                                      ⟨hRestCtx, hRestLower⟩
                                    constructor
                                    · intro hRegular
                                      exact hRestCtx hRegular
                                    · exact
                                        let hStmtLowerRegular :
                                          ∃ lowerFuel,
                                              Expressions.Block.runWithGasOracle lower
                                                  oracle lowerFuel
                                                  { stmts := stmtCode } cursor
                                                  state =
                                                .ok
                                                  (Outcome.regular
                                                    stmtOutcome.state,
                                                    cursorAfterStmt) := by
                                          rcases hStmtLower with ⟨lf, hLf⟩
                                          refine ⟨lf, ?_⟩
                                          rw [outcome_eq_regular_of_mode hMode]
                                            at hLf
                                          exact hLf
                                        Expressions.Block.runWithGasOracle_append_regular_exists
                                          lower stmtCode restCode state
                                          stmtOutcome.state restOutcome oracle
                                          cursor cursorAfterStmt cursorAfterRest
                                          hStmtLowerRegular hRestLower
                            | brk =>
                                simp [hMode] at hRun
                                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                                subst outcome
                                subst runCtx
                                subst cursorFinal
                                constructor
                                · intro hRegular
                                  simp [hMode] at hRegular
                                · exact
                                    by
                                      simpa using
                                        Expressions.Block.runWithGasOracle_append_nonregular_exists
                                          lower stmtCode restCode state stmtOutcome
                                          oracle cursor cursorAfterStmt
                                          hStmtLower (by simp [hMode])
                            | cont =>
                                simp [hMode] at hRun
                                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                                subst outcome
                                subst runCtx
                                subst cursorFinal
                                constructor
                                · intro hRegular
                                  simp [hMode] at hRegular
                                · exact
                                    by
                                      simpa using
                                        Expressions.Block.runWithGasOracle_append_nonregular_exists
                                          lower stmtCode restCode state stmtOutcome
                                          oracle cursor cursorAfterStmt
                                          hStmtLower (by simp [hMode])
                            | leave =>
                                simp [hMode] at hRun
                                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                                subst outcome
                                subst runCtx
                                subst cursorFinal
                                constructor
                                · intro hRegular
                                  simp [hMode] at hRegular
                                · exact
                                    by
                                      simpa using
                                        Expressions.Block.runWithGasOracle_append_nonregular_exists
                                          lower stmtCode restCode state stmtOutcome
                                          oracle cursor cursorAfterStmt
                                          hStmtLower (by simp [hMode])
                            | halt kind =>
                                simp [hMode] at hRun
                                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                                subst outcome
                                subst runCtx
                                subst cursorFinal
                                constructor
                                · intro hRegular
                                  simp [hMode] at hRegular
                                · exact
                                    by
                                      simpa using
                                        Expressions.Block.runWithGasOracle_append_nonregular_exists
                                          lower stmtCode restCode state stmtOutcome
                                          oracle cursor cursorAfterStmt
                                          hStmtLower (by simp [hMode])
  termination_by
    _ctx fuel block _state _outcome _runCtx _compileCtx _code _hCompile
      _hRun => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScopedWithGasOracle_toExpressions_exists
      (program : Program) (lower : Expressions.Program)
      (hLower : program.toExpressions? = some lower) :
      ∀ {ctx : Ctx} {fuel : Nat} {block : Block} {state : RunState}
        {outcome : Outcome} {lowerBlock : Expressions.Block}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        Locals.Block.compile ctx block = some lowerBlock →
        Block.runScopedWithGasOracle program ctx block oracle fuel cursor state =
          .ok (outcome, cursorFinal) →
        ∃ lowerFuel,
          Expressions.Block.runWithGasOracle lower oracle lowerFuel lowerBlock
              cursor state =
            .ok (outcome, cursorFinal) := by
    intro ctx fuel block state outcome lowerBlock oracle cursor cursorFinal
      hCompile hRun
    unfold Locals.Block.compile at hCompile
    cases hOpen : Locals.Block.compileOpen ctx block with
    | none =>
        simp [hOpen] at hCompile
    | some compiled =>
        rcases compiled with ⟨code, finalCtx⟩
        cases hFinish : finishScoped ctx finalCtx code with
        | none =>
            simp [hOpen, hFinish] at hCompile
        | some finished =>
            simp [hOpen, hFinish] at hCompile
            cases hCompile
            unfold Block.runScopedWithGasOracle at hRun
            cases hOpenRun :
                Block.runOpenWithGasOracle program ctx oracle fuel block cursor
                  state with
            | error err =>
                simp [hOpenRun] at hRun
            | ok openResult =>
                rcases openResult with
                  ⟨openOutcome, runCtx, cursorAfterOpen⟩
                simp [hOpenRun] at hRun
                have hOpenBridge :=
                  Block.runOpenWithGasOracle_toExpressions_exists program lower hLower
                    hOpen hOpenRun
                rcases hOpenBridge with ⟨hRunCtx, hOpenLower⟩
                cases hMode : openOutcome.mode with
                | regular =>
                    simp [hMode] at hRun
                    have hCtxEq : runCtx = finalCtx := hRunCtx hMode
                    subst runCtx
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        cases hCleanupRun :
                            Ctx.runCleanupToWithGasOracle finalCtx
                              ctx.layout.length oracle cursorAfterOpen
                              openOutcome.state with
                        | error err =>
                            simp [hCleanupRun] at hRun
                        | ok cleaned =>
                            rcases cleaned with ⟨cleaned, cursorAfterCleanup⟩
                            simp [hCleanupRun] at hRun
                            rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                            subst outcome
                            subst cursorFinal
                            have hCleanupCode :
                                Structured.Code.runStateWithGasOracle cleanup
                                  oracle cursorAfterOpen openOutcome.state =
                                    .ok (cleaned, cursorAfterCleanup) := by
                              unfold Ctx.runCleanupToWithGasOracle at hCleanupRun
                              simp [hCleanup] at hCleanupRun
                              exact hCleanupRun
                            exact
                              let hOpenLowerRegular :
                                  ∃ lowerFuel,
                                    Expressions.Block.runWithGasOracle lower
                                        oracle lowerFuel { stmts := code }
                                        cursor state =
                                      .ok
                                        (Outcome.regular openOutcome.state,
                                          cursorAfterOpen) := by
                                    rcases hOpenLower with ⟨lf, hLf⟩
                                    refine ⟨lf, ?_⟩
                                    rw [outcome_eq_regular_of_mode hMode] at hLf
                                    exact hLf
                              Expressions.Block.runWithGasOracle_append_regular_exists lower
                                code (codeStmt cleanup) state openOutcome.state
                                (Outcome.regular cleaned) oracle cursor
                                cursorAfterOpen cursorAfterCleanup
                                hOpenLowerRegular
                                (codeStmt_runWithGasOracle_exists lower cleanup
                                  oracle cursorAfterOpen openOutcome.state
                                  cleaned cursorAfterCleanup hCleanupCode)
                | brk =>
                    simp [hMode] at hRun
                    rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                    subst outcome
                    subst cursorFinal
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        exact
                          by
                            simpa using
                              Expressions.Block.runWithGasOracle_append_nonregular_exists lower
                                code (codeStmt cleanup) state openOutcome oracle
                                cursor cursorAfterOpen hOpenLower
                                (by simp [hMode])
                | cont =>
                    simp [hMode] at hRun
                    rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                    subst outcome
                    subst cursorFinal
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        exact
                          by
                            simpa using
                              Expressions.Block.runWithGasOracle_append_nonregular_exists lower
                                code (codeStmt cleanup) state openOutcome oracle
                                cursor cursorAfterOpen hOpenLower
                                (by simp [hMode])
                | leave =>
                    simp [hMode] at hRun
                    rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                    subst outcome
                    subst cursorFinal
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        exact
                          by
                            simpa using
                              Expressions.Block.runWithGasOracle_append_nonregular_exists lower
                                code (codeStmt cleanup) state openOutcome oracle
                                cursor cursorAfterOpen hOpenLower
                                (by simp [hMode])
                | halt kind =>
                    simp [hMode] at hRun
                    rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                    subst outcome
                    subst cursorFinal
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        exact
                          by
                            simpa using
                              Expressions.Block.runWithGasOracle_append_nonregular_exists lower
                                code (codeStmt cleanup) state openOutcome oracle
                                cursor cursorAfterOpen hOpenLower
                                (by simp [hMode])
  termination_by
    _ctx fuel block _state _outcome _lowerBlock _hCompile _hRun =>
      (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem Stmt.runForLoopWithGasOracle_toExpressions_exists
      (program : Program) (lower : Expressions.Program)
      (hLower : program.toExpressions? = some lower) :
      ∀ {loopCtx postBase bodyBase : Ctx} {fuel : Nat}
        {cond : Expr 1} {lowerCond : Expressions.Expr 1}
        {post body : Block} {lowerPost lowerBody : Expressions.Block}
        {state : RunState} {outcome : Outcome}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        Locals.Expr.compile loopCtx cond = some lowerCond →
        Locals.Block.compile postBase post = some lowerPost →
        Locals.Block.compile bodyBase body = some lowerBody →
        Stmt.runForLoopWithGasOracle program loopCtx cond postBase post bodyBase
            body oracle fuel cursor state = .ok (outcome, cursorFinal) →
        ∃ lowerFuel,
          Expressions.Stmt.runForLoopWithGasOracle lower oracle lowerFuel
            lowerCond lowerPost lowerBody cursor state =
              .ok (outcome, cursorFinal) := by
    intro loopCtx postBase bodyBase fuel cond lowerCond post body lowerPost
      lowerBody state outcome oracle cursor cursorFinal hCond hPost hBody hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoopWithGasOracle, invalid, Structured.invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoopWithGasOracle at hRun
        rw [Expr.runConditionWithGasOracle_eq_compile loopCtx cond lowerCond
            oracle cursor state hCond]
          at hRun
        cases hCondRun :
            Expressions.Expr.runConditionStateWithGasOracle lowerCond oracle cursor
              state with
        | error err =>
            simp [hCondRun] at hRun
        | ok condResult =>
            rcases condResult with
              ⟨stateAfterCond, condTrue, cursorAfterCond⟩
            cases condTrue with
            | false =>
                simp [hCondRun] at hRun
                rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                subst outcome
                subst cursorFinal
                exact
                  ⟨1, by
                    simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun]⟩
            | true =>
                simp [hCondRun] at hRun
                cases hBodyRun :
                    Block.runScopedWithGasOracle program bodyBase body oracle
                      fuel cursorAfterCond stateAfterCond with
                | error err =>
                    simp [hBodyRun] at hRun
                | ok bodyOutcome =>
                    rcases bodyOutcome with ⟨bodyOutcome, cursorAfterBody⟩
                    simp [hBodyRun] at hRun
                    rcases
                      Block.runScopedWithGasOracle_toExpressions_exists program lower hLower
                        hBody hBodyRun with
                    ⟨bodyFuel, hBodyLower⟩
                    cases hBodyMode : bodyOutcome.mode with
                    | brk =>
                        simp [hBodyMode] at hRun
                        rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                        subst outcome
                        subst cursorFinal
                        refine ⟨Nat.max bodyFuel fuel + 1, ?_⟩
                        have hBodyLower' :
                            Expressions.Block.runWithGasOracle lower
                                oracle (Nat.max bodyFuel fuel) lowerBody
                                cursorAfterCond stateAfterCond =
                                  .ok (bodyOutcome, cursorAfterBody) :=
                          Expressions.Block.runWithGasOracle_mono lower
                            (Nat.le_max_left _ _) hBodyLower
                        simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                          hBodyLower', hBodyMode]
                    | regular =>
                        simp [hBodyMode] at hRun
                        cases hPostRun :
                            Block.runScopedWithGasOracle program postBase post
                              oracle fuel cursorAfterBody bodyOutcome.state with
                        | error err =>
                            simp [hPostRun] at hRun
                        | ok postOutcome =>
                            rcases postOutcome with
                              ⟨postOutcome, cursorAfterPost⟩
                            simp [hPostRun] at hRun
                            rcases
                              Block.runScopedWithGasOracle_toExpressions_exists program lower
                                hLower hPost hPostRun with
                            ⟨postFuel, hPostLower⟩
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPostMode] at hRun
                                rcases
                                  Stmt.runForLoopWithGasOracle_toExpressions_exists program
                                    lower hLower hCond hPost hBody hRun with
                                ⟨loopFuel, hLoopLower⟩
                                refine
                                  ⟨Nat.max bodyFuel (Nat.max postFuel loopFuel) + 1,
                                    ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerBody cursorAfterCond
                                        stateAfterCond =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerPost cursorAfterBody
                                        bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_trans (Nat.le_max_left _ _)
                                      (Nat.le_max_right _ _)) hPostLower
                                have hLoopLower' :
                                    Expressions.Stmt.runForLoopWithGasOracle lower
                                        oracle (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerCond lowerPost lowerBody
                                        cursorAfterPost postOutcome.state =
                                      .ok (outcome, cursorFinal) :=
                                  Expressions.Stmt.runForLoopWithGasOracle_mono lower
                                    (Nat.le_trans (Nat.le_max_right _ _)
                                      (Nat.le_max_right _ _)) hLoopLower
                                simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode, hLoopLower']
                            | brk =>
                                simp [hPostMode, invalid, Structured.invalid]
                                  at hRun
                            | cont =>
                                simp [hPostMode, invalid, Structured.invalid]
                                  at hRun
                            | leave =>
                                simp [hPostMode] at hRun
                                rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                                subst outcome
                                subst cursorFinal
                                refine ⟨Nat.max bodyFuel postFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel postFuel)
                                        lowerBody cursorAfterCond
                                        stateAfterCond =
                                          .ok (bodyOutcome, cursorAfterBody) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel postFuel)
                                        lowerPost cursorAfterBody
                                        bodyOutcome.state =
                                          .ok (postOutcome, cursorAfterPost) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_right _ _) hPostLower
                                simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode]
                            | halt kind =>
                                simp [hPostMode] at hRun
                                rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                                subst outcome
                                subst cursorFinal
                                refine ⟨Nat.max bodyFuel postFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel postFuel)
                                        lowerBody cursorAfterCond
                                        stateAfterCond =
                                          .ok (bodyOutcome, cursorAfterBody) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel postFuel)
                                        lowerPost cursorAfterBody
                                        bodyOutcome.state =
                                          .ok (postOutcome, cursorAfterPost) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_right _ _) hPostLower
                                simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode]
                    | cont =>
                        simp [hBodyMode] at hRun
                        cases hPostRun :
                            Block.runScopedWithGasOracle program postBase post
                              oracle fuel cursorAfterBody bodyOutcome.state with
                        | error err =>
                            simp [hPostRun] at hRun
                        | ok postOutcome =>
                            rcases postOutcome with
                              ⟨postOutcome, cursorAfterPost⟩
                            simp [hPostRun] at hRun
                            rcases
                              Block.runScopedWithGasOracle_toExpressions_exists program lower
                                hLower hPost hPostRun with
                            ⟨postFuel, hPostLower⟩
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPostMode] at hRun
                                rcases
                                  Stmt.runForLoopWithGasOracle_toExpressions_exists program
                                    lower hLower hCond hPost hBody hRun with
                                ⟨loopFuel, hLoopLower⟩
                                refine
                                  ⟨Nat.max bodyFuel (Nat.max postFuel loopFuel) + 1,
                                    ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerBody cursorAfterCond
                                        stateAfterCond =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerPost cursorAfterBody
                                        bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_trans (Nat.le_max_left _ _)
                                      (Nat.le_max_right _ _)) hPostLower
                                have hLoopLower' :
                                    Expressions.Stmt.runForLoopWithGasOracle lower
                                        oracle (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerCond lowerPost lowerBody
                                        cursorAfterPost postOutcome.state =
                                      .ok (outcome, cursorFinal) :=
                                  Expressions.Stmt.runForLoopWithGasOracle_mono lower
                                    (Nat.le_trans (Nat.le_max_right _ _)
                                      (Nat.le_max_right _ _)) hLoopLower
                                simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode, hLoopLower']
                            | brk =>
                                simp [hPostMode, invalid, Structured.invalid]
                                  at hRun
                            | cont =>
                                simp [hPostMode, invalid, Structured.invalid]
                                  at hRun
                            | leave =>
                                simp [hPostMode] at hRun
                                rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                                subst outcome
                                subst cursorFinal
                                refine ⟨Nat.max bodyFuel postFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel postFuel)
                                        lowerBody cursorAfterCond
                                        stateAfterCond =
                                          .ok (bodyOutcome, cursorAfterBody) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel postFuel)
                                        lowerPost cursorAfterBody
                                        bodyOutcome.state =
                                          .ok (postOutcome, cursorAfterPost) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_right _ _) hPostLower
                                simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode]
                            | halt kind =>
                                simp [hPostMode] at hRun
                                rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                                subst outcome
                                subst cursorFinal
                                refine ⟨Nat.max bodyFuel postFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel postFuel)
                                        lowerBody cursorAfterCond
                                        stateAfterCond =
                                          .ok (bodyOutcome, cursorAfterBody) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.runWithGasOracle lower
                                        oracle (Nat.max bodyFuel postFuel)
                                        lowerPost cursorAfterBody
                                        bodyOutcome.state =
                                          .ok (postOutcome, cursorAfterPost) :=
                                  Expressions.Block.runWithGasOracle_mono lower
                                    (Nat.le_max_right _ _) hPostLower
                                simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode]
                    | leave =>
                        simp [hBodyMode] at hRun
                        rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                        subst outcome
                        subst cursorFinal
                        refine ⟨Nat.max bodyFuel fuel + 1, ?_⟩
                        have hBodyLower' :
                            Expressions.Block.runWithGasOracle lower oracle
                                (Nat.max bodyFuel fuel) lowerBody
                                cursorAfterCond stateAfterCond =
                              .ok (bodyOutcome, cursorAfterBody) :=
                          Expressions.Block.runWithGasOracle_mono lower
                            (Nat.le_max_left _ _) hBodyLower
                        simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                          hBodyLower', hBodyMode]
                    | halt kind =>
                        simp [hBodyMode] at hRun
                        rcases hRun with ⟨hOutcomeEq, hCursorEq⟩
                        subst outcome
                        subst cursorFinal
                        refine ⟨Nat.max bodyFuel fuel + 1, ?_⟩
                        have hBodyLower' :
                            Expressions.Block.runWithGasOracle lower oracle
                                (Nat.max bodyFuel fuel) lowerBody
                                cursorAfterCond stateAfterCond =
                              .ok (bodyOutcome, cursorAfterBody) :=
                          Expressions.Block.runWithGasOracle_mono lower
                            (Nat.le_max_left _ _) hBodyLower
                        simp [Expressions.Stmt.runForLoopWithGasOracle, hCondRun,
                          hBodyLower', hBodyMode]
  termination_by
    _loopCtx _postBase _bodyBase fuel _cond _lowerCond _post _body
      _lowerPost _lowerBody _state _outcome _hCond _hPost _hBody _hRun =>
      (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runWithGasOracle_toExpressions_exists
      (program : Program) (lower : Expressions.Program)
      (hLower : program.toExpressions? = some lower) :
      ∀ {ctx : Ctx} {fuel : Nat} {stmt : Stmt} {state : RunState}
        {outcome : Outcome} {runCtx compileCtx : Ctx}
        {code : List Expressions.Stmt} {oracle : Structured.GasOracle}
        {cursor cursorFinal : Nat},
        Locals.Stmt.compile ctx stmt = some (code, compileCtx) →
        Stmt.runWithGasOracle program ctx oracle fuel stmt cursor state =
          .ok (outcome, runCtx, cursorFinal) →
        (outcome.mode = .regular → runCtx = compileCtx) ∧
          ∃ lowerFuel,
            Expressions.Block.runWithGasOracle lower oracle lowerFuel
                { stmts := code } cursor state =
              .ok (outcome, cursorFinal) := by
    intro ctx fuel stmt state outcome runCtx compileCtx code oracle cursor
      cursorFinal hCompile hRun
    cases stmt with
    | expr expr =>
        unfold Locals.Stmt.compile at hCompile
        cases hCode : Locals.Expr.compileCode ctx 0 expr with
        | none =>
            simp [hCode] at hCompile
        | some exprCode =>
            simp [hCode] at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.runWithGasOracle at hRun
            simp [Stmt.runWithGasOracle] at hRun
            rw [Expr.runStateWithGasOracle_eq_compileCode ctx expr exprCode
                oracle cursor state hCode]
              at hRun
            cases hCodeRun :
                Structured.Code.runStateWithGasOracle exprCode oracle cursor
                  state with
            | error err =>
                simp [hCodeRun] at hRun
            | ok statePair =>
                rcases statePair with ⟨state', cursorAfterExpr⟩
                simp [hCodeRun] at hRun
                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                subst outcome
                subst runCtx
                subst cursorFinal
                constructor
                · intro _h
                  simp_all
                · simpa using
                    codeStmt_runWithGasOracle_exists lower exprCode oracle cursor
                      state state' cursorAfterExpr hCodeRun
    | exprs exprs =>
        unfold Locals.Stmt.compile at hCompile
        cases hCode : Locals.ExprSeq.compileCode ctx 0 exprs with
        | none =>
            simp [hCode] at hCompile
        | some exprsCode =>
            simp [hCode] at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.runWithGasOracle at hRun
            simp [Stmt.runWithGasOracle] at hRun
            rw [Expr.ExprSeq.runCodeWithGasOracle_eq_compileCode_zero ctx exprs exprsCode
                oracle cursor state.evm hCode] at hRun
            cases hCodeRun :
                Structured.Code.runWithGasOracle exprsCode oracle cursor
                  state.evm with
            | error err =>
                simp [hCodeRun] at hRun
            | ok evmPair =>
                rcases evmPair with ⟨evmAfterExprs, cursorAfterExprs⟩
                simp [hCodeRun] at hRun
                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                subst outcome
                subst runCtx
                subst cursorFinal
                have hCodeRunState :
                    Structured.Code.runStateWithGasOracle exprsCode oracle cursor
                        state =
                      .ok (state.withEVM evmAfterExprs, cursorAfterExprs) := by
                  unfold Structured.Code.runStateWithGasOracle
                  simp [hCodeRun]
                constructor
                · intro _h
                  simp_all
                · simpa using
                    codeStmt_runWithGasOracle_exists lower exprsCode oracle
                      cursor state (state.withEVM evmAfterExprs)
                      cursorAfterExprs hCodeRunState
    | let_ name value =>
        unfold Locals.Stmt.compile at hCompile
        cases hCode : Locals.Expr.compileCode ctx 0 value with
        | none =>
            simp [hCode] at hCompile
        | some valueCode =>
            simp [hCode] at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.runWithGasOracle at hRun
            simp [Stmt.runWithGasOracle] at hRun
            rw [Expr.runStateWithGasOracle_eq_compileCode ctx value valueCode
                oracle cursor state hCode]
              at hRun
            cases hCodeRun :
                Structured.Code.runStateWithGasOracle valueCode oracle cursor
                  state with
            | error err =>
                simp [hCodeRun] at hRun
            | ok statePair =>
                rcases statePair with ⟨state', cursorAfterValue⟩
                simp [hCodeRun] at hRun
                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                subst outcome
                subst runCtx
                subst cursorFinal
                constructor
                · intro _h
                  simp_all
                · simpa using
                    codeStmt_runWithGasOracle_exists lower valueCode oracle
                      cursor state state' cursorAfterValue hCodeRun
    | assign name value =>
        unfold Locals.Stmt.compile at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hValueCode : Locals.Expr.compileCode ctx 0 value with
            | none =>
                simp [hDepth, hValueCode] at hCompile
            | some valueCode =>
                cases hSwap : StackOp.swap? depth with
                | none =>
                    simp [hDepth, hValueCode, hSwap] at hCompile
                | some swapOp =>
                    simp [hDepth, hValueCode, hSwap] at hCompile
                    cases hCompile
                    subst code
                    subst compileCtx
                    unfold Stmt.runWithGasOracle at hRun
                    simp [Stmt.runWithGasOracle] at hRun
                    rw [Expr.runCodeWithGasOracle_eq_compileCode ctx 0 value valueCode
                        oracle cursor state.evm hValueCode] at hRun
                    cases hValueRun :
                        Structured.Code.runWithGasOracle valueCode oracle cursor
                          state.evm with
                    | error err =>
                        simp [hDepth, hSwap, hValueRun] at hRun
                    | ok valuePair =>
                        rcases valuePair with
                          ⟨evmAfterValue, cursorAfterValue⟩
                        cases hSwapRun :
                            swapOp.stepWithGasOracle oracle cursorAfterValue
                              evmAfterValue with
                        | error err =>
                            simp [hDepth, hSwap, hValueRun, hSwapRun] at hRun
                        | ok swapPair =>
                            rcases swapPair with
                              ⟨evmAfterSwap, cursorAfterSwap⟩
                            cases hPopRun :
                                Structured.BasicOp.pop.stepWithGasOracle oracle
                                  cursorAfterSwap evmAfterSwap with
                            | error err =>
                                simp [hDepth, hSwap, hValueRun, hSwapRun,
                                  hPopRun] at hRun
                            | ok popPair =>
                                rcases popPair with
                                  ⟨evmAfterPop, cursorAfterPop⟩
                                simp [hDepth, hSwap, hValueRun, hSwapRun,
                                  hPopRun] at hRun
                                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                                subst outcome
                                subst runCtx
                                subst cursorFinal
                                have hCodeRun :
                                    Structured.Code.runStateWithGasOracle
                                        (valueCode ++
                                          [Structured.BasicInstr.op swapOp,
                                            Structured.BasicInstr.op .pop])
                                        oracle cursor state =
                                      .ok (state.withEVM evmAfterPop,
                                        cursorAfterPop) := by
                                  unfold Structured.Code.runStateWithGasOracle
                                  rw [code_runWithGasOracle_append]
                                  simp [hValueRun, Structured.Code.runWithGasOracle,
                                    Structured.BasicInstr.stepWithGasOracle, hSwapRun,
                                    hPopRun]
                                constructor
                                · intro _h
                                  simp_all
                                · simpa using
                                    codeStmt_runWithGasOracle_exists lower
                                      (valueCode ++
                                        [Structured.BasicInstr.op swapOp,
                                          Structured.BasicInstr.op .pop])
                                      oracle cursor state
                                      (state.withEVM evmAfterPop)
                                      cursorAfterPop hCodeRun
    | assignTop name =>
        unfold Locals.Stmt.compile at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hSwap : StackOp.swap? depth with
            | none =>
                simp [hDepth, hSwap] at hCompile
            | some swapOp =>
                simp [hDepth, hSwap] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.runWithGasOracle at hRun
                simp [Stmt.runWithGasOracle] at hRun
                cases hSwapRun :
                    swapOp.stepWithGasOracle oracle cursor state.evm with
                | error err =>
                    simp [hDepth, hSwap, hSwapRun] at hRun
                | ok swapPair =>
                    rcases swapPair with ⟨evmAfterSwap, cursorAfterSwap⟩
                    cases hPopRun :
                        Structured.BasicOp.pop.stepWithGasOracle oracle
                          cursorAfterSwap evmAfterSwap with
                    | error err =>
                        simp [hDepth, hSwap, hSwapRun, hPopRun] at hRun
                    | ok popPair =>
                        rcases popPair with ⟨evmAfterPop, cursorAfterPop⟩
                        simp [hDepth, hSwap, hSwapRun, hPopRun] at hRun
                        rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                        rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                        subst outcome
                        subst runCtx
                        subst cursorFinal
                        have hCodeRun :
                            Structured.Code.runStateWithGasOracle
                                [Structured.BasicInstr.op swapOp,
                                  Structured.BasicInstr.op .pop] oracle cursor
                                state =
                              .ok (state.withEVM evmAfterPop,
                                cursorAfterPop) := by
                          unfold Structured.Code.runStateWithGasOracle
                          simp [Structured.Code.runWithGasOracle, Structured.BasicInstr.stepWithGasOracle,
                            hSwapRun, hPopRun]
                        constructor
                        · intro _h
                          simp_all
                        · simpa using
                            codeStmt_runWithGasOracle_exists lower
                              [Structured.BasicInstr.op swapOp,
                                Structured.BasicInstr.op .pop]
                              oracle cursor state (state.withEVM evmAfterPop)
                              cursorAfterPop hCodeRun
    | assignTopWithOffset offset name =>
        unfold Locals.Stmt.compile at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hSwap : StackOp.swap? (offset + depth) with
            | none =>
                simp [hDepth, hSwap] at hCompile
            | some swapOp =>
                simp [hDepth, hSwap] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.runWithGasOracle at hRun
                simp [Stmt.runWithGasOracle] at hRun
                cases hSwapRun :
                    swapOp.stepWithGasOracle oracle cursor state.evm with
                | error err =>
                    simp [hDepth, hSwap, hSwapRun] at hRun
                | ok swapPair =>
                    rcases swapPair with ⟨evmAfterSwap, cursorAfterSwap⟩
                    cases hPopRun :
                        Structured.BasicOp.pop.stepWithGasOracle oracle
                          cursorAfterSwap evmAfterSwap with
                    | error err =>
                        simp [hDepth, hSwap, hSwapRun, hPopRun] at hRun
                    | ok popPair =>
                        rcases popPair with ⟨evmAfterPop, cursorAfterPop⟩
                        simp [hDepth, hSwap, hSwapRun, hPopRun] at hRun
                        rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                        rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                        subst outcome
                        subst runCtx
                        subst cursorFinal
                        have hCodeRun :
                            Structured.Code.runStateWithGasOracle
                                [Structured.BasicInstr.op swapOp,
                                  Structured.BasicInstr.op .pop] oracle cursor
                                state =
                              .ok (state.withEVM evmAfterPop,
                                cursorAfterPop) := by
                          unfold Structured.Code.runStateWithGasOracle
                          simp [Structured.Code.runWithGasOracle, Structured.BasicInstr.stepWithGasOracle,
                            hSwapRun, hPopRun]
                        constructor
                        · intro _h
                          simp_all
                        · simpa using
                            codeStmt_runWithGasOracle_exists lower
                              [Structured.BasicInstr.op swapOp,
                                Structured.BasicInstr.op .pop]
                              oracle cursor state (state.withEVM evmAfterPop)
                              cursorAfterPop hCodeRun
    | block body =>
        unfold Locals.Stmt.compile at hCompile
        cases hOpen : Locals.Block.compileOpen ctx body with
        | none =>
            simp [hOpen] at hCompile
        | some compiled =>
            rcases compiled with ⟨bodyCode, bodyCtx⟩
            cases hFinish : finishScoped ctx bodyCtx bodyCode with
            | none =>
                simp [hOpen, hFinish] at hCompile
            | some lowerBody =>
                simp [hOpen, hFinish] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.runWithGasOracle at hRun
                simp [Stmt.runWithGasOracle] at hRun
                cases hBodyRun :
                    Block.runScopedWithGasOracle program ctx body oracle fuel
                      cursor state with
                | error err =>
                    simp [hBodyRun] at hRun
                | ok bodyPair =>
                    rcases bodyPair with ⟨bodyOutcome, cursorAfterBody⟩
                    simp [hBodyRun] at hRun
                    rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                    rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                    subst outcome
                    subst runCtx
                    subst cursorFinal
                    have hBodyCompile :
                        Locals.Block.compile ctx body = some lowerBody := by
                      simp [Locals.Block.compile, hOpen, hFinish]
                    constructor
                    · intro _h
                      simp_all
                    · rcases
                        Block.runScopedWithGasOracle_toExpressions_exists program lower
                          hLower hBodyCompile hBodyRun with
                      ⟨lf, hLf⟩
                      refine ⟨lf, ?_⟩
                      cases lowerBody
                      simpa using hLf
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Locals.Stmt.compile at hCompile
            cases hCond : Locals.Expr.compile ctx cond with
            | none =>
                simp [hCond] at hCompile
            | some lowerCond =>
                cases hOpen : Locals.Block.compileOpen ctx body with
                | none =>
                    simp [hCond, hOpen] at hCompile
                | some compiledBody =>
                    rcases compiledBody with ⟨bodyCode, bodyCtx⟩
                    cases hFinish :
                        finishScoped ctx bodyCtx bodyCode with
                    | none =>
                        simp [hCond, hOpen, hFinish] at hCompile
                    | some lowerBody =>
                        simp [hCond, hOpen, hFinish] at hCompile
                        cases hCompile
                        subst code
                        subst compileCtx
                        unfold Stmt.runWithGasOracle at hRun
                        rw [Expr.runConditionWithGasOracle_eq_compile ctx cond
                            lowerCond oracle cursor state hCond] at hRun
                        cases hCondRun :
                            Expressions.Expr.runConditionStateWithGasOracle
                              lowerCond oracle cursor state with
                        | error err =>
                            simp [hCondRun] at hRun
                        | ok condResult =>
                            rcases condResult with
                              ⟨stateAfterCond, condTrue, cursorAfterCond⟩
                            cases condTrue with
                            | false =>
                                simp [hCondRun] at hRun
                                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                                subst outcome
                                subst runCtx
                                subst cursorFinal
                                constructor
                                · intro _h
                                  simp_all
                                · refine
                                    Expressions.Block.runWithGasOracle_single_exists lower
                                      ⟨1, ?_⟩
                                  simp [Expressions.Stmt.runWithGasOracle, hCondRun]
                            | true =>
                                simp [hCondRun] at hRun
                                cases hBodyRun :
                                    Block.runScopedWithGasOracle program ctx body
                                      oracle fuel cursorAfterCond
                                      stateAfterCond with
                                | error err =>
                                    simp [hBodyRun] at hRun
                                | ok bodyPair =>
                                    rcases bodyPair with
                                      ⟨bodyOutcome, cursorAfterBody⟩
                                    simp [hBodyRun] at hRun
                                    rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                                    rcases hRestEq with
                                      ⟨hRunCtxEq, hCursorEq⟩
                                    subst outcome
                                    subst runCtx
                                    subst cursorFinal
                                    have hBodyCompile :
                                        Locals.Block.compile ctx body =
                                          some lowerBody := by
                                      simp [Locals.Block.compile, hOpen, hFinish]
                                    rcases
                                      Block.runScopedWithGasOracle_toExpressions_exists program
                                        lower hLower hBodyCompile hBodyRun with
                                    ⟨bodyFuel, hBodyLower⟩
                                    constructor
                                    · intro _h
                                      simp_all
                                    · refine
                                        Expressions.Block.runWithGasOracle_single_exists lower
                                          ⟨bodyFuel + 1, ?_⟩
                                      have hBodyLower' :
                                          Expressions.Block.runWithGasOracle lower
                                              oracle bodyFuel lowerBody
                                              cursorAfterCond stateAfterCond =
                                            .ok (bodyOutcome,
                                              cursorAfterBody) := hBodyLower
                                      simp [Expressions.Stmt.runWithGasOracle, hCondRun,
                                        hBodyLower']
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Locals.Stmt.compile at hCompile
            cases hScrutinee : Locals.Expr.compile ctx scrutinee with
            | none =>
                simp [hScrutinee] at hCompile
            | some lowerScrutinee =>
                cases hCases :
                    Locals.CaseList.compile ctx cases with
                | none =>
                    simp [hScrutinee, hCases] at hCompile
                | some lowerCases =>
                    cases hDefault :
                        Locals.Default.compile ctx defaultBody with
                    | none =>
                        simp [hScrutinee, hCases, hDefault] at hCompile
                    | some lowerDefault =>
                        simp [hScrutinee, hCases, hDefault] at hCompile
                        cases hCompile
                        subst code
                        subst compileCtx
                        unfold Stmt.runWithGasOracle at hRun
                        simp [Stmt.runWithGasOracle] at hRun
                        rw [Expr.runStateWithGasOracle_eq_compile ctx scrutinee
                            lowerScrutinee oracle cursor state hScrutinee]
                          at hRun
                        unfold Expressions.Expr.runStateWithGasOracle at hRun
                        cases hScrutineeRun :
                            Expressions.Expr.runWithGasOracle lowerScrutinee
                              oracle cursor state.evm with
                        | error err =>
                            simp [hScrutineeRun] at hRun
                        | ok scrutineePair =>
                            rcases scrutineePair with
                              ⟨evmAfterScrutinee, cursorAfterScrutinee⟩
                            cases hPop : evmAfterScrutinee.stack.pop with
                            | none =>
                                simp [hScrutineeRun, hPop] at hRun
                            | some popped =>
                                rcases popped with ⟨stack, value⟩
                                let stateAfterPop :=
                                  state.withEVM
                                    { evmAfterScrutinee with stack := stack }
                                have hSelectLower :=
                                  Switch.select_toExpressions?
                                    (ctx := ctx) (cases := cases)
                                    (defaultBody := defaultBody) (value := value)
                                    hCases hDefault
                                cases hSelected :
                                    Switch.select value cases defaultBody with
                                | none =>
                                    simp [hScrutineeRun, hPop, hSelected] at hRun
                                    rcases hRun with
                                      ⟨hOutcomeEq, hRestEq⟩
                                    rcases hRestEq with
                                      ⟨hRunCtxEq, hCursorEq⟩
                                    subst outcome
                                    subst runCtx
                                    subst cursorFinal
                                    constructor
                                    · intro _h
                                      simp_all
                                    · refine
                                        Expressions.Block.runWithGasOracle_single_exists lower
                                          ⟨1, ?_⟩
                                      simp [Expressions.Stmt.runWithGasOracle,
                                        hScrutineeRun, hPop, hSelectLower,
                                        hSelected]
                                | some selected =>
                                    simp [hScrutineeRun, hPop, hSelected] at hRun
                                    rcases
                                      Switch.select_compile_some
                                        (ctx := ctx) (cases := cases)
                                        (defaultBody := defaultBody)
                                        (lowerCases := lowerCases)
                                        (lowerDefault := lowerDefault)
                                        (value := value) (body := selected)
                                        hCases hDefault hSelected with
                                    ⟨lowerSelected, hSelectedCompile,
                                      hSelectLowerSome⟩
                                    cases hBodyRun :
                                        Block.runScopedWithGasOracle program ctx selected
                                          oracle fuel cursorAfterScrutinee
                                          stateAfterPop with
                                    | error err =>
                                        simp [stateAfterPop, hBodyRun] at hRun
                                    | ok bodyPair =>
                                        rcases bodyPair with
                                          ⟨bodyOutcome, cursorAfterBody⟩
                                        simp [stateAfterPop, hBodyRun] at hRun
                                        rcases hRun with
                                          ⟨hOutcomeEq, hRestEq⟩
                                        rcases hRestEq with
                                          ⟨hRunCtxEq, hCursorEq⟩
                                        subst outcome
                                        subst runCtx
                                        subst cursorFinal
                                        rcases
                                          Block.runScopedWithGasOracle_toExpressions_exists
                                            program lower hLower
                                            hSelectedCompile hBodyRun with
                                        ⟨bodyFuel, hBodyLower⟩
                                        constructor
                                        · intro _h
                                          simp_all
                                        · refine
                                            Expressions.Block.runWithGasOracle_single_exists
                                              lower ⟨bodyFuel + 1, ?_⟩
                                          have hBodyLower' :
                                              Expressions.Block.runWithGasOracle lower
                                                  oracle bodyFuel lowerSelected
                                                  cursorAfterScrutinee
                                                  (Structured.RunState.withEVM
                                                    state
                                                    { toSharedState :=
                                                        evmAfterScrutinee.toSharedState,
                                                      pc := evmAfterScrutinee.pc,
                                                      stack := stack,
                                                      execLength :=
                                                        evmAfterScrutinee.execLength }) =
                                                .ok (bodyOutcome,
                                                  cursorAfterBody) :=
                                            by
                                              simpa [stateAfterPop] using
                                                hBodyLower
                                          simp [Expressions.Stmt.runWithGasOracle,
                                            hScrutineeRun, hPop,
                                            hSelectLowerSome, hBodyLower']
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Locals.Stmt.compile at hCompile
            let initBase := ctx.withoutLoopControl
            cases hInitOpen :
                Locals.Block.compileOpen initBase init with
            | none =>
                simp [initBase, hInitOpen] at hCompile
            | some initCompiled =>
                rcases initCompiled with ⟨initCode, initCompileCtx⟩
                cases hCond :
                    Locals.Expr.compile initCompileCtx cond with
                | none =>
                    simp [initBase, hInitOpen, hCond] at hCompile
                | some lowerCond =>
                    let postBase := initCompileCtx.withoutLoopControl
                    cases hPostOpen :
                        Locals.Block.compileOpen postBase post with
                    | none =>
                        simp [initBase, postBase, hInitOpen, hCond, hPostOpen]
                          at hCompile
                    | some postCompiled =>
                        rcases postCompiled with ⟨postCode, postCtx⟩
                        cases hPostFinish :
                            finishScoped postBase postCtx postCode with
                        | none =>
                            simp [initBase, postBase, hInitOpen, hCond,
                              hPostOpen, hPostFinish] at hCompile
                        | some lowerPost =>
                            let bodyBase :=
                              initCompileCtx.withLoopControl
                                initCompileCtx.layout.length
                            cases hBodyOpen :
                                Locals.Block.compileOpen bodyBase body with
                            | none =>
                                simp [initBase, postBase, bodyBase, hInitOpen,
                                  hCond, hPostOpen, hPostFinish, hBodyOpen]
                                  at hCompile
                            | some bodyCompiled =>
                                rcases bodyCompiled with ⟨bodyCode, bodyCtx⟩
                                cases hBodyFinish :
                                    finishScoped bodyBase bodyCtx bodyCode with
                                | none =>
                                    simp [initBase, postBase, bodyBase,
                                      hInitOpen, hCond, hPostOpen, hPostFinish,
                                      hBodyOpen, hBodyFinish] at hCompile
                                | some lowerBody =>
                                    cases hCleanup :
                                        initCompileCtx.cleanupTo?
                                          ctx.layout.length with
                                    | none =>
                                        simp [initBase, postBase, bodyBase,
                                          hInitOpen, hCond, hPostOpen,
                                          hPostFinish, hBodyOpen, hBodyFinish,
                                          hCleanup] at hCompile
                                    | some cleanup =>
                                        simp [initBase, postBase, bodyBase,
                                          hInitOpen, hCond, hPostOpen,
                                          hPostFinish, hBodyOpen, hBodyFinish,
                                          hCleanup] at hCompile
                                        cases hCompile
                                        subst code
                                        subst compileCtx
                                        unfold Stmt.runWithGasOracle at hRun
                                        simp [Stmt.runWithGasOracle] at hRun
                                        cases hInitRun :
                                            Block.runOpenWithGasOracle program initBase
                                              oracle fuel init cursor state with
                                        | error err =>
                                            simp [initBase, hInitRun] at hRun
                                        | ok initResult =>
                                            rcases initResult with
                                              ⟨initOutcome, initRunCtx,
                                                cursorAfterInit⟩
                                            simp [initBase, hInitRun] at hRun
                                            have hInitBridge :=
                                              Block.runOpenWithGasOracle_toExpressions_exists
                                                program lower hLower hInitOpen
                                                hInitRun
                                            rcases hInitBridge with
                                              ⟨hInitCtx, hInitLower⟩
                                            let loopStmt :=
                                              Expressions.Stmt.for_
                                                { stmts := initCode } lowerCond
                                                lowerPost lowerBody
                                            have hPostCompile :
                                                Locals.Block.compile postBase post =
                                                  some lowerPost := by
                                              simp [Locals.Block.compile,
                                                hPostOpen, hPostFinish]
                                            have hBodyCompile :
                                                Locals.Block.compile bodyBase body =
                                                  some lowerBody := by
                                              simp [Locals.Block.compile,
                                                hBodyOpen, hBodyFinish]
                                            cases hInitMode :
                                                initOutcome.mode with
                                            | regular =>
                                                simp [hInitMode] at hRun
                                                have hCtxEq :
                                                    initRunCtx =
                                                      initCompileCtx :=
                                                  hInitCtx hInitMode
                                                subst initRunCtx
                                                cases hLoopRun :
                                                    Stmt.runForLoopWithGasOracle program
                                                      initCompileCtx cond postBase
                                                      post bodyBase body oracle fuel
                                                      cursorAfterInit
                                                      initOutcome.state with
                                                | error err =>
                                                    simp [postBase, bodyBase,
                                                      hLoopRun] at hRun
                                                | ok loopResult =>
                                                    rcases loopResult with
                                                      ⟨loopOutcome,
                                                        cursorAfterLoop⟩
                                                    simp [postBase, bodyBase,
                                                      hLoopRun] at hRun
                                                    rcases
                                                      Stmt.runForLoopWithGasOracle_toExpressions_exists
                                                        program lower hLower
                                                        hCond hPostCompile
                                                        hBodyCompile hLoopRun with
                                                    ⟨loopFuel, hLoopLower⟩
                                                    have hLoopStmtLower :
                                                        ∃ lf,
                                                          Expressions.Stmt.runWithGasOracle
                                                            lower oracle lf
                                                            loopStmt cursor state =
                                                              .ok
                                                                (loopOutcome,
                                                                  cursorAfterLoop) := by
                                                      rcases hInitLower with
                                                        ⟨initFuel, hInitLowerRun⟩
                                                      refine
                                                        ⟨Nat.max initFuel loopFuel + 1,
                                                          ?_⟩
                                                      have hInitLower' :
                                                          Expressions.Block.runWithGasOracle
                                                              lower oracle
                                                              (Nat.max initFuel
                                                                loopFuel)
                                                              { stmts := initCode }
                                                              cursor state =
                                                            .ok (initOutcome,
                                                              cursorAfterInit) :=
                                                        Expressions.Block.runWithGasOracle_mono
                                                          lower
                                                          (Nat.le_max_left _ _)
                                                          hInitLowerRun
                                                      have hLoopLower' :
                                                          Expressions.Stmt.runForLoopWithGasOracle
                                                              lower oracle
                                                              (Nat.max initFuel
                                                                loopFuel)
                                                              lowerCond lowerPost
                                                              lowerBody
                                                              cursorAfterInit
                                                              initOutcome.state =
                                                            .ok (loopOutcome,
                                                              cursorAfterLoop) :=
                                                        Expressions.Stmt.runForLoopWithGasOracle_mono
                                                          lower
                                                          (Nat.le_max_right _ _)
                                                          hLoopLower
                                                      simp [loopStmt,
                                                        Expressions.Stmt.runWithGasOracle,
                                                        hInitLower',
                                                        hInitMode, hLoopLower']
                                                    cases hLoopMode :
                                                        loopOutcome.mode with
                                                    | regular =>
                                                        simp [hLoopMode] at hRun
                                                        cases hCleanupRun :
                                                            Ctx.runCleanupToWithGasOracle
                                                              initCompileCtx
                                                              ctx.layout.length
                                                              oracle
                                                              cursorAfterLoop
                                                              loopOutcome.state with
                                                        | error err =>
                                                            simp [hCleanupRun]
                                                              at hRun
                                                        | ok cleanupPair =>
                                                            rcases cleanupPair with
                                                              ⟨cleaned,
                                                                cursorAfterCleanup⟩
                                                            simp [hCleanupRun]
                                                              at hRun
                                                            rcases hRun with
                                                              ⟨hOutcomeEq, hRestEq⟩
                                                            rcases hRestEq with
                                                              ⟨hRunCtxEq, hCursorEq⟩
                                                            subst outcome
                                                            subst runCtx
                                                            subst cursorFinal
                                                            have hCleanupCode :
                                                                Structured.Code.runStateWithGasOracle
                                                                    cleanup oracle
                                                                    cursorAfterLoop
                                                                    loopOutcome.state =
                                                                  .ok (cleaned,
                                                                    cursorAfterCleanup) := by
                                                              unfold Ctx.runCleanupToWithGasOracle
                                                                at hCleanupRun
                                                              simp [hCleanup]
                                                                at hCleanupRun
                                                              exact hCleanupRun
                                                            have hLoopStmtLowerRegular :
                                                                ∃ lf,
                                                                  Expressions.Stmt.runWithGasOracle
                                                                    lower oracle lf
                                                                    loopStmt
                                                                    cursor state =
                                                                      .ok
                                                                        (Outcome.regular
                                                                          loopOutcome.state,
                                                                          cursorAfterLoop) := by
                                                              rcases hLoopStmtLower with
                                                                ⟨lf, hLf⟩
                                                              refine ⟨lf, ?_⟩
                                                              rw [outcome_eq_regular_of_mode
                                                                hLoopMode] at hLf
                                                              exact hLf
                                                            constructor
                                                            · intro _h
                                                              rfl
                                                            · exact
                                                                Expressions.Block.runWithGasOracle_append_regular_exists
                                                                  lower
                                                                  [loopStmt]
                                                                  (codeStmt cleanup)
                                                                  state
                                                                  loopOutcome.state
                                                                  (Outcome.regular
                                                                    cleaned)
                                                                  oracle cursor
                                                                  cursorAfterLoop
                                                                  cursorAfterCleanup
                                                                  (Expressions.Block.runWithGasOracle_single_exists
                                                                    lower
                                                                    hLoopStmtLowerRegular)
                                                                  (codeStmt_runWithGasOracle_exists
                                                                    lower cleanup oracle
                                                                    cursorAfterLoop
                                                                    loopOutcome.state
                                                                    cleaned
                                                                    cursorAfterCleanup
                                                                    hCleanupCode)
                                                    | brk =>
                                                        simp [hLoopMode,
                                                          invalid,
                                                          Structured.invalid]
                                                          at hRun
                                                    | cont =>
                                                        simp [hLoopMode,
                                                          invalid,
                                                          Structured.invalid]
                                                          at hRun
                                                    | leave =>
                                                        simp [hLoopMode] at hRun
                                                        rcases hRun with
                                                          ⟨hOutcomeEq, hRestEq⟩
                                                        rcases hRestEq with
                                                          ⟨hRunCtxEq, hCursorEq⟩
                                                        subst outcome
                                                        subst runCtx
                                                        subst cursorFinal
                                                        constructor
                                                        · intro hRegular
                                                          simp [hLoopMode]
                                                            at hRegular
                                                        · exact
                                                            Expressions.Block.runWithGasOracle_append_nonregular_exists
                                                              lower [loopStmt]
                                                              (codeStmt cleanup)
                                                              state loopOutcome
                                                              oracle cursor
                                                              cursorAfterLoop
                                                              (Expressions.Block.runWithGasOracle_single_exists
                                                                lower hLoopStmtLower)
                                                              (by simp
                                                                [hLoopMode])
                                                    | halt kind =>
                                                        simp [hLoopMode] at hRun
                                                        rcases hRun with
                                                          ⟨hOutcomeEq, hRestEq⟩
                                                        rcases hRestEq with
                                                          ⟨hRunCtxEq, hCursorEq⟩
                                                        subst outcome
                                                        subst runCtx
                                                        subst cursorFinal
                                                        constructor
                                                        · intro hRegular
                                                          simp [hLoopMode]
                                                            at hRegular
                                                        · exact
                                                            Expressions.Block.runWithGasOracle_append_nonregular_exists
                                                              lower [loopStmt]
                                                              (codeStmt cleanup)
                                                              state loopOutcome
                                                              oracle cursor
                                                              cursorAfterLoop
                                                              (Expressions.Block.runWithGasOracle_single_exists
                                                                lower hLoopStmtLower)
                                                              (by simp
                                                                [hLoopMode])
                                            | brk =>
                                                simp [hInitMode, invalid,
                                                  Structured.invalid] at hRun
                                            | cont =>
                                                simp [hInitMode, invalid,
                                                  Structured.invalid] at hRun
                                            | leave =>
                                                simp [hInitMode] at hRun
                                                rcases hRun with
                                                  ⟨hOutcomeEq, hRestEq⟩
                                                rcases hRestEq with
                                                  ⟨hRunCtxEq, hCursorEq⟩
                                                subst outcome
                                                subst runCtx
                                                subst cursorFinal
                                                have hLoopStmtLower :
                                                    ∃ lf,
                                                      Expressions.Stmt.runWithGasOracle
                                                        lower oracle lf loopStmt
                                                        cursor state =
                                                          .ok (initOutcome,
                                                            cursorAfterInit) := by
                                                  rcases hInitLower with
                                                    ⟨initFuel, hInitLowerRun⟩
                                                  refine ⟨initFuel + 1, ?_⟩
                                                  simp [loopStmt,
                                                    Expressions.Stmt.runWithGasOracle,
                                                    hInitLowerRun, hInitMode]
                                                constructor
                                                · intro hRegular
                                                  simp [hInitMode] at hRegular
                                                · exact
                                                    Expressions.Block.runWithGasOracle_append_nonregular_exists
                                                      lower [loopStmt]
                                                      (codeStmt cleanup) state
                                                      initOutcome
                                                      oracle cursor
                                                      cursorAfterInit
                                                      (Expressions.Block.runWithGasOracle_single_exists
                                                        lower hLoopStmtLower)
                                                      (by simp [hInitMode])
                                            | halt kind =>
                                                simp [hInitMode] at hRun
                                                rcases hRun with
                                                  ⟨hOutcomeEq, hRestEq⟩
                                                rcases hRestEq with
                                                  ⟨hRunCtxEq, hCursorEq⟩
                                                subst outcome
                                                subst runCtx
                                                subst cursorFinal
                                                have hLoopStmtLower :
                                                    ∃ lf,
                                                      Expressions.Stmt.runWithGasOracle
                                                        lower oracle lf loopStmt
                                                        cursor state =
                                                          .ok (initOutcome,
                                                            cursorAfterInit) := by
                                                  rcases hInitLower with
                                                    ⟨initFuel, hInitLowerRun⟩
                                                  refine ⟨initFuel + 1, ?_⟩
                                                  simp [loopStmt,
                                                    Expressions.Stmt.runWithGasOracle,
                                                    hInitLowerRun, hInitMode]
                                                constructor
                                                · intro hRegular
                                                  simp [hInitMode] at hRegular
                                                · exact
                                                    Expressions.Block.runWithGasOracle_append_nonregular_exists
                                                      lower [loopStmt]
                                                      (codeStmt cleanup) state
                                                      initOutcome
                                                      oracle cursor
                                                      cursorAfterInit
                                                      (Expressions.Block.runWithGasOracle_single_exists
                                                        lower hLoopStmtLower)
                                                      (by simp [hInitMode])
    | brk =>
        unfold Locals.Stmt.compile at hCompile
        cases hTarget : ctx.breakDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup : ctx.cleanupTo? target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.runWithGasOracle at hRun
                simp [Stmt.runWithGasOracle] at hRun
                cases hCleanupRun :
                    Ctx.runCleanupToWithGasOracle ctx target oracle cursor
                      state with
                | error err =>
                    simp [hTarget, hCleanupRun] at hRun
                | ok cleanupPair =>
                    rcases cleanupPair with ⟨cleaned, cursorAfterCleanup⟩
                    simp [hTarget, hCleanupRun] at hRun
                    rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                    rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                    subst outcome
                    subst runCtx
                    subst cursorFinal
                    have hCleanupCode :
                        Structured.Code.runStateWithGasOracle cleanup oracle
                            cursor state =
                          .ok (cleaned, cursorAfterCleanup) := by
                      unfold Ctx.runCleanupToWithGasOracle at hCleanupRun
                      simp [hCleanup] at hCleanupRun
                      exact hCleanupRun
                    constructor
                    · intro hRegular
                      simp at hRegular
                    · simpa using
                        codeStmt_append_stmt_runWithGasOracle_exists lower cleanup
                          Expressions.Stmt.brk oracle cursor cursorAfterCleanup
                          cursorAfterCleanup state cleaned (Outcome.brk cleaned)
                          hCleanupCode
                          ⟨1, by simp [Expressions.Stmt.runWithGasOracle]⟩
    | cont =>
        unfold Locals.Stmt.compile at hCompile
        cases hTarget : ctx.continueDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup : ctx.cleanupTo? target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.runWithGasOracle at hRun
                simp [Stmt.runWithGasOracle] at hRun
                cases hCleanupRun :
                    Ctx.runCleanupToWithGasOracle ctx target oracle cursor
                      state with
                | error err =>
                    simp [hTarget, hCleanupRun] at hRun
                | ok cleanupPair =>
                    rcases cleanupPair with ⟨cleaned, cursorAfterCleanup⟩
                    simp [hTarget, hCleanupRun] at hRun
                    rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                    rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                    subst outcome
                    subst runCtx
                    subst cursorFinal
                    have hCleanupCode :
                        Structured.Code.runStateWithGasOracle cleanup oracle
                            cursor state =
                          .ok (cleaned, cursorAfterCleanup) := by
                      unfold Ctx.runCleanupToWithGasOracle at hCleanupRun
                      simp [hCleanup] at hCleanupRun
                      exact hCleanupRun
                    constructor
                    · intro hRegular
                      simp at hRegular
                    · simpa using
                        codeStmt_append_stmt_runWithGasOracle_exists lower cleanup
                          Expressions.Stmt.cont oracle cursor cursorAfterCleanup
                          cursorAfterCleanup state cleaned
                          (Outcome.cont cleaned) hCleanupCode
                          ⟨1, by simp [Expressions.Stmt.runWithGasOracle]⟩
    | leave =>
        unfold Locals.Stmt.compile at hCompile
        cases hTarget : ctx.leaveDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup : ctx.cleanupToPreserving? ctx.leaveRetc target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.runWithGasOracle at hRun
                simp [Stmt.runWithGasOracle] at hRun
                cases hCleanupRun :
                    Ctx.runCleanupToPreservingWithGasOracle ctx ctx.leaveRetc
                      target oracle cursor state with
                | error err =>
                    simp [hTarget, hCleanupRun] at hRun
                | ok cleanupPair =>
                    rcases cleanupPair with ⟨cleaned, cursorAfterCleanup⟩
                    cases hReturns : cleaned.returns with
                    | nil =>
                        simp [hTarget, hCleanupRun, hReturns, invalid,
                          Structured.invalid] at hRun
                    | cons frame rest =>
                        simp [hTarget, hCleanupRun, hReturns] at hRun
                        rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                        rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                        subst outcome
                        subst runCtx
                        subst cursorFinal
                        have hCleanupCode :
                            Structured.Code.runStateWithGasOracle cleanup oracle
                                cursor state =
                              .ok (cleaned, cursorAfterCleanup) := by
                          unfold Ctx.runCleanupToPreservingWithGasOracle at hCleanupRun
                          simp [hCleanup] at hCleanupRun
                          exact hCleanupRun
                        constructor
                        · intro hRegular
                          simp at hRegular
                        · simpa using
                            codeStmt_append_stmt_runWithGasOracle_exists lower cleanup
                              Expressions.Stmt.leave oracle cursor
                              cursorAfterCleanup cursorAfterCleanup state cleaned
                              (Outcome.leave cleaned) hCleanupCode
                              ⟨1, by simp [Expressions.Stmt.runWithGasOracle, hReturns]⟩
    | call name =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Locals.Stmt.compile at hCompile
            simp at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.runWithGasOracle at hRun
            simp [Stmt.runWithGasOracle] at hRun
            cases hLookup : ProcList.lookup? name program.procs with
            | none =>
                simp [hLookup, invalid, Structured.invalid] at hRun
            | some proc =>
                cases hSplit :
                    Structured.StackFrame.splitArgs? proc.argc state.evm.stack with
                | none =>
                    simp [hLookup, hSplit] at hRun
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    let callState :=
                      (state.withEVM { state.evm with stack := args }).pushReturn
                        callerStack proc.retc
                    let entryCtx :=
                      Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc
                    cases hBodyRun :
                        Block.runOpenWithGasOracle program entryCtx oracle fuel
                          proc.body cursor callState with
                    | error err =>
                        simp [entryCtx, hLookup, hSplit, callState, hBodyRun]
                          at hRun
                    | ok bodyResult =>
                        rcases bodyResult with
                          ⟨bodyOutcome, bodyCtx, cursorAfterBody⟩
                        simp [entryCtx, hLookup, hSplit, callState, hBodyRun]
                          at hRun
                        have hLowerProcs :=
                          Locals.Program.procs_toExpressions_of_toExpressions?
                            hLower
                        rcases
                          ProcList.lookup?_toExpressions?
                            hLowerProcs hLookup with
                        ⟨lowerProc, hLowerLookup, hProcLower⟩
                        rcases Proc.toExpressions?_body hProcLower with
                          ⟨hProcBody, hProcName, hProcArgc, hProcRetc⟩
                        change Locals.Block.compileToPreserving entryCtx
                          proc.retc 0 proc.body =
                          some lowerProc.body at hProcBody
                        unfold Locals.Block.compileToPreserving at hProcBody
                        cases hProcOpen :
                            Locals.Block.compileOpen entryCtx proc.body with
                        | none =>
                            simp [hProcOpen] at hProcBody
                        | some bodyCompiled =>
                            rcases bodyCompiled with
                              ⟨bodyCode, bodyCompileCtx⟩
                            cases hProcFinish :
                                finishToPreserving bodyCompileCtx proc.retc 0
                                  bodyCode with
                            | none =>
                                simp [hProcOpen, hProcFinish] at hProcBody
                            | some lowerBody =>
                                simp [hProcOpen, hProcFinish] at hProcBody
                                cases hProcBody
                                have hOpenBridge :=
                                  Block.runOpenWithGasOracle_toExpressions_exists program
                                    lower hLower hProcOpen hBodyRun
                                rcases hOpenBridge with
                                  ⟨hBodyCtx, hBodyLowerOpen⟩
                                have hBodyLowerNonregular
                                    (hNon : bodyOutcome.mode ≠ .regular) :
                                    ∃ lowerFuel,
                                      Expressions.Block.runWithGasOracle lower oracle
                                        lowerFuel lowerProc.body cursor callState =
                                          .ok (bodyOutcome, cursorAfterBody) := by
                                  unfold finishToPreserving at hProcFinish
                                  cases hCleanup :
                                      bodyCompileCtx.cleanupToPreserving?
                                        proc.retc 0 with
                                  | none =>
                                      simp [hCleanup] at hProcFinish
                                  | some cleanup =>
                                      simp [hCleanup] at hProcFinish
                                      rcases
                                        Expressions.Block.runWithGasOracle_append_nonregular_exists
                                          lower bodyCode (codeStmt cleanup)
                                          callState bodyOutcome oracle cursor
                                          cursorAfterBody hBodyLowerOpen hNon with
                                      ⟨lf, hLf⟩
                                      exact ⟨lf, by simpa [hProcFinish] using hLf⟩
                                cases hBodyMode : bodyOutcome.mode with
                                | regular =>
                                    simp [hBodyMode] at hRun
                                    have hCtxEq :
                                        bodyCtx = bodyCompileCtx := hBodyCtx hBodyMode
                                    subst bodyCtx
                                    unfold finishToPreserving at hProcFinish
                                    cases hCleanup :
                                        bodyCompileCtx.cleanupToPreserving?
                                          proc.retc 0 with
                                    | none =>
                                        simp [hCleanup] at hProcFinish
                                    | some cleanup =>
                                        simp [hCleanup] at hProcFinish
                                        cases hCleanupRun :
                                            Ctx.runCleanupToPreservingWithGasOracle
                                              bodyCompileCtx proc.retc 0 oracle
                                              cursorAfterBody bodyOutcome.state with
                                        | error err =>
                                            simp [hCleanupRun] at hRun
                                        | ok cleanupPair =>
                                            rcases cleanupPair with
                                              ⟨cleaned, cursorAfterCleanup⟩
                                            simp [hCleanupRun] at hRun
                                            have hCleanupCode :
                                                Structured.Code.runStateWithGasOracle cleanup
                                                  oracle cursorAfterBody
                                                  bodyOutcome.state =
                                                    .ok (cleaned,
                                                      cursorAfterCleanup) := by
                                              unfold Ctx.runCleanupToPreservingWithGasOracle
                                                at hCleanupRun
                                              simp [hCleanup] at hCleanupRun
                                              exact hCleanupRun
                                            have hBodyLowerRegularOpen :
                                                ∃ lowerFuel,
                                                  Expressions.Block.runWithGasOracle lower
                                                    oracle lowerFuel
                                                    { stmts := bodyCode } cursor
                                                    callState =
                                                      .ok
                                                        (Outcome.regular
                                                          bodyOutcome.state,
                                                          cursorAfterBody) := by
                                              rcases hBodyLowerOpen with ⟨lf, hLf⟩
                                              refine ⟨lf, ?_⟩
                                              rw [outcome_eq_regular_of_mode hBodyMode]
                                                at hLf
                                              exact hLf
                                            have hBodyLower :
                                                ∃ lowerFuel,
                                                  Expressions.Block.runWithGasOracle lower
                                                    oracle lowerFuel
                                                    lowerProc.body cursor callState =
                                                      .ok (Outcome.regular cleaned,
                                                        cursorAfterCleanup) :=
                                              by
                                                rcases
                                                  Expressions.Block.runWithGasOracle_append_regular_exists
                                                    lower bodyCode (codeStmt cleanup)
                                                    callState bodyOutcome.state
                                                    (Outcome.regular cleaned)
                                                    oracle cursor cursorAfterBody
                                                    cursorAfterCleanup
                                                    hBodyLowerRegularOpen
                                                    (codeStmt_runWithGasOracle_exists lower cleanup
                                                      oracle cursorAfterBody
                                                      bodyOutcome.state cleaned
                                                      cursorAfterCleanup
                                                      hCleanupCode) with
                                                ⟨lf, hLf⟩
                                                exact ⟨lf,
                                                  by simpa [hProcFinish] using hLf⟩
                                            cases hPopReturn : cleaned.popReturn? with
                                            | none =>
                                                simp [hPopReturn, invalid,
                                                  Structured.invalid] at hRun
                                            | some popResult =>
                                                rcases popResult with
                                                  ⟨frame, returned⟩
                                                cases hAttach :
                                                    Structured.StackFrame.attachReturns?
                                                      frame cleaned.evm.stack with
                                                | none =>
                                                    simp [hPopReturn, hAttach, invalid,
                                                      Structured.invalid] at hRun
                                                | some stack =>
                                                    simp [hPopReturn, hAttach] at hRun
                                                    rcases hRun with
                                                      ⟨hOutcomeEq, hRestEq⟩
                                                    rcases hRestEq with
                                                      ⟨hRunCtxEq, hCursorEq⟩
                                                    subst outcome
                                                    subst runCtx
                                                    subst cursorFinal
                                                    constructor
                                                    · intro _h
                                                      simp_all
                                                    · rcases hBodyLower with
                                                        ⟨bodyFuel, hBodyLower⟩
                                                      refine
                                                        Expressions.Block.runWithGasOracle_single_exists
                                                          lower ⟨bodyFuel + 1, ?_⟩
                                                      simp [Expressions.Stmt.runWithGasOracle,
                                                        hLowerLookup, hProcArgc,
                                                        hProcRetc, hSplit, callState,
                                                        hBodyLower, hPopReturn, hAttach]
                                | brk =>
                                    simp [hBodyMode, invalid, Structured.invalid] at hRun
                                | cont =>
                                    simp [hBodyMode, invalid, Structured.invalid] at hRun
                                | leave =>
                                    simp [hBodyMode] at hRun
                                    have hBodyLower :=
                                      hBodyLowerNonregular (by simp [hBodyMode])
                                    cases hPopReturn : bodyOutcome.state.popReturn? with
                                    | none =>
                                        simp [hPopReturn, invalid, Structured.invalid]
                                          at hRun
                                    | some popResult =>
                                        rcases popResult with ⟨frame, returned⟩
                                        cases hAttach :
                                            Structured.StackFrame.attachReturns? frame
                                              bodyOutcome.state.evm.stack with
                                        | none =>
                                            simp [hPopReturn, hAttach, invalid,
                                              Structured.invalid] at hRun
                                        | some stack =>
                                            simp [hPopReturn, hAttach] at hRun
                                            rcases hRun with
                                              ⟨hOutcomeEq, hRestEq⟩
                                            rcases hRestEq with
                                              ⟨hRunCtxEq, hCursorEq⟩
                                            subst outcome
                                            subst runCtx
                                            subst cursorFinal
                                            constructor
                                            · intro _h
                                              simp_all
                                            · rcases hBodyLower with
                                                ⟨bodyFuel, hBodyLower⟩
                                              refine
                                                Expressions.Block.runWithGasOracle_single_exists lower
                                                  ⟨bodyFuel + 1, ?_⟩
                                              simp [Expressions.Stmt.runWithGasOracle, hLowerLookup,
                                                hProcArgc, hProcRetc, hSplit,
                                                callState, hBodyLower, hBodyMode,
                                                hPopReturn, hAttach]
                                | halt kind =>
                                    simp [hBodyMode] at hRun
                                    have hBodyLower :=
                                      hBodyLowerNonregular (by simp [hBodyMode])
                                    rcases hRun with
                                      ⟨hOutcomeEq, hRestEq⟩
                                    rcases hRestEq with
                                      ⟨hRunCtxEq, hCursorEq⟩
                                    subst outcome
                                    subst runCtx
                                    subst cursorFinal
                                    constructor
                                    · intro hRegular
                                      simp [hBodyMode] at hRegular
                                    · rcases hBodyLower with ⟨bodyFuel, hBodyLower⟩
                                      refine
                                        Expressions.Block.runWithGasOracle_single_exists lower
                                          ⟨bodyFuel + 1, ?_⟩
                                      simp [Expressions.Stmt.runWithGasOracle, hLowerLookup,
                                        hProcArgc, hProcRetc, hSplit, callState,
                                        hBodyLower, hBodyMode]
    | terminal kind =>
            unfold Locals.Stmt.compile at hCompile
            simp at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.runWithGasOracle at hRun
            simp [Stmt.runWithGasOracle] at hRun
            cases hCleanupRun :
                Ctx.runCleanupAllWithGasOracle ctx oracle cursor state with
        | error err =>
            simp [hCleanupRun] at hRun
        | ok cleanupPair =>
            rcases cleanupPair with ⟨cleaned, cursorAfterCleanup⟩
            cases hTerminal :
                Structured.Terminal.stepWithGasOracle kind oracle
                  cursorAfterCleanup cleaned.evm with
            | error err =>
                simp [hCleanupRun, hTerminal] at hRun
            | ok terminalPair =>
                rcases terminalPair with ⟨evm, cursorAfterTerminal⟩
                simp [hCleanupRun, hTerminal] at hRun
                rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                subst outcome
                subst runCtx
                subst cursorFinal
                have hCleanupCode :
                    Structured.Code.runStateWithGasOracle ctx.cleanupAll oracle
                        cursor state =
                      .ok (cleaned, cursorAfterCleanup) := by
                  unfold Ctx.runCleanupAllWithGasOracle at hCleanupRun
                  exact hCleanupRun
                constructor
                · intro hRegular
                  simp_all
                · simpa using
                    codeStmt_append_stmt_runWithGasOracle_exists lower ctx.cleanupAll
                      (Expressions.Stmt.terminal kind) oracle cursor
                      cursorAfterCleanup cursorAfterTerminal state cleaned
                      (Outcome.halt kind (cleaned.withEVM evm)) hCleanupCode
                      ⟨1, by simp [Expressions.Stmt.runWithGasOracle, hTerminal]⟩
    | terminalArgs kind args =>
        unfold Locals.Stmt.compile at hCompile
        cases hArgsCode : Locals.ExprSeq.compileCode ctx 0 args with
        | none =>
            simp [hArgsCode] at hCompile
        | some argsCode =>
            simp [hArgsCode] at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.runWithGasOracle at hRun
            simp [Stmt.runWithGasOracle] at hRun
            rw [Expr.ExprSeq.runCodeWithGasOracle_eq_compileCode_zero ctx args
                argsCode oracle cursor state.evm hArgsCode] at hRun
            cases hArgsRun :
                Structured.Code.runWithGasOracle argsCode oracle cursor
                  state.evm with
            | error err =>
                simp [hArgsRun] at hRun
            | ok argsPair =>
                rcases argsPair with ⟨evmAfterArgs, cursorAfterArgs⟩
                cases hTerminal :
                    Structured.Terminal.stepWithGasOracle kind oracle
                      cursorAfterArgs evmAfterArgs with
                | error err =>
                    simp [hArgsRun, hTerminal] at hRun
                | ok terminalPair =>
                    rcases terminalPair with ⟨evm, cursorAfterTerminal⟩
                    simp [hArgsRun, hTerminal] at hRun
                    rcases hRun with ⟨hOutcomeEq, hRestEq⟩
                    rcases hRestEq with ⟨hRunCtxEq, hCursorEq⟩
                    subst outcome
                    subst runCtx
                    subst cursorFinal
                    have hArgsCodeRun :
                        Structured.Code.runStateWithGasOracle argsCode oracle
                            cursor state =
                          .ok (state.withEVM evmAfterArgs, cursorAfterArgs) := by
                      unfold Structured.Code.runStateWithGasOracle
                      simp [hArgsRun]
                    constructor
                    · intro hRegular
                      simp_all
                    · simpa using
                        codeStmt_append_stmt_runWithGasOracle_exists lower argsCode
                          (Expressions.Stmt.terminal kind) oracle cursor
                          cursorAfterArgs cursorAfterTerminal state
                          (state.withEVM evmAfterArgs)
                          (Outcome.halt kind (state.withEVM evm)) hArgsCodeRun
                          ⟨1, by simp [Expressions.Stmt.runWithGasOracle, hTerminal]⟩
  termination_by
    _ctx fuel stmt _state _outcome _runCtx _compileCtx _code _hCompile
      _hRun => (fuel, 3, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

theorem runStateWithGasOracle_toExpressions_exists {program : Program}
    {lower : Expressions.Program} {fuel : Nat} {state : RunState}
    {outcome : Outcome} {oracle : Structured.GasOracle}
    {cursor cursorFinal : Nat}
    (hLower : program.toExpressions? = some lower)
    (hRun :
      Direct.Program.runStateWithGasOracle fuel program oracle cursor state =
        .ok (outcome, cursorFinal)) :
    ∃ lowerFuel,
      Expressions.Block.runWithGasOracle lower oracle lowerFuel lower.body
        cursor state = .ok (outcome, cursorFinal) := by
  have hBody := Locals.Program.body_toExpressions_of_toExpressions? hLower
  exact
    Block.runScopedWithGasOracle_toExpressions_exists program lower hLower
      hBody hRun

theorem runWithGasOracle_toExpressions_exists {program : Program}
    {lower : Expressions.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome} {oracle : Structured.GasOracle}
    {cursor cursorFinal : Nat}
    (hLower : program.toExpressions? = some lower)
    (hRun :
      Direct.Program.runWithGasOracle fuel program oracle cursor initial =
        .ok (outcome, cursorFinal)) :
    ∃ lowerFuel,
      lower.runWithGasOracle lowerFuel oracle cursor initial =
        .ok (outcome, cursorFinal) := by
  exact runStateWithGasOracle_toExpressions_exists hLower hRun

end Program


end Direct

namespace Program

theorem runWithGasOracle_toExpressions_exists {program : Program}
    {lower : Expressions.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome} {oracle : Structured.GasOracle}
    {cursor cursorFinal : Nat}
    (hLower : program.toExpressions? = some lower)
    (hRun :
      program.runWithGasOracle fuel oracle cursor initial =
        .ok (outcome, cursorFinal)) :
    ∃ lowerFuel,
      lower.runWithGasOracle lowerFuel oracle cursor initial =
        .ok (outcome, cursorFinal) := by
  exact
    Direct.Program.runWithGasOracle_toExpressions_exists hLower
      (by simpa [Locals.Program.runWithGasOracle] using hRun)

noncomputable def compileCheckedWithGasOracle? (program : Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Expressions.Program.compileCheckedWithGasOracle? lower

theorem compileCheckedWithGasOracle?_eq_some {program : Program}
    {asm : Assembly.Program}
    (hCompile : compileCheckedWithGasOracle? program = some asm) :
    ∃ lower : Expressions.Program,
      program.toExpressions? = some lower ∧
        Expressions.Program.compileCheckedWithGasOracle? lower = some asm := by
  unfold compileCheckedWithGasOracle? at hCompile
  cases hLower : program.toExpressions? with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact ⟨lower, rfl, hCompile⟩

theorem compile_preserves_withGasOracle {program : Program}
    {lower : Expressions.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {oracle : Structured.GasOracle}
    {cursor cursorFinal : Nat} {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.GasParametric.compileCheckedWithGasOracle?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      program.runWithGasOracle fuel oracle cursor initial =
        .ok (outcome, cursorFinal)) :
    ∃ targetFuel targetOutcome,
      Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
          targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases runWithGasOracle_toExpressions_exists hLower hRun with
    ⟨lowerFuel, hLowerRun⟩
  exact
    Expressions.Program.compile_preserves_withGasOracle
      hCompile hInitialPc hLowerRun

theorem compile_preserves_of_compileCheckedWithGasOracle {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {oracle : Structured.GasOracle} {cursor cursorFinal : Nat}
    {outcome : Outcome}
    (hCompile : compileCheckedWithGasOracle? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      program.runWithGasOracle fuel oracle cursor initial =
        .ok (outcome, cursorFinal)) :
    ∃ targetFuel targetOutcome,
      Assembly.GasParametric.sourceRunNResultWithGasOracle asm oracle
          targetFuel cursor initial =
        .ok (targetOutcome, cursorFinal) ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileCheckedWithGasOracle?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  rcases runWithGasOracle_toExpressions_exists hLower hRun with
    ⟨lowerFuel, hLowerRun⟩
  exact
    Expressions.Program.compile_preserves_of_compileCheckedWithGasOracle
      hLowerCompile hInitialPc hLowerRun

end Program

end Locals
end EvmCompiler
