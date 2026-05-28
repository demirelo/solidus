import EvmCompiler.Functions.GasParametric
import EvmCompiler.Functions.Preservation
import EvmCompiler.Locals.GasParametricPreservation

namespace EvmCompiler

namespace Locals
namespace Direct

set_option maxHeartbeats 1000000 in
mutual
  theorem Block.runOpenWithGasOracle_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {block : Block}
        {state : RunState} {outcome : Outcome} {runCtx : Ctx}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        fuel ≤ fuel' →
        Block.runOpenWithGasOracle program ctx oracle fuel block cursor state =
          .ok (outcome, runCtx, cursorFinal) →
        Block.runOpenWithGasOracle program ctx oracle fuel' block cursor state =
          .ok (outcome, runCtx, cursorFinal) := by
    intro fuel fuel' ctx block state outcome runCtx oracle cursor cursorFinal hLe hRun
    cases fuel with
    | zero =>
        cases block
        simp [Block.runOpenWithGasOracle, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            cases block with
            | mk stmts =>
                cases stmts with
                | nil =>
                    simpa [Block.runOpenWithGasOracle] using hRun
                | cons stmt rest =>
                    cases hStmt :
                        Stmt.runWithGasOracle program ctx oracle fuel stmt cursor
                          state with
                    | error err =>
                        simp [Block.runOpenWithGasOracle, hStmt] at hRun
                    | ok stmtResult =>
                        rcases stmtResult with
                          ⟨stmtOutcome, stmtCtx, cursorAfterStmt⟩
                        have hStmt' :
                            Stmt.runWithGasOracle program ctx oracle fuel' stmt
                                cursor state =
                              .ok (stmtOutcome, stmtCtx, cursorAfterStmt) :=
                          Stmt.runWithGasOracle_mono program hFuelLe hStmt
                        cases hMode : stmtOutcome.mode with
                        | regular =>
                            simp [Block.runOpenWithGasOracle, hStmt, hStmt',
                              hMode] at hRun ⊢
                            exact
                              Block.runOpenWithGasOracle_mono program hFuelLe
                                hRun
                        | brk =>
                            simp [Block.runOpenWithGasOracle, hStmt, hStmt',
                              hMode] at hRun ⊢
                            exact hRun
                        | cont =>
                            simp [Block.runOpenWithGasOracle, hStmt, hStmt',
                              hMode] at hRun ⊢
                            exact hRun
                        | leave =>
                            simp [Block.runOpenWithGasOracle, hStmt, hStmt',
                              hMode] at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [Block.runOpenWithGasOracle, hStmt, hStmt',
                              hMode] at hRun ⊢
                            exact hRun
  termination_by
    fuel _fuel' _ctx block _state _outcome _runCtx _oracle _cursor
      _cursorFinal _hLe _hRun => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScopedWithGasOracle_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {block : Block}
        {state : RunState} {outcome : Outcome}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        fuel ≤ fuel' →
        Block.runScopedWithGasOracle program ctx block oracle fuel cursor state =
          .ok (outcome, cursorFinal) →
        Block.runScopedWithGasOracle program ctx block oracle fuel' cursor state =
          .ok (outcome, cursorFinal) := by
    intro fuel fuel' ctx block state outcome oracle cursor cursorFinal hLe hRun
    unfold Block.runScopedWithGasOracle at hRun ⊢
    cases hOpen :
        Block.runOpenWithGasOracle program ctx oracle fuel block cursor state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx, cursorAfterOpen⟩
        have hOpen' :
            Block.runOpenWithGasOracle program ctx oracle fuel' block cursor
                state =
              .ok (openOutcome, finalCtx, cursorAfterOpen) :=
          Block.runOpenWithGasOracle_mono program hLe hOpen
        cases hMode : openOutcome.mode with
        | regular =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | brk =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | cont =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | leave =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | halt kind =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
  termination_by
    fuel _fuel' _ctx block _state _outcome _oracle _cursor _cursorFinal _hLe
      _hRun => (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem Stmt.runForLoopWithGasOracle_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {loopCtx : Ctx} {cond : Expr 1}
        {postBase : Ctx} {post : Block} {bodyBase : Ctx} {body : Block}
        {state : RunState} {outcome : Outcome}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        fuel ≤ fuel' →
        Stmt.runForLoopWithGasOracle program loopCtx cond postBase post
            bodyBase body oracle fuel cursor state =
          .ok (outcome, cursorFinal) →
        Stmt.runForLoopWithGasOracle program loopCtx cond postBase post
            bodyBase body oracle fuel' cursor state =
          .ok (outcome, cursorFinal) := by
    intro fuel fuel' loopCtx cond postBase post bodyBase body state outcome
      oracle cursor cursorFinal hLe hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoopWithGasOracle, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold Stmt.runForLoopWithGasOracle at hRun ⊢
            cases hCond :
                Expr.runConditionWithGasOracle loopCtx cond oracle cursor
                  state with
            | error err =>
                simp [hCond] at hRun ⊢
            | ok condResult =>
                rcases condResult with
                  ⟨stateAfterCond, condTrue, cursorAfterCond⟩
                cases condTrue with
                | false =>
                    simp [hCond] at hRun ⊢
                    exact hRun
                | true =>
                    simp [hCond] at hRun ⊢
                    cases hBody :
                        Block.runScopedWithGasOracle program bodyBase body
                          oracle fuel cursorAfterCond stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyResult =>
                        rcases bodyResult with
                          ⟨bodyOutcome, cursorAfterBody⟩
                        have hBody' :
                            Block.runScopedWithGasOracle program bodyBase body
                                oracle fuel' cursorAfterCond stateAfterCond =
                              .ok (bodyOutcome, cursorAfterBody) :=
                          Block.runScopedWithGasOracle_mono program hFuelLe
                            hBody
                        cases hBodyMode : bodyOutcome.mode with
                        | brk =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | regular =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.runScopedWithGasOracle program postBase
                                  post oracle fuel cursorAfterBody
                                  bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postResult =>
                                rcases postResult with
                                  ⟨postOutcome, cursorAfterPost⟩
                                have hPost' :
                                    Block.runScopedWithGasOracle program postBase
                                        post oracle fuel' cursorAfterBody
                                        bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Block.runScopedWithGasOracle_mono program
                                    hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoopWithGasOracle_mono program
                                        hFuelLe hRun
                                | brk =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | cont =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.runScopedWithGasOracle program postBase
                                  post oracle fuel cursorAfterBody
                                  bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postResult =>
                                rcases postResult with
                                  ⟨postOutcome, cursorAfterPost⟩
                                have hPost' :
                                    Block.runScopedWithGasOracle program postBase
                                        post oracle fuel' cursorAfterBody
                                        bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Block.runScopedWithGasOracle_mono program
                                    hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoopWithGasOracle_mono program
                                        hFuelLe hRun
                                | brk =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | leave =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
  termination_by
    fuel _fuel' _loopCtx _cond _postBase _post _bodyBase _body _state
      _outcome _oracle _cursor _cursorFinal _hLe _hRun => (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runWithGasOracle_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {stmt : Stmt}
        {state : RunState} {outcome : Outcome} {runCtx : Ctx}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        fuel ≤ fuel' →
        Stmt.runWithGasOracle program ctx oracle fuel stmt cursor state =
          .ok (outcome, runCtx, cursorFinal) →
        Stmt.runWithGasOracle program ctx oracle fuel' stmt cursor state =
          .ok (outcome, runCtx, cursorFinal) := by
    intro fuel fuel' ctx stmt state outcome runCtx oracle cursor cursorFinal hLe hRun
    cases stmt with
    | expr expr =>
        simpa [Stmt.runWithGasOracle] using hRun
    | exprs exprs =>
        simpa [Stmt.runWithGasOracle] using hRun
    | let_ name value =>
        simpa [Stmt.runWithGasOracle] using hRun
    | assign name value =>
        simpa [Stmt.runWithGasOracle] using hRun
    | assignTop name =>
        simpa [Stmt.runWithGasOracle] using hRun
    | assignTopWithOffset offset name =>
        simpa [Stmt.runWithGasOracle] using hRun
    | block body =>
        unfold Stmt.runWithGasOracle at hRun ⊢
        cases hBody :
            Block.runScopedWithGasOracle program ctx body oracle fuel cursor
              state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyResult =>
            rcases bodyResult with ⟨bodyOutcome, cursorAfterBody⟩
            have hBody' :
                Block.runScopedWithGasOracle program ctx body oracle fuel'
                    cursor state =
                  .ok (bodyOutcome, cursorAfterBody) :=
              Block.runScopedWithGasOracle_mono program hLe hBody
            simp [hBody, hBody'] at hRun ⊢
            exact hRun
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.runWithGasOracle at hRun ⊢
                cases hCond :
                    Expr.runConditionWithGasOracle ctx cond oracle cursor
                      state with
                | error err =>
                    simp [hCond] at hRun ⊢
                | ok condResult =>
                    rcases condResult with
                      ⟨stateAfterCond, condTrue, cursorAfterCond⟩
                    cases condTrue with
                    | false =>
                        simp [hCond] at hRun ⊢
                        exact hRun
                    | true =>
                        simp [hCond] at hRun ⊢
                        cases hBody :
                            Block.runScopedWithGasOracle program ctx body
                              oracle fuel cursorAfterCond stateAfterCond with
                        | error err =>
                            simp [hBody] at hRun
                        | ok bodyResult =>
                            rcases bodyResult with
                              ⟨bodyOutcome, cursorAfterBody⟩
                            have hBody' :
                                Block.runScopedWithGasOracle program ctx body
                                    oracle fuel' cursorAfterCond
                                    stateAfterCond =
                                  .ok (bodyOutcome, cursorAfterBody) :=
                              Block.runScopedWithGasOracle_mono program hFuelLe
                                hBody
                            simp [hBody, hBody'] at hRun ⊢
                            exact hRun
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.runWithGasOracle at hRun ⊢
                cases hScrutinee :
                    Expr.runStateWithGasOracle ctx scrutinee oracle cursor
                      state with
                | error err =>
                    simp [hScrutinee] at hRun ⊢
                | ok scrutineeResult =>
                    rcases scrutineeResult with
                      ⟨stateAfterScrutinee, cursorAfterScrutinee⟩
                    cases hPop : stateAfterScrutinee.evm.stack.pop with
                    | none =>
                        simp [hScrutinee, hPop, invalid, Structured.invalid]
                          at hRun ⊢
                    | some pair =>
                        rcases pair with ⟨stack, value⟩
                        cases hSelected :
                            Switch.select value cases defaultBody with
                        | none =>
                            simp [hScrutinee, hPop, hSelected] at hRun ⊢
                            exact hRun
                        | some selected =>
                            simp [hScrutinee, hPop, hSelected] at hRun ⊢
                            cases hBody :
                                Block.runScopedWithGasOracle program ctx
                                  selected oracle fuel cursorAfterScrutinee
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) with
                            | error err =>
                                simp [hBody] at hRun
                            | ok bodyResult =>
                                rcases bodyResult with
                                  ⟨bodyOutcome, cursorAfterBody⟩
                                have hBody' :
                                    Block.runScopedWithGasOracle program ctx
                                      selected oracle fuel'
                                      cursorAfterScrutinee
                                      (stateAfterScrutinee.withEVM
                                        { stateAfterScrutinee.evm with
                                          stack := stack }) =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Block.runScopedWithGasOracle_mono program
                                    hFuelLe hBody
                                simp [hBody, hBody'] at hRun ⊢
                                exact hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.runWithGasOracle at hRun ⊢
                let initBase := ctx.withoutLoopControl
                cases hInit :
                    Block.runOpenWithGasOracle program initBase oracle fuel init
                      cursor state with
                | error err =>
                    simp [initBase, hInit] at hRun
                | ok initResult =>
                    rcases initResult with
                      ⟨initOutcome, initCtx, cursorAfterInit⟩
                    have hInit' :
                        Block.runOpenWithGasOracle program initBase oracle
                            fuel' init cursor state =
                          .ok (initOutcome, initCtx, cursorAfterInit) :=
                      Block.runOpenWithGasOracle_mono program hFuelLe hInit
                    cases hInitMode : initOutcome.mode with
                    | regular =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        let postBase := initCtx.withoutLoopControl
                        let bodyBase :=
                          initCtx.withLoopControl initCtx.layout.length
                        cases hLoop :
                            Stmt.runForLoopWithGasOracle program initCtx cond
                              postBase post bodyBase body oracle fuel
                              cursorAfterInit initOutcome.state with
                        | error err =>
                            simp [postBase, bodyBase, hLoop] at hRun
                        | ok loopResult =>
                            rcases loopResult with
                              ⟨loopOutcome, cursorAfterLoop⟩
                            have hLoop' :
                                Stmt.runForLoopWithGasOracle program initCtx
                                    cond postBase post bodyBase body oracle
                                    fuel' cursorAfterInit initOutcome.state =
                                  .ok (loopOutcome, cursorAfterLoop) :=
                              Stmt.runForLoopWithGasOracle_mono program
                                hFuelLe hLoop
                            cases hLoopMode : loopOutcome.mode with
                            | regular =>
                                simp [postBase, bodyBase, hLoop, hLoop',
                                  hLoopMode] at hRun ⊢
                                exact hRun
                            | brk =>
                                simp [postBase, bodyBase, hLoop, hLoop',
                                  hLoopMode] at hRun ⊢
                                exact hRun
                            | cont =>
                                simp [postBase, bodyBase, hLoop, hLoop',
                                  hLoopMode] at hRun ⊢
                                exact hRun
                            | leave =>
                                simp [postBase, bodyBase, hLoop, hLoop',
                                  hLoopMode] at hRun ⊢
                                exact hRun
                            | halt kind =>
                                simp [postBase, bodyBase, hLoop, hLoop',
                                  hLoopMode] at hRun ⊢
                                exact hRun
                    | brk =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
                    | cont =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
                    | leave =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
                    | halt kind =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
    | brk =>
        simpa [Stmt.runWithGasOracle] using hRun
    | cont =>
        simpa [Stmt.runWithGasOracle] using hRun
    | leave =>
        simpa [Stmt.runWithGasOracle] using hRun
    | call name =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.runWithGasOracle at hRun ⊢
                cases hLookup : ProcList.lookup? name program.procs with
                | none =>
                    simp [hLookup] at hRun ⊢
                    exact hRun
                | some proc =>
                    cases hSplit :
                        Structured.StackFrame.splitArgs? proc.argc
                          state.evm.stack with
                    | none =>
                        simp [hLookup, hSplit] at hRun ⊢
                    | some split =>
                        rcases split with ⟨args, callerStack⟩
                        let callState :=
                          (state.withEVM { state.evm with stack := args })
                            |>.pushReturn callerStack proc.retc
                        cases hBody :
                            Block.runOpenWithGasOracle program
                              (Ctx.procEntryWithLayoutAndRetc
                                proc.entryLayout proc.retc)
                              oracle fuel proc.body cursor callState with
                        | error err =>
                            simp [hLookup, hSplit, callState, hBody] at hRun
                        | ok bodyResult =>
                            rcases bodyResult with
                              ⟨bodyOutcome, bodyCtx, cursorAfterBody⟩
                            have hBody' :
                                Block.runOpenWithGasOracle program
                                  (Ctx.procEntryWithLayoutAndRetc
                                    proc.entryLayout proc.retc)
                                  oracle fuel' proc.body cursor callState =
                                    .ok (bodyOutcome, bodyCtx,
                                      cursorAfterBody) :=
                              Block.runOpenWithGasOracle_mono program hFuelLe
                                hBody
                            cases hBodyMode : bodyOutcome.mode <;>
                              simp [hLookup, hSplit, callState, hBody, hBody',
                                hBodyMode] at hRun ⊢ <;>
                              exact hRun
    | terminal kind =>
        simpa [Stmt.runWithGasOracle] using hRun
    | terminalArgs kind args =>
        simpa [Stmt.runWithGasOracle] using hRun
  termination_by
    fuel _fuel' _ctx stmt _state _outcome _runCtx _oracle _cursor _cursorFinal
      _hLe _hRun => (fuel, 3, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Block

theorem runOpenWithGasOracle_nil_ok {program : Program} {ctx : Ctx}
    {fuel : Nat} {state : RunState} {outcome : Outcome} {runCtx : Ctx}
    {oracle : Structured.GasOracle} {cursor cursorFinal : Nat}
    (hRun :
      Block.runOpenWithGasOracle program ctx oracle fuel { stmts := [] }
          cursor state =
        .ok (outcome, runCtx, cursorFinal)) :
    outcome = Structured.Outcome.regular state ∧ runCtx = ctx ∧
      cursorFinal = cursor := by
  cases fuel with
  | zero =>
      simp [Block.runOpenWithGasOracle, invalid, Structured.invalid] at hRun
  | succ fuel =>
      have hTriple :
          (Structured.Outcome.regular state, ctx, cursor) =
            (outcome, runCtx, cursorFinal) := by
        simpa [Block.runOpenWithGasOracle] using hRun
      injection hTriple with hOutcome hCursorPair
      injection hCursorPair with hCtx hCursor
      exact ⟨hOutcome.symm, hCtx.symm, hCursor.symm⟩

theorem runOpenWithGasOracle_append_regular_exists (program : Program) :
    ∀ (left right : List Stmt) (ctx midCtx : Ctx)
      (state mid : RunState) (outcome : Outcome) (runCtx : Ctx)
      (oracle : Structured.GasOracle)
      (cursor cursorMid cursorFinal : Nat),
      (∃ fuel,
        Block.runOpenWithGasOracle program ctx oracle fuel { stmts := left }
          cursor state =
          .ok (Structured.Outcome.regular mid, midCtx, cursorMid)) →
      (∃ fuel,
        Block.runOpenWithGasOracle program midCtx oracle fuel { stmts := right }
          cursorMid mid =
          .ok (outcome, runCtx, cursorFinal)) →
      ∃ fuel,
        Block.runOpenWithGasOracle program ctx oracle fuel
          { stmts := left ++ right } cursor state =
          .ok (outcome, runCtx, cursorFinal) := by
  intro left
  induction left with
  | nil =>
      intro right ctx midCtx state mid outcome runCtx oracle cursor cursorMid
        cursorFinal hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      rcases runOpenWithGasOracle_nil_ok hLeft with
        ⟨hOutcome, hCtx, hCursor⟩
      cases hOutcome
      cases hCtx
      cases hCursor
      simpa using hRight
  | cons stmt rest ih =>
      intro right ctx midCtx state mid outcome runCtx oracle cursor cursorMid
        cursorFinal hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.runOpenWithGasOracle, invalid, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt :
              Stmt.runWithGasOracle program ctx oracle fuelLeft stmt cursor
                state with
          | error err =>
              simp [Block.runOpenWithGasOracle, hStmt] at hLeft
          | ok stmtResult =>
              rcases stmtResult with
                ⟨stmtOutcome, stmtCtx, cursorAfterStmt⟩
              cases hMode : stmtOutcome.mode with
              | regular =>
                  simp [Block.runOpenWithGasOracle, hStmt, hMode] at hLeft
                  have hRest :
                      ∃ fuel,
                        Block.runOpenWithGasOracle program stmtCtx oracle fuel
                            { stmts := rest } cursorAfterStmt
                            stmtOutcome.state =
                          .ok (Structured.Outcome.regular mid, midCtx,
                            cursorMid) :=
                    ⟨fuelLeft, hLeft⟩
                  rcases ih right stmtCtx midCtx stmtOutcome.state mid outcome
                      runCtx oracle cursorAfterStmt cursorMid cursorFinal
                      hRest hRight with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.runWithGasOracle program ctx oracle
                          (Nat.max fuelLeft fuelRest) stmt cursor state =
                        .ok (stmtOutcome, stmtCtx, cursorAfterStmt) :=
                    Stmt.runWithGasOracle_mono program (Nat.le_max_left _ _)
                      hStmt
                  have hRestAppend' :
                      Block.runOpenWithGasOracle program stmtCtx oracle
                          (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } cursorAfterStmt
                          stmtOutcome.state =
                        .ok (outcome, runCtx, cursorFinal) :=
                    Block.runOpenWithGasOracle_mono program
                      (Nat.le_max_right _ _) hRestAppend
                  simp [fuel, Block.runOpenWithGasOracle, hStmt', hMode,
                    hRestAppend']
              | brk =>
                  have hTriple :
                      (stmtOutcome, ctx, cursorAfterStmt) =
                        (Structured.Outcome.regular mid, midCtx,
                          cursorMid) := by
                    simpa [Block.runOpenWithGasOracle, hStmt, hMode] using hLeft
                  injection hTriple with hOutcome _hCursor
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | cont =>
                  have hTriple :
                      (stmtOutcome, ctx, cursorAfterStmt) =
                        (Structured.Outcome.regular mid, midCtx,
                          cursorMid) := by
                    simpa [Block.runOpenWithGasOracle, hStmt, hMode] using hLeft
                  injection hTriple with hOutcome _hCursor
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | leave =>
                  have hTriple :
                      (stmtOutcome, ctx, cursorAfterStmt) =
                        (Structured.Outcome.regular mid, midCtx,
                          cursorMid) := by
                    simpa [Block.runOpenWithGasOracle, hStmt, hMode] using hLeft
                  injection hTriple with hOutcome _hCursor
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode
              | halt kind =>
                  have hTriple :
                      (stmtOutcome, ctx, cursorAfterStmt) =
                        (Structured.Outcome.regular mid, midCtx,
                          cursorMid) := by
                    simpa [Block.runOpenWithGasOracle, hStmt, hMode] using hLeft
                  injection hTriple with hOutcome _hCursor
                  rw [hOutcome] at hMode
                  simp [Structured.Outcome.regular] at hMode

theorem runOpenWithGasOracle_append_nonregular_exists (program : Program) :
    ∀ (left right : List Stmt) (ctx : Ctx) (state : RunState)
      (outcome : Outcome) (runCtx : Ctx)
      (oracle : Structured.GasOracle) (cursor cursorFinal : Nat),
      (∃ fuel,
        Block.runOpenWithGasOracle program ctx oracle fuel { stmts := left }
          cursor state =
          .ok (outcome, runCtx, cursorFinal)) →
      outcome.mode ≠ .regular →
      ∃ fuel,
        Block.runOpenWithGasOracle program ctx oracle fuel
          { stmts := left ++ right } cursor state =
          .ok (outcome, runCtx, cursorFinal) := by
  intro left
  induction left with
  | nil =>
      intro right ctx state outcome runCtx oracle cursor cursorFinal hLeft hMode
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      rcases runOpenWithGasOracle_nil_ok hLeft with ⟨hOutcome, _hCtx, _hCursor⟩
      cases hOutcome
      simp at hMode
  | cons stmt rest ih =>
      intro right ctx state outcome runCtx oracle cursor cursorFinal hLeft hMode
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.runOpenWithGasOracle, invalid, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt :
              Stmt.runWithGasOracle program ctx oracle fuelLeft stmt cursor
                state with
          | error err =>
              simp [Block.runOpenWithGasOracle, hStmt] at hLeft
          | ok stmtResult =>
              rcases stmtResult with
                ⟨stmtOutcome, stmtCtx, cursorAfterStmt⟩
              cases hModeStmt : stmtOutcome.mode with
              | regular =>
                  simp [Block.runOpenWithGasOracle, hStmt, hModeStmt] at hLeft
                  rcases ih right stmtCtx stmtOutcome.state outcome runCtx
                      oracle cursorAfterStmt cursorFinal ⟨fuelLeft, hLeft⟩
                      hMode with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.runWithGasOracle program ctx oracle
                          (Nat.max fuelLeft fuelRest) stmt cursor state =
                        .ok (stmtOutcome, stmtCtx, cursorAfterStmt) :=
                    Stmt.runWithGasOracle_mono program (Nat.le_max_left _ _)
                      hStmt
                  have hRestAppend' :
                      Block.runOpenWithGasOracle program stmtCtx oracle
                          (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } cursorAfterStmt
                          stmtOutcome.state =
                        .ok (outcome, runCtx, cursorFinal) :=
                    Block.runOpenWithGasOracle_mono program
                      (Nat.le_max_right _ _) hRestAppend
                  simp [fuel, Block.runOpenWithGasOracle, hStmt', hModeStmt,
                    hRestAppend']
              | brk =>
                  simp [Block.runOpenWithGasOracle, hStmt, hModeStmt] at hLeft
                  rcases hLeft with ⟨hOutcomeEq, hCtxEq, hCursorEq⟩
                  subst stmtOutcome
                  subst runCtx
                  subst cursorFinal
                  exact ⟨fuelLeft + 1, by
                    simp [Block.runOpenWithGasOracle, hStmt, hModeStmt]⟩
              | cont =>
                  simp [Block.runOpenWithGasOracle, hStmt, hModeStmt] at hLeft
                  rcases hLeft with ⟨hOutcomeEq, hCtxEq, hCursorEq⟩
                  subst stmtOutcome
                  subst runCtx
                  subst cursorFinal
                  exact ⟨fuelLeft + 1, by
                    simp [Block.runOpenWithGasOracle, hStmt, hModeStmt]⟩
              | leave =>
                  simp [Block.runOpenWithGasOracle, hStmt, hModeStmt] at hLeft
                  rcases hLeft with ⟨hOutcomeEq, hCtxEq, hCursorEq⟩
                  subst stmtOutcome
                  subst runCtx
                  subst cursorFinal
                  exact ⟨fuelLeft + 1, by
                    simp [Block.runOpenWithGasOracle, hStmt, hModeStmt]⟩
              | halt kind =>
                  simp [Block.runOpenWithGasOracle, hStmt, hModeStmt] at hLeft
                  rcases hLeft with ⟨hOutcomeEq, hCtxEq, hCursorEq⟩
                  subst stmtOutcome
                  subst runCtx
                  subst cursorFinal
                  exact ⟨fuelLeft + 1, by
                    simp [Block.runOpenWithGasOracle, hStmt, hModeStmt]⟩

end Block

end Direct
end Locals

namespace Functions

namespace FunDef

def lowerBodyResultWithGasOracle (retc : Nat) (bodyCtx : Locals.Ctx)
    (bodyOutcome : Outcome) (oracle : Structured.GasOracle) (cursor : Nat) :
    Except EVMException (Outcome × Nat) :=
  match bodyOutcome.mode with
  | .regular => do
      let (stateAfterCleanup, cursor') ←
        Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle bodyCtx retc 0
          oracle cursor bodyOutcome.state
      .ok (Structured.Outcome.regular stateAfterCleanup, cursor')
  | .brk | .cont =>
      Structured.invalid
  | .leave | .halt _ =>
      .ok (bodyOutcome, cursor)

end FunDef

namespace Lower

theorem evalArgsWithGasOracle_runOpen_exists
    (program : Program) (ctx : Ctx) :
    ∀ {args : List (Expr 1)} {state state' : RunState}
      {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
      Direct.evalArgsWithGasOracle ctx args oracle cursor state =
        .ok (state', cursorFinal) →
      ∃ fuel,
        Locals.Direct.Block.runOpenWithGasOracle program.toLocals ctx oracle
          fuel { stmts := evalArgs args } cursor state =
          .ok (Structured.Outcome.regular state', ctx, cursorFinal) := by
  intro args
  cases args with
  | nil =>
      intro state state' oracle cursor cursorFinal hRun
      simp [Direct.evalArgsWithGasOracle] at hRun
      rcases hRun with ⟨hState, hCursor⟩
      cases hState
      cases hCursor
      exact ⟨1, by
        simp [evalArgs, Locals.Direct.Block.runOpenWithGasOracle,
          Structured.Outcome.regular]⟩
  | cons arg rest =>
      intro state state' oracle cursor cursorFinal hRun
      unfold Direct.evalArgsWithGasOracle at hRun
      cases hArgs :
          Locals.Direct.Expr.ExprSeq.runCodeWithGasOracle ctx 0
            (Lower.argExprs (arg :: rest)) oracle cursor state.evm with
      | error err =>
          simp [hArgs] at hRun
      | ok argsResult =>
          rcases argsResult with ⟨evmAfterArgs, cursorAfterArgs⟩
          simp [hArgs] at hRun
          rcases hRun with ⟨hState, hCursor⟩
          cases hState
          cases hCursor
          refine ⟨2, ?_⟩
          simp [evalArgs, Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle, hArgs,
            Structured.Outcome.regular]

theorem pushReturnsWithGasOracle_runOpen_exists
    (program : Program) (ctx : Ctx) :
    ∀ {returns : List Name} {state state' : RunState}
      {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
      Direct.pushReturnsWithGasOracle ctx returns oracle cursor state =
        .ok (state', cursorFinal) →
      ∃ fuel,
        Locals.Direct.Block.runOpenWithGasOracle program.toLocals ctx oracle
          fuel { stmts := pushReturns returns } cursor state =
          .ok (Structured.Outcome.regular state', ctx, cursorFinal) := by
  intro returns
  cases returns with
  | nil =>
      intro state state' oracle cursor cursorFinal hRun
      simp [Direct.pushReturnsWithGasOracle] at hRun
      rcases hRun with ⟨hState, hCursor⟩
      cases hState
      cases hCursor
      exact ⟨1, by
        simp [pushReturns, Locals.Direct.Block.runOpenWithGasOracle,
          Structured.Outcome.regular]⟩
  | cons name rest =>
      intro state state' oracle cursor cursorFinal hRun
      unfold Direct.pushReturnsWithGasOracle at hRun
      cases hExprs :
          Locals.Direct.Expr.ExprSeq.runCodeWithGasOracle ctx 0
            (returnExprs (name :: rest)) oracle cursor state.evm with
      | error err =>
          simp [hExprs] at hRun
      | ok exprResult =>
          rcases exprResult with ⟨evmAfterReturns, cursorAfterReturns⟩
          simp [hExprs] at hRun
          rcases hRun with ⟨hState, hCursor⟩
          cases hState
          cases hCursor
          refine ⟨2, ?_⟩
          simp [pushReturns, Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle, hExprs,
            Structured.Outcome.regular]

theorem initReturnsWithGasOracle_runOpen_exists (program : Program) :
    ∀ {returns : List Name} {ctx ctx' : Ctx} {state state' : RunState}
      {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
      Direct.initReturnsWithGasOracle returns ctx oracle cursor state =
        .ok (state', ctx', cursorFinal) →
      ∃ fuel,
        Locals.Direct.Block.runOpenWithGasOracle program.toLocals ctx oracle
          fuel { stmts := initReturns returns } cursor state =
          .ok (Structured.Outcome.regular state', ctx', cursorFinal) := by
  intro returns
  induction returns with
  | nil =>
      intro ctx ctx' state state' oracle cursor cursorFinal hRun
      simp [Direct.initReturnsWithGasOracle] at hRun
      rcases hRun with ⟨hState, hCtx, hCursor⟩
      cases hState
      cases hCtx
      cases hCursor
      exact ⟨1, by
        simp [initReturns, Locals.Direct.Block.runOpenWithGasOracle,
          Structured.Outcome.regular]⟩
  | cons name rest ih =>
      intro ctx ctx' state state' oracle cursor cursorFinal hRun
      unfold Direct.initReturnsWithGasOracle at hRun
      cases hHead :
          Locals.Direct.Expr.runStateWithGasOracle ctx (.lit Direct.zero)
            oracle cursor state with
      | error err =>
          simp [hHead] at hRun
      | ok headResult =>
          rcases headResult with ⟨stateAfterHead, cursorAfterHead⟩
          simp [hHead] at hRun
          rcases ih hRun with ⟨fuelRest, hRest⟩
          refine ⟨fuelRest + 1, ?_⟩
          have hHead' :
              Locals.Direct.Expr.runStateWithGasOracle ctx (.lit zero) oracle
                  cursor state =
                .ok (stateAfterHead, cursorAfterHead) := by
            simpa [Direct.zero, zero] using hHead
          simp [initReturns, Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle]
          rw [hHead']
          exact hRest

theorem assignReturnedTopsWithGasOracle_runOpen_exists
    (program : Program) (ctx : Ctx) :
    ∀ {targets : List Name} {state state' : RunState}
      {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
      Direct.assignReturnedTopsWithGasOracle ctx targets oracle cursor state =
        .ok (state', cursorFinal) →
      ∃ fuel,
        Locals.Direct.Block.runOpenWithGasOracle program.toLocals ctx oracle
          fuel { stmts := assignReturnedTopsRev targets } cursor state =
          .ok (Structured.Outcome.regular state', ctx, cursorFinal) := by
  intro targets
  induction targets with
  | nil =>
      intro state state' oracle cursor cursorFinal hRun
      simp [Direct.assignReturnedTopsWithGasOracle] at hRun
      rcases hRun with ⟨hState, hCursor⟩
      cases hState
      cases hCursor
      exact ⟨1, by
        simp [assignReturnedTopsRev, Locals.Direct.Block.runOpenWithGasOracle,
          Structured.Outcome.regular]⟩
  | cons name rest ih =>
      intro state state' oracle cursor cursorFinal hRun
      unfold Direct.assignReturnedTopsWithGasOracle at hRun
      cases hHead :
          Direct.assignTopWithOffsetWithGasOracle ctx rest.length name oracle
            cursor state with
      | error err =>
          simp [hHead] at hRun
      | ok headResult =>
          rcases headResult with ⟨stateAfterHead, cursorAfterHead⟩
          simp [hHead] at hRun
          rcases ih hRun with ⟨fuelRest, hRest⟩
          refine ⟨fuelRest + 1, ?_⟩
          simp [assignReturnedTopsRev,
            Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle, Structured.Outcome.regular]
          unfold Direct.assignTopWithOffsetWithGasOracle at hHead
          cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
          | none =>
              simp [hDepth, Structured.invalid] at hHead
          | some depth =>
              cases hSwap :
                  Locals.StackOp.swap? (rest.length + depth) with
              | none =>
                  simp [hDepth, hSwap, Structured.invalid] at hHead
              | some swapOp =>
                  cases hSwapStep :
                      swapOp.stepWithGasOracle oracle cursor state.evm with
                  | error err =>
                      simp [hDepth, hSwap, hSwapStep] at hHead
                  | ok swapResult =>
                      rcases swapResult with ⟨evmAfterSwap, cursorAfterSwap⟩
                      cases hPop :
                          Structured.BasicOp.pop.stepWithGasOracle oracle
                            cursorAfterSwap evmAfterSwap with
                      | error err =>
                          simp [hDepth, hSwap, hSwapStep, hPop] at hHead
                      | ok popResult =>
                          rcases popResult with ⟨evmAfterPop, cursorAfterPop⟩
                          simp [hDepth, hSwap, hSwapStep, hPop] at hHead
                          rcases hHead with ⟨hState, hCursor⟩
                          cases hState
                          cases hCursor
                          simp [hDepth, hSwap, hSwapStep, hPop, hRest,
                            Structured.Outcome.regular]

end Lower

namespace Direct

theorem triple_run_ctx_eq {observed expected : Outcome} {ctx runCtx : Ctx}
    {cursor cursorFinal : Nat}
    (h : (observed, ctx, cursor) = (expected, runCtx, cursorFinal)) :
    runCtx = ctx := by
  injection h with _ hTail
  injection hTail with hCtx _
  exact hCtx.symm

theorem triple_outcome_eq {observed expected : Outcome} {ctx runCtx : Ctx}
    {cursor cursorFinal : Nat}
    (h : (observed, ctx, cursor) = (expected, runCtx, cursorFinal)) :
    observed = expected := by
  exact congrArg Prod.fst h

theorem ok_triple_run_ctx_eq {observed expected : Outcome} {ctx runCtx : Ctx}
    {cursor cursorFinal : Nat}
    (h : (Except.ok (observed, ctx, cursor) :
        Except EVMException (Outcome × Ctx × Nat)) =
      .ok (expected, runCtx, cursorFinal)) :
    runCtx = ctx := by
  apply triple_run_ctx_eq
  simpa using h

theorem ok_triple_outcome_eq {observed expected : Outcome} {ctx runCtx : Ctx}
    {cursor cursorFinal : Nat}
    (h : (Except.ok (observed, ctx, cursor) :
        Except EVMException (Outcome × Ctx × Nat)) =
      .ok (expected, runCtx, cursorFinal)) :
    observed = expected := by
  apply triple_outcome_eq
  simpa using h

theorem Stmt.runWithGasOracle_nonregular_ctx (program : Program)
    {returns : List Name} {ctx : Ctx} {fuel : Nat} {stmt : Stmt}
    {state : RunState} {outcome : Outcome} {runCtx : Ctx}
    {oracle : Structured.GasOracle} {cursor cursorFinal : Nat}
    (hRun :
      Stmt.runWithGasOracle program returns ctx oracle fuel stmt cursor state =
        .ok (outcome, runCtx, cursorFinal))
    (hNonregular : outcome.mode ≠ .regular) :
    runCtx = ctx := by
  cases stmt with
  | expr expr =>
      unfold Stmt.runWithGasOracle at hRun
      cases hExpr :
          Locals.Direct.Expr.runStateWithGasOracle ctx expr oracle cursor
            state with
      | error err =>
          simp [hExpr] at hRun
      | ok exprResult =>
          rcases exprResult with ⟨state', cursor'⟩
          exact ok_triple_run_ctx_eq (by simpa [hExpr] using hRun)
  | let_ name value =>
      unfold Stmt.runWithGasOracle at hRun
      cases hExpr :
          Locals.Direct.Expr.runStateWithGasOracle ctx value oracle cursor
            state with
      | error err =>
          simp [hExpr] at hRun
      | ok exprResult =>
          rcases exprResult with ⟨state', cursor'⟩
          have hOutcome :
              Structured.Outcome.regular state' = outcome :=
            ok_triple_outcome_eq (ctx := ctx.withLayout (name :: ctx.layout))
              (runCtx := runCtx) (cursor := cursor')
              (cursorFinal := cursorFinal) (by simpa [hExpr] using hRun)
          have hRegular : outcome.mode = .regular := by
            rw [← hOutcome]
            rfl
          exact (hNonregular hRegular).elim
  | assign name value =>
      unfold Stmt.runWithGasOracle at hRun
      cases hValue :
          Locals.Direct.Expr.runStateWithGasOracle ctx value oracle cursor
            state with
      | error err =>
          simp [hValue] at hRun
      | ok valueResult =>
          rcases valueResult with ⟨stateAfterValue, cursorAfterValue⟩
          cases hAssign :
              assignTopWithGasOracle ctx name oracle cursorAfterValue
                stateAfterValue with
          | error err =>
              simp [hValue, hAssign] at hRun
          | ok assignResult =>
              rcases assignResult with ⟨stateAfterAssign, cursorAfterAssign⟩
              exact ok_triple_run_ctx_eq
                (by simpa [hValue, hAssign] using hRun)
  | block body =>
      unfold Stmt.runWithGasOracle at hRun
      cases hBody :
          Block.runScopedWithGasOracle program returns ctx body oracle fuel
            cursor state with
      | error err =>
          simp [hBody] at hRun
      | ok bodyResult =>
          rcases bodyResult with ⟨bodyOutcome, cursorAfterBody⟩
          exact ok_triple_run_ctx_eq (by simpa [hBody] using hRun)
  | if_ cond body =>
      cases fuel with
      | zero =>
          simp [Stmt.runWithGasOracle, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.runWithGasOracle at hRun
          cases hCond :
              Locals.Direct.Expr.runConditionWithGasOracle ctx cond oracle
                cursor state with
          | error err =>
              simp [hCond] at hRun
          | ok condResult =>
              rcases condResult with
                ⟨stateAfterCond, condTrue, cursorAfterCond⟩
              cases condTrue with
              | false =>
                  exact ok_triple_run_ctx_eq (by simpa [hCond] using hRun)
              | true =>
                  simp [hCond] at hRun
                  cases hBody :
                      Block.runScopedWithGasOracle program returns ctx body
                        oracle fuel cursorAfterCond stateAfterCond with
                  | error err =>
                      simp [hBody] at hRun
                  | ok bodyResult =>
                      rcases bodyResult with
                        ⟨bodyOutcome, cursorAfterBody⟩
                      exact ok_triple_run_ctx_eq (by simpa [hBody] using hRun)
  | switch scrutinee cases defaultBody =>
      cases fuel with
      | zero =>
          simp [Stmt.runWithGasOracle, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.runWithGasOracle at hRun
          cases hScrutinee :
              Locals.Direct.Expr.runStateWithGasOracle ctx scrutinee oracle
                cursor state with
          | error err =>
              simp [hScrutinee] at hRun
          | ok scrutineeResult =>
              rcases scrutineeResult with
                ⟨stateAfterScrutinee, cursorAfterScrutinee⟩
              cases hPop : stateAfterScrutinee.evm.stack.pop with
              | none =>
                  simp [hScrutinee, hPop, Structured.invalid] at hRun
              | some pair =>
                  rcases pair with ⟨stack, value⟩
                  let stateAfterPop :=
                    stateAfterScrutinee.withEVM
                      { stateAfterScrutinee.evm with stack := stack }
                  cases hSelected : Switch.select value cases defaultBody with
                  | none =>
                      exact ok_triple_run_ctx_eq
                        (by
                          simpa [hScrutinee, hPop, hSelected, stateAfterPop]
                            using hRun)
                  | some body =>
                      simp [hScrutinee, hPop, hSelected, stateAfterPop] at hRun
                      cases hBody :
                          Block.runScopedWithGasOracle program returns ctx body
                            oracle fuel cursorAfterScrutinee stateAfterPop with
                      | error err =>
                          have hBody' :
                              Block.runScopedWithGasOracle program returns ctx
                                  body oracle fuel cursorAfterScrutinee
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) = .error err := by
                            simpa [stateAfterPop] using hBody
                          simp [hBody'] at hRun
                      | ok bodyResult =>
                          rcases bodyResult with
                            ⟨bodyOutcome, cursorAfterBody⟩
                          have hBody' :
                              Block.runScopedWithGasOracle program returns ctx
                                  body oracle fuel cursorAfterScrutinee
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) =
                                .ok (bodyOutcome, cursorAfterBody) := by
                            simpa [stateAfterPop] using hBody
                          exact ok_triple_run_ctx_eq
                            (by simpa [hBody'] using hRun)
  | for_ init cond post body =>
      cases fuel with
      | zero =>
          simp [Stmt.runWithGasOracle, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.runWithGasOracle at hRun
          let initBase := ctx.withoutLoopControl
          cases hInit :
              Block.runOpenWithGasOracle program returns initBase oracle fuel
                init cursor state with
          | error err =>
              simp [initBase, hInit] at hRun
          | ok initResult =>
              rcases initResult with ⟨initOutcome, initCtx, cursorAfterInit⟩
              cases hInitMode : initOutcome.mode with
              | regular =>
                  simp [initBase, hInit, hInitMode] at hRun
                  let postBase := initCtx.withoutLoopControl
                  let bodyBase := initCtx.withLoopControl initCtx.layout.length
                  cases hLoop :
                      Stmt.runForLoopWithGasOracle program returns initCtx cond
                        postBase post bodyBase body oracle fuel cursorAfterInit
                        initOutcome.state with
                  | error err =>
                      simp [postBase, bodyBase, hLoop] at hRun
                  | ok loopResult =>
                      rcases loopResult with ⟨loopOutcome, cursorAfterLoop⟩
                      cases hLoopMode : loopOutcome.mode with
                      | regular =>
                          simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                          cases hCleanup :
                              Locals.Direct.Ctx.runCleanupToWithGasOracle initCtx
                                ctx.layout.length oracle cursorAfterLoop
                                loopOutcome.state with
                          | error err =>
                              simp [hCleanup] at hRun
                          | ok cleanupResult =>
                              rcases cleanupResult with
                                ⟨stateAfterCleanup, cursorAfterCleanup⟩
                              exact ok_triple_run_ctx_eq
                                (by simpa [hCleanup] using hRun)
                      | brk =>
                          simp [postBase, bodyBase, hLoop, hLoopMode,
                            Structured.invalid] at hRun
                      | cont =>
                          simp [postBase, bodyBase, hLoop, hLoopMode,
                            Structured.invalid] at hRun
                      | leave =>
                          exact ok_triple_run_ctx_eq
                            (by
                              simpa [postBase, bodyBase, hLoop, hLoopMode]
                                using hRun)
                      | halt kind =>
                          exact ok_triple_run_ctx_eq
                            (by
                              simpa [postBase, bodyBase, hLoop, hLoopMode]
                                using hRun)
              | brk =>
                  simp [initBase, hInit, hInitMode, Structured.invalid] at hRun
              | cont =>
                  simp [initBase, hInit, hInitMode, Structured.invalid] at hRun
              | leave =>
                  exact ok_triple_run_ctx_eq
                    (by simpa [initBase, hInit, hInitMode] using hRun)
              | halt kind =>
                  exact ok_triple_run_ctx_eq
                    (by simpa [initBase, hInit, hInitMode] using hRun)
  | brk =>
      unfold Stmt.runWithGasOracle at hRun
      cases hTarget : ctx.breakDepth? with
      | none =>
          simp [hTarget, Structured.invalid] at hRun
      | some target =>
          cases hCleanup :
              Locals.Direct.Ctx.runCleanupToWithGasOracle ctx target oracle
                cursor state with
          | error err =>
              simp [hTarget, hCleanup] at hRun
          | ok cleanupResult =>
              rcases cleanupResult with ⟨state', cursor'⟩
              exact ok_triple_run_ctx_eq
                (by simpa [hTarget, hCleanup] using hRun)
  | cont =>
      unfold Stmt.runWithGasOracle at hRun
      cases hTarget : ctx.continueDepth? with
      | none =>
          simp [hTarget, Structured.invalid] at hRun
      | some target =>
          cases hCleanup :
              Locals.Direct.Ctx.runCleanupToWithGasOracle ctx target oracle
                cursor state with
          | error err =>
              simp [hTarget, hCleanup] at hRun
          | ok cleanupResult =>
              rcases cleanupResult with ⟨state', cursor'⟩
              exact ok_triple_run_ctx_eq
                (by simpa [hTarget, hCleanup] using hRun)
  | leave =>
      unfold Stmt.runWithGasOracle at hRun
      cases hPush : pushReturnsWithGasOracle ctx returns oracle cursor state with
      | error err =>
          simp [hPush] at hRun
      | ok pushResult =>
          rcases pushResult with ⟨stateAfterReturns, cursorAfterReturns⟩
          cases hTarget : ctx.leaveDepth? with
          | none =>
              simp [hPush, hTarget, Structured.invalid] at hRun
          | some target =>
              cases hCleanup :
                  Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle ctx
                    ctx.leaveRetc target oracle cursorAfterReturns
                    stateAfterReturns with
              | error err =>
                  simp [hPush, hTarget, hCleanup] at hRun
              | ok cleanupResult =>
                  rcases cleanupResult with
                    ⟨stateAfterCleanup, cursorAfterCleanup⟩
                  cases hReturns : stateAfterCleanup.returns with
                  | nil =>
                      simp [hPush, hTarget, hCleanup, hReturns,
                        Structured.invalid] at hRun
                  | cons ret rest =>
                      exact ok_triple_run_ctx_eq
                        (by
                          simpa [hPush, hTarget, hCleanup, hReturns]
                            using hRun)
  | call targets functionName args =>
      cases fuel with
      | zero =>
          simp [Stmt.runWithGasOracle, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.runWithGasOracle at hRun
          cases hArgs : evalArgsWithGasOracle ctx args oracle cursor state with
          | error err =>
              simp [hArgs] at hRun
          | ok argsResult =>
              rcases argsResult with ⟨stateAfterArgs, cursorAfterArgs⟩
              cases hLookup :
                  FunList.find? functionName program.functions with
              | none =>
                  simp [hArgs, hLookup, Structured.invalid] at hRun
              | some fn =>
                  cases hSplit :
                      Structured.StackFrame.splitArgs? fn.params.length
                        stateAfterArgs.evm.stack with
                  | none =>
                      simp [hArgs, hLookup, hSplit, Structured.invalid] at hRun
                  | some split =>
                      rcases split with ⟨argStack, callerStack⟩
                      let callState :=
                        (stateAfterArgs.withEVM
                            { stateAfterArgs.evm with stack := argStack })
                          |>.pushReturn callerStack fn.returns.length
                      cases hBody :
                          FunDef.runBodyWithGasOracle program fn oracle fuel
                            cursorAfterArgs callState with
                      | error err =>
                          simp [hArgs, hLookup, hSplit, callState, hBody]
                            at hRun
                      | ok bodyResult =>
                          rcases bodyResult with
                            ⟨callOutcome, cursorAfterBody⟩
                          cases hMode : callOutcome.mode with
                          | regular =>
                              simp [hArgs, hLookup, hSplit, callState, hBody,
                                hMode] at hRun
                              cases hPopRet : callOutcome.state.popReturn? with
                              | none =>
                                  simp [hPopRet, Structured.invalid] at hRun
                              | some retPair =>
                                  rcases retPair with ⟨frame, returned⟩
                                  cases hAttach :
                                      Structured.StackFrame.attachReturns? frame
                                        callOutcome.state.evm.stack with
                                  | none =>
                                      simp [hPopRet, hAttach,
                                        Structured.invalid] at hRun
                                  | some stack =>
                                      let stateWithReturns :=
                                        returned.withEVM
                                          { callOutcome.state.evm with
                                            stack := stack }
                                      cases hAssign :
                                          assignReturnedTopsWithGasOracle ctx
                                            targets.reverse oracle
                                            cursorAfterBody stateWithReturns with
                                      | error err =>
                                          simp [hPopRet, hAttach,
                                            stateWithReturns, hAssign] at hRun
                                      | ok assignResult =>
                                          rcases assignResult with
                                            ⟨stateAfterAssign,
                                              cursorAfterAssign⟩
                                          exact ok_triple_run_ctx_eq
                                            (by
                                              simpa [hPopRet, hAttach,
                                                stateWithReturns, hAssign]
                                                using hRun)
                          | leave =>
                              simp [hArgs, hLookup, hSplit, callState, hBody,
                                hMode] at hRun
                              cases hPopRet : callOutcome.state.popReturn? with
                              | none =>
                                  simp [hPopRet, Structured.invalid] at hRun
                              | some retPair =>
                                  rcases retPair with ⟨frame, returned⟩
                                  cases hAttach :
                                      Structured.StackFrame.attachReturns? frame
                                        callOutcome.state.evm.stack with
                                  | none =>
                                      simp [hPopRet, hAttach,
                                        Structured.invalid] at hRun
                                  | some stack =>
                                      let stateWithReturns :=
                                        returned.withEVM
                                          { callOutcome.state.evm with
                                            stack := stack }
                                      cases hAssign :
                                          assignReturnedTopsWithGasOracle ctx
                                            targets.reverse oracle
                                            cursorAfterBody stateWithReturns with
                                      | error err =>
                                          simp [hPopRet, hAttach,
                                            stateWithReturns, hAssign] at hRun
                                      | ok assignResult =>
                                          rcases assignResult with
                                            ⟨stateAfterAssign,
                                              cursorAfterAssign⟩
                                          exact ok_triple_run_ctx_eq
                                            (by
                                              simpa [hPopRet, hAttach,
                                                stateWithReturns, hAssign]
                                                using hRun)
                          | brk =>
                              simp [hArgs, hLookup, hSplit, callState, hBody,
                                hMode, Structured.invalid] at hRun
                          | cont =>
                              simp [hArgs, hLookup, hSplit, callState, hBody,
                                hMode, Structured.invalid] at hRun
                          | halt kind =>
                              exact ok_triple_run_ctx_eq
                                (by
                                  simpa [hArgs, hLookup, hSplit, callState,
                                    hBody, hMode] using hRun)
  | terminal kind =>
      unfold Stmt.runWithGasOracle at hRun
      cases hCleanup :
          Locals.Direct.Ctx.runCleanupAllWithGasOracle ctx oracle cursor state with
      | error err =>
          simp [hCleanup] at hRun
      | ok cleanupResult =>
          rcases cleanupResult with ⟨stateAfterCleanup, cursorAfterCleanup⟩
          cases hTerminal :
              Structured.Terminal.stepWithGasOracle kind oracle
                cursorAfterCleanup stateAfterCleanup.evm with
          | error err =>
              simp [hCleanup, hTerminal] at hRun
          | ok terminalResult =>
              rcases terminalResult with ⟨evm, cursor'⟩
              exact ok_triple_run_ctx_eq
                (by simpa [hCleanup, hTerminal] using hRun)
  | terminalArgs kind args =>
      unfold Stmt.runWithGasOracle at hRun
      cases hArgs :
          Locals.Direct.Expr.ExprSeq.runCodeWithGasOracle ctx 0 args oracle
            cursor state.evm with
      | error err =>
          simp [hArgs] at hRun
      | ok argsResult =>
          rcases argsResult with ⟨evmAfterArgs, cursorAfterArgs⟩
          cases hTerminal :
              Structured.Terminal.stepWithGasOracle kind oracle cursorAfterArgs
                evmAfterArgs with
          | error err =>
              simp [hArgs, hTerminal] at hRun
          | ok terminalResult =>
              rcases terminalResult with ⟨evm, cursor'⟩
              exact ok_triple_run_ctx_eq
                (by simpa [hArgs, hTerminal] using hRun)

set_option maxHeartbeats 2500000 in
mutual
  theorem Block.runOpenWithGasOracle_toLocals_exists (program : Program) :
      ∀ {returns : List Name} {ctx : Ctx} {fuel : Nat}
        {block : Block} {state : RunState} {outcome : Outcome}
        {runCtx : Ctx} {oracle : Structured.GasOracle}
        {cursor cursorFinal : Nat},
        Block.runOpenWithGasOracle program returns ctx oracle fuel block cursor
          state =
          .ok (outcome, runCtx, cursorFinal) →
        ∃ lowerFuel,
          Locals.Direct.Block.runOpenWithGasOracle program.toLocals ctx oracle
            lowerFuel (Block.toLocals returns block) cursor state =
            .ok (outcome, runCtx, cursorFinal) := by
    intro returns ctx fuel block state outcome runCtx oracle cursor cursorFinal
      hRun
    cases fuel with
    | zero =>
        cases block
        simp [Block.runOpenWithGasOracle, Structured.invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                have hTriple :
                    (Structured.Outcome.regular state, ctx, cursor) =
                      (outcome, runCtx, cursorFinal) := by
                  simpa [Block.runOpenWithGasOracle] using hRun
                injection hTriple with hOutcome hTail
                injection hTail with hCtx hCursor
                cases hOutcome
                cases hCtx
                cases hCursor
                exact ⟨1, by
                  simp [Block.toLocals, StmtList.toLocals,
                    Locals.Direct.Block.runOpenWithGasOracle,
                    Structured.Outcome.regular]⟩
            | cons stmt rest =>
                cases hStmt :
                    Stmt.runWithGasOracle program returns ctx oracle fuel stmt
                      cursor state with
                | error err =>
                    simp [Block.runOpenWithGasOracle, hStmt] at hRun
                | ok stmtResult =>
                    rcases stmtResult with
                      ⟨stmtOutcome, stmtCtx, cursorAfterStmt⟩
                    rcases Stmt.runWithGasOracle_toLocals_exists program
                        hStmt with
                      ⟨stmtFuel, hStmtLower⟩
                    cases hMode : stmtOutcome.mode with
                    | regular =>
                        simp [Block.runOpenWithGasOracle, hStmt, hMode] at hRun
                        rcases Block.runOpenWithGasOracle_toLocals_exists
                            program hRun with
                          ⟨restFuel, hRestLower⟩
                        have hStmtLowerRegular :
                            Locals.Direct.Block.runOpenWithGasOracle
                              program.toLocals ctx oracle stmtFuel
                              { stmts := Stmt.toLocals returns stmt } cursor
                              state =
                              .ok (Structured.Outcome.regular
                                stmtOutcome.state, stmtCtx,
                                cursorAfterStmt) := by
                          have hEq :
                              stmtOutcome =
                                Structured.Outcome.regular
                                  stmtOutcome.state :=
                            Outcome.eq_regular_of_mode hMode
                          rw [hEq] at hStmtLower
                          exact hStmtLower
                        simpa [Block.toLocals, StmtList.toLocals] using
                          Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                            program.toLocals
                            (Stmt.toLocals returns stmt)
                            (StmtList.toLocals returns rest)
                            ctx stmtCtx state stmtOutcome.state outcome runCtx
                            oracle cursor cursorAfterStmt cursorFinal
                            ⟨stmtFuel, hStmtLowerRegular⟩
                            ⟨restFuel, hRestLower⟩
                    | brk =>
                        have hTriple :
                            (stmtOutcome, ctx, cursorAfterStmt) =
                              (outcome, runCtx, cursorFinal) := by
                          simpa [Block.runOpenWithGasOracle, hStmt, hMode]
                            using hRun
                        injection hTriple with hOutcome hTail
                        injection hTail with hCtx hCursor
                        rw [← hOutcome, ← hCtx, ← hCursor]
                        have hNonregular : stmtOutcome.mode ≠ .regular := by
                          simp [hMode]
                        have hStmtCtx : stmtCtx = ctx :=
                          Stmt.runWithGasOracle_nonregular_ctx program hStmt
                            hNonregular
                        simpa [Block.toLocals, StmtList.toLocals] using
                          Locals.Direct.Block.runOpenWithGasOracle_append_nonregular_exists
                            program.toLocals
                            (Stmt.toLocals returns stmt)
                            (StmtList.toLocals returns rest)
                            ctx state stmtOutcome ctx oracle cursor
                            cursorAfterStmt
                            ⟨stmtFuel, by
                              simpa [hStmtCtx] using hStmtLower⟩
                            hNonregular
                    | cont =>
                        have hTriple :
                            (stmtOutcome, ctx, cursorAfterStmt) =
                              (outcome, runCtx, cursorFinal) := by
                          simpa [Block.runOpenWithGasOracle, hStmt, hMode]
                            using hRun
                        injection hTriple with hOutcome hTail
                        injection hTail with hCtx hCursor
                        rw [← hOutcome, ← hCtx, ← hCursor]
                        have hNonregular : stmtOutcome.mode ≠ .regular := by
                          simp [hMode]
                        have hStmtCtx : stmtCtx = ctx :=
                          Stmt.runWithGasOracle_nonregular_ctx program hStmt
                            hNonregular
                        simpa [Block.toLocals, StmtList.toLocals] using
                          Locals.Direct.Block.runOpenWithGasOracle_append_nonregular_exists
                            program.toLocals
                            (Stmt.toLocals returns stmt)
                            (StmtList.toLocals returns rest)
                            ctx state stmtOutcome ctx oracle cursor
                            cursorAfterStmt
                            ⟨stmtFuel, by
                              simpa [hStmtCtx] using hStmtLower⟩
                            hNonregular
                    | leave =>
                        have hTriple :
                            (stmtOutcome, ctx, cursorAfterStmt) =
                              (outcome, runCtx, cursorFinal) := by
                          simpa [Block.runOpenWithGasOracle, hStmt, hMode]
                            using hRun
                        injection hTriple with hOutcome hTail
                        injection hTail with hCtx hCursor
                        rw [← hOutcome, ← hCtx, ← hCursor]
                        have hNonregular : stmtOutcome.mode ≠ .regular := by
                          simp [hMode]
                        have hStmtCtx : stmtCtx = ctx :=
                          Stmt.runWithGasOracle_nonregular_ctx program hStmt
                            hNonregular
                        simpa [Block.toLocals, StmtList.toLocals] using
                          Locals.Direct.Block.runOpenWithGasOracle_append_nonregular_exists
                            program.toLocals
                            (Stmt.toLocals returns stmt)
                            (StmtList.toLocals returns rest)
                            ctx state stmtOutcome ctx oracle cursor
                            cursorAfterStmt
                            ⟨stmtFuel, by
                              simpa [hStmtCtx] using hStmtLower⟩
                            hNonregular
                    | halt kind =>
                        have hTriple :
                            (stmtOutcome, ctx, cursorAfterStmt) =
                              (outcome, runCtx, cursorFinal) := by
                          simpa [Block.runOpenWithGasOracle, hStmt, hMode]
                            using hRun
                        injection hTriple with hOutcome hTail
                        injection hTail with hCtx hCursor
                        rw [← hOutcome, ← hCtx, ← hCursor]
                        have hNonregular : stmtOutcome.mode ≠ .regular := by
                          simp [hMode]
                        have hStmtCtx : stmtCtx = ctx :=
                          Stmt.runWithGasOracle_nonregular_ctx program hStmt
                            hNonregular
                        simpa [Block.toLocals, StmtList.toLocals] using
                          Locals.Direct.Block.runOpenWithGasOracle_append_nonregular_exists
                            program.toLocals
                            (Stmt.toLocals returns stmt)
                            (StmtList.toLocals returns rest)
                            ctx state stmtOutcome ctx oracle cursor
                            cursorAfterStmt
                            ⟨stmtFuel, by
                              simpa [hStmtCtx] using hStmtLower⟩
                            hNonregular
  termination_by
    returns _ctx fuel block _state _outcome _runCtx _oracle _cursor
      _cursorFinal _hRun => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScopedWithGasOracle_toLocals_exists (program : Program) :
      ∀ {returns : List Name} {ctx : Ctx} {fuel : Nat}
        {block : Block} {state : RunState} {outcome : Outcome}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        Block.runScopedWithGasOracle program returns ctx block oracle fuel
          cursor state =
          .ok (outcome, cursorFinal) →
        ∃ lowerFuel,
          Locals.Direct.Block.runScopedWithGasOracle program.toLocals ctx
            (Block.toLocals returns block) oracle lowerFuel cursor state =
            .ok (outcome, cursorFinal) := by
    intro returns ctx fuel block state outcome oracle cursor cursorFinal hRun
    unfold Block.runScopedWithGasOracle at hRun
    cases hOpen :
        Block.runOpenWithGasOracle program returns ctx oracle fuel block cursor
          state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx, cursorAfterOpen⟩
        rcases Block.runOpenWithGasOracle_toLocals_exists program hOpen with
          ⟨openFuel, hOpenLower⟩
        cases hMode : openOutcome.mode with
        | regular =>
            simp [hOpen, hMode] at hRun
            cases hCleanup :
                Locals.Direct.Ctx.runCleanupToWithGasOracle finalCtx
                  ctx.layout.length oracle cursorAfterOpen
                  openOutcome.state with
            | error err =>
                simp [hCleanup] at hRun
            | ok cleanupResult =>
                rcases cleanupResult with ⟨stateAfterCleanup, cursorAfterCleanup⟩
                have hPair :
                    (Structured.Outcome.regular stateAfterCleanup,
                        cursorAfterCleanup) = (outcome, cursorFinal) := by
                  simpa [hCleanup] using hRun
                injection hPair with hOutcome hCursor
                rw [← hOutcome, ← hCursor]
                refine ⟨openFuel, ?_⟩
                unfold Locals.Direct.Block.runScopedWithGasOracle
                simp [hOpenLower, hMode, hCleanup,
                  Structured.Outcome.regular]
        | brk =>
            simp [hOpen, hMode] at hRun
            have hPair : (openOutcome, cursorAfterOpen) =
                (outcome, cursorFinal) := by
              simpa using hRun
            injection hPair with hOutcome hCursor
            rw [← hOutcome, ← hCursor]
            exact ⟨openFuel, by
              unfold Locals.Direct.Block.runScopedWithGasOracle
              simp [hOpenLower, hMode]⟩
        | cont =>
            simp [hOpen, hMode] at hRun
            have hPair : (openOutcome, cursorAfterOpen) =
                (outcome, cursorFinal) := by
              simpa using hRun
            injection hPair with hOutcome hCursor
            rw [← hOutcome, ← hCursor]
            exact ⟨openFuel, by
              unfold Locals.Direct.Block.runScopedWithGasOracle
              simp [hOpenLower, hMode]⟩
        | leave =>
            simp [hOpen, hMode] at hRun
            have hPair : (openOutcome, cursorAfterOpen) =
                (outcome, cursorFinal) := by
              simpa using hRun
            injection hPair with hOutcome hCursor
            rw [← hOutcome, ← hCursor]
            exact ⟨openFuel, by
              unfold Locals.Direct.Block.runScopedWithGasOracle
              simp [hOpenLower, hMode]⟩
        | halt kind =>
            simp [hOpen, hMode] at hRun
            have hPair : (openOutcome, cursorAfterOpen) =
                (outcome, cursorFinal) := by
              simpa using hRun
            injection hPair with hOutcome hCursor
            rw [← hOutcome, ← hCursor]
            exact ⟨openFuel, by
              unfold Locals.Direct.Block.runScopedWithGasOracle
              simp [hOpenLower, hMode]⟩
  termination_by
    returns _ctx fuel block _state _outcome _oracle _cursor _cursorFinal
      _hRun => (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem FunDef.runBodyWithGasOracle_toLocals_open_exists
      (program : Program) :
      ∀ {fn : FunDef} {fuel : Nat} {state : RunState}
        {outcome : Outcome} {oracle : Structured.GasOracle}
        {cursor cursorFinal : Nat},
        FunDef.runBodyWithGasOracle program fn oracle fuel cursor state =
          .ok (outcome, cursorFinal) →
        ∃ openFuel lowerBodyOutcome lowerBodyCtx cursorAfterOpen,
          Locals.Direct.Block.runOpenWithGasOracle program.toLocals
            (Locals.Ctx.procEntryWithLayoutAndRetc
              fn.params.reverse fn.returns.length)
            oracle openFuel
            { stmts :=
                Lower.initReturns fn.returns ++
                  (StmtList.toLocals fn.returns fn.body.stmts ++
                    Lower.pushReturns fn.returns) }
            cursor state =
            .ok (lowerBodyOutcome, lowerBodyCtx, cursorAfterOpen) ∧
          FunDef.lowerBodyResultWithGasOracle fn.returns.length
            lowerBodyCtx lowerBodyOutcome oracle cursorAfterOpen =
            .ok (outcome, cursorFinal) := by
    intro fn fuel state outcome oracle cursor cursorFinal hRun
    cases fuel with
    | zero =>
        simp [FunDef.runBodyWithGasOracle, Structured.invalid] at hRun
    | succ fuel =>
        unfold FunDef.runBodyWithGasOracle at hRun
        let entryCtx :=
          Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length
        cases hInit :
            initReturnsWithGasOracle fn.returns entryCtx oracle cursor state with
        | error err =>
            simp [entryCtx, hInit] at hRun
        | ok initResult =>
            rcases initResult with ⟨stateAfterInit, initCtx, cursorAfterInit⟩
            rcases Lower.initReturnsWithGasOracle_runOpen_exists program hInit
              with ⟨initFuel, hInitLower⟩
            cases hBody :
                Block.runOpenWithGasOracle program fn.returns initCtx oracle
                  fuel fn.body cursorAfterInit stateAfterInit with
            | error err =>
                simp [entryCtx, hInit, hBody] at hRun
            | ok bodyResult =>
                rcases bodyResult with
                  ⟨bodyOutcome, bodyCtx, cursorAfterBody⟩
                rcases Block.runOpenWithGasOracle_toLocals_exists program
                    hBody with
                  ⟨bodyFuel, hBodyLower⟩
                cases hMode : bodyOutcome.mode with
                | regular =>
                    simp [entryCtx, hInit, hBody, hMode] at hRun
                    cases hPush :
                        pushReturnsWithGasOracle bodyCtx fn.returns oracle
                          cursorAfterBody bodyOutcome.state with
                    | error err =>
                        simp [hPush] at hRun
                    | ok pushResult =>
                        rcases pushResult with
                          ⟨stateAfterReturns, cursorAfterReturns⟩
                        rcases Lower.pushReturnsWithGasOracle_runOpen_exists
                            program bodyCtx hPush with
                          ⟨pushFuel, hPushLower⟩
                        cases hCleanup :
                            Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle
                              bodyCtx fn.returns.length 0 oracle
                              cursorAfterReturns stateAfterReturns with
                        | error err =>
                            simp [hPush, hCleanup] at hRun
                        | ok cleanupResult =>
                            rcases cleanupResult with
                              ⟨stateAfterCleanup, cursorAfterCleanup⟩
                            have hPair :
                                (Structured.Outcome.regular stateAfterCleanup,
                                    cursorAfterCleanup) =
                                  (outcome, cursorFinal) := by
                              simpa [hPush, hCleanup] using hRun
                            injection hPair with hOutcome hCursor
                            rw [← hOutcome, ← hCursor]
                            have hBodyRegular :
                                Locals.Direct.Block.runOpenWithGasOracle
                                  program.toLocals initCtx oracle bodyFuel
                                  (Block.toLocals fn.returns fn.body)
                                  cursorAfterInit stateAfterInit =
                                  .ok (Structured.Outcome.regular
                                    bodyOutcome.state, bodyCtx,
                                    cursorAfterBody) := by
                              have hEq :
                                  bodyOutcome =
                                    Structured.Outcome.regular
                                      bodyOutcome.state :=
                                Outcome.eq_regular_of_mode hMode
                              rw [hEq] at hBodyLower
                              exact hBodyLower
                            rcases
                              Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                                program.toLocals
                                (StmtList.toLocals fn.returns fn.body.stmts)
                                (Lower.pushReturns fn.returns)
                                initCtx bodyCtx stateAfterInit
                                bodyOutcome.state
                                (Structured.Outcome.regular stateAfterReturns)
                                bodyCtx oracle cursorAfterInit cursorAfterBody
                                cursorAfterReturns
                                ⟨bodyFuel, by
                                  simpa [Block.toLocals_eq_stmts] using
                                    hBodyRegular⟩
                                ⟨pushFuel, hPushLower⟩ with
                              ⟨bodyPushFuel, hBodyPushLower⟩
                            rcases
                              Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                                program.toLocals
                                (Lower.initReturns fn.returns)
                                (StmtList.toLocals fn.returns fn.body.stmts ++
                                  Lower.pushReturns fn.returns)
                                entryCtx initCtx state stateAfterInit
                                (Structured.Outcome.regular stateAfterReturns)
                                bodyCtx oracle cursor cursorAfterInit
                                cursorAfterReturns
                                ⟨initFuel, by
                                  simpa [entryCtx] using hInitLower⟩
                                ⟨bodyPushFuel, hBodyPushLower⟩ with
                              ⟨openFuel, hOpenLower⟩
                            refine ⟨openFuel,
                              Structured.Outcome.regular stateAfterReturns,
                              bodyCtx, cursorAfterReturns, ?_, ?_⟩
                            · simpa [FunDef.toLocalsProc, entryCtx,
                                List.append_assoc] using hOpenLower
                            · simp [FunDef.lowerBodyResultWithGasOracle,
                                hCleanup, Structured.Outcome.regular]
                | brk =>
                    simp [entryCtx, hInit, hBody, hMode, Structured.invalid]
                      at hRun
                | cont =>
                    simp [entryCtx, hInit, hBody, hMode, Structured.invalid]
                      at hRun
                | leave =>
                    simp [entryCtx, hInit, hBody, hMode] at hRun
                    have hPair :
                        (bodyOutcome, cursorAfterBody) =
                          (outcome, cursorFinal) := by
                      simpa using hRun
                    injection hPair with hOutcome hCursor
                    rw [← hOutcome, ← hCursor]
                    have hBodyMode : bodyOutcome.mode ≠ .regular := by
                      simp [hMode]
                    rcases
                      Locals.Direct.Block.runOpenWithGasOracle_append_nonregular_exists
                        program.toLocals
                        (StmtList.toLocals fn.returns fn.body.stmts)
                        (Lower.pushReturns fn.returns)
                        initCtx stateAfterInit bodyOutcome bodyCtx oracle
                        cursorAfterInit cursorAfterBody
                        ⟨bodyFuel, by
                          simpa [Block.toLocals_eq_stmts] using hBodyLower⟩
                        hBodyMode with
                      ⟨bodyPushFuel, hBodyPushLower⟩
                    rcases
                      Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                        program.toLocals
                        (Lower.initReturns fn.returns)
                        (StmtList.toLocals fn.returns fn.body.stmts ++
                          Lower.pushReturns fn.returns)
                        entryCtx initCtx state stateAfterInit bodyOutcome
                        bodyCtx oracle cursor cursorAfterInit cursorAfterBody
                        ⟨initFuel, by simpa [entryCtx] using hInitLower⟩
                        ⟨bodyPushFuel, hBodyPushLower⟩ with
                      ⟨openFuel, hOpenLower⟩
                    refine ⟨openFuel, bodyOutcome, bodyCtx, cursorAfterBody,
                      ?_, ?_⟩
                    · simpa [FunDef.toLocalsProc, entryCtx, List.append_assoc]
                        using hOpenLower
                    · simp [FunDef.lowerBodyResultWithGasOracle, hMode]
                | halt kind =>
                    simp [entryCtx, hInit, hBody, hMode] at hRun
                    have hPair :
                        (bodyOutcome, cursorAfterBody) =
                          (outcome, cursorFinal) := by
                      simpa using hRun
                    injection hPair with hOutcome hCursor
                    rw [← hOutcome, ← hCursor]
                    have hBodyMode : bodyOutcome.mode ≠ .regular := by
                      simp [hMode]
                    rcases
                      Locals.Direct.Block.runOpenWithGasOracle_append_nonregular_exists
                        program.toLocals
                        (StmtList.toLocals fn.returns fn.body.stmts)
                        (Lower.pushReturns fn.returns)
                        initCtx stateAfterInit bodyOutcome bodyCtx oracle
                        cursorAfterInit cursorAfterBody
                        ⟨bodyFuel, by
                          simpa [Block.toLocals_eq_stmts] using hBodyLower⟩
                        hBodyMode with
                      ⟨bodyPushFuel, hBodyPushLower⟩
                    rcases
                      Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                        program.toLocals
                        (Lower.initReturns fn.returns)
                        (StmtList.toLocals fn.returns fn.body.stmts ++
                          Lower.pushReturns fn.returns)
                        entryCtx initCtx state stateAfterInit bodyOutcome
                        bodyCtx oracle cursor cursorAfterInit cursorAfterBody
                        ⟨initFuel, by simpa [entryCtx] using hInitLower⟩
                        ⟨bodyPushFuel, hBodyPushLower⟩ with
                      ⟨openFuel, hOpenLower⟩
                    refine ⟨openFuel, bodyOutcome, bodyCtx, cursorAfterBody,
                      ?_, ?_⟩
                    · simpa [FunDef.toLocalsProc, entryCtx, List.append_assoc]
                        using hOpenLower
                    · simp [FunDef.lowerBodyResultWithGasOracle, hMode]
  termination_by
    fn fuel _state _outcome _oracle _cursor _cursorFinal _hRun =>
      (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runForLoopWithGasOracle_toLocals_exists (program : Program) :
      ∀ {returns : List Name} {loopCtx : Ctx} {cond : Expr 1}
        {postBase : Ctx} {post : Block} {bodyBase : Ctx} {body : Block}
        {fuel : Nat} {state : RunState} {outcome : Outcome}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        Stmt.runForLoopWithGasOracle program returns loopCtx cond postBase post
          bodyBase body oracle fuel cursor state =
          .ok (outcome, cursorFinal) →
        ∃ lowerFuel,
          Locals.Direct.Stmt.runForLoopWithGasOracle program.toLocals loopCtx
            cond postBase (Block.toLocals returns post)
            bodyBase (Block.toLocals returns body) oracle lowerFuel cursor
            state =
            .ok (outcome, cursorFinal) := by
    intro returns loopCtx cond postBase post bodyBase body fuel state outcome
      oracle cursor cursorFinal hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoopWithGasOracle, Structured.invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoopWithGasOracle at hRun
        unfold Locals.Direct.Stmt.runForLoopWithGasOracle
        cases hCond :
            Locals.Direct.Expr.runConditionWithGasOracle loopCtx cond oracle
              cursor state with
        | error err =>
            simp [hCond] at hRun
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue, cursorAfterCond⟩
            cases condTrue with
            | false =>
                have hPair :
                    (Structured.Outcome.regular stateAfterCond,
                        cursorAfterCond) =
                      (outcome, cursorFinal) := by
                  simpa [hCond] using hRun
                injection hPair with hOutcome hCursor
                rw [← hOutcome, ← hCursor]
                exact ⟨1, by
                  simp [hCond, Structured.Outcome.regular]⟩
            | true =>
                simp [hCond] at hRun
                cases hBody :
                    Block.runScopedWithGasOracle program returns bodyBase body
                      oracle fuel cursorAfterCond stateAfterCond with
                | error err =>
                    simp [hBody] at hRun
                | ok bodyResult =>
                    rcases bodyResult with ⟨bodyOutcome, cursorAfterBody⟩
                    rcases Block.runScopedWithGasOracle_toLocals_exists
                        program hBody with
                      ⟨bodyFuel, hBodyLower⟩
                    cases hBodyMode : bodyOutcome.mode with
                    | brk =>
                        have hPair :
                            (Structured.Outcome.regular bodyOutcome.state,
                                cursorAfterBody) =
                              (outcome, cursorFinal) := by
                          simpa [hBody, hBodyMode] using hRun
                        injection hPair with hOutcome hCursor
                        rw [← hOutcome, ← hCursor]
                        refine ⟨bodyFuel + 1, ?_⟩
                        simp [hCond, hBodyLower, hBodyMode,
                          Structured.Outcome.regular]
                    | regular =>
                        simp [hBody, hBodyMode] at hRun
                        cases hPost :
                            Block.runScopedWithGasOracle program returns
                              postBase post oracle fuel cursorAfterBody
                              bodyOutcome.state with
                        | error err =>
                            simp [hPost] at hRun
                        | ok postResult =>
                            rcases postResult with
                              ⟨postOutcome, cursorAfterPost⟩
                            rcases Block.runScopedWithGasOracle_toLocals_exists
                                program hPost with
                              ⟨postFuel, hPostLower⟩
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPost, hPostMode] at hRun
                                rcases Stmt.runForLoopWithGasOracle_toLocals_exists
                                    program hRun with
                                  ⟨loopFuel, hLoopLower⟩
                                let innerFuel := Nat.max bodyFuel
                                  (Nat.max postFuel loopFuel)
                                refine ⟨innerFuel + 1, ?_⟩
                                simp [hCond]
                                have hBodyLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterCond
                                      stateAfterCond =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals postBase
                                      (Block.toLocals returns post) oracle
                                      innerFuel cursorAfterBody
                                      bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_trans
                                        (Nat.le_max_left _ _)
                                        (Nat.le_max_right _ _)) hPostLower
                                have hLoopLower' :
                                    Locals.Direct.Stmt.runForLoopWithGasOracle
                                      program.toLocals loopCtx cond postBase
                                      (Block.toLocals returns post) bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterPost
                                      postOutcome.state =
                                      .ok (outcome, cursorFinal) :=
                                  Locals.Direct.Stmt.runForLoopWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_trans
                                        (Nat.le_max_right _ _)
                                        (Nat.le_max_right _ _)) hLoopLower
                                simp [hBodyLower', hBodyMode, hPostLower',
                                  hPostMode, hLoopLower']
                            | brk =>
                                simp [hPost, hPostMode, Structured.invalid]
                                  at hRun
                            | cont =>
                                simp [hPost, hPostMode, Structured.invalid]
                                  at hRun
                            | leave =>
                                simp [hPost, hPostMode] at hRun
                                let innerFuel := Nat.max bodyFuel postFuel
                                refine ⟨innerFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterCond
                                      stateAfterCond =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals postBase
                                      (Block.toLocals returns post) oracle
                                      innerFuel cursorAfterBody
                                      bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hPostLower
                                simpa [hCond, hBodyLower', hBodyMode,
                                  hPostLower', hPostMode] using hRun
                            | halt kind =>
                                simp [hPost, hPostMode] at hRun
                                let innerFuel := Nat.max bodyFuel postFuel
                                refine ⟨innerFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterCond
                                      stateAfterCond =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals postBase
                                      (Block.toLocals returns post) oracle
                                      innerFuel cursorAfterBody
                                      bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hPostLower
                                simpa [hCond, hBodyLower', hBodyMode,
                                  hPostLower', hPostMode] using hRun
                    | cont =>
                        simp [hBody, hBodyMode] at hRun
                        cases hPost :
                            Block.runScopedWithGasOracle program returns
                              postBase post oracle fuel cursorAfterBody
                              bodyOutcome.state with
                        | error err =>
                            simp [hPost] at hRun
                        | ok postResult =>
                            rcases postResult with
                              ⟨postOutcome, cursorAfterPost⟩
                            rcases Block.runScopedWithGasOracle_toLocals_exists
                                program hPost with
                              ⟨postFuel, hPostLower⟩
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPost, hPostMode] at hRun
                                rcases Stmt.runForLoopWithGasOracle_toLocals_exists
                                    program hRun with
                                  ⟨loopFuel, hLoopLower⟩
                                let innerFuel := Nat.max bodyFuel
                                  (Nat.max postFuel loopFuel)
                                refine ⟨innerFuel + 1, ?_⟩
                                simp [hCond]
                                have hBodyLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterCond
                                      stateAfterCond =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals postBase
                                      (Block.toLocals returns post) oracle
                                      innerFuel cursorAfterBody
                                      bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_trans
                                        (Nat.le_max_left _ _)
                                        (Nat.le_max_right _ _)) hPostLower
                                have hLoopLower' :
                                    Locals.Direct.Stmt.runForLoopWithGasOracle
                                      program.toLocals loopCtx cond postBase
                                      (Block.toLocals returns post) bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterPost
                                      postOutcome.state =
                                      .ok (outcome, cursorFinal) :=
                                  Locals.Direct.Stmt.runForLoopWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_trans
                                        (Nat.le_max_right _ _)
                                        (Nat.le_max_right _ _)) hLoopLower
                                simp [hBodyLower', hBodyMode, hPostLower',
                                  hPostMode, hLoopLower']
                            | brk =>
                                simp [hPost, hPostMode, Structured.invalid]
                                  at hRun
                            | cont =>
                                simp [hPost, hPostMode, Structured.invalid]
                                  at hRun
                            | leave =>
                                simp [hPost, hPostMode] at hRun
                                let innerFuel := Nat.max bodyFuel postFuel
                                refine ⟨innerFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterCond
                                      stateAfterCond =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals postBase
                                      (Block.toLocals returns post) oracle
                                      innerFuel cursorAfterBody
                                      bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hPostLower
                                simpa [hCond, hBodyLower', hBodyMode,
                                  hPostLower', hPostMode] using hRun
                            | halt kind =>
                                simp [hPost, hPostMode] at hRun
                                let innerFuel := Nat.max bodyFuel postFuel
                                refine ⟨innerFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterCond
                                      stateAfterCond =
                                      .ok (bodyOutcome, cursorAfterBody) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Locals.Direct.Block.runScopedWithGasOracle
                                      program.toLocals postBase
                                      (Block.toLocals returns post) oracle
                                      innerFuel cursorAfterBody
                                      bodyOutcome.state =
                                      .ok (postOutcome, cursorAfterPost) :=
                                  Locals.Direct.Block.runScopedWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hPostLower
                                simpa [hCond, hBodyLower', hBodyMode,
                                  hPostLower', hPostMode] using hRun
                    | leave =>
                        refine ⟨bodyFuel + 1, ?_⟩
                        simpa [hCond, hBody, hBodyLower, hBodyMode] using hRun
                    | halt kind =>
                        refine ⟨bodyFuel + 1, ?_⟩
                        simpa [hCond, hBody, hBodyLower, hBodyMode] using hRun
  termination_by
    returns _loopCtx _cond _postBase _post _bodyBase _body fuel _state
      _outcome _oracle _cursor _cursorFinal _hRun => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runWithGasOracle_toLocals_exists (program : Program) :
      ∀ {returns : List Name} {ctx : Ctx} {fuel : Nat} {stmt : Stmt}
        {state : RunState} {outcome : Outcome} {runCtx : Ctx}
        {oracle : Structured.GasOracle} {cursor cursorFinal : Nat},
        Stmt.runWithGasOracle program returns ctx oracle fuel stmt cursor
          state =
          .ok (outcome, runCtx, cursorFinal) →
        ∃ lowerFuel,
          Locals.Direct.Block.runOpenWithGasOracle program.toLocals ctx oracle
            lowerFuel { stmts := Stmt.toLocals returns stmt } cursor state =
            .ok (outcome, runCtx, cursorFinal) := by
    intro returns ctx fuel stmt state outcome runCtx oracle cursor cursorFinal
      hRun
    cases stmt with
    | expr expr =>
        exact ⟨2, by
          simpa [Stmt.runWithGasOracle, Stmt.toLocals,
            Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle,
            Structured.Outcome.regular] using hRun⟩
    | let_ name value =>
        exact ⟨2, by
          simpa [Stmt.runWithGasOracle, Stmt.toLocals,
            Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle,
            Structured.Outcome.regular] using hRun⟩
    | assign name value =>
        unfold Stmt.runWithGasOracle Locals.Direct.Expr.runStateWithGasOracle
          at hRun
        cases hCode :
            Locals.Direct.Expr.runCodeWithGasOracle ctx 0 value oracle cursor
              state.evm with
        | error err =>
            simp [hCode] at hRun
        | ok codeResult =>
            rcases codeResult with ⟨evmAfterValue, cursorAfterValue⟩
            simp [hCode] at hRun
            cases hAssign :
                assignTopWithGasOracle ctx name oracle cursorAfterValue
                  (state.withEVM evmAfterValue) with
            | error err =>
                simp [hAssign] at hRun
            | ok assignResult =>
                rcases assignResult with
                  ⟨stateAfterAssign, cursorAfterAssign⟩
                have hTriple :
                    (Structured.Outcome.regular stateAfterAssign, ctx,
                        cursorAfterAssign) =
                      (outcome, runCtx, cursorFinal) := by
                  simpa [hAssign] using hRun
                injection hTriple with hOutcome hTail
                injection hTail with hCtx hCursor
                rw [← hOutcome, ← hCtx, ← hCursor]
                unfold assignTopWithGasOracle at hAssign
                cases hDepth : Locals.Layout.lookupDepth? name ctx.layout with
                | none =>
                    simp [hDepth, Structured.invalid] at hAssign
                | some depth =>
                    cases hSwapOp : Locals.StackOp.swap? depth with
                    | none =>
                        simp [hDepth, hSwapOp, Structured.invalid] at hAssign
                    | some swapOp =>
                        cases hSwap :
                            swapOp.stepWithGasOracle oracle cursorAfterValue
                              evmAfterValue with
                        | error err =>
                            simp [hDepth, hSwapOp, hSwap] at hAssign
                        | ok swapResult =>
                            rcases swapResult with
                              ⟨evmAfterSwap, cursorAfterSwap⟩
                            cases hPop :
                                Structured.BasicOp.pop.stepWithGasOracle oracle
                                  cursorAfterSwap evmAfterSwap with
                            | error err =>
                                simp [hDepth, hSwapOp, hSwap, hPop] at hAssign
                            | ok popResult =>
                                rcases popResult with
                                  ⟨evmAfterPop, cursorAfterPop⟩
                                simp [hDepth, hSwapOp, hSwap, hPop] at hAssign
                                rcases hAssign with ⟨hState, hCursorAssign⟩
                                cases hState
                                cases hCursorAssign
                                refine ⟨2, ?_⟩
                                simp [Stmt.toLocals,
                                  Locals.Direct.Block.runOpenWithGasOracle,
                                  Locals.Direct.Stmt.runWithGasOracle, hDepth,
                                  hSwapOp, hCode, hSwap, hPop,
                                  Structured.Outcome.regular]
    | block body =>
        unfold Stmt.runWithGasOracle at hRun
        cases hBody :
            Block.runScopedWithGasOracle program returns ctx body oracle fuel
              cursor state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyResult =>
            rcases bodyResult with ⟨bodyOutcome, cursorAfterBody⟩
            rcases Block.runScopedWithGasOracle_toLocals_exists program
                hBody with
              ⟨bodyFuel, hBodyLower⟩
            have hTriple :
                (bodyOutcome, ctx, cursorAfterBody) =
                  (outcome, runCtx, cursorFinal) := by
              simpa [hBody] using hRun
            injection hTriple with hOutcome hTail
            injection hTail with hCtx hCursor
            rw [← hOutcome, ← hCtx, ← hCursor]
            exact ⟨bodyFuel + 2, by
              simp [Stmt.toLocals, Locals.Direct.Block.runOpenWithGasOracle,
                Locals.Direct.Stmt.runWithGasOracle]
              have hBodyLower' :
                  Locals.Direct.Block.runScopedWithGasOracle program.toLocals
                    ctx (Block.toLocals returns body) oracle (bodyFuel + 1)
                    cursor state =
                    .ok (bodyOutcome, cursorAfterBody) :=
                Locals.Direct.Block.runScopedWithGasOracle_mono program.toLocals
                  (Nat.le_succ bodyFuel) hBodyLower
              cases hMode : bodyOutcome.mode with
              | regular =>
                  have hEq :
                      bodyOutcome =
                        Structured.Outcome.regular bodyOutcome.state :=
                    Outcome.eq_regular_of_mode hMode
                  rw [hEq] at hBodyLower' ⊢
                  simp [hBodyLower', Structured.Outcome.regular]
              | brk =>
                  simp [hBodyLower', hMode]
              | cont =>
                  simp [hBodyLower', hMode]
              | leave =>
                  simp [hBodyLower', hMode]
              | halt kind =>
                  simp [hBodyLower', hMode]⟩
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, Structured.invalid] at hRun
        | succ fuel =>
            unfold Stmt.runWithGasOracle at hRun
            cases hCond :
                Locals.Direct.Expr.runConditionWithGasOracle ctx cond oracle
                  cursor state with
            | error err =>
                simp [hCond] at hRun
            | ok condResult =>
                rcases condResult with
                  ⟨stateAfterCond, condTrue, cursorAfterCond⟩
                cases condTrue with
                | false =>
                    have hTriple :
                        (Structured.Outcome.regular stateAfterCond, ctx,
                            cursorAfterCond) =
                          (outcome, runCtx, cursorFinal) := by
                      simpa [hCond] using hRun
                    injection hTriple with hOutcome hTail
                    injection hTail with hCtx hCursor
                    rw [← hOutcome, ← hCtx, ← hCursor]
                    exact ⟨2, by
                      simp [Stmt.toLocals,
                        Locals.Direct.Block.runOpenWithGasOracle,
                        Locals.Direct.Stmt.runWithGasOracle, hCond,
                        Structured.Outcome.regular]⟩
                | true =>
                    simp [hCond] at hRun
                    cases hBody :
                        Block.runScopedWithGasOracle program returns ctx body
                          oracle fuel cursorAfterCond stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyResult =>
                        rcases bodyResult with
                          ⟨bodyOutcome, cursorAfterBody⟩
                        rcases Block.runScopedWithGasOracle_toLocals_exists
                            program hBody with
                          ⟨bodyFuel, hBodyLower⟩
                        have hTriple :
                            (bodyOutcome, ctx, cursorAfterBody) =
                              (outcome, runCtx, cursorFinal) := by
                          simpa [hBody] using hRun
                        injection hTriple with hOutcome hTail
                        injection hTail with hCtx hCursor
                        rw [← hOutcome, ← hCtx, ← hCursor]
                        refine ⟨bodyFuel + 2, ?_⟩
                        simp [Stmt.toLocals,
                          Locals.Direct.Block.runOpenWithGasOracle,
                          Locals.Direct.Stmt.runWithGasOracle, hCond]
                        have hBodyLower' :
                            Locals.Direct.Block.runScopedWithGasOracle
                              program.toLocals ctx
                              (Block.toLocals returns body) oracle bodyFuel
                              cursorAfterCond stateAfterCond =
                              .ok (bodyOutcome, cursorAfterBody) :=
                          hBodyLower
                        cases hMode : bodyOutcome.mode with
                        | regular =>
                            have hEq :
                                bodyOutcome =
                                  Structured.Outcome.regular
                                    bodyOutcome.state :=
                              Outcome.eq_regular_of_mode hMode
                            rw [hEq] at hBodyLower' ⊢
                            simp [hBodyLower', Structured.Outcome.regular]
                        | brk =>
                            simp [hBodyLower', hMode]
                        | cont =>
                            simp [hBodyLower', hMode]
                        | leave =>
                            simp [hBodyLower', hMode]
                        | halt kind =>
                            simp [hBodyLower', hMode]
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, Structured.invalid] at hRun
        | succ fuel =>
            unfold Stmt.runWithGasOracle at hRun
            cases hScrutinee :
                Locals.Direct.Expr.runStateWithGasOracle ctx scrutinee oracle
                  cursor state with
            | error err =>
                simp [hScrutinee] at hRun
            | ok scrutineeResult =>
                rcases scrutineeResult with
                  ⟨stateAfterScrutinee, cursorAfterScrutinee⟩
                cases hPop : stateAfterScrutinee.evm.stack.pop with
                | none =>
                    simp [hScrutinee, hPop, Structured.invalid] at hRun
                | some pair =>
                    rcases pair with ⟨stack, value⟩
                    let stateAfterPop :=
                      stateAfterScrutinee.withEVM
                        { stateAfterScrutinee.evm with stack := stack }
                    cases hSelected : Switch.select value cases defaultBody with
                    | none =>
                        have hTriple :
                            (Structured.Outcome.regular stateAfterPop, ctx,
                                cursorAfterScrutinee) =
                              (outcome, runCtx, cursorFinal) := by
                          simpa [hScrutinee, hPop, hSelected, stateAfterPop]
                            using hRun
                        injection hTriple with hOutcome hTail
                        injection hTail with hCtx hCursor
                        rw [← hOutcome, ← hCtx, ← hCursor]
                        exact ⟨2, by
                          simp [Stmt.toLocals,
                            Locals.Direct.Block.runOpenWithGasOracle,
                            Locals.Direct.Stmt.runWithGasOracle, hScrutinee,
                            hPop, Switch.select_toLocals, hSelected,
                            stateAfterPop, Structured.Outcome.regular]⟩
                    | some selected =>
                        simp [hScrutinee, hPop, hSelected, stateAfterPop]
                          at hRun
                        cases hBody :
                            Block.runScopedWithGasOracle program returns ctx
                              selected oracle fuel cursorAfterScrutinee
                              stateAfterPop with
                        | error err =>
                            have hBody' :
                                Block.runScopedWithGasOracle program returns ctx
                                  selected oracle fuel cursorAfterScrutinee
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) = .error err := by
                              simpa [stateAfterPop] using hBody
                            simp [hBody'] at hRun
                        | ok bodyResult =>
                            rcases bodyResult with
                              ⟨bodyOutcome, cursorAfterBody⟩
                            have hBody' :
                                Block.runScopedWithGasOracle program returns ctx
                                  selected oracle fuel cursorAfterScrutinee
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) =
                                  .ok (bodyOutcome, cursorAfterBody) := by
                              simpa [stateAfterPop] using hBody
                            rcases Block.runScopedWithGasOracle_toLocals_exists
                                program hBody with
                              ⟨bodyFuel, hBodyLower⟩
                            have hTriple :
                                (bodyOutcome, ctx, cursorAfterBody) =
                                  (outcome, runCtx, cursorFinal) := by
                              simpa [hBody'] using hRun
                            injection hTriple with hOutcome hTail
                            injection hTail with hCtx hCursor
                            rw [← hOutcome, ← hCtx, ← hCursor]
                            refine ⟨bodyFuel + 2, ?_⟩
                            simp [Stmt.toLocals,
                              Locals.Direct.Block.runOpenWithGasOracle,
                              Locals.Direct.Stmt.runWithGasOracle, hScrutinee,
                              hPop, Switch.select_toLocals, hSelected]
                            have hBodyLowerExplicit :
                                Locals.Direct.Block.runScopedWithGasOracle
                                  program.toLocals ctx
                                  (Block.toLocals returns selected) oracle
                                  bodyFuel cursorAfterScrutinee
                                  (stateAfterScrutinee.withEVM
                                    { stateAfterScrutinee.evm with
                                      stack := stack }) =
                                  .ok (bodyOutcome, cursorAfterBody) := by
                              simpa [stateAfterPop] using hBodyLower
                            cases hMode : bodyOutcome.mode with
                            | regular =>
                                have hEq :
                                    bodyOutcome =
                                      Structured.Outcome.regular
                                        bodyOutcome.state :=
                                  Outcome.eq_regular_of_mode hMode
                                rw [hEq] at hBodyLowerExplicit ⊢
                                simp [hBodyLowerExplicit,
                                  Structured.Outcome.regular]
                            | brk =>
                                simp [hBodyLowerExplicit, hMode]
                            | cont =>
                                simp [hBodyLowerExplicit, hMode]
                            | leave =>
                                simp [hBodyLowerExplicit, hMode]
                            | halt kind =>
                                simp [hBodyLowerExplicit, hMode]
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, Structured.invalid] at hRun
        | succ fuel =>
            unfold Stmt.runWithGasOracle at hRun
            let initBase := ctx.withoutLoopControl
            cases hInit :
                Block.runOpenWithGasOracle program returns initBase oracle fuel
                  init cursor state with
            | error err =>
                simp [initBase, hInit] at hRun
            | ok initResult =>
                rcases initResult with
                  ⟨initOutcome, initCtx, cursorAfterInit⟩
                rcases Block.runOpenWithGasOracle_toLocals_exists program
                    hInit with
                  ⟨initFuel, hInitLower⟩
                cases hInitMode : initOutcome.mode with
                | regular =>
                    simp [initBase, hInit, hInitMode] at hRun
                    have hInitLowerRegular :
                        Locals.Direct.Block.runOpenWithGasOracle
                          program.toLocals initBase oracle initFuel
                          (Block.toLocals returns init) cursor state =
                          .ok (Structured.Outcome.regular initOutcome.state,
                            initCtx, cursorAfterInit) := by
                      have hEq :
                          initOutcome =
                            Structured.Outcome.regular initOutcome.state :=
                        Outcome.eq_regular_of_mode hInitMode
                      rw [hEq] at hInitLower
                      exact hInitLower
                    let postBase := initCtx.withoutLoopControl
                    let bodyBase :=
                      initCtx.withLoopControl initCtx.layout.length
                    cases hLoop :
                        Stmt.runForLoopWithGasOracle program returns initCtx
                          cond postBase post bodyBase body oracle fuel
                          cursorAfterInit initOutcome.state with
                    | error err =>
                        simp [postBase, bodyBase, hLoop] at hRun
                    | ok loopResult =>
                        rcases loopResult with
                          ⟨loopOutcome, cursorAfterLoop⟩
                        rcases Stmt.runForLoopWithGasOracle_toLocals_exists
                            program hLoop with
                          ⟨loopFuel, hLoopLower⟩
                        cases hLoopMode : loopOutcome.mode with
                        | regular =>
                            simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                            cases hCleanup :
                                Locals.Direct.Ctx.runCleanupToWithGasOracle
                                  initCtx ctx.layout.length oracle
                                  cursorAfterLoop loopOutcome.state with
                            | error err =>
                                simp [hCleanup] at hRun
                            | ok cleanupResult =>
                                rcases cleanupResult with
                                  ⟨stateAfterCleanup, cursorAfterCleanup⟩
                                have hTriple :
                                    (Structured.Outcome.regular
                                        stateAfterCleanup, ctx,
                                      cursorAfterCleanup) =
                                      (outcome, runCtx, cursorFinal) := by
                                  simpa [hCleanup] using hRun
                                injection hTriple with hOutcome hTail
                                injection hTail with hCtx hCursor
                                rw [← hOutcome, ← hCtx, ← hCursor]
                                let innerFuel := Nat.max initFuel loopFuel
                                refine ⟨innerFuel + 2, ?_⟩
                                simp [Stmt.toLocals,
                                  Locals.Direct.Block.runOpenWithGasOracle,
                                  Locals.Direct.Stmt.runWithGasOracle,
                                  initBase]
                                have hInitLower' :
                                    Locals.Direct.Block.runOpenWithGasOracle
                                      program.toLocals initBase oracle
                                      innerFuel (Block.toLocals returns init)
                                      cursor state =
                                      .ok (Structured.Outcome.regular
                                        initOutcome.state, initCtx,
                                        cursorAfterInit) :=
                                  Locals.Direct.Block.runOpenWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_left _ _)
                                    hInitLowerRegular
                                have hLoopLower' :
                                    Locals.Direct.Stmt.runForLoopWithGasOracle
                                      program.toLocals initCtx cond postBase
                                      (Block.toLocals returns post) bodyBase
                                      (Block.toLocals returns body) oracle
                                      innerFuel cursorAfterInit
                                      initOutcome.state =
                                      .ok (loopOutcome, cursorAfterLoop) :=
                                  Locals.Direct.Stmt.runForLoopWithGasOracle_mono
                                    program.toLocals (by
                                      dsimp [innerFuel]
                                      exact Nat.le_max_right _ _) hLoopLower
                                simpa [hInitLower', hInitMode, initBase,
                                  postBase, bodyBase, hLoopLower', hLoopMode,
                                  hCleanup, Structured.Outcome.regular]
                        | brk =>
                            simp [postBase, bodyBase, hLoop, hLoopMode,
                              Structured.invalid] at hRun
                        | cont =>
                            simp [postBase, bodyBase, hLoop, hLoopMode,
                              Structured.invalid] at hRun
                        | leave =>
                            simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                            have hTriple :
                                (loopOutcome, ctx, cursorAfterLoop) =
                                  (outcome, runCtx, cursorFinal) := by
                              simpa using hRun
                            injection hTriple with hOutcome hTail
                            injection hTail with hCtx hCursor
                            rw [← hOutcome, ← hCtx, ← hCursor]
                            let innerFuel := Nat.max initFuel loopFuel
                            refine ⟨innerFuel + 2, ?_⟩
                            simp [Stmt.toLocals,
                              Locals.Direct.Block.runOpenWithGasOracle,
                              Locals.Direct.Stmt.runWithGasOracle, initBase]
                            have hInitLower' :
                                Locals.Direct.Block.runOpenWithGasOracle
                                  program.toLocals initBase oracle innerFuel
                                  (Block.toLocals returns init) cursor state =
                                  .ok (Structured.Outcome.regular
                                    initOutcome.state, initCtx,
                                    cursorAfterInit) :=
                              Locals.Direct.Block.runOpenWithGasOracle_mono
                                program.toLocals (by
                                  dsimp [innerFuel]
                                  exact Nat.le_max_left _ _) hInitLowerRegular
                            have hLoopLower' :
                                Locals.Direct.Stmt.runForLoopWithGasOracle
                                  program.toLocals initCtx cond postBase
                                  (Block.toLocals returns post) bodyBase
                                  (Block.toLocals returns body) oracle
                                  innerFuel cursorAfterInit
                                  initOutcome.state =
                                  .ok (loopOutcome, cursorAfterLoop) :=
                              Locals.Direct.Stmt.runForLoopWithGasOracle_mono
                                program.toLocals (by
                                  dsimp [innerFuel]
                                  exact Nat.le_max_right _ _) hLoopLower
                            simpa [hInitLower', hInitMode, initBase, postBase,
                              bodyBase, hLoopLower', hLoopMode]
                        | halt kind =>
                            simp [postBase, bodyBase, hLoop, hLoopMode] at hRun
                            have hTriple :
                                (loopOutcome, ctx, cursorAfterLoop) =
                                  (outcome, runCtx, cursorFinal) := by
                              simpa using hRun
                            injection hTriple with hOutcome hTail
                            injection hTail with hCtx hCursor
                            rw [← hOutcome, ← hCtx, ← hCursor]
                            let innerFuel := Nat.max initFuel loopFuel
                            refine ⟨innerFuel + 2, ?_⟩
                            simp [Stmt.toLocals,
                              Locals.Direct.Block.runOpenWithGasOracle,
                              Locals.Direct.Stmt.runWithGasOracle, initBase]
                            have hInitLower' :
                                Locals.Direct.Block.runOpenWithGasOracle
                                  program.toLocals initBase oracle innerFuel
                                  (Block.toLocals returns init) cursor state =
                                  .ok (Structured.Outcome.regular
                                    initOutcome.state, initCtx,
                                    cursorAfterInit) :=
                              Locals.Direct.Block.runOpenWithGasOracle_mono
                                program.toLocals (by
                                  dsimp [innerFuel]
                                  exact Nat.le_max_left _ _) hInitLowerRegular
                            have hLoopLower' :
                                Locals.Direct.Stmt.runForLoopWithGasOracle
                                  program.toLocals initCtx cond postBase
                                  (Block.toLocals returns post) bodyBase
                                  (Block.toLocals returns body) oracle
                                  innerFuel cursorAfterInit
                                  initOutcome.state =
                                  .ok (loopOutcome, cursorAfterLoop) :=
                              Locals.Direct.Stmt.runForLoopWithGasOracle_mono
                                program.toLocals (by
                                  dsimp [innerFuel]
                                  exact Nat.le_max_right _ _) hLoopLower
                            simpa [hInitLower', hInitMode, initBase, postBase,
                              bodyBase, hLoopLower', hLoopMode]
                | brk =>
                    simp [initBase, hInit, hInitMode, Structured.invalid]
                      at hRun
                | cont =>
                    simp [initBase, hInit, hInitMode, Structured.invalid]
                      at hRun
                | leave =>
                    simp [initBase, hInit, hInitMode] at hRun
                    have hTriple :
                        (initOutcome, ctx, cursorAfterInit) =
                          (outcome, runCtx, cursorFinal) := by
                      simpa using hRun
                    injection hTriple with hOutcome hTail
                    injection hTail with hCtx hCursor
                    rw [← hOutcome, ← hCtx, ← hCursor]
                    have hNonregular : initOutcome.mode ≠ .regular := by
                      simp [hInitMode]
                    refine ⟨initFuel + 2, ?_⟩
                    simp [Stmt.toLocals,
                      Locals.Direct.Block.runOpenWithGasOracle,
                      Locals.Direct.Stmt.runWithGasOracle, initBase]
                    simpa [initBase, hInitLower, hInitMode]
                | halt kind =>
                    simp [initBase, hInit, hInitMode] at hRun
                    have hTriple :
                        (initOutcome, ctx, cursorAfterInit) =
                          (outcome, runCtx, cursorFinal) := by
                      simpa using hRun
                    injection hTriple with hOutcome hTail
                    injection hTail with hCtx hCursor
                    rw [← hOutcome, ← hCtx, ← hCursor]
                    have hNonregular : initOutcome.mode ≠ .regular := by
                      simp [hInitMode]
                    refine ⟨initFuel + 2, ?_⟩
                    simp [Stmt.toLocals,
                      Locals.Direct.Block.runOpenWithGasOracle,
                      Locals.Direct.Stmt.runWithGasOracle, initBase]
                    simpa [initBase, hInitLower, hInitMode]
    | terminal kind =>
        exact ⟨1, by
          simpa [Stmt.runWithGasOracle, Stmt.toLocals,
            Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle, Structured.Outcome.halt]
            using hRun⟩
    | terminalArgs kind args =>
        exact ⟨1, by
          simpa [Stmt.runWithGasOracle, Stmt.toLocals,
            Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle, Structured.Outcome.halt]
            using hRun⟩
    | brk =>
        exact ⟨1, by
          simpa [Stmt.runWithGasOracle, Stmt.toLocals,
            Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle] using hRun⟩
    | cont =>
        exact ⟨1, by
          simpa [Stmt.runWithGasOracle, Stmt.toLocals,
            Locals.Direct.Block.runOpenWithGasOracle,
            Locals.Direct.Stmt.runWithGasOracle] using hRun⟩
    | leave =>
        unfold Stmt.runWithGasOracle at hRun
        cases hPush : pushReturnsWithGasOracle ctx returns oracle cursor state with
        | error err =>
            simp [hPush] at hRun
        | ok pushResult =>
            rcases pushResult with ⟨stateAfterReturns, cursorAfterReturns⟩
            rcases Lower.pushReturnsWithGasOracle_runOpen_exists program ctx
                hPush with
              ⟨pushFuel, hPushLower⟩
            cases hTarget : ctx.leaveDepth? with
            | none =>
                simp [hPush, hTarget, Structured.invalid] at hRun
            | some target =>
                cases hCleanup :
                    Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle ctx
                      ctx.leaveRetc target oracle cursorAfterReturns
                      stateAfterReturns with
                | error err =>
                    simp [hPush, hTarget, hCleanup] at hRun
                | ok cleanupResult =>
                    rcases cleanupResult with
                      ⟨stateAfterCleanup, cursorAfterCleanup⟩
                    cases hReturns : stateAfterCleanup.returns with
                    | nil =>
                        simp [hPush, hTarget, hCleanup, hReturns,
                          Structured.invalid] at hRun
                    | cons ret rest =>
                        have hTriple :
                            (Structured.Outcome.leave stateAfterCleanup, ctx,
                                cursorAfterCleanup) =
                              (outcome, runCtx, cursorFinal) := by
                          simpa [hPush, hTarget, hCleanup, hReturns] using hRun
                        injection hTriple with hOutcome hTail
                        injection hTail with hCtx hCursor
                        rw [← hOutcome, ← hCtx, ← hCursor]
                        rcases
                          Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                            program.toLocals
                            (Lower.pushReturns returns)
                            [Locals.Stmt.leave]
                            ctx ctx state stateAfterReturns
                            (Structured.Outcome.leave stateAfterCleanup) ctx
                            oracle cursor cursorAfterReturns
                            cursorAfterCleanup
                            ⟨pushFuel, hPushLower⟩
                            ⟨1, by
                              simp [Locals.Direct.Block.runOpenWithGasOracle,
                                Locals.Direct.Stmt.runWithGasOracle, hTarget,
                                hCleanup, hReturns,
                                Structured.Outcome.leave]⟩ with
                          ⟨lowerFuel, hLower⟩
                        exact ⟨lowerFuel, by
                          simpa [Stmt.toLocals, List.append_assoc] using
                            hLower⟩
    | call targets functionName args =>
        cases fuel with
        | zero =>
            simp [Stmt.runWithGasOracle, Structured.invalid] at hRun
        | succ fuel =>
            unfold Stmt.runWithGasOracle at hRun
            cases hArgs :
                evalArgsWithGasOracle ctx args oracle cursor state with
            | error err =>
                simp [hArgs] at hRun
            | ok argsResult =>
                rcases argsResult with ⟨stateAfterArgs, cursorAfterArgs⟩
                rcases Lower.evalArgsWithGasOracle_runOpen_exists program ctx
                    hArgs with
                  ⟨argsFuel, hArgsLower⟩
                cases hLookup :
                    FunList.find? functionName program.functions with
                | none =>
                    simp [hArgs, hLookup, Structured.invalid] at hRun
                | some fn =>
                    have hLowerLookup :=
                      FunList.lookup_toLocals (name := functionName)
                        (functions := program.functions) (fn := fn) hLookup
                    have hLowerLookup' :
                        Locals.Direct.ProcList.lookup? functionName
                            program.toLocals.procs =
                          some fn.toLocalsProc := by
                      simpa [Program.toLocals] using hLowerLookup
                    cases hSplit :
                        Structured.StackFrame.splitArgs? fn.params.length
                          stateAfterArgs.evm.stack with
                    | none =>
                        simp [hArgs, hLookup, hSplit, Structured.invalid]
                          at hRun
                    | some split =>
                        rcases split with ⟨argStack, callerStack⟩
                        let callState :=
                          (stateAfterArgs.withEVM
                            { stateAfterArgs.evm with stack := argStack })
                            |>.pushReturn callerStack fn.returns.length
                        cases hBody :
                            FunDef.runBodyWithGasOracle program fn oracle fuel
                              cursorAfterArgs callState with
                        | error err =>
                            simp [hArgs, hLookup, hSplit, callState, hBody]
                              at hRun
                        | ok bodyResult =>
                            rcases bodyResult with
                              ⟨callOutcome, cursorAfterBody⟩
                            rcases
                              FunDef.runBodyWithGasOracle_toLocals_open_exists
                                program hBody with
                              ⟨bodyFuel, lowerBodyOutcome, lowerBodyCtx,
                                cursorAfterOpen, hBodyLowerOpen, hBodyRel⟩
                            have hBodyLowerOpen' :
                                Locals.Direct.Block.runOpenWithGasOracle
                                  program.toLocals
                                  (Locals.Ctx.procEntryWithLayoutAndRetc
                                    fn.params.reverse fn.returns.length)
                                  oracle bodyFuel
                                  {
                                    stmts :=
                                      Lower.initReturns fn.returns ++
                                        (StmtList.toLocals fn.returns
                                          fn.body.stmts ++
                                          Lower.pushReturns fn.returns) }
                                  cursorAfterArgs
                                  ((stateAfterArgs.withEVM
                                    { stateAfterArgs.evm with
                                      stack := argStack })
                                    |>.pushReturn callerStack
                                      fn.returns.length) =
                                  .ok (lowerBodyOutcome, lowerBodyCtx,
                                    cursorAfterOpen) := by
                              simpa [FunDef.toLocalsProc, callState] using
                                hBodyLowerOpen
                            cases hBodyMode : callOutcome.mode with
                            | regular =>
                                simp [hArgs, hLookup, hSplit, callState, hBody,
                                  hBodyMode] at hRun
                                cases hPopRet : callOutcome.state.popReturn? with
                                | none =>
                                    simp [hPopRet, Structured.invalid] at hRun
                                | some retPair =>
                                    rcases retPair with ⟨frame, returned⟩
                                    cases hAttach :
                                        Structured.StackFrame.attachReturns?
                                          frame callOutcome.state.evm.stack with
                                    | none =>
                                        simp [hPopRet, hAttach,
                                          Structured.invalid] at hRun
                                    | some stack =>
                                        let stateWithReturns :=
                                          returned.withEVM
                                            { callOutcome.state.evm with
                                              stack := stack }
                                        cases hAssign :
                                            assignReturnedTopsWithGasOracle ctx
                                              targets.reverse oracle
                                              cursorAfterBody
                                              stateWithReturns with
                                        | error err =>
                                            simp [hPopRet, hAttach,
                                              stateWithReturns, hAssign] at hRun
                                        | ok assignResult =>
                                            rcases assignResult with
                                              ⟨stateAfterAssign,
                                                cursorAfterAssign⟩
                                            have hTriple :
                                                (Structured.Outcome.regular
                                                    stateAfterAssign, ctx,
                                                  cursorAfterAssign) =
                                                  (outcome, runCtx,
                                                    cursorFinal) := by
                                              simpa [hPopRet, hAttach,
                                                stateWithReturns, hAssign]
                                                using hRun
                                            injection hTriple with hOutcome hTail
                                            injection hTail with hCtx hCursor
                                            rw [← hOutcome, ← hCtx, ← hCursor]
                                            rcases
                                              Lower.assignReturnedTopsWithGasOracle_runOpen_exists
                                                program ctx hAssign with
                                              ⟨assignFuel, hAssignLower⟩
                                            let callFuel := bodyFuel + 2
                                            have hCallLower :
                                                Locals.Direct.Block.runOpenWithGasOracle
                                                  program.toLocals ctx oracle
                                                  callFuel
                                                  { stmts := [Locals.Stmt.call
                                                    functionName] }
                                                  cursorAfterArgs stateAfterArgs =
                                                  .ok (Structured.Outcome.regular
                                                    stateWithReturns, ctx,
                                                    cursorAfterBody) := by
                                                unfold callFuel
                                                simp [Locals.Direct.Block.runOpenWithGasOracle,
                                                  Locals.Direct.Stmt.runWithGasOracle,
                                                  hLowerLookup',
                                                  FunDef.toLocalsProc, hSplit,
                                                  callState]
                                                rw [hBodyLowerOpen']
                                                cases hLowerMode :
                                                    lowerBodyOutcome.mode with
                                                | regular =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode] at hBodyRel
                                                    cases hCleanup :
                                                        Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle
                                                          lowerBodyCtx
                                                          fn.returns.length 0
                                                          oracle cursorAfterOpen
                                                          lowerBodyOutcome.state with
                                                    | error err =>
                                                        simp [hCleanup] at hBodyRel
                                                    | ok cleanupResult =>
                                                        rcases cleanupResult with
                                                          ⟨cleaned,
                                                            cursorAfterCleanup⟩
                                                        have hEq :
                                                            (Structured.Outcome.regular
                                                                cleaned,
                                                              cursorAfterCleanup) =
                                                              (callOutcome,
                                                                cursorAfterBody) := by
                                                          simpa [hCleanup,
                                                            Structured.Outcome.regular]
                                                            using hBodyRel
                                                        injection hEq with
                                                          hOutcomeEq hCursorEq
                                                        cases hOutcomeEq
                                                        cases hCursorEq
                                                        have hPopRetClean :
                                                            cleaned.popReturn? =
                                                              some (frame,
                                                                returned) := by
                                                          simpa [Structured.Outcome.regular]
                                                            using hPopRet
                                                        have hAttachClean :
                                                            Structured.StackFrame.attachReturns?
                                                              frame
                                                              cleaned.evm.stack =
                                                              some stack := by
                                                          simpa [Structured.Outcome.regular]
                                                            using hAttach
                                                        simp [hLowerMode,
                                                          hCleanup,
                                                          hPopRetClean,
                                                          hAttachClean,
                                                          stateWithReturns,
                                                          Structured.Outcome.regular]
                                                | brk =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode,
                                                      Structured.invalid] at hBodyRel
                                                | cont =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode,
                                                      Structured.invalid] at hBodyRel
                                                | leave =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode] at hBodyRel
                                                    have hEq :
                                                        (lowerBodyOutcome,
                                                          cursorAfterOpen) =
                                                          (callOutcome,
                                                            cursorAfterBody) := by
                                                      simpa using hBodyRel
                                                    injection hEq with
                                                      hOutcomeEq hCursorEq
                                                    rw [hOutcomeEq] at hLowerMode
                                                    simp [hLowerMode] at hBodyMode
                                                | halt lowerKind =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode] at hBodyRel
                                                    have hEq :
                                                        (lowerBodyOutcome,
                                                          cursorAfterOpen) =
                                                          (callOutcome,
                                                            cursorAfterBody) := by
                                                      simpa using hBodyRel
                                                    injection hEq with
                                                      hOutcomeEq hCursorEq
                                                    rw [hOutcomeEq] at hLowerMode
                                                    simp [hLowerMode] at hBodyMode
                                            rcases
                                              Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                                                program.toLocals
                                                (Lower.evalArgs args)
                                                [Locals.Stmt.call functionName]
                                                ctx ctx state stateAfterArgs
                                                (Structured.Outcome.regular
                                                  stateWithReturns) ctx oracle
                                                cursor cursorAfterArgs
                                                cursorAfterBody
                                                ⟨argsFuel, hArgsLower⟩
                                                ⟨callFuel, hCallLower⟩ with
                                              ⟨argsCallFuel, hArgsCallLower⟩
                                            rcases
                                              Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                                                program.toLocals
                                                (Lower.evalArgs args ++
                                                  [Locals.Stmt.call functionName])
                                                (Lower.assignReturnedTops targets)
                                                ctx ctx state stateWithReturns
                                                (Structured.Outcome.regular
                                                  stateAfterAssign) ctx oracle
                                                cursor cursorAfterBody
                                                cursorAfterAssign
                                                ⟨argsCallFuel, by
                                                  simpa [List.append_assoc]
                                                    using hArgsCallLower⟩
                                                ⟨assignFuel, by
                                                  simpa [Lower.assignReturnedTops]
                                                    using hAssignLower⟩ with
                                              ⟨lowerFuel, hLower⟩
                                            exact ⟨lowerFuel, by
                                              simpa [Stmt.toLocals,
                                                List.append_assoc,
                                                Lower.assignReturnedTops] using
                                                hLower⟩
                            | leave =>
                                simp [hArgs, hLookup, hSplit, callState, hBody,
                                  hBodyMode] at hRun
                                cases hPopRet : callOutcome.state.popReturn? with
                                | none =>
                                    simp [hPopRet, Structured.invalid] at hRun
                                | some retPair =>
                                    rcases retPair with ⟨frame, returned⟩
                                    cases hAttach :
                                        Structured.StackFrame.attachReturns?
                                          frame callOutcome.state.evm.stack with
                                    | none =>
                                        simp [hPopRet, hAttach,
                                          Structured.invalid] at hRun
                                    | some stack =>
                                        let stateWithReturns :=
                                          returned.withEVM
                                            { callOutcome.state.evm with
                                              stack := stack }
                                        cases hAssign :
                                            assignReturnedTopsWithGasOracle ctx
                                              targets.reverse oracle
                                              cursorAfterBody
                                              stateWithReturns with
                                        | error err =>
                                            simp [hPopRet, hAttach,
                                              stateWithReturns, hAssign] at hRun
                                        | ok assignResult =>
                                            rcases assignResult with
                                              ⟨stateAfterAssign,
                                                cursorAfterAssign⟩
                                            have hTriple :
                                                (Structured.Outcome.regular
                                                    stateAfterAssign, ctx,
                                                  cursorAfterAssign) =
                                                  (outcome, runCtx,
                                                    cursorFinal) := by
                                              simpa [hPopRet, hAttach,
                                                stateWithReturns, hAssign]
                                                using hRun
                                            injection hTriple with hOutcome hTail
                                            injection hTail with hCtx hCursor
                                            rw [← hOutcome, ← hCtx, ← hCursor]
                                            rcases
                                              Lower.assignReturnedTopsWithGasOracle_runOpen_exists
                                                program ctx hAssign with
                                              ⟨assignFuel, hAssignLower⟩
                                            let callFuel := bodyFuel + 2
                                            have hCallLower :
                                                Locals.Direct.Block.runOpenWithGasOracle
                                                  program.toLocals ctx oracle
                                                  callFuel
                                                  { stmts := [Locals.Stmt.call
                                                    functionName] }
                                                  cursorAfterArgs stateAfterArgs =
                                                  .ok (Structured.Outcome.regular
                                                    stateWithReturns, ctx,
                                                    cursorAfterBody) := by
                                                unfold callFuel
                                                simp [Locals.Direct.Block.runOpenWithGasOracle,
                                                  Locals.Direct.Stmt.runWithGasOracle,
                                                  hLowerLookup',
                                                  FunDef.toLocalsProc, hSplit,
                                                  callState]
                                                rw [hBodyLowerOpen']
                                                cases hLowerMode :
                                                    lowerBodyOutcome.mode with
                                                | regular =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode] at hBodyRel
                                                    cases hCleanup :
                                                        Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle
                                                          lowerBodyCtx
                                                          fn.returns.length 0
                                                          oracle cursorAfterOpen
                                                          lowerBodyOutcome.state with
                                                    | error err =>
                                                        simp [hCleanup] at hBodyRel
                                                    | ok cleanupResult =>
                                                        rcases cleanupResult with
                                                          ⟨cleaned,
                                                            cursorAfterCleanup⟩
                                                        have hEq :
                                                            (Structured.Outcome.regular
                                                                cleaned,
                                                              cursorAfterCleanup) =
                                                              (callOutcome,
                                                                cursorAfterBody) := by
                                                          simpa [hCleanup,
                                                            Structured.Outcome.regular]
                                                            using hBodyRel
                                                        injection hEq with
                                                          hOutcomeEq hCursorEq
                                                        rw [← hOutcomeEq] at hBodyMode
                                                        simp at hBodyMode
                                                | brk =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode,
                                                      Structured.invalid] at hBodyRel
                                                | cont =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode,
                                                      Structured.invalid] at hBodyRel
                                                | leave =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode] at hBodyRel
                                                    have hEq :
                                                        (lowerBodyOutcome,
                                                          cursorAfterOpen) =
                                                          (callOutcome,
                                                            cursorAfterBody) := by
                                                      simpa using hBodyRel
                                                    injection hEq with
                                                      hOutcomeEq hCursorEq
                                                    cases hOutcomeEq
                                                    cases hCursorEq
                                                    simp [hLowerMode, hPopRet,
                                                      hAttach, stateWithReturns,
                                                      Structured.Outcome.regular]
                                                | halt lowerKind =>
                                                    simp [FunDef.lowerBodyResultWithGasOracle,
                                                      hLowerMode] at hBodyRel
                                                    have hEq :
                                                        (lowerBodyOutcome,
                                                          cursorAfterOpen) =
                                                          (callOutcome,
                                                            cursorAfterBody) := by
                                                      simpa using hBodyRel
                                                    injection hEq with
                                                      hOutcomeEq hCursorEq
                                                    rw [hOutcomeEq] at hLowerMode
                                                    simp [hLowerMode] at hBodyMode
                                            rcases
                                              Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                                                program.toLocals
                                                (Lower.evalArgs args)
                                                [Locals.Stmt.call functionName]
                                                ctx ctx state stateAfterArgs
                                                (Structured.Outcome.regular
                                                  stateWithReturns) ctx oracle
                                                cursor cursorAfterArgs
                                                cursorAfterBody
                                                ⟨argsFuel, hArgsLower⟩
                                                ⟨callFuel, hCallLower⟩ with
                                              ⟨argsCallFuel, hArgsCallLower⟩
                                            rcases
                                              Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                                                program.toLocals
                                                (Lower.evalArgs args ++
                                                  [Locals.Stmt.call functionName])
                                                (Lower.assignReturnedTops targets)
                                                ctx ctx state stateWithReturns
                                                (Structured.Outcome.regular
                                                  stateAfterAssign) ctx oracle
                                                cursor cursorAfterBody
                                                cursorAfterAssign
                                                ⟨argsCallFuel, by
                                                  simpa [List.append_assoc]
                                                    using hArgsCallLower⟩
                                                ⟨assignFuel, by
                                                  simpa [Lower.assignReturnedTops]
                                                    using hAssignLower⟩ with
                                              ⟨lowerFuel, hLower⟩
                                            exact ⟨lowerFuel, by
                                              simpa [Stmt.toLocals,
                                                List.append_assoc,
                                                Lower.assignReturnedTops] using
                                                hLower⟩
                            | brk =>
                                simp [hArgs, hLookup, hSplit, callState, hBody,
                                  hBodyMode, Structured.invalid] at hRun
                            | cont =>
                                simp [hArgs, hLookup, hSplit, callState, hBody,
                                  hBodyMode, Structured.invalid] at hRun
                            | halt kind =>
                                simp [hArgs, hLookup, hSplit, callState, hBody,
                                  hBodyMode] at hRun
                                have hTriple :
                                    (Structured.Outcome.halt kind
                                        callOutcome.state, ctx,
                                      cursorAfterBody) =
                                      (outcome, runCtx, cursorFinal) := by
                                  simpa using hRun
                                injection hTriple with hOutcome hTail
                                injection hTail with hCtx hCursor
                                rw [← hOutcome, ← hCtx, ← hCursor]
                                let callFuel := bodyFuel + 2
                                have hCallLower :
                                    Locals.Direct.Block.runOpenWithGasOracle
                                      program.toLocals ctx oracle callFuel
                                      { stmts := [Locals.Stmt.call
                                        functionName] } cursorAfterArgs
                                      stateAfterArgs =
                                      .ok (Structured.Outcome.halt kind
                                        callOutcome.state, ctx,
                                        cursorAfterBody) := by
                                  unfold callFuel
                                  simp [Locals.Direct.Block.runOpenWithGasOracle,
                                    Locals.Direct.Stmt.runWithGasOracle,
                                    hLowerLookup', FunDef.toLocalsProc, hSplit,
                                    callState]
                                  rw [hBodyLowerOpen']
                                  cases hLowerMode : lowerBodyOutcome.mode with
                                  | regular =>
                                      simp [FunDef.lowerBodyResultWithGasOracle,
                                        hLowerMode] at hBodyRel
                                      cases hCleanup :
                                          Locals.Direct.Ctx.runCleanupToPreservingWithGasOracle
                                            lowerBodyCtx fn.returns.length 0
                                            oracle cursorAfterOpen
                                            lowerBodyOutcome.state with
                                      | error err =>
                                          simp [hCleanup] at hBodyRel
                                      | ok cleanupResult =>
                                          rcases cleanupResult with
                                            ⟨cleaned, cursorAfterCleanup⟩
                                          have hEq :
                                              (Structured.Outcome.regular
                                                  cleaned, cursorAfterCleanup) =
                                                (callOutcome,
                                                  cursorAfterBody) := by
                                            simpa [hCleanup,
                                              Structured.Outcome.regular]
                                              using hBodyRel
                                          injection hEq with hOutcomeEq hCursorEq
                                          rw [← hOutcomeEq] at hBodyMode
                                          simp at hBodyMode
                                  | brk =>
                                      simp [FunDef.lowerBodyResultWithGasOracle,
                                        hLowerMode, Structured.invalid]
                                        at hBodyRel
                                  | cont =>
                                      simp [FunDef.lowerBodyResultWithGasOracle,
                                        hLowerMode, Structured.invalid]
                                        at hBodyRel
                                  | leave =>
                                      simp [FunDef.lowerBodyResultWithGasOracle,
                                        hLowerMode] at hBodyRel
                                      have hEq :
                                          (lowerBodyOutcome, cursorAfterOpen) =
                                            (callOutcome, cursorAfterBody) := by
                                        simpa using hBodyRel
                                      injection hEq with hOutcomeEq hCursorEq
                                      rw [hOutcomeEq] at hLowerMode
                                      simp [hLowerMode] at hBodyMode
                                  | halt lowerKind =>
                                      simp [FunDef.lowerBodyResultWithGasOracle,
                                        hLowerMode] at hBodyRel
                                      have hEq :
                                          (lowerBodyOutcome, cursorAfterOpen) =
                                            (callOutcome, cursorAfterBody) := by
                                        simpa using hBodyRel
                                      injection hEq with hOutcomeEq hCursorEq
                                      cases hOutcomeEq
                                      have hKindEq : lowerKind = kind := by
                                        rw [hBodyMode] at hLowerMode
                                        cases hLowerMode
                                        rfl
                                      subst lowerKind
                                      cases hCursorEq
                                      simp [hLowerMode,
                                        Structured.Outcome.halt]
                                rcases
                                  Locals.Direct.Block.runOpenWithGasOracle_append_regular_exists
                                    program.toLocals
                                    (Lower.evalArgs args)
                                    [Locals.Stmt.call functionName]
                                    ctx ctx state stateAfterArgs
                                    (Structured.Outcome.halt kind
                                      callOutcome.state) ctx oracle cursor
                                    cursorAfterArgs cursorAfterBody
                                    ⟨argsFuel, hArgsLower⟩
                                    ⟨callFuel, hCallLower⟩ with
                                  ⟨argsCallFuel, hArgsCallLower⟩
                                have hNonregular :
                                    (Structured.Outcome.halt kind
                                      callOutcome.state).mode ≠ .regular := by
                                  simp [Structured.Outcome.halt]
                                rcases
                                  Locals.Direct.Block.runOpenWithGasOracle_append_nonregular_exists
                                    program.toLocals
                                    (Lower.evalArgs args ++
                                      [Locals.Stmt.call functionName])
                                    (Lower.assignReturnedTops targets)
                                    ctx state
                                    (Structured.Outcome.halt kind
                                      callOutcome.state) ctx oracle cursor
                                    cursorAfterBody
                                    ⟨argsCallFuel, by
                                      simpa [List.append_assoc] using
                                        hArgsCallLower⟩
                                    hNonregular with
                                  ⟨lowerFuel, hLower⟩
                                exact ⟨lowerFuel, by
                                  simpa [Stmt.toLocals, List.append_assoc,
                                    Lower.assignReturnedTops] using hLower⟩
  termination_by
    returns _ctx fuel stmt _state _outcome _runCtx _oracle _cursor
      _cursorFinal _hRun => (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

theorem runStateWithGasOracle_toLocals_exists {program : Program}
    {fuel : Nat} {state : RunState} {outcome : Outcome}
    {oracle : Structured.GasOracle} {cursor cursorFinal : Nat}
    (hRun :
      Program.runStateWithGasOracle fuel program oracle cursor state =
        .ok (outcome, cursorFinal)) :
    ∃ lowerFuel,
      Locals.Direct.Program.runStateWithGasOracle lowerFuel program.toLocals
          oracle cursor state =
        .ok (outcome, cursorFinal) := by
  exact Block.runScopedWithGasOracle_toLocals_exists program hRun

theorem runWithGasOracle_toLocals_exists {program : Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    {oracle : Structured.GasOracle} {cursor cursorFinal : Nat}
    (hRun :
      Program.runWithGasOracle fuel program oracle cursor initial =
        .ok (outcome, cursorFinal)) :
    ∃ lowerFuel,
      Locals.Program.runWithGasOracle lowerFuel program.toLocals oracle cursor
          initial =
        .ok (outcome, cursorFinal) := by
  exact runStateWithGasOracle_toLocals_exists hRun

end Program

end Direct

namespace Program

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
  rcases Direct.Program.runWithGasOracle_toLocals_exists
      (by simpa [Program.runWithGasOracle] using hRun) with
    ⟨lowerFuel, hLowerRun⟩
  have hLowerLocals :
      program.toLocals.toExpressions? = some lower := by
    simpa [Program.toExpressions?] using hLower
  exact
    Locals.Program.compile_preserves_withGasOracle
      (program := program.toLocals) (lower := lower) (asm := asm)
      hLowerLocals hCompile hInitialPc hLowerRun

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
  rcases Direct.Program.runWithGasOracle_toLocals_exists
      (by simpa [Program.runWithGasOracle] using hRun) with
    ⟨lowerFuel, hLowerRun⟩
  have hLowerLocals :
      program.toLocals.toExpressions? = some lower := by
    simpa [Program.toExpressions?] using hLower
  have hLocalsCompile :
      Locals.Program.compileCheckedWithGasOracle? program.toLocals = some asm := by
    unfold Locals.Program.compileCheckedWithGasOracle?
    simp [hLowerLocals, hLowerCompile]
  exact
    Locals.Program.compile_preserves_of_compileCheckedWithGasOracle
      hLocalsCompile hInitialPc hLowerRun

end Program

end Functions

end EvmCompiler
